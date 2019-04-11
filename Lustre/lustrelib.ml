(* *********************************************************************)
(*                    The Velus Lustre compiler                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

open Format
open Veluscommon

open BinNums
open BinPos
open FMapPositive

type ident = Common.ident
type idents = ident list

let extern_atom = Camlcoq.extern_atom

module type SYNTAX =
  sig
    type typ
    type const
    type unop
    type binop

    type clock =
    | Cbase
    | Con of clock * ident * bool

    type ckid =
    | Vidx of positive
    | Vnm  of ident

    type sclock =
    | Sbase
    | Son of sclock * ckid * bool

    type nclock =
    | Cstream of sclock
    | Cnamed  of ckid * sclock

    type ann = typ * nclock
    type lann = typ list * nclock

    type exp =
    | Econst of const
    | Evar   of ident * ann
    | Eunop  of unop * exp * ann
    | Ebinop of binop * exp * exp * ann
    | Efby   of exp list * exp list * ann list
    | Ewhen  of exp list * ident * bool * lann
    | Emerge of ident * exp list * exp list * lann
    | Eite   of exp * exp list * exp list * lann
    | Eapp   of ident * exp list * ann list

    type equation = idents * exp list

    type node = {
          n_name     : ident;
          n_hasstate : bool;
          n_in       : (ident * (typ * clock)) list;
          n_out      : (ident * (typ * clock)) list;
          n_vars     : (ident * (typ * clock)) list;
          n_eqs      : equation list;
        }

    type global = node list
  end

module PrintFun (L: SYNTAX)
                (PrintOps : PRINT_OPS with type typ   = L.typ
                                       and type const = L.const
                                       and type unop  = L.unop
                                       and type binop = L.binop) :
  sig
    val print_fullclocks : bool ref
    val print_appclocks  : bool ref

    val print_exp        : formatter -> L.exp -> unit
    val print_equation   : formatter -> L.equation -> unit
    val print_node       : formatter -> L.node -> unit
    val print_global     : formatter -> L.global -> unit
  end
  =
  struct
    let print_fullclocks = ref false
    let print_appclocks  = ref false

    let precedence = function
      | L.Econst _ -> (16, NA)
      | L.Evar _   -> (16, NA)
      | L.Eunop  (op, _, _)    -> PrintOps.prec_unop op
      | L.Ebinop (op, _, _, _) -> PrintOps.prec_binop op
      | L.Efby _   -> (14, RtoL) (* higher than * / % *)
      | L.Ewhen _  -> (12, LtoR) (* precedence of + - *)
      | L.Emerge _ -> ( 5, LtoR) (* precedence of lor - 1 *)
      | L.Eite _   -> ( 5, LtoR)
      | L.Eapp _   -> ( 4, NA)

    let rec print_clock p ck =
      match ck with
      | L.Cbase -> fprintf p "."
      | L.Con (ck', x, b) ->
          fprintf p "%a %s %s"
            print_clock ck'
            (if b then "on" else "onot")
            (extern_atom x)

    let print_ckid p = function
      | L.Vidx i -> fprintf p "?c%d" (int_of_positive i)
      | L.Vnm x  -> pp_print_string p (extern_atom x)

    let rec print_sclock p sck =
      match sck with
      | L.Sbase -> fprintf p "."
      | L.Son (ck', cid, b) ->
          fprintf p "%a %s %a"
            print_sclock ck'
            (if b then "on" else "onot")
            print_ckid cid

    let print_nclock p = function
      | L.Cstream sck -> print_sclock p sck
      | L.Cnamed (cid, sck) ->
          fprintf p "(%a : @[<hov 2>%a@])" print_ckid cid print_sclock sck

    let print_ncks =
      pp_print_list ~pp_sep:(fun p () -> fprintf p " *@ ") print_nclock

    let rec exp prec p e =
      let (prec', assoc) = precedence e in
      let (prec1, prec2) =
        if assoc = LtoR
        then (prec', prec' + 1)
        else (prec' + 1, prec') in
      if prec' < prec
      then fprintf p "@[<hov 2>("
      else fprintf p "@[<hov 2>";
      begin match e with
      | L.Econst c ->
          PrintOps.print_const p c
      | L.Evar (id, _) ->
          fprintf p "%s" (extern_atom id)
      | L.Eunop  (op, e, (ty, _)) ->
          PrintOps.print_unop p op ty (exp prec') e
      | L.Ebinop (op, e1, e2, (ty, _)) ->
          PrintOps.print_binop p op ty (exp prec1) e1 (exp prec2) e2
      | L.Efby (e0s, es, _) ->
          fprintf p "%a fby@ %a" (exp_list prec1) e0s (exp_list prec2) es
      | L.Ewhen (e, x, v, _) ->
          if v
          then fprintf p "%a when %s" (exp_list prec') e (extern_atom x)
          else fprintf p "%a when not %s" (exp_list prec') e (extern_atom x)
      | L.Emerge (id, e1s, e2s, _) ->
          fprintf p "merge %s@ %a@ %a"
            (extern_atom id) (exp_list 16) e1s (exp_list 16) e2s
      | L.Eite (e, e1s, e2s, _) ->
          fprintf p "if %a@ then %a@ else %a"
            (exp 16) e (exp_list 16) e1s (exp_list 16) e2s
      | L.Eapp (f, es, anns) ->
          if !print_appclocks
          then fprintf p "%s@[<v 1>%a@ (* @[<hov>%a@] *)@]"
                 (extern_atom f) exp_arg_list es print_ncks (List.map snd anns)
          else fprintf p "%s%a" (extern_atom f) exp_arg_list es
      end;
      if prec' < prec then fprintf p ")@]" else fprintf p "@]"

    and exp_list prec p es =
      match es with
      | [e] -> exp prec p e
      | _   -> exp_arg_list p es

    and exp_arg_list p es =
      fprintf p "(@[<hv 0>%a@])"
        (pp_print_list ~pp_sep:(fun p () -> fprintf p ",@ ") (exp 0)) es

    let print_exp = exp 0

    let print_clock_decl p ck =
      match ck with
      | L.Cbase -> ()
      | L.Con (ck', x, b) ->
          if !print_fullclocks
          then fprintf p " :: @[<hov 3>%a@]" print_clock ck
          else fprintf p " when%s %s"
                (if b then "" else " not")
                (extern_atom x)

    let print_decl p (id, (ty, ck)) =
      fprintf p "%s@ : %a%a"
        (extern_atom id)
        PrintOps.print_typ ty
        print_clock_decl ck

    let print_decl_list =
      pp_print_list ~pp_sep:(fun p () -> fprintf p ",@ ") print_decl

    let print_ident p i = pp_print_string p (extern_atom i)

    let print_pattern p xs =
      match xs with
      | [x] -> print_ident p x
      | xs  ->
        fprintf p "(@[<hv 0>%a@])"
          (pp_print_list ~pp_sep:(fun p () -> fprintf p ",@ ") print_ident) xs

    let rec print_equation p (xs, es) =
      fprintf p "@[<hov 2>%a =@ %a;@]"
        print_pattern xs (exp_list 0) es

    let print_node p { L.n_name     = name;
                       L.n_hasstate = hasstate;
                       L.n_in       = inputs;
                       L.n_out      = outputs;
                       L.n_vars     = locals;
                       L.n_eqs      = eqs } =
      fprintf p "@[<v>";
      fprintf p "@[<hov 0>";
        fprintf p "@[<h>%s %s (%a)@]@;"
          (if hasstate then "node" else "fun")
          (extern_atom name)
          print_decl_list inputs;
        fprintf p "@[<h>returns (%a)@]@;"
          print_decl_list outputs;
      fprintf p "@]@;";
      if List.length locals > 0 then
        fprintf p "@[<h>var @[<hov 4>%a@];@]@;"
          print_decl_list locals;
      fprintf p "@[<v 2>let@;%a@;<0 -2>@]"
        (pp_print_list print_equation) (List.rev eqs);
      fprintf p "tel@]"

    let print_global p prog =
      fprintf p "@[<v 0>";
      List.iter (fprintf p "@;%a@;" print_node) (List.rev prog);
      fprintf p "@]@."
  end

