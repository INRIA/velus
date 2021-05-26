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
    type cconst
    type unop
    type binop
    type enumtag

    type clock =
    | Cbase
    | Con of clock * ident * (typ * enumtag)

    type nclock = clock * ident option

    type ann = typ * nclock
    type lann = typ list * nclock

    type exp =
    | Econst of cconst
    | Eenum of enumtag * typ
    | Evar   of ident * ann
    | Eunop  of unop * exp * ann
    | Ebinop of binop * exp * exp * ann
    | Efby   of exp list * exp list * exp list * ann list
    | Earrow of exp list * exp list * exp list * ann list
    | Ewhen  of exp list * ident * enumtag * lann
    | Emerge of (ident * typ) * exp list list * lann
    | Ecase  of exp * exp list option list * exp list * lann
    | Eapp   of ident * exp list * exp list * ann list

    type equation = idents * exp list

    type node = {
          n_name     : ident;
          n_hasstate : bool;
          n_in       : (ident * (typ * clock)) list;
          n_out      : (ident * (typ * clock)) list;
          n_vars     : (ident * (typ * clock)) list;
          n_eqs      : equation list;
        }

    type global = {
      enums: (ident * Datatypes.nat) list;
      nodes: node list
    }
  end

module PrintFun
    (PrintOps: PRINT_OPS)
    (L: SYNTAX with type typ     = PrintOps.typ
                and type cconst  = PrintOps.cconst
                and type unop    = PrintOps.unop
                and type binop   = PrintOps.binop
                and type enumtag = PrintOps.enumtag) :
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
      | L.Eenum _ -> (16, NA)
      | L.Evar _   -> (16, NA)
      | L.Eunop  (op, _, _)    -> PrintOps.prec_unop op
      | L.Ebinop (op, _, _, _) -> PrintOps.prec_binop op
      | L.Efby _   -> (14, RtoL) (* higher than * / % *)
      | L.Earrow _ -> (14, RtoL)
      | L.Ewhen _  -> (12, LtoR) (* precedence of + - *)
      | L.Emerge _ -> ( 5, LtoR) (* precedence of lor - 1 *)
      | L.Ecase _   -> ( 5, LtoR)
      | L.Eapp _   -> ( 4, NA)

    let print_ident p i = pp_print_string p (extern_atom i)

    let rec print_clock p ck =
      match ck with
      | L.Cbase -> fprintf p "."
      | L.Con (ck', x, (_, c)) ->
        fprintf p "%a on (%a=%a)"
          print_clock ck'
          print_ident x
          PrintOps.print_enumtag c

    let print_nclock p = function
      | (ck, None) -> print_clock p ck
      | (ck, Some cid) ->
         fprintf p "(%a : @[<hov 2>%a@])"
           print_ident cid
           print_clock ck

    let print_ncks =
      pp_print_list ~pp_sep:(fun p () -> fprintf p " *@ ") print_nclock

    let print_comma_list p =
      pp_print_list ~pp_sep:(fun p () -> fprintf p ",@ ") p

    let print_semicol_list p =
      pp_print_list ~pp_sep:(fun p () -> fprintf p ";@ ") p

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
        PrintOps.print_cconst p c
      | L.Eenum (c, _) ->
        PrintOps.print_enumtag p c
      | L.Evar (id, _) ->
        print_ident p id
      | L.Eunop  (op, e, (ty, _)) ->
        PrintOps.print_unop p op ty (exp prec') e
      | L.Ebinop (op, e1, e2, (ty, _)) ->
        PrintOps.print_binop p op ty (exp prec1) e1 (exp prec2) e2
      | L.Efby (e0s, es, [], _) ->
        fprintf p "%a fby@ %a" (exp_list prec1) e0s (exp_list prec2) es
      | L.Efby (e0s, es, er, _) ->
        fprintf p "reset@ %a fby@ %a every@ %a" (exp_list prec1) e0s (exp_list prec2) es (exp_list prec') er
      | L.Earrow (e0s, es, [], _) ->
        fprintf p "%a ->@ %a" (exp_list prec1) e0s (exp_list prec2) es
      | L.Earrow (e0s, es, er, _) ->
        fprintf p "reset@ %a ->@ %a every@ %a" (exp_list prec1) e0s (exp_list prec2) es (exp_list prec') er
      | L.Ewhen (e, x, c, _) ->
        fprintf p "%a when (%a=%a)"
          (exp_list prec') e
          print_ident x
          PrintOps.print_enumtag c
      | L.Emerge ((id, _), es, _) ->
        fprintf p "merge %a@ %a"
          print_ident id
          (PrintOps.print_branches exp_enclosed_list) (List.map (fun ce -> Some ce)es, None)
      | L.Ecase (e, es, d, _) ->
        fprintf p "case %a@ %a"
          (exp 16) e
          (PrintOps.print_branches exp_enclosed_list) (es, Some d)
      | L.Eapp (f, es, [], anns) ->
        if !print_appclocks
        then fprintf p "%a@[<v 1>%a@ (* @[<hov>%a@] *)@]"
            print_ident f
            exp_arg_list es
            print_ncks (List.map snd anns)
        else fprintf p "%a%a"
            print_ident f
            exp_arg_list es
      | L.Eapp (f, es, er, anns) ->
        if !print_appclocks
        then fprintf p "(restart@ %a@ every@ %a)@[<v 1>%a@ (* @[<hov>%a@] *)@]"
            print_ident f
            (exp_list prec') er
            exp_arg_list es
            print_ncks (List.map snd anns)
        else fprintf p "(restart@ %a@ every@ %a)%a"
            print_ident f
            (exp_list prec') er
            exp_arg_list es
      end;
      if prec' < prec then fprintf p ")@]" else fprintf p "@]"

    and exp_list prec p es =
      match es with
      | [e] -> exp prec p e
      | _   -> exp_arg_list p es

    and exp_arg_list p es =
      fprintf p "(@[<hv 0>%a@])"
        (print_comma_list (exp 0)) es

    and exp_enclosed_list p es =
      fprintf p "@[<hv 0>%a@]"
        (print_comma_list (exp 0)) es

    let print_exp = exp 0

    let print_clock_decl p ck =
      match ck with
      | L.Cbase -> ()
      | L.Con (ck', x, (_, c)) ->
        if !print_fullclocks
        then fprintf p " :: @[<hov 3>%a@]" print_clock ck
        else fprintf p " when (%a=%a)"
            print_ident x
            PrintOps.print_enumtag c

    let print_decl p (id, (ty, ck)) =
      fprintf p "%a@ : %a%a"
        print_ident id
        PrintOps.print_typ ty
        print_clock_decl ck

    let print_decl_list = print_semicol_list print_decl

    let print_pattern p xs =
      match xs with
      | [x] -> print_ident p x
      | xs  -> fprintf p "(@[<hv 0>%a@])"
                 (print_comma_list print_ident) xs

    let rec print_equation p (xs, es) =
      fprintf p "@[<hov 2>%a =@ %a;@]"
        print_pattern xs (exp_list 0) es

    let print_semicol_list_as name px p xs =
    if List.length xs > 0 then
      fprintf p "@[<h>%s @[<hov 4>%a@];@]@;"
        name
        (print_semicol_list px) xs

    let print_node p { L.n_name     = name;
                       L.n_hasstate = hasstate;
                       L.n_in       = inputs;
                       L.n_out      = outputs;
                       L.n_vars     = locals;
                       L.n_eqs      = eqs } =
      fprintf p "@[<v>\
                 @[<hov 0>\
                 @[<h>%s %a (%a)@]@;\
                 @[<h>returns (%a)@]@;\
                 @]@;\
                 %a\
                 @[<v 2>let@;%a@;<0 -2>@]\
                 tel@]"
        (if hasstate then "node" else "fun")
        print_ident name
        print_decl_list inputs
        print_decl_list outputs
        (print_semicol_list_as "var" print_decl) locals
        (pp_print_list print_equation) (List.rev eqs)

    let print_global p prog =
      fprintf p "@[<v 0>%a@]@."
        (pp_print_list ~pp_sep:(fun p () -> fprintf p "@;@;") print_node)
        (List.rev prog.L.nodes)
  end
