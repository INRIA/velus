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

    type lexp =
    | Econst of const
    | Evar of ident * typ
    | Ewhen of lexp * ident * bool
    | Eunop of unop * lexp * typ
    | Ebinop of binop * lexp * lexp * typ

    type lexps = lexp list

    type cexp =
    | Emerge of ident * cexp * cexp
    | Eite of lexp * cexp * cexp
    | Eexp of lexp

    type equation =
    | EqDef of ident * clock * cexp
    | EqApp of idents * clock * ident * lexps
    | EqFby of ident * clock * const * lexp

    type node = {
      n_name : ident;
      n_in   : (ident * (typ * clock)) list;
      n_out  : (ident * (typ * clock)) list;
      n_vars : (ident * (typ * clock)) list;
      n_eqs  : equation list }

    type global = node list
  end

module PrintFun (NL: SYNTAX)
                (PrintOps : PRINT_OPS with type typ   = NL.typ
                                       and type const = NL.const
                                       and type unop  = NL.unop
                                       and type binop = NL.binop) :
  sig
    val print_fullclocks : bool ref
    val print_lexpr    : formatter -> NL.lexp -> unit
    val print_cexpr    : formatter -> NL.cexp -> unit
    val print_equation : formatter -> NL.equation -> unit
    val print_node     : Format.formatter -> NL.node -> unit
    val print_global   : Format.formatter -> NL.global -> unit
  end
  =
  struct
    let print_fullclocks = ref false

    let lprecedence = function
      | NL.Econst _ -> (16, NA)
      | NL.Evar _   -> (16, NA)
      | NL.Ewhen _  -> (12, LtoR) (* precedence of +/- *)
      | NL.Eunop  (op, _, _)    -> PrintOps.prec_unop op
      | NL.Ebinop (op, _, _, _) -> PrintOps.prec_binop op

    let cprecedence = function
      | NL.Emerge _ -> (5, LtoR) (* precedence of lor - 1 *)
      | NL.Eite _   -> (5, LtoR)
      | NL.Eexp _   -> (5, LtoR)

    let rec lexpr p (prec, e) =
      let (prec', assoc) = lprecedence e in
      let (prec1, prec2) =
        if assoc = LtoR
        then (prec', prec' + 1)
        else (prec' + 1, prec') in
      if prec' < prec
      then fprintf p "@[<hov 2>("
      else fprintf p "@[<hov 2>";
      begin match e with
      | NL.Econst c ->
          PrintOps.print_const p c
      | NL.Evar (id, _) ->
          fprintf p "%s" (extern_atom id)
      | NL.Ewhen (e, x, v) ->
          if v
          then fprintf p "%a when %s" lexpr (prec', e) (extern_atom x)
          else fprintf p "%a when not %s" lexpr (prec', e) (extern_atom x)
      | NL.Eunop  (op, e, ty) ->
          PrintOps.print_unop p op ty lexpr (prec', e)
      | NL.Ebinop (op, e1, e2, ty) ->
          PrintOps.print_binop p op ty lexpr (prec1, e1) (prec2, e2)
      end;
      if prec' < prec then fprintf p ")@]" else fprintf p "@]"

    let print_lexpr p e = lexpr p (0, e)

    let rec print_lexpr_list p (first, rl) =
      match rl with
      | [] -> ()
      | r :: rl ->
          if not first then fprintf p ",@ ";
          lexpr p (2, r);
          print_lexpr_list p (false, rl)

    let rec cexpr p (prec, e) =
      let (prec', assoc) = cprecedence e in
      if prec' < prec
      then fprintf p "@[<hov 2>("
      else fprintf p "@[<hov 2>";
      begin match e with
      | NL.Emerge (id, ce1, ce2) ->
          fprintf p "@[<hv 6>merge %s@ %a@ %a@]"
            (extern_atom id) cexpr (16, ce1) cexpr (16, ce2)
      | NL.Eite (e, ce1, ce2) ->
          fprintf p "@[<hv 0>if %a@ then %a@ else %a@]"
            lexpr (prec', e) cexpr (prec', ce1) cexpr (prec', ce2)
      | NL.Eexp e ->
          lexpr p (prec' + 1, e)
      end;
      if prec' < prec then fprintf p ")@]" else fprintf p "@]"

    let print_cexpr p e = cexpr p (0, e)

    let print_list print_ele p =
      let rec print first rl =
        match rl with
        | [] -> ()
        | r :: rl ->
            (if first
             then print_ele p r
             else fprintf p ",@;<1 0>%a" print_ele r);
            print false rl
      in
      print true

    let rec print_clock p ck =
      match ck with
      | NL.Cbase -> fprintf p "."
      | NL.Con (ck', x, b) ->
          fprintf p "%a %s %s"
            print_clock ck'
            (if b then "on" else "onot")
            (extern_atom x)

    let print_clock_decl p ck =
      match ck with
      | NL.Cbase -> ()
      | NL.Con (ck', x, b) ->
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

    let print_decl_list = print_list print_decl

    let print_ident p i = fprintf p "%s" (extern_atom i)

    let print_multiple_results p xs =
      match xs with
      | [x] -> print_ident p x
      | xs  -> fprintf p "(%a)" (print_list print_ident) xs

    let rec print_equation p eq =
      match eq with
      | NL.EqDef (x, ck, e) ->
          fprintf p "@[<hov 2>%s =@ %a;@]"
            (extern_atom x) print_cexpr e
      | NL.EqApp (xs, ck, f, es) ->
          fprintf p "@[<hov 2>%a =@ %s(@[<hv 0>%a@]);@]"
            print_multiple_results xs
            (extern_atom f)
            (print_list print_lexpr) es
      | NL.EqFby (x, ck, v0, e) ->
          fprintf p "@[<hov 2>%s =@ %a fby@ %a;@]"
            (extern_atom x) PrintOps.print_const v0 print_lexpr e

    let print_equations p =
      let rec print first eqs =
        match eqs with
        | [] -> ()
        | eq :: eqs ->
            (if first
             then print_equation p eq
             else fprintf p "@;%a" print_equation eq);
            print false eqs
      in
      print true

    let print_node p { NL.n_name = name;
                       NL.n_in   = inputs;
                       NL.n_out  = outputs;
                       NL.n_vars = locals;
                       NL.n_eqs  = eqs } =
      fprintf p "@[<v>";
      fprintf p "@[<hov 0>";
        fprintf p "@[<h>node %s (%a)@]@;"
          (extern_atom name)
          print_decl_list inputs;
        fprintf p "@[<h>returns (%a)@]@;"
          print_decl_list outputs;
      fprintf p "@]@;";
      if List.length locals > 0 then
        fprintf p "@[<h>var @[<hov 4>%a@];@]@;"
          print_decl_list locals;
      fprintf p "@[<v 2>let@;%a@;<0 -2>@]" print_equations (List.rev eqs);
      fprintf p "tel@]"

    let print_global p prog =
      fprintf p "@[<v 0>";
      List.iter (fprintf p "@;%a@;" print_node) prog;
      fprintf p "@]@."
  end

module SchedulerFun (NL: SYNTAX) :
  sig
    val schedule : NL.equation list -> BinNums.positive list
  end
  =
  struct

    let schedule eqs = []

  end

