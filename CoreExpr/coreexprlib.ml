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

  end

module PrintFun (CE: SYNTAX)
                (PrintOps : PRINT_OPS with type typ   = CE.typ
                                       and type const = CE.const
                                       and type unop  = CE.unop
                                       and type binop = CE.binop) :
  sig
    val print_lexpr    : formatter -> CE.lexp -> unit
    val print_cexpr    : formatter -> CE.cexp -> unit
    val print_clock    : formatter -> CE.clock -> unit
    val print_list     : (formatter -> 'a -> unit) -> formatter -> 'a list -> unit
  end
  =
  struct

    let lprecedence = function
      | CE.Econst _ -> (16, NA)
      | CE.Evar _   -> (16, NA)
      | CE.Ewhen _  -> (12, LtoR) (* precedence of +/- *)
      | CE.Eunop  (op, _, _)    -> PrintOps.prec_unop op
      | CE.Ebinop (op, _, _, _) -> PrintOps.prec_binop op

    let cprecedence = function
      | CE.Emerge _ -> (5, LtoR) (* precedence of lor - 1 *)
      | CE.Eite _   -> (5, LtoR)
      | CE.Eexp _   -> (5, LtoR)

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
      | CE.Econst c ->
          PrintOps.print_const p c
      | CE.Evar (id, _) ->
          fprintf p "%s" (extern_atom id)
      | CE.Ewhen (e, x, v) ->
          if v
          then fprintf p "%a when %s" lexpr (prec', e) (extern_atom x)
          else fprintf p "%a when not %s" lexpr (prec', e) (extern_atom x)
      | CE.Eunop  (op, e, ty) ->
          PrintOps.print_unop p op ty lexpr (prec', e)
      | CE.Ebinop (op, e1, e2, ty) ->
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
      | CE.Emerge (id, ce1, ce2) ->
          fprintf p "@[<hv 6>merge %s@ %a@ %a@]"
            (extern_atom id) cexpr (16, ce1) cexpr (16, ce2)
      | CE.Eite (e, ce1, ce2) ->
          fprintf p "@[<hv 0>if %a@ then %a@ else %a@]"
            lexpr (prec', e) cexpr (prec', ce1) cexpr (prec', ce2)
      | CE.Eexp e ->
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
      | CE.Cbase -> fprintf p "."
      | CE.Con (ck', x, b) ->
          fprintf p "%a %s %s"
            print_clock ck'
            (if b then "on" else "onot")
            (extern_atom x)

    end
