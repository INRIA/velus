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
  type ctype
  type cconst
  type unop
  type binop
  type enumtag

  type clock =
    | Cbase
    | Con of clock * ident * (typ * enumtag)

  type exp =
    | Econst of cconst
    | Eenum of enumtag * typ
    | Evar of ident * typ
    | Ewhen of exp * (ident * typ) * enumtag
    | Eunop of unop * exp * typ
    | Ebinop of binop * exp * exp * typ

  type cexp =
    | Emerge of (ident * typ) * cexp list * typ
    | Ecase of exp * cexp option list * cexp
    | Eexp of exp

  type rhs =
    | Eextcall of ident * exp list * ctype
    | Ecexp of cexp

  val typeof : exp -> typ
end

module PrintFun (CE: SYNTAX)
    (PrintOps : PRINT_OPS with type typ     = CE.typ
                           and type ctype   = CE.ctype
                           and type cconst  = CE.cconst
                           and type unop    = CE.unop
                           and type binop   = CE.binop
                           and type enumtag = CE.enumtag) :
sig
  val print_ident           : formatter -> ident -> unit
  val print_exp             : formatter -> CE.exp -> unit
  val print_cexp            : formatter -> CE.cexp -> unit
  val print_rhs             : formatter -> CE.rhs -> unit
  val print_fullclocks      : bool ref
  val print_clock           : formatter -> CE.clock -> unit
  val print_clock_decl      : formatter -> CE.clock -> unit
  val print_decl            : formatter -> (ident * (CE.typ * CE.clock)) -> unit
  val print_decl_list       : formatter -> (ident * (CE.typ * CE.clock)) list -> unit
  val print_comma_list      : (formatter -> 'a -> unit) -> formatter -> 'a list -> unit
  val print_comma_list_as   : string -> (formatter -> 'a -> unit) -> formatter -> 'a list -> unit
  val print_semicol_list    : (formatter -> 'a -> unit) -> formatter -> 'a list -> unit
  val print_semicol_list_as : string -> (formatter -> 'a -> unit) -> formatter -> 'a list -> unit
  val print_pattern         : formatter -> idents -> unit
end
=
struct

  let lprecedence = function
    | CE.Econst _ -> (16, NA)
    | CE.Eenum _  -> (16, NA)
    | CE.Evar _   -> (16, NA)
    | CE.Ewhen _  -> (12, LtoR) (* precedence of +/- *)
    | CE.Eunop  (op, _, _)    -> PrintOps.prec_unop op
    | CE.Ebinop (op, _, _, _) -> PrintOps.prec_binop op

  let cprecedence = function
    | CE.Emerge _ -> (5, LtoR) (* precedence of lor - 1 *)
    | CE.Ecase _  -> (5, LtoR)
    | CE.Eexp _   -> (5, LtoR)

  let print_ident p i = pp_print_string p (extern_atom i)

  let print_sep_list print =
    pp_print_list ~pp_sep:(fun p () -> fprintf p "@ ") print

  let rec exp prec p e =
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
        PrintOps.print_cconst p c
      | CE.Eenum (c, ty) ->
        PrintOps.print_enumtag p (c, ty)
      | CE.Evar (id, _) ->
        print_ident p id
      | CE.Ewhen (e, (x, tx), c) ->
        fprintf p "%a when %a(%a)"
          (exp prec') e
          PrintOps.print_enumtag (c, tx)
          print_ident x
      | CE.Eunop  (op, e, ty) ->
        PrintOps.print_unop p op ty (exp prec') e
      | CE.Ebinop (op, e1, e2, ty) ->
        PrintOps.print_binop p op ty (exp prec1) e1 (exp prec2) e2
    end;
    if prec' < prec then fprintf p ")@]" else fprintf p "@]"

  let print_exp = exp 0

  let print_branch_tag p (ty, i) =
    PrintOps.print_enumtag p (PrintOps.enumtag_of_int i, ty)

  let rec cexp prec p e =
    let (prec', assoc) = cprecedence e in
    if prec' < prec
    then fprintf p "@[<hov 2>("
    else fprintf p "@[<hov 2>";
    begin match e with
      | CE.Emerge ((id, ty), ces, _) ->
        fprintf p "@[<v 2>merge %a@ %a@]"
          print_ident id
          branches (ty, List.mapi (fun i e -> (i, e)) ces, None)
      | CE.Ecase (e, ces, d) ->
        let ty = CE.typeof e in
        fprintf p "@[<v 2>case %a of@ %a@]"
          (exp prec') e
          branches (ty,
                    List.filter_map
                      (fun (i, e) -> match e with None -> None | Some e -> Some (i, e))
                      (List.mapi (fun i e -> (i, e)) ces),
                    if List.exists Option.is_none ces then Some d else None)
      | CE.Eexp e ->
        exp (prec' + 1) p e
    end;
    if prec' < prec then fprintf p ")@]" else fprintf p "@]"

  and branches p (ty, brs, d) =
    print_sep_list (fun p (k, e) ->
        fprintf p "(%a => %a)"
          print_branch_tag (ty, k)
          (cexp 16) e
      ) p brs;
    match d with
    | None -> ()
    | Some e ->
      fprintf p "@ (_ => %a)"
        (cexp 16) e

  let print_cexp = cexp 0

  let print_comma_list print =
    pp_print_list ~pp_sep:(fun p () -> fprintf p ",@ ") print

  let print_rhs p = function
    | CE.Eextcall (f, es, _) ->
      fprintf p "external %a@,(@[<hov 0>%a@])"
        print_ident f
        (print_comma_list print_exp) es
    | CE.Ecexp e -> print_cexp p e

  let rec print_clock p ck =
    match ck with
    | CE.Cbase -> fprintf p "."
    | CE.Con (ck', x, (ty, c)) ->
      fprintf p "%a on (%a=%a)"
        print_clock ck'
        print_ident x
        PrintOps.print_enumtag (c, ty)

  let print_fullclocks = ref false

  let print_clock_decl p ck =
    match ck with
    | CE.Cbase -> ()
    | CE.Con (ck', x, (ty, c)) ->
      if !print_fullclocks
      then fprintf p " :: @[<hov 3>%a@]" print_clock ck
      else fprintf p " when %a(%a)"
          PrintOps.print_enumtag (c, ty)
          print_ident x

  let print_decl p (id, (ty, ck)) =
    fprintf p "@[%a : %a%a@]"
      print_ident id
      PrintOps.print_typ ty
      print_clock_decl ck

  let print_comma_list p =
    pp_print_list ~pp_sep:(fun p () -> fprintf p ",@ ") p

  let print_semicol_list p =
    pp_print_list ~pp_sep:(fun p () -> fprintf p ";@ ") p

  let print_pattern p xs =
    match xs with
    | [x] -> print_ident p x
    | xs  -> fprintf p "(@[<hv 0>%a@])"
               (print_comma_list print_ident) xs

  let print_decl_list = print_semicol_list print_decl

  let print_comma_list_as name px p xs =
    if List.length xs > 0 then
      fprintf p "@[<h>%s @[<hov 4>%a@];@]@;"
        name
        (print_comma_list px) xs

  let print_semicol_list_as name px p xs =
    if xs <> [] then
      fprintf p "%s @[<hov 0>%a@];@;"
        name
        (print_semicol_list px) xs
end
