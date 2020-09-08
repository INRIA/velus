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

open ClockDefs
type ident = ClockDefs.ident
type idents = ident list

let extern_atom = Camlcoq.extern_atom

module L = FtoLustre.L

module LustreOpNames =
struct
  let is_bool = function
    | Interface.Op.Tint (Ctypes.IBool, _) -> true
    | _ -> false

  let name_unop ty = function
    | Cop.Onotbool -> "not"
    | Cop.Onotint  -> "lnot"
    | Cop.Oneg     -> "-"
    | Cop.Oabsfloat -> "__builtin_fabs"

  let name_binop ty = function
    | Cop.Oadd -> "+"
    | Cop.Osub -> "-"
    | Cop.Omul -> "*"
    | Cop.Odiv -> "/"
    | Cop.Omod -> "mod"
    | Cop.Oand -> if is_bool ty then "and" else "land"
    | Cop.Oor  -> if is_bool ty then "or"  else "lor"
    | Cop.Oxor -> if is_bool ty then "xor" else "lxor"
    | Cop.Oshl -> "lsl"
    | Cop.Oshr -> "lsr"
    | Cop.Oeq  -> "="
    | Cop.One  -> "<>"
    | Cop.Olt  -> "<"
    | Cop.Ogt  -> ">"
    | Cop.Ole  -> "<="
    | Cop.Oge  -> ">="
end

module PrintOps = struct
  module Ops = Interface.Op

  type typ   = Ops.coq_type
  type const = Ops.const
  type unop  = Ops.unop
  type binop = Ops.binop

  let print_typ p ty = Ops.string_of_type ty |> fmt_coqstring p

  let print_const p c =
    match c with
    | Ops.Cint (n, Ctypes.I32, Ctypes.Unsigned) ->
      fprintf p "%luU"   (Camlcoq.camlint_of_coqint n)
    | Ops.Cint (n, _, _) ->
      fprintf p "%ld"    (Camlcoq.camlint_of_coqint n)
    | Ops.Cfloat f ->
      fprintf p "%.15F"  (Camlcoq.camlfloat_of_coqfloat f)
    | Ops.Csingle f ->
      fprintf p "%.15Ff"   (Camlcoq.camlfloat_of_coqfloat32 f)
    | Ops.Clong (n, Ctypes.Unsigned) ->
      fprintf p "%LuLLU" (Camlcoq.camlint64_of_coqint n)
    | Ops.Clong (n, _) ->
      fprintf p "%LdLL"  (Camlcoq.camlint64_of_coqint n)

  let print_unop p uop ty print_exp e =
    match uop with
    | Ops.UnaryOp op ->
      fprintf p "%s %a" (LustreOpNames.name_unop ty op) print_exp e
    | Ops.CastOp ty ->
      fprintf p "(%a : %a)" print_exp e print_typ ty

  let print_binop p op ty print_exp1 e1 print_exp2 e2 =
    fprintf p "%a@ %s %a" print_exp1 e1
      (LustreOpNames.name_binop ty op)
      print_exp2 e2

  let prec_unop op = (15, RtoL)
  let prec_binop =
    let open Cop in function
      | Omul|Odiv|Omod  -> (13, LtoR)
      | Oadd|Osub       -> (12, LtoR)
      | Oshl|Oshr       -> (11, LtoR)
      | Olt|Ogt|Ole|Oge -> (10, LtoR)
      | Oeq|One         -> ( 9, LtoR)
      | Oand            -> ( 8, LtoR)
      | Oxor            -> ( 7, LtoR)
      | Oor             -> ( 6, LtoR)
end

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

let print_ident p i = pp_print_string p (extern_atom i)

let rec print_clock p ck =
  match ck with
  | Cbase -> fprintf p "."
  | Con (ck', x, b) ->
    fprintf p "%a %s %a"
      print_clock ck'
      (if b then "on" else "onot")
      print_ident x

let print_nclock p (ck, id) =
  fprintf p "%a" print_clock ck

let print_ncks =
  pp_print_list ~pp_sep:(fun p () -> fprintf p " *@ ") print_nclock

let print_comma_list p =
  pp_print_list ~pp_sep:(fun p () -> fprintf p ",@ ") p

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
      print_ident p id
    | L.Eunop  (op, e, (ty, _)) ->
      PrintOps.print_unop p op ty (exp prec') e
    | L.Ebinop (op, e1, e2, (ty, _)) ->
      PrintOps.print_binop p op ty (exp prec1) e1 (exp prec2) e2
    | L.Efby (e0s, es, _) ->
      fprintf p "%a fby@ %a" (exp_list prec1) e0s (exp_list prec2) es
    | L.Ewhen (e, x, v, _) ->
      fprintf p "%a when%s %a"
        (exp_list prec') e
        (if v then "" else " not")
        print_ident x
    | L.Emerge (id, e1s, e2s, _) ->
      fprintf p "merge %a@ %a@ %a"
        print_ident id
        (exp_list 16) e1s
        (exp_list 16) e2s
    | L.Eite (e, e1s, e2s, _) ->
      fprintf p "if %a@ then %a@ else %a"
        (exp 16) e
        (exp_list 16) e1s
        (exp_list 16) e2s
    | L.Eapp (f, es, None, anns) ->
      if !print_appclocks
      then fprintf p "%a@[<v 1>%a@ (* @[<hov>%a@] *)@]"
          print_ident f
          exp_arg_list es
          print_ncks (List.map snd anns)
      else fprintf p "%a%a"
          print_ident f
          exp_arg_list es
    | L.Eapp (f, es, Some r, anns) ->
      if !print_appclocks
      then fprintf p "%a@[<v 1>%a@ every@ %a@ (* @[<hov>%a@] *)@]"
          print_ident f
          exp_arg_list es
          (exp prec') r
          print_ncks (List.map snd anns)
      else fprintf p "(restart %a every@ %a)%a"
          print_ident f
          (exp prec') r
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

let print_exp = exp 0

let print_clock_decl p ck =
  match ck with
  | Cbase -> ()
  | Con (ck', x, b) ->
    if !print_fullclocks
    then fprintf p " :: @[<hov 3>%a@]" print_clock ck
    else fprintf p " when%s %a"
        (if b then "" else " not")
        print_ident x

let print_decl p (id, (ty, ck)) =
  fprintf p "%a@ : %a%a"
    print_ident id
    PrintOps.print_typ ty
    print_clock_decl ck

let print_decl_list = print_comma_list print_decl

let print_pattern p xs =
  match xs with
  | [x] -> print_ident p x
  | xs  -> fprintf p "(@[<hv 0>%a@])"
             (print_comma_list print_ident) xs

let rec print_equation p (xs, es) =
  fprintf p "@[<hov 2>%a =@ %a;@]"
    print_pattern xs (exp_list 0) es

let print_comma_list_as name px p xs =
  if List.length xs > 0 then
    fprintf p "@[<h>%s @[<hov 4>%a@];@]@;"
      name
      (print_comma_list px) xs

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
    (print_comma_list_as "var" print_decl) locals
    (pp_print_list print_equation) (List.rev eqs)

let print_global p prog =
  fprintf p "@[<v 0>%a@]@."
    (pp_print_list ~pp_sep:(fun p () -> fprintf p "@;@;") print_node)
    prog
