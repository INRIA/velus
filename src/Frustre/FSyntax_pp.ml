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

module FS = FSyntax
module C = ClockDefs

let print_fullclocks = ref false
let show_annot_clocks = ref false
let show_annot_types = ref false

open Format
open BinNums

type ident = BinNums.positive

let string_of_ident = Camlcoq.extern_atom
let ident_of_string = Camlcoq.intern_string

let print_fullclocks = ref false
let print_appclocks  = ref false

let fprintf = Format.fprintf

let ident p i = Format.pp_print_string p (string_of_ident i)

let string_of_type =
  let open FS in
  function
  | Tint (IBool, sg)     -> "bool"
  | Tint (I8, Signed)    -> "int8"
  | Tint (I8, Unsigned)  -> "uint8"
  | Tint (I16, Signed)   -> "int16"
  | Tint (I16, Unsigned) -> "uint16"
  | Tint (I32, Signed)   -> "int32"
  | Tint (I32, Unsigned) -> "uint32"
  | Tlong Signed         -> "int64"
  | Tlong Unsigned       -> "uint64"
  | Tfloat F32           -> "float32"
  | Tfloat F64           -> "float64"

let typ p ty = Format.pp_print_string p (string_of_type ty)

let sep p () = Format.(pp_print_string p ";"; pp_print_cut p ())

let typs = Format.pp_print_list ~pp_sep:sep typ

let to_binaryfloat = function
  | FS.F754_zero s           -> Binary.B754_zero s
  | FS.F754_infinity s       -> Binary.B754_infinity s
  | FS.F754_nan (b, pl)      -> Binary.B754_nan (b, pl)
  | FS.F754_finite (s, m, e) -> Binary.B754_finite (s, m, e)

let const p c =
  let open FS in
  match c with
  | Cint (n, I32, Unsigned) ->
      fprintf p "%luU"   (Camlcoq.camlint_of_coqint n)
  | Cint (n, _, _) ->
      fprintf p "%ld"    (Camlcoq.camlint_of_coqint n)
  | Cfloat f ->
      fprintf p "%.15F"  (Camlcoq.camlfloat_of_coqfloat (to_binaryfloat f))
  | Csingle f ->
      fprintf p "%.15Ff" (Camlcoq.camlfloat_of_coqfloat32 (to_binaryfloat f))
  | Clong (n, Unsigned) ->
      fprintf p "%LuLLU" (Camlcoq.camlint64_of_coqint n)
  | Clong (n, _) ->
      fprintf p "%LdLL"  (Camlcoq.camlint64_of_coqint n)

let name_unop ty = function
  | FS.Onotbool  -> "not"
  | FS.Onotint   -> "lnot"
  | FS.Oneg      -> "-"
  | FS.Ocast ty' -> assert false

let unop p uop ty exp e =
  match uop with
  | FS.Ocast ty' -> fprintf p "(%a : %a)" exp e typ ty
  | _ -> fprintf p "%s %a" (name_unop ty uop) exp e

let is_bool_type = function
  | FS.Tint (FS.IBool, sg) -> true
  | _ -> false

let name_binop ty = function
  | FS.Oadd -> "+"
  | FS.Osub -> "-"
  | FS.Omul -> "*"
  | FS.Odiv -> "/"
  | FS.Omod -> "mod"
  | FS.Oand -> if is_bool_type ty then "and" else "land"
  | FS.Oor  -> if is_bool_type ty then "or"  else "lor"
  | FS.Oxor -> if is_bool_type ty then "xor" else "lxor"
  | FS.Oshl -> "lsl"
  | FS.Oshr -> "lsr"
  | FS.Oeq  -> "="
  | FS.One  -> "<>"
  | FS.Olt  -> "<"
  | FS.Ogt  -> ">"
  | FS.Ole  -> "<="
  | FS.Oge  -> ">="

let binop p op ty exp1 e1 exp2 e2 =
  fprintf p "%a@ %s %a" exp1 e1 (name_binop ty op) exp2 e2

type associativity = LtoR | RtoL | NA

let prec_unop op = (15, RtoL)
let prec_binop =
  let open FS in function
  |Omul|Odiv|Omod  -> (13, LtoR)
  |Oadd|Osub       -> (12, LtoR)
  |Oshl|Oshr       -> (11, LtoR)
  |Olt|Ogt|Ole|Oge -> (10, LtoR)
  |Oeq|One         -> ( 9, LtoR)
  |Oand            -> ( 8, LtoR)
  |Oxor            -> ( 7, LtoR)
  |Oor             -> ( 6, LtoR)

let precedence = function
  | FS.Econst _ -> (16, NA)
  | FS.Evar _   -> (16, NA)
  | FS.Eunop  (op, _, _)    -> prec_unop op
  | FS.Ebinop (op, _, _, _) -> prec_binop op
  | FS.Efby _   -> (14, RtoL) (* higher than * / % *)
  | FS.Ewhen _  -> (12, LtoR) (* precedence of + - *)
  | FS.Emerge _ -> ( 5, LtoR) (* precedence of lor - 1 *)
  | FS.Eite _   -> ( 5, LtoR)
  | FS.Eapp _   -> ( 4, NA)

let clock_index p i =
  Format.(pp_print_string p "?c"; pp_print_int p (Camlcoq.P.to_int i))

let rec clock p = function
  | C.Cbase -> Format.pp_print_char p '.'
  | C.Con (ck', x, b) ->
      Format.fprintf p "%a %s %a" clock ck' (if b then "on" else "onot") ident x

let clocks p cks =
  Format.(fprintf p "(@[<hv 0>%a@])"
    (pp_print_list ~pp_sep:(fun p () -> fprintf p ",@ ") clock) cks)

let ckid p i = clock_index p i

let rec sclock p = function
  | C.Cbase -> Format.pp_print_char p '.'
  | C.Con (ck', x, b) ->
      Format.fprintf p "%a %s %a" sclock ck' (if b then "on" else "onot") ckid x

let sclocks p cks =
  Format.(fprintf p "(@[<hv 0>%a@])"
    (pp_print_list ~pp_sep:(fun p () -> fprintf p ",@ ") sclock) cks)

let nclock p = function
  | (sck, None) -> sclock p sck
  | (sck, Some i) -> Format.printf "(%a : %a)" ckid i sclock sck

let nclocks p cks =
  match cks with
  | [ck] -> nclock p ck
  | _ -> Format.(fprintf p "[@[<hv 0>%a@]]"
           (pp_print_list ~pp_sep:(fun p () -> fprintf p ",@ ") nclock) cks)

let clock_decl p ck =
  if !print_fullclocks
  then Format.fprintf p " :: %a" clock ck
  else
    match ck with
    | C.Cbase -> ()
    | C.Con (_, x, b) ->
        Format.fprintf p " when%s %a" (if b then "" else " not") ident x

let annot_typs p = function
  | FS.Econst c                    -> typ p (FS.ty_const c)
  | FS.Evar (_, (ty, ck))          -> typ p ty
  | FS.Eunop (_, _, (ty, ck))      -> typ p ty
  | FS.Ebinop (_, _, _, (ty, ck))  -> typ p ty
  | FS.Efby (_, _, tycks)          -> typs p (List.map fst tycks)
  | FS.Ewhen (_, _, _, (tys, ck))  -> typs p tys
  | FS.Emerge (_, _, _, (tys, ck)) -> typs p tys
  | FS.Eite (_, _, _, (tys, ck))   -> typs p tys
  | FS.Eapp (_, _, tycks)          -> typs p (List.map fst tycks)

let annot_cks p = function
  | FS.Econst c                    -> sclock p C.Cbase
  | FS.Evar (_, (ty, ck))          -> nclock p ck
  | FS.Eunop (_, _, (ty, ck))      -> nclock p ck
  | FS.Ebinop (_, _, _, (ty, ck))  -> nclock p ck
  | FS.Efby (_, _, tycks)          -> nclocks p (List.map snd tycks)
  | FS.Ewhen (_, _, _, (tys, ck))  -> nclock p ck
  | FS.Emerge (_, _, _, (tys, ck)) -> nclock p ck
  | FS.Eite (_, _, _, (tys, ck))   -> nclock p ck
  | FS.Eapp (_, _, tycks)          -> nclocks p (List.map snd tycks)

let rec exp prec p e =
  let (prec', assoc) = precedence e in
  let (prec1, prec2) =
    if assoc = LtoR
    then (prec', prec' + 1)
    else (prec' + 1, prec') in
  let parentheses = prec' < prec || !show_annot_clocks || !show_annot_types in
  if parentheses
  then fprintf p "@[<hov 2>("
  else fprintf p "@[<hov 2>";
  begin match e with
  | FS.Econst c ->
      const p c
  | FS.Evar (id, _) ->
      fprintf p "%a" ident id
  | FS.Eunop  (op, e, (ty, _)) ->
      unop p op ty (exp prec') e
  | FS.Ebinop (op, e1, e2, (ty, _)) ->
      binop p op ty (exp prec1) e1 (exp prec2) e2
  | FS.Efby (e0s, es, _) ->
      fprintf p "%a fby@ %a" (exp_list prec1) e0s (exp_list prec2) es
  | FS.Ewhen (e, x, v, _) ->
      if v
      then fprintf p "%a when %a" (exp_list prec') e ident x
      else fprintf p "%a when not %a" (exp_list prec') e ident x
  | FS.Emerge (id, e1s, e2s, _) ->
      fprintf p "merge %a@ %a@ %a" ident id (exp_list 16) e1s (exp_list 16) e2s
  | FS.Eite (e, e1s, e2s, _) ->
      fprintf p "if %a@ then %a@ else %a"
        (exp 16) e (exp_list 16) e1s (exp_list 16) e2s
  | FS.Eapp (f, es, anns) ->
      if !print_appclocks
      then fprintf p "%a@[<v 1>%a@ (* @[<hov>%a@] *)@]"
             ident f exp_arg_list es nclocks (List.map snd anns)
      else fprintf p "%a%a" ident f exp_arg_list es
  end;
  if !show_annot_types then fprintf p " : @[%a@]" annot_typs e;
  if !show_annot_clocks then fprintf p " :: @[%a@]" annot_cks e;
  if parentheses then fprintf p ")@]" else fprintf p "@]"

and exp_list prec p es =
  match es with
  | [e] -> exp prec p e
  | _   -> exp_arg_list p es

and exp_arg_list p es =
  fprintf p "(@[<hv 0>%a@])"
    (pp_print_list ~pp_sep:(fun p () -> fprintf p ",@ ") (exp 0)) es

let exp = exp 0

let decl p (id, (ty, ck)) =
  fprintf p "%a@ : %a%a" ident id typ ty clock_decl ck

let decl_list =
  pp_print_list ~pp_sep:(fun p () -> fprintf p ",@ ") decl

let pattern p xs =
  match xs with
  | [x] -> ident p x
  | xs  ->
    fprintf p "(@[<hv 0>%a@])"
      (pp_print_list ~pp_sep:(fun p () -> fprintf p ",@ ") ident) xs

let rec equation p (xs, es) =
  fprintf p "@[<hov 2>%a =@ %a;@]"
    pattern xs (exp_list 0) es

let node p { FS.n_name     = name;
             FS.n_hasstate = hasstate;
             FS.n_in       = inputs;
             FS.n_out      = outputs;
             FS.n_vars     = locals;
             FS.n_eqs      = eqs } =
  fprintf p "@[<v>";
  fprintf p "@[<hov 0>";
    fprintf p "@[<h>%s %a (%a)@]@;"
      (if hasstate then "node" else "fun")
      ident name decl_list inputs;
    fprintf p "@[<h>returns (%a)@]@;" decl_list outputs;
  fprintf p "@]@;";
  if List.length locals > 0 then
    fprintf p "@[<h>var @[<hov 4>%a@];@]@;" decl_list locals;
  fprintf p "@[<v 2>let@;%a@;<0 -2>@]" (pp_print_list equation) (List.rev eqs);
  fprintf p "tel@]"

let global p prog =
  fprintf p "@[<v 0>";
  List.iter (fprintf p "@;%a@;" node) prog;
  fprintf p "@]@."

