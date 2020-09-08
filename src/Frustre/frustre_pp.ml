(***********************************************************************)
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

module F = Frustre

type ident = F.ident
type idents = ident list

let print_fullclocks = ref false
let show_annot_clocks = ref false
let show_annot_types = ref false

let fprintf = Format.fprintf

let ident p i =
  Format.(pp_print_string p (F.string_of_ident i))

let string_of_type =
  let open Ctypes in
  function
  | F.Tint (IBool, sg)     -> "bool"
  | F.Tint (I8, Signed)    -> "int8"
  | F.Tint (I8, Unsigned)  -> "uint8"
  | F.Tint (I16, Signed)   -> "int16"
  | F.Tint (I16, Unsigned) -> "uint16"
  | F.Tint (I32, Signed)   -> "int32"
  | F.Tint (I32, Unsigned) -> "uint32"
  | F.Tlong Signed         -> "int64"
  | F.Tlong Unsigned       -> "uint64"
  | F.Tfloat F32           -> "float32"
  | F.Tfloat F64           -> "float64"

let typ p ty = Format.pp_print_string p (string_of_type ty)

let sep p () = Format.(pp_print_string p ";"; pp_print_cut p ())

let typs = Format.pp_print_list ~pp_sep:sep typ

let clock_index p i = Format.(pp_print_string p "?c"; pp_print_int p i)

let ckid p = function
  | F.Vidx i -> clock_index p i
  | F.Vnm x  -> ident p x

let rec sclock p ck =
  match F.find_clock ck with
  | F.Sbase -> Format.pp_print_char p '.'
  | F.Son (ck', b, x) ->
      Format.fprintf p "%a %s %a" sclock ck' (if b then "on" else "onot") ckid x
  | F.Svar { contents = F.Sindex i } -> clock_index p i
  | F.Svar { contents = F.Slink _ } -> assert false

let sclocks p cks =
  Format.(fprintf p "(@[<hv 0>%a@])"
    (pp_print_list ~pp_sep:(fun p () -> fprintf p ",@ ") sclock) cks)

let nclock p = function
  | F.Cstream sck -> sclock p sck
  | F.Cnamed (i, sck) -> Format.printf "(%a : %a)" ckid i sclock sck

let nclocks p cks =
  match cks with
  | [ck] -> nclock p ck
  | _ -> Format.(fprintf p "[@[<hv 0>%a@]]"
           (pp_print_list ~pp_sep:(fun p () -> fprintf p ",@ ") nclock) cks)

let clock_decl p ck =
  if !print_fullclocks
  then Format.fprintf p " :: %a" sclock ck
  else
    match F.find_clock ck with
    | F.Sbase -> ()
    | F.Son (_, b, x) ->
        Format.fprintf p " when%s %a" (if b then "" else " not") ckid x
    | F.Svar { contents = F.Sindex i } -> clock_index p i
    | F.Svar { contents = F.Slink _ } -> assert false

let const p c =
  match c with
  | F.Cint (n, Ctypes.I32, Ctypes.Unsigned) ->
      fprintf p "%luU"   (Camlcoq.camlint_of_coqint n)
  | F.Cint (n, _, _) ->
      fprintf p "%ld"    (Camlcoq.camlint_of_coqint n)
  | F.Cfloat f ->
      fprintf p "%.15F"  (Camlcoq.camlfloat_of_coqfloat f)
  | F.Csingle f ->
      fprintf p "%.15Ff" (Camlcoq.camlfloat_of_coqfloat32 f)
  | F.Clong (n, Ctypes.Unsigned) ->
      fprintf p "%LuLLU" (Camlcoq.camlint64_of_coqint n)
  | F.Clong (n, _) ->
      fprintf p "%LdLL"  (Camlcoq.camlint64_of_coqint n)

let name_unop ty = function
  | F.Enotbool  -> "not"
  | F.Enotint   -> "lnot"
  | F.Eneg      -> "-"
  | F.Ecast ty' -> "cast"

let unop p uop ty print_exp e =
  match uop with
  | F.Ecast ty' -> fprintf p "(%a : %a)" print_exp e typ ty
  | _ -> fprintf p "%s %a" (name_unop ty uop) print_exp e

let is_bool_type = function
  | F.Tint (Ctypes.IBool, sg) -> true
  | _ -> false

let name_binop ty = function
  | F.Eadd -> "+"
  | F.Esub -> "-"
  | F.Emul -> "*"
  | F.Ediv -> "/"
  | F.Emod -> "mod"
  | F.Eand -> if is_bool_type ty then "and" else "land"
  | F.Eor  -> if is_bool_type ty then "or"  else "lor"
  | F.Exor -> if is_bool_type ty then "xor" else "lxor"
  | F.Eshl -> "lsl"
  | F.Eshr -> "lsr"
  | F.Eeq  -> "="
  | F.Ene  -> "<>"
  | F.Elt  -> "<"
  | F.Egt  -> ">"
  | F.Ele  -> "<="
  | F.Ege  -> ">="

let binop p op ty print_exp1 e1 print_exp2 e2 =
  fprintf p "%a@ %s %a" print_exp1 e1 (name_binop ty op) print_exp2 e2

type associativity = LtoR | RtoL | NA

let prec_unop op = (15, RtoL)
let prec_binop =
  let open F in function
  |Emul|Ediv|Emod  -> (13, LtoR)
  |Eadd|Esub       -> (12, LtoR)
  |Eshl|Eshr       -> (11, LtoR)
  |Elt|Egt|Ele|Ege -> (10, LtoR)
  |Eeq|Ene         -> ( 9, LtoR)
  |Eand            -> ( 8, LtoR)
  |Exor            -> ( 7, LtoR)
  |Eor             -> ( 6, LtoR)

let precedence = function
  | F.Econst _ -> (16, NA)
  | F.Evar _   -> (16, NA)
  | F.Eunop  (op, _)    -> prec_unop op
  | F.Ebinop (op, _, _) -> prec_binop op
  | F.Efby _   -> (14, RtoL) (* higher than * / % *)
  | F.Ewhen _  -> (12, LtoR) (* precedence of + - *)
  | F.Emerge _ -> ( 5, LtoR) (* precedence of lor - 1 *)
  | F.Eite _   -> ( 5, LtoR)
  | F.Eapp _   -> ( 4, NA)

let single_typ = function
  | [] -> F.typ_bool (* Use bool if untyped *)
  | ty::_ -> ty

let rec exp prec p { F.e_desc; F.e_typ; F.e_clk } =
  let (prec', assoc) = precedence e_desc in
  let (prec1, prec2) =
    if assoc = LtoR
    then (prec', prec' + 1)
    else (prec' + 1, prec') in
  let parentheses = prec' < prec || !show_annot_clocks || !show_annot_types in
  if parentheses
  then fprintf p "@[<hov 2>("
  else fprintf p "@[<hov 2>";
  begin match e_desc with
  | F.Econst c ->
      const p c
  | F.Evar id ->
      ident p id
  | F.Eunop  (op, e) ->
      unop p op (single_typ e_typ) (exp prec') e
  | F.Ebinop (op, e1, e2) ->
      binop p op (single_typ e_typ) (exp prec1) e1 (exp prec2) e2
  | F.Efby (e0s, es) ->
      fprintf p "%a fby@ %a" (exp_list prec1) e0s (exp_list prec2) es
  | F.Ewhen (e, x, v) ->
      if v
      then fprintf p "%a when %a" (exp_list prec') e ident x
      else fprintf p "%a when not %a" (exp_list prec') e ident x
  | F.Emerge (id, e1s, e2s) ->
      fprintf p "merge %a@ %a@ %a" ident id (exp_list 16) e1s (exp_list 16) e2s
  | F.Eite (e, e1s, e2s) ->
      fprintf p "if %a@ then %a@ else %a"
        (exp 16) e (exp_list 16) e1s (exp_list 16) e2s
  | F.Eapp (f, es, None) ->
      fprintf p "%a%a" ident f exp_arg_list es
  | F.Eapp (f, es, Some er) ->
      fprintf p "(restart %a every %a)%a" ident f (exp prec') er exp_arg_list es 
  end;
  if !show_annot_types then fprintf p " : @[%a@]" typs e_typ;
  if !show_annot_clocks then fprintf p " :: @[%a@]" nclocks e_clk;
  fprintf p (if parentheses then ")@]" else "@]")

and exp_list prec p es =
  match es with
  | [e] -> exp prec p e
  | _   -> exp_arg_list p es

and exp_arg_list p es =
  Format.(fprintf p "(@[<hv 0>%a@])"
    (pp_print_list ~pp_sep:(fun p () -> fprintf p ",@ ") (exp 0)) es)

let exp = exp 0

let decl env p id =
  match F.Env.find id env with
  | { F.v_typ = ty; F.v_clk = ck } ->
      fprintf p "%a@ : %a%a" ident id typ ty clock_decl ck
  | exception Not_found ->
      fprintf p "%a@ : ?" ident id

let decl_list env =
  Format.(pp_print_list ~pp_sep:(fun p () -> fprintf p ",@ ") (decl env))

let pattern p xs =
  match xs with
  | [x] -> ident p x
  | xs  ->
    Format.(fprintf p "(@[<hv 0>%a@])"
      (pp_print_list ~pp_sep:(fun p () -> fprintf p ",@ ") ident) xs)

let rec equation p { F.eq_desc = (xs, es) } =
  Format.(fprintf p "@[<hov 2>%a =@ %a;@]" pattern xs (exp_list 0) es)

let annot p { F.v_typ = ty; F.v_clk = ck } =
  Format.(fprintf p ":%a :: %a" typ ty sclock ck)

let node p { F.n_name     = name;
             F.n_hasstate = hasstate;
             F.n_in       = inputs;
             F.n_out      = outputs;
             F.n_vars     = locals;
             F.n_eqs      = eqs;
             F.n_env      = env } =
  fprintf p "@[<v>";
  fprintf p "@[<hov 0>";
    fprintf p "@[<h>%s %a (%a)@]@;"
      (if hasstate then "node" else "fun")
      ident name (decl_list env) inputs;
    fprintf p "@[<h>returns (%a)@]@;" (decl_list env) outputs;
  fprintf p "@]@;";
  if List.length locals > 0 then
    fprintf p "@[<h>var @[<hov 4>%a@];@]@;" (decl_list env) locals;
  fprintf p "@[<v 2>let@;%a@;<0 -2>@]"
    (Format.pp_print_list equation) (List.rev eqs);
  fprintf p "tel@]"

let decl p { F.desc = d } =
  match d with
  | F.Enodedecl n -> node p n

let global p prog =
  fprintf p "@[<v 0>";
  List.iter (fprintf p "@;%a@;" decl) prog;
  fprintf p "@]@."

