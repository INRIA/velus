(* *********************************************************************)
(*                                                                     *)
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

(* Identifiers *)

type ident = BinNums.positive

let string_of_ident = Camlcoq.extern_atom
let ident_of_string = Camlcoq.intern_string

let fprint_ident ff id = Format.pp_print_string ff (string_of_ident id)

let compare_from_comparison f x y =
  match f x y with
  | Datatypes.Eq -> 0
  | Datatypes.Lt -> -1
  | Datatypes.Gt -> 1

module IdentOrd = struct
  type t = ident
  let compare = compare_from_comparison BinPos.Pos.compare
  let fprint = fprint_ident
end

module Env =
struct
  include (Map.Make(IdentOrd))

  let singleton i tentry = add i tentry empty

  let fprint_t fprint_v ff s =
    Format.fprintf ff "{@[<hv 2>@ ";
    iter (fun k v -> Format.fprintf ff "%a->%a@ " fprint_ident k fprint_v v) s;
    Format.fprintf ff "@]}"

  let append env0 env =
    fold (fun key v env -> add key v env) env0 env
end

module ISet = Set.Make(IdentOrd)

(* Types *)

type typ =
  | Tint   of Ctypes.intsize * Ctypes.signedness
  | Tlong  of Ctypes.signedness
  | Tfloat of Ctypes.floatsize

let typ_bool = Tint (Ctypes.IBool, Ctypes.Signed)

(* Clocks *)

type clock =
  | Cbase
  | Con of clock * bool * ident

type ckid =
  | Vidx of int
  | Vnm of ident

type sclock =
  | Sbase
  | Svar of link ref
  | Son of sclock * bool * ckid

and link =
  | Sindex of int
  | Slink of sclock

type nclock =
  | Cstream of sclock
  | Cnamed of ckid * sclock

let reset_clocks, fresh_clock =
  let index = ref 0 in
  (fun () -> index := 0),
  (fun () -> incr index; Svar (ref (Sindex !index)))

exception Unify

let rec find_clock ck =
  match ck with
  | Sbase | Son _ | Svar { contents = Sindex _ } -> ck
  | Svar ({ contents = Slink ck } as link) ->
      let ck = find_clock ck in
      link.contents <- Slink ck;
      ck

let rec occurs_check idx ck =
  match find_clock ck with
  | Sbase -> ()
  | Svar { contents = Sindex n } when idx <> n -> ()
  | Son (ck', _, _) -> occurs_check idx ck'
  | _ -> raise Unify

let rec unify_clocks ck1 ck2 =
  let ck1 = find_clock ck1 in
  let ck2 = find_clock ck2 in
  if ck1 == ck2 then ()
  else
    match ck1, ck2 with
    | Sbase,
      Sbase -> ()
    | Svar { contents = Sindex n1 },
      Svar { contents = Sindex n2 } when n1 = n2 -> ()
    | Son (ck1, c1, n1),
      Son (ck2, c2, n2) when (c1 = c2) && (n1 = n2) -> unify_clocks ck1 ck2
    | Svar ({ contents = Sindex n } as v), ck
    | ck, Svar ({ contents = Sindex n } as v) ->
        occurs_check n ck;
        v.contents <- Slink ck
    | _ -> raise Unify

and unify_clocks_list cks1 cks2 =
  try List.iter2 unify_clocks cks1 cks2
  with Invalid_argument _ -> raise Unify

(* Annotated AST *)

type const =
  | Cint    of Integers.Int.int * Ctypes.intsize * Ctypes.signedness
  | Clong   of Integers.Int64.int * Ctypes.signedness
  | Cfloat  of Floats.float
  | Csingle of Floats.float32

type unop = Eneg | Enotint | Enotbool | Ecast of typ

type binop =
    Eadd | Esub | Emul | Ediv | Emod
  | Eand | Eor | Exor
  | Eshl | Eshr
  | Eeq | Ene | Elt | Egt | Ele | Ege

type location = FrustreAst.astloc

type 'a localized = { desc: 'a; loc: location }

type exp = {
    mutable e_desc : desc;
            e_loc  : location;
    mutable e_typ  : typ list;
    mutable e_clk  : nclock list;
  }

and desc =
  | Econst of const
  | Evar   of ident
  | Eunop  of unop * exp
  | Ebinop of binop * exp * exp
  | Efby   of exp list * exp list
  | Ewhen  of exp list * ident * bool
  | Emerge of ident * exp list * exp list
  | Eite   of exp * exp list * exp list
  | Eapp   of ident * exp list

type equation = {
    eq_desc : eqdesc;
    eq_loc  : location
  }

and eqdesc = ident list * exp list

type annot = {
    v_typ : typ;
    v_clk : sclock;
    v_loc : location;
  }

type node = {
    n_name        : ident;
    n_hasstate    : bool;
    n_in          : ident list;
    n_out         : ident list;
    n_vars        : ident list;
    mutable n_eqs : equation list;
    n_env         : annot Env.t
  }

type implementation_desc =
  | Enodedecl of node

and implementation = implementation_desc localized

