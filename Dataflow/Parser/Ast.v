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

(* This module draws on the work of Jacques-Henri Jourdan for the CompCert
   project (CompCert/cparser/Cabs.v). *)

(* OCaml's string type. *)
Parameter string : Type.
(* OCaml's int64 type, used to represent individual characters in literals. *)
Parameter char_code : Type.
(* Context information. *)
Parameter astloc : Type.

Record floatInfo := {
  isHex_FI:bool;
  integer_FI:option string;
  fraction_FI:option string;
  exponent_FI:option string;
  suffix_FI:option string
}.

Inductive type_name :=
| Tint8
| Tuint8
| Tint16
| Tuint16
| Tint32
| Tuint32
| Tint64
| Tuint64
| Tfloat32
| Tfloat64
| Tbool : type_name.

Inductive unary_operator :=
| MINUS | NOT | BNOT.

Inductive binary_operator :=
| ADD | SUB | MUL | DIV | MOD
| BAND | BOR
| LAND | LOR | XOR | LSL | LSR
| EQ | NE | LT | GT | LE | GE.

Inductive constant :=
(* The string is the textual representation of the constant in
   the source code. *)
| CONST_BOOL  : bool -> constant
| CONST_INT   : string -> constant
| CONST_FLOAT : floatInfo -> constant
| CONST_CHAR  : bool -> list char_code -> constant.

Inductive clock :=
| BASE  : clock
| ON    : clock -> bool -> string -> clock.

Inductive expression :=
| UNARY    : unary_operator -> expression -> astloc -> expression
| BINARY   : binary_operator -> expression -> expression -> astloc -> expression
| IFTE     : expression -> expression -> expression -> astloc -> expression
| CAST     : type_name -> expression -> astloc -> expression
| CALL     : string -> list expression -> astloc -> expression
| CONSTANT : constant -> astloc -> expression
| VARIABLE : string -> astloc -> expression
| FBY      : constant -> expression -> astloc -> expression
| WHEN     : expression -> bool -> string -> astloc -> expression
| MERGE    : string -> expression -> expression -> astloc -> expression.

(* TODO: Reorganize to add astloc as usual, with "decorating wrapper"? *)
Definition expression_loc (e: expression) : astloc :=
  match e with
  | UNARY _ _ l => l
  | BINARY _ _ _ l => l
  | IFTE _ _ _ l => l
  | CAST _ _ l => l
  | CALL _ _ l => l
  | CONSTANT _ l => l
  | VARIABLE _ l => l
  | FBY _ _ l => l
  | WHEN _ _ _ l => l
  | MERGE _ _ _ l => l
  end.
    
Definition var_decls := list (string * type_name * clock).

Definition equation : Type := (list string * expression * astloc)%type.

Inductive declaration :=
      (*  name      inputs       outputs      locals   *)
| NODE : string -> var_decls -> var_decls -> var_decls
         -> list equation -> declaration.

