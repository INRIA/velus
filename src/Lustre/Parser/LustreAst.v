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

(* From Coq Require Numbers.BinNums. *)
From Velus Require Import Common.

(* Definition ident := Coq.Numbers.BinNums.positive. *)

(* This module draws on the work of Jacques-Henri Jourdan for the CompCert
   project (CompCert/cparser/Cabs.v). *)

(* OCaml's string type. *)
Parameter string : Type.

Parameter string_zero : string.
Parameter string_one : string.

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
| Tfloat64 : type_name
| Tenum_name : ident -> type_name.

Inductive unary_operator :=
| MINUS | NOT | BNOT.

Inductive binary_operator :=
| ADD | SUB | MUL | DIV | MOD
| BAND | BOR
| LAND | LOR | XOR | LSL | LSR
| EQ | NE | LT | GT | LE | GE.

(* The string is the textual representation of the constant in
   the source code. *)
Inductive constant :=
| CONST_ENUM  : ident -> constant
| CONST_INT   : string -> constant
| CONST_FLOAT : floatInfo -> constant
| CONST_CHAR  : bool -> list char_code -> constant.

Inductive clock :=
| BASE  : clock
| ON    : clock -> ident -> ident -> clock. (* ck on x = C *)

Inductive preclock :=
| FULLCK : clock -> preclock
| WHENCK : ident -> ident -> preclock. (* when x = C *)

Inductive expression :=
| UNARY    : unary_operator -> list expression -> astloc -> expression
| BINARY   : binary_operator -> list expression -> list expression -> astloc
             -> expression
| CASE     : list expression -> list (ident * list expression) -> list expression -> astloc
             -> expression
| CAST     : type_name -> list expression -> astloc -> expression
| APP      : ident -> list expression -> list expression -> astloc -> expression
| CONSTANT : constant -> astloc -> expression
| VARIABLE : ident -> astloc -> expression
| LAST     : ident -> astloc -> expression
| FBY      : list expression -> list expression -> astloc -> expression
| ARROW    : list expression -> list expression -> astloc -> expression
| WHEN     : list expression -> ident -> ident -> astloc -> expression
| MERGE    : ident -> list (ident * list expression) -> astloc -> expression.

Definition expression_loc (e: expression) : astloc :=
  match e with
  | UNARY _ _ l => l
  | BINARY _ _ _ l => l
  | CASE _ _ _ l => l
  | CAST _ _ l => l
  | APP _ _ _ l => l
  | CONSTANT _ l => l
  | VARIABLE _ l => l
  | LAST _ l => l
  | FBY _ _ l => l
  | ARROW _ _ l => l
  | WHEN _ _ _ l => l
  | MERGE _ _ l => l
  end.

Definition var_decls : Type := list (ident * (type_name * preclock * astloc)).
Definition local_decls : Type := list (ident * (type_name * preclock * list expression * astloc)).

Definition equation : Type := (list ident * list expression * astloc)%type.

Definition transition : Type := (list expression * (ident * bool) * astloc).

Inductive block :=
| BEQ      : equation -> block
| BRESET   : list block -> list expression -> astloc -> block
| BSWITCH  : list expression -> list (ident * list block) -> astloc -> block
| BAUTO    : list (list expression * ident * astloc) * ident -> list (ident * (local_decls * list block * list transition)) -> astloc -> block
| BLOCAL   : local_decls -> list block -> astloc -> block.

Inductive declaration :=
      (*  name  has_state  inputs       outputs      locals   *)
| NODE : ident -> bool -> var_decls -> var_decls
         -> block -> astloc -> declaration
| TYPE : ident -> list ident -> astloc -> declaration.

Definition declaration_loc (d: declaration) : astloc :=
  match d with
  | NODE name has_state inputs outputs eqs loc => loc
  | TYPE name constructors loc => loc
  end.

(** Custom induction schemes *)

From Coq Require Import List.

Section expression_ind2.
  Variable P : expression -> Prop.

  Hypothesis UNARYCase:
    forall u es a,
      Forall P es ->
      P (UNARY u es a).

  Hypothesis BINARYCase:
    forall b es1 es2 a,
      Forall P es1 ->
      Forall P es2 ->
      P (BINARY b es1 es2 a).

  Hypothesis CASECase:
    forall es brs d a,
      Forall P es ->
      Forall (fun e => Forall P (snd e)) brs ->
      Forall P d ->
      P (CASE es brs d a).

  Hypothesis CASTCase:
    forall t es a,
      Forall P es ->
      P (CAST t es a).

  Hypothesis APPCase:
    forall f es r a,
      Forall P es ->
      Forall P r ->
      P (APP f es r a).

  Hypothesis CONSTANTCase:
    forall c a,
      P (CONSTANT c a).

  Hypothesis VARIABLECase:
    forall x a,
      P (VARIABLE x a).

  Hypothesis LASTCase:
    forall x a,
      P (LAST x a).

  Hypothesis FBYCase:
    forall e0s es a,
      Forall P e0s ->
      Forall P es ->
      P (FBY e0s es a).

  Hypothesis ARROWCase:
    forall e0s es a,
      Forall P e0s ->
      Forall P es ->
      P (ARROW e0s es a).

  Hypothesis WHENCase:
    forall es x b a,
      Forall P es ->
      P (WHEN es x b a).

  Hypothesis MERGECase:
    forall x es a,
      Forall (fun e => Forall P (snd e)) es ->
      P (MERGE x es a).

  Local Ltac SolveForall :=
    match goal with
    | |- Forall ?P ?l => induction l; auto
    | _ => idtac
    end.

  Fixpoint expression_ind2 (e: expression) : P e.
  Proof.
    destruct e.
    - apply UNARYCase; SolveForall.
    - apply BINARYCase; SolveForall.
    - apply CASECase; SolveForall.
      constructor; auto.
      SolveForall.
    - apply CASTCase; SolveForall.
    - apply APPCase; SolveForall.
    - apply CONSTANTCase; SolveForall.
    - apply VARIABLECase; SolveForall.
    - apply LASTCase; SolveForall.
    - apply FBYCase; SolveForall.
    - apply ARROWCase; SolveForall.
    - apply WHENCase; SolveForall.
    - apply MERGECase; SolveForall.
      constructor; auto.
      SolveForall.
  Qed.

End expression_ind2.

Section block_ind2.
  Variable P : block -> Prop.

  Hypothesis EQCase : forall equ,
    P (BEQ equ).

  Hypothesis RESETCase : forall blks er loc,
      Forall P blks ->
      P (BRESET blks er loc).

  Hypothesis SWITCHCase : forall ec branches loc,
      Forall (fun blks => Forall P (snd blks)) branches ->
      P (BSWITCH ec branches loc).

  Hypothesis AUTOCase : forall ini states loc,
      Forall (fun '(_, (_, blks, _)) => Forall P blks) states ->
      P (BAUTO ini states loc).

  Hypothesis LOCALCase : forall locs blks loc,
      Forall P blks ->
      P (BLOCAL locs blks loc).

  Fixpoint block_ind2 (bck: block) : P bck.
  Proof.
    destruct bck.
    - apply EQCase; auto.
    - apply RESETCase.
      induction l; auto.
    - apply SWITCHCase.
      induction l0 as [|(?&?)]; constructor; eauto; simpl.
      induction l0; auto.
    - apply AUTOCase.
      induction l as [|(?&(?&?)&?)]; constructor; eauto; simpl.
      induction l0; auto.
    - apply LOCALCase.
      induction l0; auto.
  Qed.
End block_ind2.
