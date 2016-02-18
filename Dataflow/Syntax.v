Require Import Rustre.Common.
Require Import PArith.
Require Import Rustre.Nelist.

Import List.ListNotations.
Open Scope list_scope.


(** * Dataflow language *)

Inductive clock : Set :=
| Cbase : clock                          (* base clock *)
| Con : clock -> ident -> bool -> clock. (* subclock *)

Implicit Type ck : clock.

(** ** Syntax *)

Inductive lexp : Set :=
  | Econst : const -> lexp
  | Evar : ident -> lexp
  | Ewhen : lexp -> ident -> bool -> lexp
  | Eop : operator -> nelist lexp -> lexp.

Definition lexps := nelist lexp.

Inductive cexp : Set :=
  | Emerge : ident -> cexp -> cexp -> cexp 
  | Eexp : lexp -> cexp.

Implicit Type le: lexp.
Implicit Type les: lexps.
Implicit Type ce: cexp.

(** ** Equations *)

Inductive equation : Type :=
  | EqDef : ident -> clock -> cexp -> equation
  | EqApp : ident -> clock -> ident -> lexps -> equation
  | EqFby : ident -> clock -> const -> lexp -> equation.

Implicit Type eqn: equation.

(** ** Node *)

Record node : Set := mk_node {
  n_name : ident;
  n_input : nelist ident;
  n_output : ident;
  n_eqs : list equation }.

Implicit Type N: node.

(** ** Program *)

Definition global := list node.

Implicit Type G: global.

Definition find_node (f : ident) : global -> option node :=
  List.find (fun n=> ident_eqb n.(n_name) f).


(** Stronger induction scheme for lexp *)
Definition lexp_ind2 : forall P : lexp -> Prop,
  (forall c, P (Econst c)) ->
  (forall i, P (Evar i)) ->
  (forall le, P le -> forall i b, P (Ewhen le i b)) ->
  (forall op les, Nelist.Forall P les -> P (Eop op les)) ->
  forall le, P le.
Proof.
intros P Hconst Hvar Hwhen Hop. fix 1.
intro le.
destruct le as [c | i | le | op les].
+ apply Hconst.
+ apply Hvar.
+ apply Hwhen. apply lexp_ind2.
+ apply Hop. induction les; constructor.
  - apply lexp_ind2.
  - apply lexp_ind2.
  - apply IHles.
Defined.
