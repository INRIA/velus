Require Import Rustre.Common.
Require Import Rustre.Dataflow.Syntax.

(** 

The predicate [Is_free x t : Prop] states that the variable [x] is
used in the term [t]. If [t] is an equation, this collects the
variables in the right-hand side of the equation. In particular, if
[t] is [x = v0 fby x], [x] will (perhaps confusingly) be free.

 *)

Inductive Is_free_in_clock : ident -> clock -> Prop :=
| FreeCon1:
    forall x ck' xc,
      Is_free_in_clock x (Con ck' x xc)
| FreeCon2:
    forall x y ck' xc,
      Is_free_in_clock x ck'
      -> Is_free_in_clock x (Con ck' y xc).

(* Warning: induction scheme is not strong enough. *)
Inductive Is_free_in_lexp : ident -> lexp -> Prop :=
| FreeEvar: forall x, Is_free_in_lexp x (Evar x)
| FreeEwhen1: forall e c cv x,
    Is_free_in_lexp x e ->
    Is_free_in_lexp x (Ewhen e c cv)
| FreeEwhen2: forall e c cv,
    Is_free_in_lexp c (Ewhen e c cv)
| FreeEop : forall c op es,
    Nelist.Exists (Is_free_in_lexp c) es -> Is_free_in_lexp c (Eop op es).

Inductive Is_free_in_laexp : ident -> laexp -> Prop :=
| freeLAexp1: forall ck e x,
    Is_free_in_lexp x e ->
    Is_free_in_laexp x (LAexp ck e)
| freeLAexp2: forall ck e x,
    Is_free_in_clock x ck ->
    Is_free_in_laexp x (LAexp ck e).

Inductive Is_free_in_cexp : ident -> cexp -> Prop :=
| FreeEmerge_cond: forall i t f,
    Is_free_in_cexp i (Emerge i t f)
| FreeEmerge_true: forall i t f x,
    Is_free_in_cexp x t ->
    Is_free_in_cexp x (Emerge i t f)
| FreeEmerge_false: forall i t f x,
    Is_free_in_cexp x f ->
    Is_free_in_cexp x (Emerge i t f)
| FreeEexp: forall e x,
    Is_free_in_lexp x e ->
    Is_free_in_cexp x (Eexp e).

Inductive Is_free_in_caexp : ident -> caexp -> Prop :=
| FreeCAexp1: forall ck ce x,
    Is_free_in_cexp x ce ->
    Is_free_in_caexp x (CAexp ck ce)
| FreeCAexp2: forall ck ce x,
    Is_free_in_clock x ck ->
    Is_free_in_caexp x (CAexp ck ce).

Inductive Is_free_in_equation : ident -> equation -> Prop :=
| FreeEqDef:
    forall x cae i,
      Is_free_in_caexp i cae ->
      Is_free_in_equation i (EqDef x cae)
| FreeEqApp:
    forall x f lae i,
      Is_free_in_laexp i lae ->
      Is_free_in_equation i (EqApp x f lae)
| FreeEqFby:
    forall x v lae i,
      Is_free_in_laexp i lae ->
      Is_free_in_equation i (EqFby x v lae).

Hint Constructors Is_free_in_clock Is_free_in_lexp
     Is_free_in_laexp Is_free_in_cexp Is_free_in_caexp
     Is_free_in_equation.
