Require Import Rustre.Common.
Require Import Rustre.Heap.
Require Import Rustre.Dataflow.
Require Import Rustre.Minimp.Syntax.
Require Import Rustre.Minimp.Semantics.
Require Import Rustre.Translation.


(* Assumption: the base clock is [true] *)
Inductive Is_present_in (mems: PS.t) heap stack
  : clock -> Prop :=
| IsCbase: Is_present_in mems heap stack Cbase
| IsCon:
    forall ck c v,
      Is_present_in mems heap stack ck
      -> exp_eval heap stack (tovar mems c) (Cbool v)
      -> Is_present_in mems heap stack (Con ck c v).

Inductive Is_absent_in (mems: PS.t) heap stack: clock -> Prop :=
| IsAbs1:
    forall ck c v,
      Is_absent_in mems heap stack ck
      -> Is_absent_in mems heap stack (Con ck c v)
| IsAbs2:
    forall ck c v1 v2,
         Is_present_in mems heap stack ck
      -> exp_eval heap stack (tovar mems c) (Cbool v1)
      -> v2 <> v1
      -> Is_absent_in mems heap stack (Con ck c v2).


Lemma exp_eval_tovar_Cbool_dec:
  forall menv env mems c v,
    {exp_eval menv env (tovar mems c) (Cbool v)}
    + {~exp_eval menv env (tovar mems c) (Cbool v)}.
Proof.
  Ltac no_match := right; inversion_clear 1; try unfold mfind_mem in *;
                   match goal with
                   | H: PM.find _ _ = _ |- _ => rewrite H in *; discriminate
                   end.
  intros menv env mems c v.
  unfold tovar.
  destruct (PS.mem c mems).
  - case_eq (mfind_mem c menv).
    + intro c0; destruct c0.
      * no_match.
      * destruct b; destruct v; (left; apply estate; assumption) || no_match.
    + no_match.
  - case_eq (PM.find c env).
    + intro c0; destruct c0.
      * no_match.
      * destruct b; destruct v; (left; apply evar; assumption) || no_match.
    + no_match.
Qed.



Lemma Is_present_in_dec:
  forall mems menv env ck,
    {Is_present_in mems menv env ck}+{~Is_present_in mems menv env ck}.
Proof.
  intros.
  induction ck.
  - left; constructor.
  - destruct IHck.
    + destruct (exp_eval_tovar_Cbool_dec menv env mems i b); destruct b;
      (left; constructor; assumption) || right; inversion_clear 1; auto.
    + right; inversion_clear 1; auto.
Qed.


Lemma Is_absent_in_disj:
  forall mems menv env ck c v,
    Is_absent_in mems menv env (Con ck c v)
    -> (Is_absent_in mems menv env ck
        \/ (forall v', exp_eval menv env (tovar mems c) (Cbool v')
                       -> v' <> v)).
Proof.
  intros until c.
  inversion_clear 1 as [ | ? ? ? ? Hp Hexp Hneq]; intuition.
  right; intros v' Hexp'.
  intro HR; rewrite <-HR in *; clear HR.
  apply Hneq.
  pose proof (exp_eval_det _ _ _ _ _ Hexp Hexp') as Heq.
  injection Heq; intuition.
Qed.
