Require Import Rustre.Common.
Require Import Rustre.RMemory.
Require Import Rustre.Dataflow.
Require Import Rustre.Minimp.Syntax.
Require Import Rustre.Minimp.Semantics.
Require Import Rustre.DataflowToMinimp.Translation.


(** * Tying clock semantics and imperative semantics *)

(** 

The translation of equations is always guarded by a [Control ck]. When
[ck] is false, the equation is not executed. It is therefore crucial
to tie the result of [Control ck] with the dataflow semantics of
[ck]. This is achieved by the following inductive relation.

Assumption: the base clock is [true] *)

Module Type ISPRESENT
       (Import Op : OPERATORS)
       (Import SynDF : Rustre.Dataflow.Syntax.SYNTAX Op)
       (Import SynMP : Rustre.Minimp.Syntax.SYNTAX Op)
       (Import SemMP : Rustre.Minimp.Semantics.SEMANTICS Op SynMP)
       (Import Trans : TRANSLATION Op SynDF SynMP).
    
  Inductive Is_present_in (mems: PS.t) heap stack
  : clock -> Prop :=
  | IsCbase: Is_present_in mems heap stack Cbase
  | IsCon:
      forall ck c ty v,
        Is_present_in mems heap stack ck
        -> exp_eval heap stack (tovar mems (c, ty)) (Vbool v)
        -> Is_present_in mems heap stack (Con ck c ty v).

  Inductive Is_absent_in (mems: PS.t) heap stack: clock -> Prop :=
  | IsAbs1:
      forall ck c ty v,
        Is_absent_in mems heap stack ck
        -> Is_absent_in mems heap stack (Con ck c ty v)
  | IsAbs2:
      forall ck c ty v1 v2,
        Is_present_in mems heap stack ck
        -> exp_eval heap stack (tovar mems (c, ty)) (Vbool v1)
        -> v2 <> v1
        -> Is_absent_in mems heap stack (Con ck c ty v2).


  (** ** Properties *)

  Lemma exp_eval_tovar_Cbool_dec:
    forall menv env mems c v,
      {exp_eval menv env (tovar mems c) (Vbool v)}
      + {~exp_eval menv env (tovar mems c) (Vbool v)}.
  Proof.
    Ltac no_match := right; inversion_clear 1; try unfold mfind_mem in *;
                     match goal with
                     | H: PM.find _ _ = _,
                          H': PM.find _ _ = _ |- _ => rewrite H in H'; discriminate
                     end.
    intros menv env mems c v.
    unfold tovar; destruct c as [c ty].
    destruct (PS.mem c mems).
    - case_eq (mfind_mem c menv).
      + intro c0; destruct c0.
        * destruct b; destruct v; (left; apply estate; assumption) || no_match.
        * no_match.
      + no_match.
    - case_eq (PM.find c env).
      + intro c0; destruct c0.
        * destruct b; destruct v; (left; apply evar; assumption) || no_match.
        * no_match.
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
      + destruct (exp_eval_tovar_Cbool_dec menv env mems (i, t) b); destruct b;
        (left; constructor; assumption) || right; inversion_clear 1; auto.
      + right; inversion_clear 1; auto.
  Qed.


  Lemma Is_absent_in_disj:
    forall mems menv env ck c ty v,
      Is_absent_in mems menv env (Con ck c ty v)
      -> (Is_absent_in mems menv env ck
         \/ (forall v', exp_eval menv env (tovar mems (c, ty)) (Vbool v')
                  -> v' <> v)).
  Proof.
    intros until c.
    inversion_clear 1 as [ | ? ? ? ? ? Hp Hexp Hneq]; intuition.
    right; intros v' Hexp'.
    intro HR; rewrite <-HR in *; clear HR.
    apply Hneq.
    pose proof (exp_eval_det _ _ _ _ _ Hexp Hexp') as Heq.
    now inversion Heq. 
  Qed.

End ISPRESENT.