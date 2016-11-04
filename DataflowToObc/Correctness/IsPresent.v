Require Import Rustre.Common.
Require Import Rustre.Operators.
Require Import Rustre.RMemory.
Require Import Rustre.Dataflow.
Require Import Rustre.Obc.Syntax.
Require Import Rustre.Obc.Semantics.
Require Import Rustre.DataflowToObc.Translation.


(** * Tying clock semantics and imperative semantics *)

(** 

The translation of equations is always guarded by a [Control ck]. When
[ck] is false, the equation is not executed. It is therefore crucial
to tie the result of [Control ck] with the dataflow semantics of
[ck]. This is achieved by the following inductive relation.

Assumption: the base clock is [true] *)

Module Type ISPRESENT
       (Import Ids : IDS)
       (Import Op  : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import SynDF : Rustre.Dataflow.Syntax.SYNTAX Ids Op)
       (Import SynMP : Rustre.Obc.Syntax.SYNTAX Ids Op OpAux)
       (Import SemMP : Rustre.Obc.Semantics.SEMANTICS Ids Op OpAux SynMP)
       (Import Mem   : MEMORIES Ids Op SynDF)
       (Import Trans : TRANSLATION Ids Op OpAux SynDF SynMP Mem).

  Inductive Is_present_in (mems: PS.t) heap stack
  : clock -> Prop :=
  | IsCbase: Is_present_in mems heap stack Cbase
  | IsCon:
      forall ck c v b,
        Is_present_in mems heap stack ck
        -> exp_eval heap stack (tovar mems (c, bool_type)) v
        -> val_to_bool v = Some b
        -> Is_present_in mems heap stack (Con ck c b).

  Inductive Is_absent_in (mems: PS.t) heap stack: clock -> Prop :=
  | IsAbs1:
      forall ck c v,
        Is_absent_in mems heap stack ck
        -> Is_absent_in mems heap stack (Con ck c v)
  | IsAbs2:
      forall ck c v b,
        Is_present_in mems heap stack ck
        -> exp_eval heap stack (tovar mems (c, bool_type)) v
        -> val_to_bool v = Some b
        -> Is_absent_in mems heap stack (Con ck c (negb b)).

  (** ** Properties *)

  Lemma exp_eval_tovar_dec:
    forall menv env mems c,
      {exp_eval menv env (tovar mems c) true_val}
      + {exp_eval menv env (tovar mems c) false_val}
      + {~exp_eval menv env (tovar mems c) true_val
         /\ ~exp_eval menv env (tovar mems c) false_val}.
  Proof.
    Ltac no_match := right; split; inversion 1; subst; unfold mfind_mem in *;
                     match goal with
                     | H: PM.find _ _ = _,
                       H': PM.find _ _ = _ |- _ => rewrite H in H';
                                                   inversion H'
                     end.
    intros menv env mems c.
    unfold tovar; destruct c as [c ty].
    destruct (PS.mem c mems).
    - case_eq (mfind_mem c menv); [|now no_match].
      intro v.
      destruct (val_dec v true_val) as [Ht|Ht].
      + rewrite Ht. left; left; now constructor.
      + intro.
        destruct (val_dec v false_val) as [Hf|Hf].
        rewrite Hf in *.
        left; right; now constructor.
        now no_match; [apply Ht|apply Hf].
    - case_eq (PM.find c env); [|now no_match].
      intro v.
      destruct (val_dec v true_val) as [Ht|Ht].
      + rewrite Ht; left; left; now constructor.
      + destruct (val_dec v false_val) as [Hf|Hf].
        rewrite Hf; left; right; now constructor.
        now no_match; [apply Ht|apply Hf].
  Qed.
  
  Lemma Is_present_in_dec:
    forall mems menv env ck,
      {Is_present_in mems menv env ck}+{~Is_present_in mems menv env ck}.
  Proof.
    intros.
    induction ck.
    - left; constructor.
    - destruct IHck.
      + destruct (exp_eval_tovar_dec menv env mems (i, bool_type))
          as [[HH|HH]|[HH1 HH2]].
        * destruct b; [left|right].
          econstructor (eauto); apply val_to_bool_true.
          inversion 1; subst.
          apply exp_eval_det with (1:=HH) in H4.
          now subst; rewrite val_to_bool_true in *.
        * destruct b; [right|left].
          inversion 1; subst.
          apply exp_eval_det with (1:=HH) in H4.
          now subst; rewrite val_to_bool_false in *.
          econstructor (eauto); apply val_to_bool_false.
        * right. inversion_clear 1.
          destruct b.
          apply val_to_bool_true' in H2.
          rewrite H2 in *. now apply HH1.
          apply val_to_bool_false' in H2.
          rewrite H2 in *. now apply HH2.
      + right; inversion_clear 1; auto.
  Qed.

  Lemma Is_absent_in_disj:
    forall mems menv env ck c v,
      Is_absent_in mems menv env (Con ck c v)
      -> (Is_absent_in mems menv env ck
         \/ (forall v', exp_eval menv env (tovar mems (c, bool_type)) v'
             -> (if v then v' <> true_val else v' <> false_val))).
  Proof.
    intros until c.
    inversion_clear 1 as [|? ? ? b ? Hexp Hvb]; intuition.
    right; intros v' Hexp'; destruct b.
    - apply val_to_bool_true' in Hvb; subst.
      apply exp_eval_det with (1:=Hexp') in Hexp; subst.
      apply true_not_false_val.
    - apply val_to_bool_false' in Hvb; subst.
      apply exp_eval_det with (1:=Hexp') in Hexp; subst.
      simpl. intro H; symmetry in H.
      now apply true_not_false_val.
  Qed.

End ISPRESENT.

Module IsPresentFun
       (Import Ids : IDS)
       (Import Op  : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import SynDF : Rustre.Dataflow.Syntax.SYNTAX Ids Op)
       (Import SynMP : Rustre.Obc.Syntax.SYNTAX Ids Op OpAux)
       (Import SemMP : Rustre.Obc.Semantics.SEMANTICS Ids Op OpAux SynMP)
       (Import Mem   : MEMORIES Ids Op SynDF)
       (Import Trans : TRANSLATION Ids Op OpAux SynDF SynMP Mem)
       <: ISPRESENT Ids Op OpAux SynDF SynMP SemMP Mem Trans.

    Include ISPRESENT Ids Op OpAux SynDF SynMP SemMP Mem Trans.
End IsPresentFun.