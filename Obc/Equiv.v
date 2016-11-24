Require Import Coq.FSets.FMapPositive.
Require Import PArith.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Obc.Syntax.
Require Import Velus.Obc.Semantics.

Require Import Relations.
Require Import Morphisms.
Require Import Setoid.

(** * Equivalence of Obc programs *)

(**

To prove the soundness of the if-then-else fusing optimization, we
define (and prove some properties about) equivalence of Obc
programs.

 *)
Module Type EQUIV
       (Ids          : IDS)
       (Op           : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Syn   : SYNTAX Ids Op OpAux)
       (Import Sem   : SEMANTICS Ids Op OpAux Syn).
  
  Definition stmt_eval_eq s1 s2: Prop :=
    forall prog menv env menv' env',
      stmt_eval prog menv env s1 (menv', env')
      <->
      stmt_eval prog menv env s2 (menv', env').
  
  Lemma stmt_eval_eq_refl:
    reflexive stmt stmt_eval_eq.
  Proof. now apply iff_refl. Qed.

  Lemma stmt_eval_eq_sym:
    symmetric stmt stmt_eval_eq.
  Proof.
    intros s1 s2 Heq prog menv env menv' env'.
    split; apply Heq.
  Qed.

  Lemma stmt_eval_eq_trans:
    transitive stmt stmt_eval_eq.
  Proof.
    intros s1 s2 s3 Heq1 Heq2 prog menv env menv' env'.
    split; intro HH; [apply Heq2, Heq1|apply Heq1, Heq2]; exact HH.
  Qed.

  Add Relation stmt (stmt_eval_eq)
      reflexivity proved by stmt_eval_eq_refl
      symmetry proved by stmt_eval_eq_sym
      transitivity proved by stmt_eval_eq_trans
        as stmt_eval_equiv.

  Instance stmt_eval_eq_Proper:
    Proper (eq ==> eq ==> eq ==> stmt_eval_eq ==> eq ==> iff) stmt_eval.
  Proof.
    intros prog' prog HR1 menv' menv HR2 env' env HR3 s1 s2 Heq r' r HR4;
    subst; destruct r as [menv' env'].
    now apply Heq.
  Qed.

  Instance stmt_eval_eq_Comp_Proper:
    Proper (stmt_eval_eq ==> stmt_eval_eq ==> stmt_eval_eq) Comp.
  Proof.
    intros s s' Hseq t t' Hteq prog menv env menv' env'.
    split; inversion_clear 1;
    [rewrite Hseq, Hteq in *; econstructor; eassumption
    |rewrite <-Hseq, <-Hteq in *; econstructor; eassumption].
  Qed.

  Lemma Comp_assoc:
    forall s1 s2 s3,
      stmt_eval_eq (Comp s1 (Comp s2 s3)) (Comp (Comp s1 s2) s3).
  Proof.
    intros prog s1 s2 s3 menv env menv' env'.
    split;
      intro HH;
      repeat progress
             match goal with
             | H:stmt_eval _ _ _ (Comp _ _) _ |- _ => inversion H; subst; clear H
             | |- _ => repeat econstructor; now eassumption
             end.
  Qed.

  Lemma stmt_eval_eq_Comp_Skip1:
    forall s, stmt_eval_eq (Comp Skip s) s.
  Proof.
    intros s prog menv env menv' env'.
    split.
    - inversion_clear 1;
      try match goal with
          | H:stmt_eval _ _ _ Skip _ |- _ => inversion H; subst; assumption
          end.
    - intro HH; econstructor; [now econstructor|eassumption].
  Qed.

  Lemma stmt_eval_eq_Comp_Skip2:
    forall s, stmt_eval_eq (Comp s Skip) s.
  Proof.
    intros s prog menv env menv' env'.
    split.
    - inversion_clear 1;
      try match goal with
          | H:stmt_eval _ _ _ Skip _ |- _ => inversion H; subst; assumption
          end.
    - intro HH; econstructor; [eassumption|now constructor].
  Qed.

  Instance stmt_eval_eq_Ifte_Proper:
    Proper (eq ==> stmt_eval_eq ==> stmt_eval_eq ==> stmt_eval_eq) Ifte.
  Proof.
    intros e e' Heeq s s' Hseq t t' Hteq prog menv env menv' env'.
    rewrite <-Heeq.
    split; inversion_clear 1;
      destruct b;
      try match goal with
          | H: exp_eval _ _ _ _ |- _ => apply Iifte with (1:=H)
          | H: stmt_eval _ _ _ _ _ |- _ =>
            (rewrite <-Hseq in H
             || rewrite <-Hteq in H
             || rewrite Hseq in H
                                || rewrite Hteq in H)
          end;
      try match goal with
          | H:val_to_bool ?v = Some true |- _ =>
            apply val_to_bool_true' in H
          | H:val_to_bool ?v = Some false |- _ =>
            apply val_to_bool_false' in H
          end; subst;
        econstructor; try eassumption;
          try apply val_to_bool_true;
          try apply val_to_bool_false';
          easy.
  Qed.
  
End EQUIV.

Module EquivFun
       (Ids          : IDS)
       (Op           : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Syn   : SYNTAX Ids Op OpAux)
       (Import Sem   : SEMANTICS Ids Op OpAux Syn)
       <: EQUIV Ids Op OpAux Syn Sem.
  Include EQUIV Ids Op OpAux Syn Sem.
End EquivFun.

