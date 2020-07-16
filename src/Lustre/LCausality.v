From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Permutation.
From Coq Require Import Setoid Morphisms.

From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.

From Velus Require Import Lustre.LSyntax.

(** * Lustre causality *)

(**
  Causality judgement over a Lustre program
  *)

Module Type LCAUSALITY
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import Syn : LSYNTAX Ids Op).

  Inductive Is_free_left (x : ident) : exp -> Prop :=
  | IFLvar : forall a,
      Is_free_left x (Evar x a)
  | IFLunop : forall op e a,
      Is_free_left x e ->
      Is_free_left x (Eunop op e a)
  | IFLbinop : forall op e1 e2 a,
      Is_free_left x e1
      \/ Is_free_left x e2 ->
      Is_free_left x (Ebinop op e1 e2 a)
  | IFLfby : forall e0s es a,
      Exists (Is_free_left x) e0s ->
      Is_free_left x (Efby e0s es a)
  | IFLwhen : forall es y b a,
      x = y
      \/ Exists (Is_free_left x) es ->
      Is_free_left x (Ewhen es y b a)
  | IFLmerge : forall ets efs y a,
      x = y
      \/ Exists (Is_free_left x) ets
      \/ Exists (Is_free_left x) efs ->
      Is_free_left x (Emerge y ets efs a)
  | IFLite : forall e ets efs a,
      Is_free_left x e
      \/ Exists (Is_free_left x) ets
      \/ Exists (Is_free_left x) efs ->
      Is_free_left x (Eite e ets efs a)
  | IFLapp : forall f es a,
      Exists (Is_free_left x) es ->
      Is_free_left x (Eapp f es None a)
  | IFLreset : forall f es r a,
      Exists (Is_free_left x) (r :: es) ->
      Is_free_left x (Eapp f es (Some r) a).

  Inductive Is_causal (inputs : list ident) : list equation -> Prop :=
  | ICnil:
      Is_causal inputs []
  | ICcons: forall eq eqs,
      Is_causal inputs eqs ->
      (forall x, Exists (Is_free_left x) (snd eq) ->
            In x (vars_defined eqs) \/ In x inputs) ->
      Is_causal inputs (eq :: eqs).
  Hint Constructors Is_causal.

  (* TODO: link with check_graph_spec *)
  Definition node_causal (n : node) :=
    exists eqs, Permutation (n_eqs n) eqs
           /\ Is_causal (map fst (n_in n)) eqs.

  Instance Is_causal_Proper:
    Proper (@Permutation ident ==> @eq (list equation) ==> iff)
           Is_causal.
  Proof.
    intros xs xs' Hperm eqs eqs' Heq; subst.
    split; intros Hcaus; induction Hcaus; auto.
    - constructor; auto.
      intros x Hex. apply H in Hex as [?|Hex]; auto.
      right. rewrite <- Hperm; auto.
    - constructor; auto.
      intros x Hex. apply H in Hex as [?|Hex]; auto.
      right. rewrite Hperm; auto.
  Qed.

  Lemma Is_causal_incl : forall ins1 ins2 eqs,
      incl ins1 ins2 ->
      Is_causal ins1 eqs ->
      Is_causal ins2 eqs.
  Proof.
    induction eqs; intros Hincl Hcaus; inv Hcaus; auto.
    constructor; auto.
    intros ? Hex. apply H2 in Hex as [?|Hex]; auto.
  Qed.

  Instance vars_defined_Proper:
    Proper (@Permutation equation ==> @Permutation ident)
           vars_defined.
  Proof.
    intros eqs eqs' Hperm; subst.
    unfold vars_defined. rewrite Hperm. reflexivity.
  Qed.

  Fact vars_defined_app : forall eqs1 eqs2,
      vars_defined (eqs1++eqs2) = vars_defined eqs1 ++ vars_defined eqs2.
  Proof.
    intros.
    unfold vars_defined. rewrite flat_map_app; auto.
  Qed.

  Lemma Is_causal_app1 : forall eqs eqs' ins,
      Is_causal ins (eqs ++ eqs') ->
      Is_causal (ins++vars_defined eqs') eqs.
  Proof.
    induction eqs; intros * Hcaus; simpl in *.
    - constructor.
    - inv Hcaus. eapply IHeqs in H1. constructor; auto.
      intros x Hex. apply H2 in Hex.
      rewrite vars_defined_app in Hex. rewrite in_app_iff in *.
      destruct Hex as [[?|?]|?]; auto.
  Qed.

  Lemma Is_causal_app2 : forall eqs eqs' ins,
      Is_causal ins eqs' ->
      Is_causal (ins++vars_defined eqs') eqs ->
      Is_causal ins (eqs ++ eqs').
  Proof.
    induction eqs; intros * Hcaus1 Hcaus2; simpl in *.
    - auto.
    - inv Hcaus2.
      constructor; auto.
      intros x Hex. apply H2 in Hex.
      rewrite vars_defined_app. rewrite in_app_iff in *.
      destruct Hex as [?|[?|?]]; auto.
  Qed.

  Lemma Is_causal_app : forall ins eqs1 eqs2,
      Is_causal ins eqs1 ->
      Is_causal ins eqs2 ->
      Is_causal ins (eqs1 ++ eqs2).
  Proof.
    intros * Hcaus1 Hcaus2.
    eapply Is_causal_app2; eauto.
    eapply Is_causal_incl; eauto.
    apply incl_appl, incl_refl.
  Qed.

  Lemma Forall_Is_causal : forall inputs eqs,
      Forall (fun '(_, es) => forall x, Exists (Is_free_left x) es -> In x inputs) eqs ->
      Is_causal inputs eqs.
  Proof.
    induction eqs; intros Hf; auto.
    inv Hf. constructor; auto.
    destruct a. intros x Hex; eauto.
  Qed.

End LCAUSALITY.

Module LCausality
       (Ids  : IDS)
       (Op   : OPERATORS)
       (Syn  : LSYNTAX Ids Op)
       <: LCAUSALITY Ids Op Syn.
  Include LCAUSALITY Ids Op Syn.
End LCausality.
