From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Obc.ObcSyntax.
From Velus Require Import Obc.ObcSemantics.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type OBCINVARIANTS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import SynObc: Velus.Obc.ObcSyntax.OBCSYNTAX Ids Op OpAux)
       (Import SemObc: Velus.Obc.ObcSemantics.OBCSEMANTICS Ids Op OpAux SynObc).

  (** ** Determine whether an Obc command can modify a variable or state. *)

  Inductive Can_write_in : ident -> stmt -> Prop :=
  | CWIAssign: forall x e,
      Can_write_in x (Assign x e)
  | CWIAssignSt: forall x e,
      Can_write_in x (AssignSt x e)
  | CWISwitch: forall x e ss d,
      Exists (fun s => Can_write_in x (or_default d s)) ss ->
      Can_write_in x (Switch e ss d)
  | CWICall_ap: forall x xs cls i f es,
      In x xs ->
      Can_write_in x (Call xs cls i f es)
  | CWIComp1: forall x s1 s2,
      Can_write_in x s1 ->
      Can_write_in x (Comp s1 s2)
  | CWIComp2: forall x s1 s2,
      Can_write_in x s2 ->
      Can_write_in x (Comp s1 s2).

  Global Hint Constructors Can_write_in : obcinv.

  Lemma cannot_write_in_Switch:
    forall x e ss d,
      ~ Can_write_in x (Switch e ss d)
      <->
      Forall (fun s => ~ Can_write_in x (or_default d s)) ss.
  Proof.
    intros; split; intro H.
    - induction ss; constructor; auto with obcinv.
      apply IHss; intro W; apply H.
      inv W; constructor. now right.
    - induction ss; intro HH; inv HH; inv H; take (Exists _ _) and inv it; eauto.
      apply IHss; auto with obcinv.
  Qed.

  Lemma Can_write_in_Comp:
    forall x s1 s2,
      Can_write_in x (Comp s1 s2) <-> (Can_write_in x s1 \/ Can_write_in x s2).
  Proof.
    split; intros HH.
    - inversion_clear HH; auto.
    - destruct HH; auto with obcinv.
  Qed.

  Lemma cannot_write_in_Comp:
    forall x s1 s2,
      ~ Can_write_in x (Comp s1 s2)
      <->
      ~ Can_write_in x s1 /\ ~ Can_write_in x s2.
  Proof.
    intros; split; intro; try (intro HH; inversion_clear HH); intuition.
  Qed.

  Ltac cannot_write :=
    repeat progress
           match goal with
           | |- forall x, Is_free_in_exp x _ -> _ => intros
           | Hfw: (forall x, Is_free_in_exp x ?e -> _),
                  Hfree: Is_free_in_exp ?x ?e |- _
             => pose proof (Hfw x Hfree); clear Hfw
           | |- _ /\ _ => split
           | |- ~Can_write_in _ _ => intro
           | H: Can_write_in _ (Comp _ _) |- _ => inversion_clear H
           | _ => now intuition
           end.

  Local Hint Constructors Is_free_in_exp : obcinv.

  Lemma cannot_write_exp_eval:
    forall prog s me ve me' ve' e v,
      (forall x, Is_free_in_exp x e -> ~ Can_write_in x s)
      -> exp_eval me ve e v
      -> stmt_eval prog me ve s (me', ve')
      -> exp_eval me' ve' e v.
  Proof.
    induction s using stmt_ind2; intros me ve me' ve' e' v Hfree Hexp Hstmt.
    - inv Hstmt.
      rewrite <-exp_eval_extend_venv; auto.
      intro Habs. apply (Hfree x); eauto with obcinv.
    - inv Hstmt.
      eapply exp_eval_extend_menv; eauto.
      intro Habs. apply (Hfree x); auto with obcinv.
    - inv Hstmt.
      take (nth_error _ _ = _) and eapply nth_error_In in it as Hin.
      pose proof Hin as Hin'; eapply Forall_forall in Hin'; eauto; simpl in Hin'.
      cases.
      eapply Hin'; eauto.
      intros ???; eapply Hfree; eauto.
      constructor; apply Exists_exists; eauto.
    - inv Hstmt.
      match goal with
      | Hs1: stmt_eval _ _ _ s1 _,
             Hs2: stmt_eval _ _ _ s2 _ |- _
        => apply IHs1 with (2:=Hexp) in Hs1;
             [apply IHs2 with (2:=Hs1) (3:=Hs2)|];
             now cannot_write
      end.
    - inv Hstmt.
      apply exp_eval_extend_menv_by_obj.
      rewrite exp_eval_adds_opt_extend_venv; auto.
      intros x Hin Hfree'. apply Hfree in Hfree'.
      auto with obcinv.
    - now inv Hstmt.
  Qed.

  Lemma Can_write_in_Switch:
    forall e ss d x,
      Can_write_in x (Switch e ss d) <-> (Exists (fun s => Can_write_in x (or_default d s)) ss).
  Proof.
    split; [inversion_clear 1|intros [HH|HH]]; auto with obcinv.
  Qed.

  (** ** Determine whether an Obc command can modify a variable . *)

  Inductive Can_write_in_var : ident -> stmt -> Prop :=
  | CWIVAssign: forall x e,
      Can_write_in_var x (Assign x e)
  | CWIVSwitch: forall x e ss d,
      Exists (fun s => Can_write_in_var x (or_default d s)) ss ->
      Can_write_in_var x (Switch e ss d)
  | CWIVCall_ap: forall x xs cls i f es,
      In x xs ->
      Can_write_in_var x (Call xs cls i f es)
  | CWIVComp1: forall x s1 s2,
      Can_write_in_var x s1 ->
      Can_write_in_var x (Comp s1 s2)
  | CWIVComp2: forall x s1 s2,
      Can_write_in_var x s2 ->
      Can_write_in_var x (Comp s1 s2).
  Global Hint Constructors Can_write_in_var : obcinv.

  Lemma Can_write_in_var_Can_write_in : forall x stmt,
      Can_write_in_var x stmt ->
      Can_write_in x stmt.
  Proof.
    intros ? stmt.
    induction stmt using stmt_ind2; intros Can; inv Can; auto using Can_write_in.
    constructor.
    eapply Forall_Exists in H2; eauto.
    eapply Exists_Exists; [|eauto]. intros ? (?&?); auto.
  Qed.
  Global Hint Resolve Can_write_in_var_Can_write_in : obcinv.

  Lemma Can_write_in_var_Switch:
    forall e ss d x,
      Can_write_in_var x (Switch e ss d) <-> (Exists (fun s => Can_write_in_var x (or_default d s)) ss).
  Proof.
    split; [inversion_clear 1|intros [HH|HH]]; auto with obcinv.
  Qed.

  Lemma cannot_write_in_var_Switch:
    forall x e ss d,
      ~ Can_write_in_var x (Switch e ss d)
      <-> Forall (fun s => ~Can_write_in_var x (or_default d s)) ss.
  Proof.
    intros. rewrite Forall_Exists_neg, Can_write_in_var_Switch. reflexivity.
  Qed.

  Lemma Can_write_in_var_Comp:
    forall x s1 s2,
      Can_write_in_var x (Comp s1 s2) <-> (Can_write_in_var x s1 \/ Can_write_in_var x s2).
  Proof.
    split; intros HH.
    - inversion_clear HH; auto.
    - destruct HH; auto with obcinv.
  Qed.

  Lemma cannot_write_in_var_Comp:
    forall x s1 s2,
      ~ Can_write_in_var x (Comp s1 s2)
      <->
      ~ Can_write_in_var x s1 /\ ~ Can_write_in_var x s2.
  Proof.
    intros; split; intro; try (intro HH; inversion_clear HH); intuition.
  Qed.

  (** ** Assert that an Obc command never writes to a variable more than once. *)

  Inductive No_Overwrites : stmt -> Prop :=
  | NoOAssign: forall x e,
      No_Overwrites (Assign x e)
  | NoOAssignSt: forall x e,
      No_Overwrites (AssignSt x e)
  | NoOSwitch: forall e ss d,
      Forall (fun s => No_Overwrites (or_default d s)) ss ->
      No_Overwrites (Switch e ss d)
  | NoOCall: forall xs cls i f es,
      No_Overwrites (Call xs cls i f es)
  | NoOComp: forall s1 s2,
      (forall x, Can_write_in_var x s1 -> ~Can_write_in_var x s2) ->
      (forall x, Can_write_in_var x s2 -> ~Can_write_in_var x s1) ->
      No_Overwrites s1 ->
      No_Overwrites s2 ->
      No_Overwrites (Comp s1 s2)
  | NoOSkip:
      No_Overwrites Skip.

  Global Hint Constructors No_Overwrites : obcinv.

  Lemma cannot_write_in_var_No_Overwrites:
    forall s,
      (forall x, ~Can_write_in_var x s) -> No_Overwrites s.
  Proof.
    induction s using stmt_ind2; auto with obcinv; intro HH.
    - setoid_rewrite cannot_write_in_var_Switch in HH.
      constructor; apply Forall_forall; intros.
      eapply Forall_forall in H; eauto.
      apply H.
      intro y; specialize (HH y).
      eapply Forall_forall in HH; eauto.
    - setoid_rewrite cannot_write_in_var_Comp in HH.
      constructor; try (apply IHs1 || apply IHs2);
        intros x Hcw; specialize (HH x); intuition.
  Qed.

  (** ** Assert that Obc calls never involve undefined variables. *)

  Inductive No_Naked_Vars : stmt -> Prop :=
  | NNVAssign: forall x e,
      No_Naked_Vars (Assign x e)
  | NNVAssignSt: forall x e,
      No_Naked_Vars (AssignSt x e)
  | NNVSwitch: forall e ss d,
      Forall (fun s => No_Naked_Vars (or_default d s)) ss ->
      No_Naked_Vars (Switch e ss d)
  | NNVCall: forall xs cls i f es,
      Forall (fun e => forall x ty, e <> Var x ty) es ->
      No_Naked_Vars (Call xs cls i f es)
  | NNVComp: forall s1 s2,
      No_Naked_Vars s1 ->
      No_Naked_Vars s2 ->
      No_Naked_Vars (Comp s1 s2)
  | NNVSkip:
      No_Naked_Vars Skip.

  Global Hint Constructors No_Naked_Vars : obcinv.

  Lemma stmt_eval_mono:
    forall p s me ve me' ve',
      stmt_eval p me ve s (me', ve') ->
      forall x, Env.In x ve -> Env.In x ve'.
  Proof.
    induction s using stmt_ind2; intros * Heval ??; inv Heval;
      eauto using Env.adds_opt_mono with env obcinv.
    take (nth_error _ _ = _) and apply nth_error_In in it.
    do 2 take (Forall _ _) and eapply Forall_forall in it; eauto.
  Qed.

  Lemma no_vars_in_args_spec:
    forall me ve es vos,
      Forall2 (exp_eval me ve) es vos ->
      Forall (fun e => forall x ty, e <> Var x ty) es ->
      Forall (fun vo => vo <> None) vos.
  Proof.
    induction 1 as [|???? Exp]; auto.
    inversion_clear 1 as [|?? E].
    constructor; auto.
    intro; subst.
    inv Exp; eapply E; eauto.
  Qed.

End OBCINVARIANTS.

Module ObcInvariantsFun
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import OpAux: OPERATORS_AUX Ids Op)
       (Import SynObc: Velus.Obc.ObcSyntax.OBCSYNTAX Ids Op OpAux)
       (Import SemObc: Velus.Obc.ObcSemantics.OBCSEMANTICS Ids Op OpAux SynObc)
       <: OBCINVARIANTS Ids Op OpAux SynObc SemObc.

  Include OBCINVARIANTS Ids Op OpAux SynObc SemObc.

End ObcInvariantsFun.
