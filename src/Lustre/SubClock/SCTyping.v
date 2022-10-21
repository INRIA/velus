From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import CommonTyping.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Fresh.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import Lustre.LTyping.
From Velus Require Import Lustre.SubClock.SubClock.

Module Type SCTYPING
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Typ : LTYPING Ids Op OpAux Cks Senv Syn)
       (Import SC : SUBCLOCK Ids Op OpAux Cks Senv Syn).

  Section subclock.
    Variable bck : clock.
    Variable sub : Env.t ident.

    Variable Γ Γ' : static_env.

    Hypothesis NoLast : forall x, ~IsLast Γ x.

    Hypothesis Hsub : forall x y ty,
        Env.find x sub = Some y ->
        HasType Γ x ty ->
        HasType Γ' y ty.

    Hypothesis Hnsub : forall x ty,
        Env.find x sub = None ->
        HasType Γ x ty ->
        HasType Γ' x ty.

    Lemma rename_var_wt : forall x ty,
        HasType Γ x ty ->
        HasType Γ' (rename_var sub x) ty.
    Proof.
      unfold rename_var.
      intros * Hin.
      destruct (Env.find _ _) eqn:Hfind; simpl in *; eauto.
    Qed.

    Context {PSyn : block -> Prop} {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Hypothesis Hwbck : wt_clock G.(types) Γ' bck.

    Lemma subclock_clock_wt : forall ck,
        wt_clock G.(types) Γ ck ->
        wt_clock G.(types) Γ' (subclock_clock bck sub ck).
    Proof.
      induction ck; intros * Hwt; inv Hwt; simpl; auto.
      constructor; eauto using rename_var_wt.
    Qed.
    Local Hint Resolve subclock_clock_wt : ltyping.

    Lemma add_whens_wt : forall e ty,
        typeof e = [ty] ->
        wt_exp G Γ' e ->
        wt_exp G Γ' (add_whens e ty bck).
    Proof.
      clear Hsub Hnsub.
      induction bck as [|??? (?&?)]; intros * Hbase Hwt; inv Hwbck;
        simpl in *; auto.
      econstructor; eauto; simpl.
      - rewrite add_whens_typeof; auto.
      - constructor; auto.
    Qed.

    Lemma subclock_exp_wt : forall e,
        wt_exp G Γ e ->
        wt_exp G Γ' (subclock_exp bck sub e).
    Proof with auto with ltyping.
      induction e using exp_ind2; intros * Hwt; inv Hwt; simpl in *.
      3-14:econstructor; simpl in *; eauto using rename_var_wt, subclock_clock_wt.
      all:try solve [rewrite Forall_map, Forall_forall in *; intros; eauto].
      all:try rewrite subclock_exp_typeof.
      all:try rewrite subclock_exp_typesof.
      all:try (rewrite map_subclock_ann_clock; auto). all:try (rewrite map_subclock_ann_type; auto); auto.
      - apply add_whens_wt...
      - apply add_whens_wt...
      - eapply NoLast in H2 as [].
      - eapply NoLast in H2 as [].
      - simpl_Forall...
      - simpl_Forall...
      - erewrite map_map, map_ext; eauto. intros (?&?); auto.
      - contradict H6. apply map_eq_nil in H6; auto.
      - rewrite Forall_map. rewrite Forall_forall in *; intros (?&?) Hin; simpl. rewrite Forall_map.
        specialize (H _ Hin). specialize (H7 _ Hin).
        rewrite Forall_forall in *; eauto.
      - rewrite Forall_map. rewrite Forall_forall; intros (?&?) Hin; simpl.
        rewrite subclock_exp_typesof.
        eapply Forall_forall in H8; eauto; auto.
      - erewrite map_map, map_ext; eauto. intros (?&?); auto.
      - contradict H9. apply map_eq_nil in H9; auto.
      - rewrite Forall_map. rewrite Forall_forall in *; intros (?&?) Hin; simpl. rewrite Forall_map.
        specialize (H _ Hin). specialize (H10 _ Hin).
        rewrite Forall_forall in *; eauto.
      - simpl_Forall. now rewrite subclock_exp_typesof.
      - erewrite map_map, map_ext; eauto. intros (?&?); auto.
      - erewrite fst_NoDupMembers, map_map, map_ext, <-fst_NoDupMembers; eauto. intros (?&?); auto.
      - contradict H10. apply map_eq_nil in H10; auto.
      - rewrite Forall_map. rewrite Forall_forall in *; intros (?&?) Hin; simpl. rewrite Forall_map.
        specialize (H _ Hin). specialize (H11 _ Hin).
        rewrite Forall_forall in *; eauto.
      - rewrite Forall_map. rewrite Forall_forall; intros (?&?) Hin; simpl.
        rewrite subclock_exp_typesof.
        eapply Forall_forall in H12; eauto; auto.
      - rewrite Forall2_map_1. eapply Forall2_impl_In; [|eauto]; intros (?&?) (?&((?&?)&?)) _ _ ?; auto.
      - rewrite Forall_map. eapply Forall_impl; [|eapply H10]; eauto; intros.
        now rewrite subclock_exp_typeof.
      - rewrite Forall_map. eapply Forall_impl; [|eauto]; intros.
        eapply subclock_clock_wt; eauto.
    Qed.

    Lemma subclock_equation_wt : forall eq,
        wt_equation G Γ eq ->
        wt_equation G Γ' (subclock_equation bck sub eq).
    Proof.
      intros (?&?) (Hwt1&Hwt2). constructor.
      - rewrite Forall_map.
        eapply Forall_impl; [|eauto]; eauto using subclock_exp_wt.
      - rewrite Forall2_map_1, subclock_exp_typesof.
        eapply Forall2_impl_In; [|eauto]; intros; eauto using rename_var_wt.
    Qed.

  End subclock.

End SCTYPING.

Module SCTypingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Typ : LTYPING Ids Op OpAux Cks Senv Syn)
       (SC  : SUBCLOCK Ids Op OpAux Cks Senv Syn)
       <: SCTYPING Ids Op OpAux Cks Senv Syn Typ SC.
  Include SCTYPING Ids Op OpAux Cks Senv Syn Typ SC.
End SCTypingFun.
