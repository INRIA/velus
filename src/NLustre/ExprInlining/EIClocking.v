From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Recdef.
From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Environment.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.Memories.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import NLustre.NLClocking.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.ExprInlining.EI.

Module Type EICLOCKING
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Ids Op)
       (Import Cks   : CLOCKS          Ids Op OpAux)
       (Import CESyn : CESYNTAX        Ids Op OpAux Cks)
       (Import CEClo : CECLOCKING      Ids Op OpAux Cks CESyn)
       (Import Syn   : NLSYNTAX        Ids Op OpAux Cks CESyn)
       (Import Ord   : NLORDERED       Ids Op OpAux Cks CESyn Syn)
       (Import Mem   : MEMORIES        Ids Op OpAux Cks CESyn Syn)
       (Import IsD   : ISDEFINED       Ids Op OpAux Cks CESyn Syn Mem)
       (Import Clo   : NLCLOCKING      Ids Op OpAux Cks CESyn Syn Ord Mem IsD CEClo)
       (Import EI   : EI             Ids Op OpAux Cks CESyn Syn).

  Lemma inlinable_wc G Γ : forall vars eqs,
      NoDupMembers Γ ->
      Forall (wc_equation G Γ) eqs ->
      Forall (fun '(x, e) => exists ck, wc_cexp Γ e ck
                          /\ forall ck' islast, In (x, (ck', islast)) Γ -> ck' = ck) (inlinable vars eqs).
  Proof.
    intros * Nd Wc.
    unfold inlinable. simpl_Forall. simpl_In. simpl_Forall.
    clear Hf. cases. inv Hf0.
    inv Wc. take (wc_rhs _ _ _) and inv it. simpl in *. do 2 esplit; eauto.
    intros * Hin.
    eapply NoDupMembers_det in H1; eauto. now inv H1.
  Qed.

  Section inline.
    Variable (G : global) (Γ : list (ident * (clock * bool))).
    Variable (x : ident) (ck : clock).

    Hypothesis Wc2 : forall ck' islast, In (x, (ck', islast)) Γ -> ck' = ck.

    Section inline_exp.
      Variable (xe : exp).

      Hypothesis Wc1 : wc_exp Γ xe ck.

      Lemma inline_in_exp_wc : forall e ck,
          wc_exp Γ e ck ->
          wc_exp Γ (inline_in_exp x xe e) ck.
      Proof.
        induction e; simpl; auto; intros * Wc; inv Wc.
        - cases_eqn Eq; eauto with nlclocking.
          rewrite equiv_decb_equiv in Eq. inv Eq.
          apply Wc2 in H2; subst; eauto.
        - eauto with nlclocking.
        - constructor; auto.
        - constructor; auto.
      Qed.
    End inline_exp.

    Section inline_cexp.
      Variable (xe : cexp).

      Hypothesis Wc1 : wc_cexp Γ xe ck.

      Lemma try_inline_in_exp_wc : forall e ck,
          wc_exp Γ e ck ->
          wc_exp Γ (try_inline_in_exp x xe e) ck.
      Proof.
        intros * Wc.
        unfold try_inline_in_exp. cases; auto.
        inv Wc1; auto using inline_in_exp_wc.
      Qed.

      Lemma inline_in_cexp_wc : forall ce ck,
          wc_cexp Γ ce ck ->
          wc_cexp Γ (inline_in_cexp x xe ce) ck.
      Proof.
        induction ce using cexp_ind2'; intros * Wc; inv Wc; simpl; auto.
        - econstructor; auto; simpl_Forall; eauto.
          + intro contra. apply map_eq_nil in contra; auto.
          + rewrite length_map. simpl_Forall; auto.
        - econstructor; eauto using try_inline_in_exp_wc.
          + intro contra. apply map_eq_nil in contra; auto.
          + intros * Hin. simpl_In. simpl_Forall. auto.
        - cases_eqn Eq; auto using try_inline_in_exp_wc with nlclocking.
          take (wc_exp _ _ _) and inv it.
          rewrite equiv_decb_equiv in Eq0. inv Eq0.
          apply Wc2 in H2; subst; auto.
      Qed.

      Lemma inline_in_equation_wc : forall equ,
          wc_equation G Γ equ ->
          wc_equation G Γ (inline_in_equation x xe equ).
      Proof.
        intros * Wc; destruct equ; simpl; auto.
        inv Wc. take (wc_rhs _ _ _) and inv it; econstructor; eauto.
        - econstructor; eauto; simpl_Forall; auto using try_inline_in_exp_wc.
        - constructor; auto using inline_in_cexp_wc.
      Qed.
    End inline_cexp.
  End inline.

  Lemma exp_inlining_node_wc : forall G n,
      wc_node G n ->
      wc_node (exp_inlining G) (exp_inlining_node n).
  Proof.
    intros * (Wc1&Wc2&Wc3&Wc4).
    repeat (split; auto). simpl.
    unfold inline_all_possible.
    eapply inlinable_wc with (vars:=idck (n_vars n)) in Wc4 as Wc5.
    2:{ erewrite fst_NoDupMembers, map_app, 2 map_map, map_app, <-app_assoc,
          Permutation.Permutation_app_comm with (l':=map _ (n_vars _)),
          map_ext with (l:=n_in _), map_ext with (l:=n_out _), map_ext with (l:=n_vars _).
        apply n_nodup.
        all:intros; destruct_conjs; auto.
    }
    rewrite Forall_rev in Wc5. rewrite <-fold_left_rev_right.
    induction Wc5 as [|(?&?)]; simpl.
    - simpl_Forall; eauto using global_iface_eq_wc_eq, exp_inlining_iface_eq.
    - unfold inline_in_equations. simpl_Forall.
      eapply inline_in_equation_wc; eauto.
  Qed.

  Theorem exp_inlining_wc : forall G,
      wc_global G ->
      wc_global (exp_inlining G).
  Proof.
    intros.
    unfold wc_global in *; simpl.
    induction H; simpl; constructor; auto.
    eapply exp_inlining_node_wc in H; auto.
  Qed.

End EICLOCKING.

Module EIClockingFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Ids Op)
       (Cks   : CLOCKS          Ids Op OpAux)
       (CESyn : CESYNTAX        Ids Op OpAux Cks)
       (CEClo : CECLOCKING      Ids Op OpAux Cks CESyn)
       (Syn   : NLSYNTAX        Ids Op OpAux Cks CESyn)
       (Ord   : NLORDERED       Ids Op OpAux Cks CESyn Syn)
       (Mem   : MEMORIES        Ids Op OpAux Cks CESyn Syn)
       (IsD   : ISDEFINED       Ids Op OpAux Cks CESyn Syn Mem)
       (Clo   : NLCLOCKING      Ids Op OpAux Cks CESyn Syn Ord Mem IsD CEClo)
       (EI   : EI             Ids Op OpAux Cks CESyn Syn)
  <: EICLOCKING Ids Op OpAux Cks CESyn CEClo Syn Ord Mem IsD Clo EI.
  Include EICLOCKING Ids Op OpAux Cks CESyn CEClo Syn Ord Mem IsD Clo EI.
End EIClockingFun.
