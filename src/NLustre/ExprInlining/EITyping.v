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
From Velus Require Import CoreExpr.CETyping.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.NLTyping.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.ExprInlining.EI.

Module Type EITYPING
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Ids Op)
       (Import Cks   : CLOCKS          Ids Op OpAux)
       (Import CESyn : CESYNTAX        Ids Op OpAux Cks)
       (Import CETyp : CETYPING        Ids Op OpAux Cks CESyn)
       (Import Syn   : NLSYNTAX        Ids Op OpAux Cks CESyn)
       (Import Ord   : NLORDERED       Ids Op OpAux Cks CESyn Syn)
       (Import Typ   : NLTYPING        Ids Op OpAux Cks CESyn Syn Ord CETyp)
       (Import EI   : EI             Ids Op OpAux Cks CESyn Syn).

  Lemma inlinable_wt G Γ : forall vars eqs,
      NoDupMembers Γ ->
      Forall (wt_equation G Γ) eqs ->
      Forall (fun '(x, e) => wt_cexp G.(types) Γ e
                          /\ forall ty, In (x, ty) Γ -> typeofc e = ty) (inlinable vars eqs).
  Proof.
    intros * Nd Wt.
    unfold inlinable. simpl_Forall. simpl_In. simpl_Forall.
    clear Hf. cases. inv Hf0.
    inv Wt. take (wt_rhs _ _ _ _) and inv it. simpl in *. split; auto.
    intros * Hin; eauto using NoDupMembers_det.
  Qed.

  Section inline_typeof.
    Variable (G : global) (Γ : list (ident * type)).
    Variable (x : ident).

    Section inline_exp.
      Variable (xe : exp).

      Hypothesis Wt2 : forall ty, In (x, ty) Γ -> typeof xe = ty.

      Lemma inline_in_exp_typeof : forall e,
          wt_exp G.(types) Γ e ->
          typeof (inline_in_exp x xe e) = typeof e.
      Proof.
        induction e; intros * Wt; inv Wt; simpl; auto.
        cases_eqn Eq; auto.
        rewrite equiv_decb_equiv in Eq. inv Eq; eauto.
      Qed.

    End inline_exp.

    Section inline_cexp.
      Variable (xe : cexp).

      Hypothesis Wt2 : forall ty, In (x, ty) Γ -> typeofc xe = ty.

      Lemma try_inline_in_exp_typeof : forall e,
          wt_exp G.(types) Γ e ->
          typeof (try_inline_in_exp x xe e) = typeof e.
      Proof.
        intros * Hwt. unfold try_inline_in_exp.
        cases. auto using inline_in_exp_typeof.
      Qed.

      Lemma inline_in_cexp_typeofc : forall e,
          wt_cexp G.(types) Γ e ->
          typeofc (inline_in_cexp x xe e) = typeofc e.
      Proof.
        induction e; intros * Wt; inv Wt; simpl; auto.
        cases_eqn Eq; simpl; try rewrite try_inline_in_exp_typeof; auto.
        take (wt_exp _ _ _) and inv it.
        rewrite equiv_decb_equiv in Eq0. inv Eq0; eauto.
      Qed.

    End inline_cexp.

  End inline_typeof.

  Section inline.
    Variable (G : global) (Γ : list (ident * type)).
    Variable (x : ident).

    Section inline_exp.
      Variable (xe : exp).

      Hypothesis Wt1 : wt_exp G.(types) Γ xe.
      Hypothesis Wt2 : forall ty, In (x, ty) Γ -> typeof xe = ty.

      Lemma inline_in_exp_wt : forall e,
          wt_exp G.(types) Γ e ->
          wt_exp G.(types) Γ (inline_in_exp x xe e).
      Proof.
        induction e; simpl; auto; intros * Wt; inv Wt.
        - cases; auto with nltyping.
        - auto with nltyping.
        - constructor; auto.
          erewrite inline_in_exp_typeof; eauto.
        - constructor; auto.
          erewrite 2 inline_in_exp_typeof; eauto.
      Qed.
    End inline_exp.

    Section inline_cexp.
      Variable (xe : cexp).

      Hypothesis Wt1 : wt_cexp G.(types) Γ xe.
      Hypothesis Wt2 : forall ty, In (x, ty) Γ -> typeofc xe = ty.

      Lemma try_inline_in_exp_wt : forall e,
          wt_exp G.(types) Γ e ->
          wt_exp G.(types) Γ (try_inline_in_exp x xe e).
      Proof.
        intros * Wt.
        unfold try_inline_in_exp. cases; auto.
        inv Wt1; auto using inline_in_exp_wt.
      Qed.

      Lemma inline_in_cexp_wt : forall ce,
          wt_cexp G.(types) Γ ce ->
          wt_cexp G.(types) Γ (inline_in_cexp x xe ce).
      Proof.
        induction ce using cexp_ind2'; intros * Wt; inv Wt; simpl; auto.
        - constructor; auto; simpl_Forall; auto.
          + now rewrite map_length.
          + erewrite inline_in_cexp_typeofc; eauto.
        - econstructor; eauto using try_inline_in_exp_wt.
          + erewrite try_inline_in_exp_typeof; eauto.
          + now rewrite map_length.
          + intros * Hin. simpl_In. simpl_Forall.
            erewrite 2 inline_in_cexp_typeofc; eauto.
          + intros * Hin. simpl_In. simpl_Forall. auto.
        - cases; auto using try_inline_in_exp_wt with nltyping.
      Qed.

      Lemma inline_in_equation_wt : forall equ,
          wt_equation G Γ equ ->
          wt_equation G Γ (inline_in_equation x xe equ).
      Proof.
        intros * Wt; destruct equ; simpl; auto.
        inv Wt. take (wt_rhs _ _ _ _) and inv it; econstructor; eauto.
        - econstructor; eauto; simpl_Forall; auto using try_inline_in_exp_wt.
          erewrite try_inline_in_exp_typeof; eauto.
        - simpl. erewrite inline_in_cexp_typeofc; eauto.
        - constructor; auto using inline_in_cexp_wt.
      Qed.
    End inline_cexp.
  End inline.

  Lemma exp_inlining_node_wt : forall G n,
      wt_node G n ->
      wt_node (exp_inlining G) (exp_inlining_node n).
  Proof.
    intros * (Wt1&Wt2).
    split; auto. simpl.
    unfold inline_all_possible.
    eapply inlinable_wt with (vars:=idsnd (n_vars n)) in Wt1 as Wt3; [|apply NoDupMembers_idfst, n_nodup].
    rewrite Forall_rev in Wt3. rewrite <-fold_left_rev_right.
    induction Wt3 as [|(?&?)]; simpl.
    - simpl_Forall; eauto using global_iface_eq_wt_eq, exp_inlining_iface_eq.
    - unfold inline_in_equations. simpl_Forall.
      eapply inline_in_equation_wt; eauto.
  Qed.

  Theorem exp_inlining_wt : forall G,
      wt_global G ->
      wt_global (exp_inlining G).
  Proof.
    intros.
    eapply CommonTyping.transform_units_wt_program; eauto.
    intros. eapply exp_inlining_node_wt; eauto.
  Qed.

End EITYPING.

Module EITypingFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Ids Op)
       (Cks   : CLOCKS          Ids Op OpAux)
       (CESyn : CESYNTAX        Ids Op OpAux Cks)
       (CETyp : CETYPING        Ids Op OpAux Cks CESyn)
       (Syn   : NLSYNTAX        Ids Op OpAux Cks CESyn)
       (Ord   : NLORDERED       Ids Op OpAux Cks CESyn Syn)
       (Typ   : NLTYPING        Ids Op OpAux Cks CESyn Syn Ord CETyp)
       (EI   : EI             Ids Op OpAux Cks CESyn Syn)
  <: EITYPING Ids Op OpAux Cks CESyn CETyp Syn Ord Typ EI.
  Include EITYPING Ids Op OpAux Cks CESyn CETyp Syn Ord Typ EI.
End EITypingFun.
