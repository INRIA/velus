From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Recdef.
From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Environment.
From Velus Require Import IndexedStreams.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CETyping.
From Velus Require Import CoreExpr.CESemantics.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.NLTyping.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.NLIndexedSemantics.
From Velus Require Import NLustre.ExprInlining.EI.
From Velus Require Import NLustre.ExprInlining.EITyping.

Module Type EICORRECTNESS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX      Ids Op)
       (Import Cks   : CLOCKS             Ids Op OpAux)
       (Import Str   : INDEXEDSTREAMS     Ids Op OpAux Cks)
       (Import CESyn : CESYNTAX           Ids Op OpAux Cks)
       (Import CETyp : CETYPING           Ids Op OpAux Cks CESyn)
       (Import CESem : CESEMANTICS        Ids Op OpAux Cks CESyn Str)
       (Import Syn   : NLSYNTAX           Ids Op OpAux Cks CESyn)
       (Import Ord   : NLORDERED          Ids Op OpAux Cks CESyn Syn)
       (Import Typ   : NLTYPING           Ids Op OpAux Cks CESyn Syn Ord CETyp)
       (Import Sem   : NLINDEXEDSEMANTICS Ids Op OpAux Cks CESyn Syn Str Ord CESem)
       (Import EI    : EI                 Ids Op OpAux Cks CESyn Syn)
       (Import EITyp : EITYPING           Ids Op OpAux Cks CESyn CETyp Syn Ord Typ EI).

  (** ** Preservation of Ordered_nodes *)

  Lemma exp_inlining_Is_node_in : forall f vars eqs,
    Is_node_in f (inline_all_possible vars eqs) ->
    Is_node_in f eqs.
  Proof.
    intros * Hin. unfold inline_all_possible in *.
    rewrite <-fold_left_rev_right in Hin.
    induction (rev _) as [|(?&?)]; simpl in *; auto.
    apply IHl; clear IHl.
    unfold Is_node_in, inline_in_equations in *. solve_Exists.
    destruct x; simpl in *; auto.
    destruct r; inv Hin.
  Qed.

  Theorem exp_inlining_Ordered : forall G,
    Ordered_nodes G ->
    Ordered_nodes (exp_inlining G).
  Proof.
    intros * Hord.
    eapply transform_units_Ordered_program; eauto.
    intros * Hin; simpl in *.
    eapply exp_inlining_Is_node_in; eauto.
  Qed.

  (** ** Preservation of semantics *)

  Section inline.
    Variable (G : global).
    Variable (Γ : list (ident * type)).
    Variable (b : bool) (R : env) (x : ident).

    Section inline_exp.
      Variable (xe : exp).

      Hypothesis Wt1 : forall ty, In (x, ty) Γ -> typeof xe = ty.
      Hypothesis Sem1 : forall v, sem_var_instant R x v -> sem_exp_instant b R xe v.

      Lemma inline_in_exp_sem : forall e v,
          wt_exp G.(types) Γ e ->
          sem_exp_instant b R e v ->
          sem_exp_instant b R (inline_in_exp x xe e) v.
      Proof.
        induction e; intros * Wt Sem; inv Wt; simpl; eauto.
        - cases_eqn Eq; auto.
          rewrite equiv_decb_equiv in Eq; inv Eq.
          inv Sem; eauto.
        - inv Sem. 1,2:econstructor; eauto.
          eapply Swhen_abs; eauto.
        - inv Sem; econstructor; eauto.
          erewrite inline_in_exp_typeof; eauto.
        - inv Sem; econstructor; eauto.
          erewrite 2 inline_in_exp_typeof; eauto.
      Qed.
    End inline_exp.

    Section inline_cexp.
      Variable (xe : cexp).

      Hypothesis Wt1 : forall ty, In (x, ty) Γ -> typeofc xe = ty.
      Hypothesis Sem1 : forall v, sem_var_instant R x v -> sem_cexp_instant b R xe v.

      Lemma try_inline_in_exp_sem : forall e v,
          wt_exp G.(types) Γ e ->
          sem_exp_instant b R e v ->
          sem_exp_instant b R (try_inline_in_exp x xe e) v.
      Proof.
        intros * Wt Sem. unfold try_inline_in_exp.
        cases; auto.
        eapply inline_in_exp_sem; eauto.
        intros * Hv. specialize (Sem1 _ Hv). inv Sem1; auto.
      Qed.

      Lemma inline_in_cexp_sem : forall e v,
          wt_cexp G.(types) Γ e ->
          sem_cexp_instant b R e v ->
          sem_cexp_instant b R (inline_in_cexp x xe e) v.
      Proof.
        induction e using cexp_ind2; intros * Wt Sem; inv Wt; simpl.
        - (* merge *)
          inv Sem.
          1:(apply Forall_app in H as (Hind1&Hind2); inv Hind2;
             apply Forall_app in H7 as (Hwt1&Hwt2); inv Hwt2;
             apply Forall_app in H14 as (Hs1&Hs2)).
          1-2:econstructor.
          2:rewrite map_app; simpl; auto. all:eauto; simpl_Forall; eauto.
          + now rewrite map_length.
          + apply in_app_iff in H as [|]; simpl_In; simpl_Forall; eauto.
        - (* case *)
          inv Sem; econstructor; eauto using try_inline_in_exp_sem; simpl_Forall.
          + destruct a; simpl in *; eauto.
          + destruct x0; simpl in *; eauto.
        - (* exp *)
          inv Sem.
          destruct e; eauto;
            try (constructor; eauto using try_inline_in_exp_sem).
          inv H1. cases_eqn Eq; auto with nlsem.
          rewrite equiv_decb_equiv in Eq; inv Eq; auto.
      Qed.

    End inline_cexp.
  End inline.

  Lemma inlinable_sem : forall H G bs vars eqs,
      Forall (sem_equation G bs H) eqs ->
      Forall (fun '(x, ce) => forall n vs, sem_var_instant (H n) x vs -> sem_cexp_instant (bs n) (H n) ce vs) (inlinable vars eqs).
  Proof.
    intros * Hsem.
    unfold inlinable. simpl_Forall. simpl_In. simpl_Forall.
    destruct x as [?? []| |]; inv Hf0.
    cases; inv H1.
    intros * Hv.
    inv Hsem. specialize (H5 n). specialize (H7 n). simpl in *.
    eapply sem_var_instant_det in Hv; [|eauto]; subst.
    take (sem_arhs_instant _ _ _ _ _) and inv it; take (sem_rhs_instant _ _ _ _) and inv it; auto.
  Qed.

  Lemma inline_all_possible_sem G Γ bs H : forall vars eqs,
      NoDupMembers Γ ->
      Forall (wt_equation G Γ) eqs ->
      Forall (sem_equation G bs H) eqs ->
      Forall (sem_equation G bs H) (inline_all_possible vars eqs).
  Proof.
    intros * Nd Wt Sem.
    assert (Forall (sem_equation G bs H) (inline_all_possible vars eqs)
            /\ Forall (wt_equation G Γ) (inline_all_possible vars eqs)) as (?&?); auto.
    unfold inline_all_possible.
    apply inlinable_wt with (vars:=vars) in Wt as Wt'; [|auto]. rewrite Forall_rev in Wt'.
    apply inlinable_sem with (vars:=vars) in Sem as Sem'. rewrite Forall_rev in Sem'.
    rewrite <-fold_left_rev_right.
    induction (rev (inlinable vars eqs)) as [|(?&?)]; inv Wt'; inv Sem'; simpl; auto.
    specialize (IHl H3 H5) as (Sem'&Wt').
    unfold inline_in_equations. split; simpl_Forall; eauto using inline_in_equation_wt.
    destruct x as [?? []| |]; simpl; eauto; inv Wt'; inv Sem'.
    1,2:(econstructor; eauto; take (wt_rhs _ _ _ _) and inv it;
         intros k; take (sem_arhs _ _ _ _ _) and specialize (it k); simpl in *).
    - inv it; econstructor; eauto.
      1,2:take (sem_rhs_instant _ _ _ _) and inv it; econstructor; eauto.
      3:instantiate (1:=tyins). 1-4:simpl_Forall.
      1,3:erewrite try_inline_in_exp_typeof; eauto.
      1,2:eapply try_inline_in_exp_sem; eauto.
    - inv it; econstructor; eauto.
      1-2:take (sem_rhs_instant _ _ _ _) and inv it; constructor.
      1,2:eapply inline_in_cexp_sem; eauto.
         Qed.

  Theorem exp_inlining_sem : forall G f ins outs,
      wt_global G ->
      Ordered_nodes G ->
      sem_node G f ins outs ->
      sem_node (exp_inlining G) f ins outs.
  Proof.
    intros [].
    unfold exp_inlining.
    induction nodes0; intros * Wt Hord Hsem; simpl; auto.
    destruct (ident_eq_dec (n_name a) f).
    - inv Wt. inv Hsem. rewrite find_node_now in H3; inv H3; auto.
      econstructor; simpl; auto. rewrite find_node_now; eauto.
      1-3:simpl; eauto.
      eapply Forall_sem_equation_global_tl in H7; eauto.
      2:{ eapply not_Is_called_in_self in Hord; eauto.
          setoid_rewrite find_unit_now; eauto. simpl; eauto. }
      eapply Forall_sem_equation_global_tl'; eauto.
      1,2:eapply exp_inlining_Ordered in Hord; eauto.
      { eapply not_Is_called_in_self in Hord; eauto.
        setoid_rewrite find_unit_now; eauto. simpl; eauto. }
      destruct H1 as (Wt&_). inv Wt. simpl in *.
      eapply inline_all_possible_sem; eauto.
      2:{ simpl_Forall. eapply global_iface_eq_wt_eq; [|eauto]. apply exp_inlining_iface_eq. }
      1:{ apply NoDupMembers_idty. apply n_nodup. }
      simpl_Forall. take (sem_equation _ _ _ _) and inv it; eauto with nlsem.
      econstructor; eauto.
      intros. take (forall k, _) and specialize (it k).
      inv Hord; eauto.
    - eapply sem_node_cons in Hsem; eauto.
      eapply sem_node_cons'; eauto.
      + eapply exp_inlining_Ordered in Hord; eauto.
      + inv Wt; inv Hord; eauto.
  Qed.

End EICORRECTNESS.

Module EICorrectnessFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX      Ids Op)
       (Cks   : CLOCKS             Ids Op OpAux)
       (Str   : INDEXEDSTREAMS     Ids Op OpAux Cks)
       (CESyn : CESYNTAX           Ids Op OpAux Cks)
       (CETyp : CETYPING           Ids Op OpAux Cks CESyn)
       (CESem : CESEMANTICS        Ids Op OpAux Cks CESyn Str)
       (Syn   : NLSYNTAX           Ids Op OpAux Cks CESyn)
       (Ord   : NLORDERED          Ids Op OpAux Cks CESyn Syn)
       (Typ   : NLTYPING           Ids Op OpAux Cks CESyn Syn Ord CETyp)
       (Sem   : NLINDEXEDSEMANTICS Ids Op OpAux Cks CESyn Syn Str Ord CESem)
       (EI    : EI                 Ids Op OpAux Cks CESyn Syn)
       (EITyp : EITYPING           Ids Op OpAux Cks CESyn CETyp Syn Ord Typ EI)
<: EICORRECTNESS Ids Op OpAux Cks Str CESyn CETyp CESem Syn Ord Typ Sem EI EITyp.
  Include EICORRECTNESS Ids Op OpAux Cks Str CESyn CETyp CESem Syn Ord Typ Sem EI EITyp.
End EICorrectnessFun.
