From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Coq.Program.Equality.

From Velus Require Import Common Operators.
From Velus Require CoindStreams.
From Velus Require Import Environment.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LSemantics Lustre.LTyping.

(** * Proofs pertaining to the normalization process *)

Local Set Warnings "-masking-absolute-name".
Module Type NORMPROOFS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Syn   : LSYNTAX   Ids Op)
       (Import Typ   : LTYPING Ids Op Syn)
       (Import Lord  : LORDERED   Ids Op Syn)
       (Import Str   : CoindStreams.COINDSTREAMS   Op OpAux)
       (Import Sem   : LSEMANTICS Ids Op OpAux Syn Lord Str).

  Import Env.

  Fact refines_sem_var: forall H H' id v,
      refines eq H H' ->
      sem_var H id v -> sem_var H' id v.
  Proof.
    intros H H' id v Href Hsem.
    destruct Hsem.
    econstructor; try apply H1.
    edestruct Href; unfold MapsTo in *.
    - apply H0.
    - destruct H2; rewrite H2; auto.
  Qed.

  Local Ltac SolveForall :=
      match goal with
      | H: Forall ?P1 ?l |- Forall ?P2 ?l =>
        induction H; eauto
      | H: Forall ?P1 ?l |- Forall ?P2 (List.map ?f ?l) =>
        induction H; simpl; eauto
      | H: Forall2 ?P1 ?l1 ?l2 |- Forall2 ?P2 ?l1 ?l2 =>
        induction H; eauto
      | _ => idtac
      end.

  Hint Constructors Forall.
  Fact refines_sem_exp: forall G H H' b e v,
    refines eq H H' ->
    sem_exp G H b e v ->
    sem_exp G H' b e v.
  Proof.
    intros G H H' b e v Href Hsem. revert H' Href.
    induction Hsem using sem_exp_ind2 with (P_equation := fun H b e => True) (P_node := fun i xs ys => True); intros; auto.
    - constructor; auto.
    - constructor. eapply refines_sem_var; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto; clear H0 H2 H4.
      + clear H3; SolveForall.
      + clear H1; SolveForall.
    - econstructor; eauto.
      + clear H0 H3; SolveForall.
      + eapply refines_sem_var; eauto.
    - econstructor; eauto; clear H1 H3 H5.
      + eapply refines_sem_var; eauto.
      + clear H0 H4; SolveForall.
      + clear H0 H2; SolveForall.
    - econstructor; eauto; clear H0 H2 H4.
      + clear H3; SolveForall.
      + clear H1; SolveForall.
    - econstructor; eauto.
      clear H0 H2; SolveForall.
    - econstructor; eauto.
      2: (intro k; destruct (H3 k) as [H4 _]; apply H4).
      clear H0 H2 H3; SolveForall.
  Qed.

  Fact refines_sem_equation: forall G H H' b equ,
      refines eq H H' ->
      sem_equation G H b equ ->
      sem_equation G H' b equ.
  Proof.
    intros G H H' b [xs es] Href Hsem.
    destruct Hsem.
    apply Seq with (ss:=ss).
    - clear H1; SolveForall.
      constructor; auto. eapply refines_sem_exp; eauto.
    - clear H0; SolveForall.
      constructor; auto. eapply refines_sem_var; eauto.
  Qed.

  (** Substitute `ev` to `v` in `e` *)
  Fixpoint subst_in_expr v ev e :=
    match e with
    | Econst c => Econst c
    | Evar v' a => if ident_eqb v v' then ev else Evar v' a
    | Eunop op e a => Eunop op (subst_in_expr v ev e) a
    | Ebinop op el er ann =>
      Ebinop op (subst_in_expr v ev el) (subst_in_expr v ev er) ann
    | Efby es1 es2 anns => Efby (List.map (subst_in_expr v ev) es1)
                               (List.map (subst_in_expr v ev) es2) anns
    | Ewhen es id on ann =>
      Ewhen (List.map (subst_in_expr v ev) es) id on ann
    | Emerge id es1 es2 ann => Emerge id (List.map (subst_in_expr v ev) es1)
                                     (List.map (subst_in_expr v ev) es2) ann
    | Eite ec et ee ann => Eite (subst_in_expr v ev ec)
                               (List.map (subst_in_expr v ev) et)
                               (List.map (subst_in_expr v ev) ee) ann
    | Eapp id es er anns => Eapp id (List.map (subst_in_expr v ev) es)
                                (match er with
                                 | None => None
                                 | Some er => Some (subst_in_expr v ev er)
                                 end) anns
    end.
  Definition subst_in_exprs v ev es := List.map (subst_in_expr v ev) es.

  Fact subst_exp_typeof : forall G vars e t et ty,
      NoDupMembers vars ->
      List.In (t, ty) vars ->
      typeof et = [ty] ->
      wt_exp G vars e ->
      wt_exp G vars (subst_in_expr t et e) ->
      typeof (subst_in_expr t et e) = typeof e.
  Proof.
    intros G vars e t et ty Hndup Hin Het Hwt1 Hwt2.
    induction e; simpl; auto.
    destruct (ident_eqb t i) eqn:Hti; simpl in *; auto.
    rewrite Hti in *.
    rewrite ident_eqb_eq in Hti; subst; simpl in *.
    inv Hwt1; simpl.
    rewrite Het.
    specialize (NoDupMembers_det _ _ _ vars Hndup Hin H1) as Htyty0.
    rewrite Htyty0. reflexivity.
  Qed.

  Fact wt_one_equation : forall G vars x e,
      wt_equation G vars ([x], [e]) ->
      (exists ty, wt_exp G vars e /\ typeof e = [ty] /\ List.In (x, ty) vars).
  Proof.
    intros G vars x e Hwt.
    destruct Hwt as [Hwt Hvar]; simpl in Hvar.
    inv Hwt. clear H2. rename H1 into Hwt.
    inv Hvar. inv H3. rename H2 into Hin.
    rewrite List.app_nil_r in H1.
    exists y; auto.
  Qed.

  Local Hint Resolve subst_exp_typeof.
  Lemma subst_exp_wt : forall G vars e t et,
      NoDupMembers vars ->
      wt_exp G vars e -> wt_equation G vars ([t], [et]) ->
      wt_exp G vars (subst_in_expr t et e).
  Proof with eauto.
    intros G vars e t et Hndup Hwt1 Hwt2.
    (* Transform wt_equation into something usable *)
    apply wt_one_equation in Hwt2.
    destruct Hwt2 as [ty [Hwt2 [Hty Hin]]].

    (* Main induction *)
    induction Hwt1 using wt_exp_ind2; simpl.
    - (* const *) constructor.
    - (* var *)
      destruct (ident_eqb t x) eqn:Htx.
      + rewrite ident_eqb_eq in Htx; subst...
      + constructor; auto.
    - (* unop *)
      econstructor...
      rewrite <- H...
    - (* binop *)
      econstructor...
      + rewrite <- H...
      + rewrite <- H0...
    - (* fby *)
      econstructor...
      + clear H H4. SolveForall.
      + clear H0 H3. SolveForall.
      + rewrite <- H3; clear H3.
        induction es; simpl... inv H0; inv H2.
        f_equal...
      + rewrite <- H4; clear H4.
        induction e0s; simpl... inv H; inv H1.
        f_equal...
    - (* when *)
      econstructor...
      + clear H H1. SolveForall.
      + rewrite <- H1; clear H1.
        induction es; simpl... inv H; inv H0.
        f_equal...
    - (* ite *)
      econstructor...
      + clear H H4. SolveForall.
      + clear H1 H5. SolveForall.
      + rewrite <- H4; clear H4.
        induction ets; simpl... inv H; inv H0.
        f_equal...
      + rewrite <- H5; clear H5.
        induction efs; simpl... inv H1; inv H2.
        f_equal...
    - (* merge *)
      econstructor...
      + clear H H4. SolveForall.
      + clear H1 H5. SolveForall.
      + rewrite <- H3...
      + rewrite <- H4; clear H4.
        induction ets; simpl... inv H; inv H0; subst.
        f_equal...
      + rewrite <- H5; clear H5.
        induction efs; simpl... inv H1; inv H2; subst.
        f_equal...
    - (* app *)
      econstructor...
      + clear H H2. SolveForall.
      + generalize dependent (n_in n). induction es; intros clocks Hfor; simpl in *.
        * inv Hfor. constructor.
        * inv H; inv H0.
          apply Forall2_app_inv_l in Hfor. destruct Hfor as [n1 [n2 [Hn1 [Hn2 Hn1n2]]]]. rewrite Hn1n2; clear Hn1n2.
          apply Forall2_app... clear IHes.
          erewrite subst_exp_typeof...
    - (* app (reset) *)
      econstructor...
      + clear H H2. SolveForall.
      + generalize dependent (n_in n). induction es; intros clocks Hfor; simpl in *.
        * inv Hfor. constructor.
        * inv H; inv H0.
          apply Forall2_app_inv_l in Hfor. destruct Hfor as [n1 [n2 [Hn1 [Hn2 Hn1n2]]]]. rewrite Hn1n2; clear Hn1n2.
          apply Forall2_app; auto. clear IHes.
          erewrite subst_exp_typeof...
      + rewrite <- H5...
  Qed.

  Corollary subst_exp_typeof2: forall G vars e t et,
      NoDupMembers vars ->
      wt_exp G vars e ->
      wt_equation G vars ([t], [et]) ->
      typeof (subst_in_expr t et e) = typeof e.
  Proof.
    intros G vars e t et Hndup Hwt1 Hwt2.
    specialize (wt_one_equation _ _ _ _ Hwt2) as [ty [Hwt3 [Hty Hin]]].
    eapply subst_exp_typeof; eauto.
    eapply subst_exp_wt; eauto.
  Qed.

  Local Hint Constructors sem_exp.
  Local Hint Resolve subst_exp_typeof2.
  Lemma subst_exp_sem1 : forall G vars H b e t et v,
      NoDupMembers vars ->
      wt_exp G vars e ->
      wt_equation G vars ([t], [et]) ->
      sem_equation G H b ([t], [et]) ->
      sem_exp G H b e v ->
      sem_exp G H b (subst_in_expr t et e) v.
  Proof with eauto.
    intros G vars H b e t et v Hndup Hwt1 Hwt2 Hsemt Hsem. revert t Hwt1 Hwt2 Hsemt.
    induction Hsem using sem_exp_ind2 with (P_equation := fun H b e => True) (P_node := fun i xs ys => True);
      intros; simpl; auto; inv Hwt1; eauto.
    - (* var *)
      destruct (ident_eqb t0 x) eqn:Ht0x; auto.
      + rewrite ident_eqb_eq in Ht0x; subst.
        destruct H0.
        inv Hsemt.
        inv H10; inv H8.
        destruct H7.
        inv H9; inv H12.
        unfold MapsTo in *. rewrite H0 in H2; inv H2...
        rewrite <- H5 in H1; rewrite H1; rewrite H6; clear H1 H5 H6.
        simpl. rewrite List.app_nil_r. assumption.
    - (* unop *)
      econstructor...
      rewrite <- H0...
    - (* binop *)
      econstructor...
      * rewrite <- H0...
      * rewrite <- H1...
    - (* fby *)
      econstructor; eauto; clear H0 H2 H4.
      + clear H11. induction H1; simpl...
        inv H8...
      + clear H10. induction H3; simpl...
        inv H9...
    - (* when *)
      econstructor; eauto; clear H0 H2 H3.
      induction H1; simpl...
      inv H8...
    - (* ite *)
      econstructor; eauto; clear H0 H1 H3 H5 H12 H14.
      + clear H4. induction H2; simpl...
        inv H10...
      + clear H2. induction H4; simpl...
        inv H11...
    - (* merge *)
      econstructor; eauto; clear H0 H2 H4 H14.
      + clear H3. induction H1; simpl...
        inv H10...
      + clear H1. induction H3; simpl...
        inv H11...
    - (* app *)
      econstructor; eauto; clear H0 H2 H8.
      induction H1; simpl...
      inv H6...
    - (* app (reset) *)
      econstructor; eauto; clear H0 H10.
      2: (intro k; destruct (H3 k); eauto).
      clear H3. induction H1; simpl...
      inv H8...
  Qed.

  Local Ltac rewrite_types :=
    match goal with
    | H1 : (typeof (subst_in_expr _ _ ?e) = ?ty1), H2 : (typeof ?e = ?ty2) |- ?ty1 = ?ty2 =>
      rewrite <- H1; rewrite <- H2; eapply subst_exp_typeof2; eauto
    | _ => idtac
    end.

  Hypothesis sem_exp_det : forall G H b e v1 v2,
      sem_exp G H b e v1 ->
      sem_exp G H b e v2 ->
      Forall2 (fun v1 v2 => Streams.EqSt v1 v2) v1 v2.

  Lemma subst_exp_sem2 : forall G vars H b e t et v,
      NoDupMembers vars ->
      wt_exp G vars e ->
      wt_equation G vars ([t], [et]) ->
      sem_equation G H b ([t], [et]) ->
      sem_exp G H b (subst_in_expr t et e) v ->
      sem_exp G H b e v.
  Proof with eauto.
    intros G vars H b e t et v Hndup Hwt1 Hwt2 Hsemt Hsem. generalize dependent v.
    induction e using exp_ind2; intros v Hsem; simpl in *; inv Hwt1; eauto.
    - (* var *)
      destruct (ident_eqb t x) eqn:Htx; auto.
      rewrite ident_eqb_eq in Htx; subst.
      destruct Hwt2 as [Hwt2 Hty2].
      inv Hsemt.
      inv H7; inv H6; simpl in *; rewrite List.app_nil_r in *.
      inv H8; inv H7.
      specialize (sem_exp_det _ _ _ _ _ _ Hsem H4) as Hdet.
      inv Hdet; inv H8.
      constructor. rewrite H7. assumption.
    - (* unop *)
      inv Hsem. econstructor...
      assert ([ty0] = [tye]) as Hty0e by rewrite_types.
      inv Hty0e...
    - (* binop *)
      inv Hsem. econstructor...
      assert ([ty0] = [ty1]) as Hty01 by rewrite_types.
      assert ([ty3] = [ty2]) as Hty32 by rewrite_types.
      inv Hty01; inv Hty32...
    - (* fby *)
      inv Hsem.
      repeat take (Forall2 _ (List.map _ _) _) and rewrite Forall2_map_1 in it.
      rewrite Forall_forall in *.
      econstructor...
      + apply Forall2_impl_In with (2:=it).
        intros...
      + apply Forall2_impl_In with (2:=it0).
        intros...
    - (* when *)
      inv Hsem.
      econstructor...
      take (Forall2 _ (List.map _ _) _) and rewrite Forall2_map_1 in it.
      apply Forall2_impl_In with (2:=it).
      intros.
      rewrite Forall_forall in *...
    - (* ite *)
      inv Hsem.
      repeat take (Forall2 _ (List.map _ _) _) and rewrite Forall2_map_1 in it.
      rewrite Forall_forall in *.
      econstructor...
      + apply Forall2_impl_In with (2:=it).
        intros...
      + apply Forall2_impl_In with (2:=it0).
        intros...
    - (* merge *)
      inv Hsem.
      repeat take (Forall2 _ (List.map _ _) _) and rewrite Forall2_map_1 in it.
      rewrite Forall_forall in *.
      econstructor...
      + apply Forall2_impl_In with (2:=it).
        intros...
      + apply Forall2_impl_In with (2:=it0).
        intros...
    - (* app *)
      inv Hsem.
      take (Forall2 _ (List.map _ _) _) and rewrite Forall2_map_1 in it.
      rewrite Forall_forall in *.
      econstructor...
      apply Forall2_impl_In with (2:=it).
      intros...
    - (* app (reset) *)
      inv Hsem.
      take (Forall2 _ (List.map _ _) _) and rewrite Forall2_map_1 in it.
      rewrite Forall_forall in *.
      econstructor...
      apply Forall2_impl_In with (2:=it).
      intros...
  Qed.

  Lemma subst_eq_sem : forall G vars H b x e t et,
      NoDupMembers vars ->
      wt_exp G vars e ->
      wt_equation G vars ([t], [et]) ->
      sem_equation G H b ([t], [et]) ->
      (sem_equation G H b (x, [e]) <-> sem_equation G H b (x, [subst_in_expr t et e])).
  Proof.
    intros. split; intro Hsem; inv Hsem; econstructor; eauto.
    + inv H9; inv H8; simpl in H10; rewrite List.app_nil_r in H10.
      constructor; eauto. eapply subst_exp_sem1; eauto.
    + inv H9; inv H8; simpl in H10; rewrite List.app_nil_r in H10.
      constructor; eauto. eapply subst_exp_sem2; eauto.
  Qed.

End NORMPROOFS.
