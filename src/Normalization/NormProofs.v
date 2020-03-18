From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Coq.Program.Equality.

From Velus Require Import Common Operators.
From Velus Require CoindStreams.
From Velus Require Import Environment.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LSemantics Lustre.LTyping.
From Velus Require Import Normalization.Fresh Normalization.Norm.

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
       (Import Sem   : LSEMANTICS Ids Op OpAux Syn Lord Str)
       (Import Norm  : NORM Ids Op Syn).

  Import Env.

  Fact idents_for_anns_values : forall anns idents st st',
      idents_for_anns anns st = (idents, st') ->
      Forall2 (fun a '(id, a') => a = a') anns idents.
  Proof.
    induction anns; intros idents st st' Hanns; simpl in *.
    - inv Hanns. constructor.
    - repeat inv_bind.
      specialize (IHanns _ _ _ H0).
      constructor; eauto.
  Qed.

  Ltac idents_for_anns_length :=
    match goal with
    | H : idents_for_anns ?anns _ = (?ids, _) |- length ?ids = length ?anns =>
      apply idents_for_anns_values in H;
      rewrite Forall2_forall2 in H; destruct H;
      auto
    | H : idents_for_anns (List.map _ ?anns) _ = (?ids, _) |- length ?ids = length ?anns =>
      apply idents_for_anns_values in H;
      rewrite Forall2_forall2 in H; destruct H;
      rewrite map_length in *; auto
    end.

  Ltac rewrite_Forall_forall :=
    match goal with
    | H : Forall _ _ |- _ =>
      rewrite Forall_forall in H
    | H : Forall2 _ _ _ |- _ =>
      rewrite Forall2_forall2 in H; destruct H
    | H : Forall3 _ _ _ _ |- _ =>
      rewrite Forall3_forall3 in H; destruct H as [? [? ?]]
    | |- Forall _ _ =>
      rewrite Forall_forall; split; auto; intros; subst
    | |- Forall2 _ _ _ =>
      rewrite Forall2_forall2; repeat split; auto; intros; subst
    | |- Forall3 _ _ _ _ =>
      rewrite Forall3_forall3; repeat split; auto; intros; subst
    end.

  Fact normalize_exp_length : forall G vars e is_control es' eqs' st st',
      wt_exp G vars e ->
      normalize_exp is_control e st = (es', eqs', st') ->
      length es' = numstreams e.
  Proof.
    intros G vars e.
    rewrite <- numstreams_length_typeof.
    induction e using exp_ind2; intros is_control es' eqs' st st' Hwt Hnorm;
      [| | | | | | destruct is_control | destruct is_control | ];
      simpl in *; inv Hwt; inv Hnorm; repeat inv_bind;
        repeat rewrite map_length in *; auto;
          try idents_for_anns_length.
    - (* when *)
      apply map_bind2_values in H0.
      assert (Forall2 (fun e x => length x = length (typeof e)) es x1) as Hlen.
      { repeat rewrite_Forall_forall.
        specialize (H2 a b0 [] _ _ _ _ H3 eq_refl eq_refl eq_refl); destruct H2 as [st'' [st''' ?]].
        eapply nth_In in H3. eapply H; eauto.
      } clear H H0.
      assert (length (concat x1) = length (typesof es)) as Hlen'.
      { unfold typesof. rewrite flat_map_concat_map.
        induction Hlen; simpl; auto.
        inv H4. repeat rewrite app_length; auto. }
      rewrite combine_length. rewrite Hlen'.
      apply OrdersEx.Nat_as_DT.min_id.
    - (* merge (control) *)
      apply map_bind2_values in H1; apply map_bind2_values in H2.
      assert (Forall2 (fun e x => length x = length (typeof e)) ets x3) as Hlen1.
      { repeat rewrite_Forall_forall.
        specialize (H11 a b [] _ _ _ _ H12 eq_refl eq_refl eq_refl); destruct H11 as [? [? ?]].
        eapply H; try apply H5; try apply nth_In; eauto.
      } clear H H1.
      assert (Forall2 (fun e x => length x = length (typeof e)) efs x5) as Hlen2.
      { repeat rewrite_Forall_forall.
        specialize (H4 a b [] _ _ _ _ H8 eq_refl eq_refl eq_refl); destruct H4 as [? [? ?]].
        eapply H0; try apply H6; try apply nth_In; eauto.
      } clear H0 H2.
      assert (length (concat x3) = length (typesof ets)) as Hlen1'.
      { clear H5 H9. unfold typesof. rewrite flat_map_concat_map.
        induction Hlen1; simpl; auto.
        repeat rewrite app_length; eauto.
      } clear Hlen1.
      assert (length (concat x5) = length (typesof ets)) as Hlen2'.
      { rewrite <- H9. clear H6 H9. unfold typesof. rewrite flat_map_concat_map.
        induction Hlen2; simpl; auto.
        repeat rewrite app_length; eauto.
      } clear Hlen2.
      repeat rewrite combine_length. rewrite Hlen1'; rewrite Hlen2'.
      repeat rewrite PeanoNat.Nat.min_id. reflexivity.
    - (* ite (control) *)
      apply map_bind2_values in H2; apply map_bind2_values in H3.
      assert (Forall2 (fun e x => length x = length (typeof e)) ets x5) as Hlen1.
      { repeat rewrite_Forall_forall.
        specialize (H13 a b [] _ _ _ _ H14 eq_refl eq_refl eq_refl); destruct H13 as [? [? ?]].
        eapply H; try apply H6; try apply nth_In; eauto.
      } clear H H2.
      assert (Forall2 (fun e x => length x = length (typeof e)) efs x7) as Hlen2.
      { repeat rewrite_Forall_forall.
        specialize (H9 a b [] _ _ _ _ H12 eq_refl eq_refl eq_refl); destruct H9 as [? [? ?]].
        eapply H0; eauto; try apply H7; try apply nth_In; eauto.
      } clear H0 H3.
      assert (length (concat x5) = length (typesof ets)) as Hlen1'.
      { clear H6 H10. unfold typesof. rewrite flat_map_concat_map.
        induction Hlen1; simpl; auto.
        repeat rewrite app_length; eauto.
      } clear Hlen1.
      assert (length (concat x7) = length (typesof ets)) as Hlen2'.
      { rewrite <- H10. clear H7 H10. unfold typesof. rewrite flat_map_concat_map.
        induction Hlen2; simpl; auto.
        repeat rewrite app_length; eauto.
      } clear Hlen2.
      repeat rewrite combine_length. rewrite Hlen1'; rewrite Hlen2'.
      repeat rewrite PeanoNat.Nat.min_id. reflexivity.
  Qed.

  Fact normalize_exps_length : forall G vars es es' eqs' st st',
      Forall (wt_exp G vars) es ->
      normalize_exps es st = (es', eqs', st') ->
      length es' = length (typesof es).
  Proof.
    intros G vars es es' eqs' st st' Hwt Hnorm.
    unfold normalize_exps in Hnorm.
    repeat inv_bind.
    apply map_bind2_values in H.
    assert (Forall2 (fun x e => length x = length (typeof e)) x es) as Hf.
    { repeat rewrite_Forall_forall.
      replace (length x) in *.
      specialize (H1 b a [] _ _ _ _ H2 eq_refl eq_refl eq_refl); destruct H1 as [? [? H1]].
      eapply normalize_exp_length in H1; eauto.
      + rewrite numstreams_length_typeof. assumption.
      + eapply Hwt. apply nth_In; auto.
    } clear H Hwt.
    induction Hf; simpl; auto.
    repeat rewrite app_length; auto.
  Qed.

  Fact normalize_exp_typeof : forall G vars e is_control es' eqs' st st',
      wt_exp G vars e ->
      normalize_exp is_control e st = (es', eqs', st')  ->
      typesof es' = typeof e.
  Proof.
    induction e; intros is_control es' eqs' st st' Hwt Hnorm;
      specialize (normalize_exp_length _ _ _ _ es' eqs' st st' Hwt Hnorm) as Hlength;
      simpl in *.
    - (* const *)
      repeat inv_bind; reflexivity.
    - (* var *)
      repeat inv_bind; reflexivity.
    - (* unop *)
      repeat inv_bind; reflexivity.
    - (* binop *)
      repeat inv_bind; reflexivity.
    - (* fby *)
      repeat inv_bind.
      apply idents_for_anns_values in H2.
      clear H1 Hwt; (induction H2; [ auto | destruct y; subst; simpl; f_equal; auto ]).
    - (* when *)
      destruct l0. repeat inv_bind.
      rewrite map_length in Hlength.
      assert (Forall2 (fun '(e, ty) ty' => typeof (Ewhen [e] i b ([ty], n)) = [ty']) (combine (concat x0) l0) l0) as Hf.
      { rewrite_Forall_forall.
        destruct nth eqn:Hnth; simpl; f_equal.
        destruct a.
        specialize (combine_length_r _ _ Hlength) as Hlen'.
        specialize (combine_nth_r _ _ n0 e0 t1 Hlen') as [d Hnth'].
        rewrite Hnth' in Hnth; inv Hnth.
        apply nth_indep; rewrite <- Hlength; auto.
      } clear Hwt.
      induction Hf; simpl; auto.
      destruct x; simpl in *. inv H0. f_equal; auto.
    - (* merge *)
      clear Hwt.
      destruct l1.
      destruct is_control; repeat inv_bind; rewrite map_length in *.
      + (* control *)
        assert (Forall2 (fun '(e1, e2, ty) ty' => typeof (Emerge i [e1] [e2] ([ty], n)) = [ty'])
                        (combine (combine (concat x2) (concat x4)) l1) l1) as Hf.
        { rewrite_Forall_forall.
          destruct (nth n0 _ a) eqn:Hnth. destruct p; simpl; f_equal.
          destruct a as [[d1 d2] d3].
          specialize (combine_length_r _ _ Hlength) as Hlen'.
          specialize (combine_nth_r _ _ n0 (d1, d2) d3 Hlen') as [d Hnth'].
          rewrite Hnth' in Hnth; inv Hnth.
          apply nth_indep; rewrite <- Hlength; auto.
        }
        induction Hf; simpl; auto.
        destruct x as [[e1 e2] a]. inv Hlength. simpl in *.
        inv H1. f_equal; auto.
      + (* exp *)
        apply idents_for_anns_values in H1.
        assert (Forall2 (fun ty '(id, a) => (typeof (Evar id a)) = [ty]) l1 x5) as Hf.
        { repeat rewrite_Forall_forall.
          destruct (nth _ _ b) eqn:Hnth; simpl. f_equal.
          rewrite map_length in *.
          specialize (H2 a0 b n0 _ _ H3 eq_refl eq_refl); rewrite Hnth in H2.
          symmetry in H2. erewrite map_nth' in H2; eauto.
          destruct a0; inv H2; simpl; eauto.
        }
        clear H1. induction Hf; simpl; auto.
        destruct y; simpl in *. inv Hlength. inv H1. f_equal; auto.
    - (* ite *)
      clear Hwt.
      destruct l1.
      destruct is_control; repeat inv_bind; rewrite map_length in *.
      + (* control *)
        assert (Forall2 (fun '(e1, e2, ty) ty' => typeof (Eite (hd_default x) [e1] [e2] ([ty], n)) = [ty'])
                        (combine (combine (concat x5) (concat x7)) l1) l1) as Hf.
        { rewrite_Forall_forall.
          destruct (nth n0 _ a) eqn:Hnth. destruct p; simpl; f_equal.
          destruct a as [[d1 d2] d3].
          specialize (combine_length_r _ _ Hlength) as Hlen'.
          specialize (combine_nth_r _ _ n0 (d1, d2) d3 Hlen') as [d Hnth'].
          rewrite Hnth' in Hnth; inv Hnth.
          apply nth_indep; rewrite <- Hlength; auto.
        }
        induction Hf; simpl; auto.
        destruct x2 as [[e1 e2] a]. inv Hlength. simpl in *.
        inv H2. f_equal; auto.
      + (* exp *)
        apply idents_for_anns_values in H2.
        assert (Forall2 (fun ty '(id, a) => (typeof (Evar id a)) = [ty]) l1 x8) as Hf.
        { repeat rewrite_Forall_forall.
          destruct (nth _ _ b) eqn:Hnth; simpl. f_equal.
          rewrite map_length in *.
          specialize (H3 a0 b n0 _ _ H4 eq_refl eq_refl); rewrite Hnth in H3.
          symmetry in H3. erewrite map_nth' in H3; eauto.
          destruct a0; inv H3; simpl; eauto.
        }
        clear H2. induction Hf; simpl; auto.
        destruct y; simpl in *. inv Hlength. inv H2. f_equal; auto.
    - (* app *)
      clear Hwt.
      repeat inv_bind.
      apply idents_for_anns_values in H1.
      induction H1; simpl in *; auto.
      destruct y; subst; simpl. inv Hlength. f_equal; auto.
  Qed.

  Fact fby_iteexp_typeof : forall e0 e ann es' eqs' st st',
      fby_iteexp e0 e ann st = (es', eqs', st') ->
      typeof es' = [fst ann].
  Proof.
    intros e0 e ann es' eqs' st st' Hfby.
    destruct ann as [ty cl]; simpl.
    specialize (fby_iteexp_spec e0 e ty cl) as [[c [Heq Hspec]]|Hspec].
    - rewrite Hspec in Hfby; clear Hspec. inv Hfby. auto.
    - rewrite Hspec in Hfby; clear Hspec.
      repeat inv_bind. reflexivity.
  Qed.

  Fact normalize_fby_length : forall inits es anns es' eqs' st st',
      length inits = length anns ->
      length es = length anns ->
      normalize_fby inits es anns st = (es', eqs', st') ->
      length es' = length anns.
  Proof.
    intros inits es anns es' eqs' st st' Hlen1 Hlen2 Hnorm.
    unfold normalize_fby in Hnorm.
    repeat inv_bind.
    apply map_bind2_values in H.
    rewrite_Forall_forall; clear H0 H1.
    repeat rewrite combine_length in H.
    replace (length inits) in *.
    replace (length es) in *.
    repeat rewrite PeanoNat.Nat.min_id in H.
    auto.
  Qed.

  Fact normalize_fby_typeof : forall inits es anns es' eqs' st st',
      length inits = length anns ->
      length es = length anns ->
      normalize_fby inits es anns st = (es', eqs', st') ->
      typesof es' = List.map fst anns.
  Proof.
    intros inits es anns es' eqs' st st' Hlen1 Hlen2 Hnorm.
    specialize (normalize_fby_length _ _ _ _ _ _ _ Hlen1 Hlen2 Hnorm) as Hlen.
    unfold normalize_fby in Hnorm.
    repeat inv_bind.
    apply map_bind2_values in H.
    assert (Forall2 (fun e a => typeof e = [fst a]) es' anns) as Hf.
    { repeat rewrite_Forall_forall.
      rewrite <- H in H2.
      specialize (H1 (a, a, b) a [] _ _ _ _ H2 eq_refl eq_refl eq_refl); destruct H1 as [? [? ?]].
      destruct nth eqn:Hnth in H1. destruct p.
      apply fby_iteexp_typeof in H1.
      rewrite combine_nth in Hnth; auto.
      + inv Hnth. assumption.
      + rewrite combine_length.
        replace (length inits). replace (length es).
        apply PeanoNat.Nat.min_id.
    } clear H Hlen Hlen1 Hlen2.
    induction Hf; simpl; auto.
    rewrite H. simpl. f_equal; auto.
  Qed.

  Fact normalize_top_typeof : forall G vars e es' eqs' st st',
      wt_exp G vars e ->
      normalize_top e st = (es', eqs', st') ->
      typesof es' = typeof e.
  Proof.
    intros G vars e es' eqs' st st' Hwt Hnorm.
    destruct e; unfold normalize_top in Hnorm;
      try (solve [eapply normalize_exp_typeof in Hnorm; eauto]).
    - (* fby *)
      repeat inv_bind. inv Hwt.
      eapply normalize_fby_typeof; eauto.
      + replace (length l1) with (length (typesof l)) by (rewrite H8; apply map_length).
        eapply normalize_exps_length; eauto.
      + replace (length l1) with (length (typesof l0)) by (rewrite H7; apply map_length).
        eapply normalize_exps_length; eauto.
    - (* app *)
      destruct o; repeat inv_bind; apply app_nil_r.
  Qed.

  Ltac singleton_length :=
    simpl in *;
    match goal with
    | H : length ?x = 1 |- _ =>
      destruct x; simpl in H; try congruence;
      destruct x; simpl in H; try congruence;
      simpl in *; clear H
    end.

  (* TODO is this necessary ? *)
  Hint Constructors wt_exp.
  Fact normalize_wt : forall G vars e is_control es' eqs' st st',
      wt_exp G vars e ->
      normalize_exp is_control e st = (es', eqs', st') ->
      (Forall (wt_exp G vars) es' /\ Forall (wt_equation G vars) eqs'). (* vars ? surement pas *)
  Proof.
    intros G vars e is_control es' eqs' st st' Hwt;
      revert is_control eqs' es' st st'.
    induction Hwt using wt_exp_ind2;
      intros is_control eqs' es' st st' Hnorm; simpl in *.
    - (* const *)
      repeat inv_bind; eauto.
    - (* var *)
      repeat inv_bind; eauto.
    - (* unop *)
      repeat inv_bind.
      specialize (IHHwt _ _ _ _ _ H2) as [? ?].
      split; auto.
      repeat constructor.
      specialize (normalize_exp_length _ _ _ _ _ _ _ _ Hwt H2) as Hlen.
      rewrite <- numstreams_length_typeof in Hlen.
      replace (typeof e) in *.
      singleton_length.
      inv H3. econstructor; eauto.
      eapply normalize_exp_typeof in Hwt; eauto.
      simpl in *; rewrite app_nil_r in Hwt; rewrite Hwt; auto.
    - (* binop *)
      repeat inv_bind.
      specialize (IHHwt1 _ _ _ _ _ H3) as [? ?].
      specialize (IHHwt2 _ _ _ _ _ H4) as [? ?].
      split; [ | rewrite Forall_app; auto ].
      repeat constructor.
      specialize (normalize_exp_length _ _ _ _ _ _ _ _ Hwt1 H3) as Hlen1.
      specialize (normalize_exp_length _ _ _ _ _ _ _ _ Hwt2 H4) as Hlen2.
      rewrite <- numstreams_length_typeof in Hlen1.
      rewrite <- numstreams_length_typeof in Hlen2.
      replace (typeof e1) in *.
      replace (typeof e2) in *.
      repeat singleton_length.
      eapply normalize_exp_typeof in Hwt1; eauto.
      eapply normalize_exp_typeof in Hwt2; eauto.
      inv H5. inv H7.
      econstructor; eauto;
        simpl in *; rewrite app_nil_r in *;
          try rewrite Hwt1; try rewrite Hwt2; auto.
  Admitted.

  (* Fact refines_sem_var: forall H H' id v, *)
  (*     refines eq H H' -> *)
  (*     sem_var H id v -> sem_var H' id v. *)
  (* Proof. *)
  (*   intros H H' id v Href Hsem. *)
  (*   destruct Hsem. *)
  (*   econstructor; try apply H1. *)
  (*   edestruct Href; unfold MapsTo in *. *)
  (*   - apply H0. *)
  (*   - destruct H2; rewrite H2; auto. *)
  (* Qed. *)

  (* Local Ltac SolveForall := *)
  (*     match goal with *)
  (*     | H: Forall ?P1 ?l |- Forall ?P2 ?l => *)
  (*       induction H; eauto *)
  (*     | H: Forall ?P1 ?l |- Forall ?P2 (List.map ?f ?l) => *)
  (*       induction H; simpl; eauto *)
  (*     | H: Forall2 ?P1 ?l1 ?l2 |- Forall2 ?P2 ?l1 ?l2 => *)
  (*       induction H; eauto *)
  (*     | _ => idtac *)
  (*     end. *)

  (* Hint Constructors Forall. *)
  (* Fact refines_sem_exp: forall G H H' b e v, *)
  (*   refines eq H H' -> *)
  (*   sem_exp G H b e v -> *)
  (*   sem_exp G H' b e v. *)
  (* Proof. *)
  (*   intros G H H' b e v Href Hsem. revert H' Href. *)
  (*   induction Hsem using sem_exp_ind2 with (P_equation := fun H b e => True) (P_node := fun i xs ys => True); intros; auto. *)
  (*   - constructor; auto. *)
  (*   - constructor. eapply refines_sem_var; eauto. *)
  (*   - econstructor; eauto. *)
  (*   - econstructor; eauto. *)
  (*   - econstructor; eauto; clear H0 H2 H4. *)
  (*     + clear H3; SolveForall. *)
  (*     + clear H1; SolveForall. *)
  (*   - econstructor; eauto. *)
  (*     + clear H0 H3; SolveForall. *)
  (*     + eapply refines_sem_var; eauto. *)
  (*   - econstructor; eauto; clear H1 H3 H5. *)
  (*     + eapply refines_sem_var; eauto. *)
  (*     + clear H0 H4; SolveForall. *)
  (*     + clear H0 H2; SolveForall. *)
  (*   - econstructor; eauto; clear H0 H2 H4. *)
  (*     + clear H3; SolveForall. *)
  (*     + clear H1; SolveForall. *)
  (*   - econstructor; eauto. *)
  (*     clear H0 H2; SolveForall. *)
  (*   - econstructor; eauto. *)
  (*     2: (intro k; destruct (H3 k) as [H4 _]; apply H4). *)
  (*     clear H0 H2 H3; SolveForall. *)
  (* Qed. *)

  (* Fact refines_sem_equation: forall G H H' b equ, *)
  (*     refines eq H H' -> *)
  (*     sem_equation G H b equ -> *)
  (*     sem_equation G H' b equ. *)
  (* Proof. *)
  (*   intros G H H' b [xs es] Href Hsem. *)
  (*   destruct Hsem. *)
  (*   apply Seq with (ss:=ss). *)
  (*   - clear H1; SolveForall. *)
  (*     constructor; auto. eapply refines_sem_exp; eauto. *)
  (*   - clear H0; SolveForall. *)
  (*     constructor; auto. eapply refines_sem_var; eauto. *)
  (* Qed. *)

  (* (** Substitute `ev` to `v` in `e` *) *)
  (* Fixpoint subst_in_expr v ev e := *)
  (*   match e with *)
  (*   | Econst c => Econst c *)
  (*   | Evar v' a => if ident_eqb v v' then ev else Evar v' a *)
  (*   | Eunop op e a => Eunop op (subst_in_expr v ev e) a *)
  (*   | Ebinop op el er ann => *)
  (*     Ebinop op (subst_in_expr v ev el) (subst_in_expr v ev er) ann *)
  (*   | Efby es1 es2 anns => Efby (List.map (subst_in_expr v ev) es1) *)
  (*                              (List.map (subst_in_expr v ev) es2) anns *)
  (*   | Ewhen es id on ann => *)
  (*     Ewhen (List.map (subst_in_expr v ev) es) id on ann *)
  (*   | Emerge id es1 es2 ann => Emerge id (List.map (subst_in_expr v ev) es1) *)
  (*                                    (List.map (subst_in_expr v ev) es2) ann *)
  (*   | Eite ec et ee ann => Eite (subst_in_expr v ev ec) *)
  (*                              (List.map (subst_in_expr v ev) et) *)
  (*                              (List.map (subst_in_expr v ev) ee) ann *)
  (*   | Eapp id es er anns => Eapp id (List.map (subst_in_expr v ev) es) *)
  (*                               (match er with *)
  (*                                | None => None *)
  (*                                | Some er => Some (subst_in_expr v ev er) *)
  (*                                end) anns *)
  (*   end. *)
  (* Definition subst_in_exprs v ev es := List.map (subst_in_expr v ev) es. *)

  (* Fact subst_exp_typeof : forall G vars e t et ty, *)
  (*     NoDupMembers vars -> *)
  (*     List.In (t, ty) vars -> *)
  (*     typeof et = [ty] -> *)
  (*     wt_exp G vars e -> *)
  (*     wt_exp G vars (subst_in_expr t et e) -> *)
  (*     typeof (subst_in_expr t et e) = typeof e. *)
  (* Proof. *)
  (*   intros G vars e t et ty Hndup Hin Het Hwt1 Hwt2. *)
  (*   induction e; simpl; auto. *)
  (*   destruct (ident_eqb t i) eqn:Hti; simpl in *; auto. *)
  (*   rewrite Hti in *. *)
  (*   rewrite ident_eqb_eq in Hti; subst; simpl in *. *)
  (*   inv Hwt1; simpl. *)
  (*   rewrite Het. *)
  (*   specialize (NoDupMembers_det _ _ _ vars Hndup Hin H1) as Htyty0. *)
  (*   rewrite Htyty0. reflexivity. *)
  (* Qed. *)

  (* Fact wt_one_equation : forall G vars x e, *)
  (*     wt_equation G vars ([x], [e]) -> *)
  (*     (exists ty, wt_exp G vars e /\ typeof e = [ty] /\ List.In (x, ty) vars). *)
  (* Proof. *)
  (*   intros G vars x e Hwt. *)
  (*   destruct Hwt as [Hwt Hvar]; simpl in Hvar. *)
  (*   inv Hwt. clear H2. rename H1 into Hwt. *)
  (*   inv Hvar. inv H3. rename H2 into Hin. *)
  (*   rewrite List.app_nil_r in H1. *)
  (*   exists y; auto. *)
  (* Qed. *)

  (* Local Hint Resolve subst_exp_typeof. *)
  (* Lemma subst_exp_wt : forall G vars e t et, *)
  (*     NoDupMembers vars -> *)
  (*     wt_exp G vars e -> wt_equation G vars ([t], [et]) -> *)
  (*     wt_exp G vars (subst_in_expr t et e). *)
  (* Proof with eauto. *)
  (*   intros G vars e t et Hndup Hwt1 Hwt2. *)
  (*   (* Transform wt_equation into something usable *) *)
  (*   apply wt_one_equation in Hwt2. *)
  (*   destruct Hwt2 as [ty [Hwt2 [Hty Hin]]]. *)

  (*   (* Main induction *) *)
  (*   induction Hwt1 using wt_exp_ind2; simpl. *)
  (*   - (* const *) constructor. *)
  (*   - (* var *) *)
  (*     destruct (ident_eqb t x) eqn:Htx. *)
  (*     + rewrite ident_eqb_eq in Htx; subst... *)
  (*     + constructor; auto. *)
  (*   - (* unop *) *)
  (*     econstructor... *)
  (*     rewrite <- H... *)
  (*   - (* binop *) *)
  (*     econstructor... *)
  (*     + rewrite <- H... *)
  (*     + rewrite <- H0... *)
  (*   - (* fby *) *)
  (*     econstructor... *)
  (*     + clear H H4. SolveForall. *)
  (*     + clear H0 H3. SolveForall. *)
  (*     + rewrite <- H3; clear H3. *)
  (*       induction es; simpl... inv H0; inv H2. *)
  (*       f_equal... *)
  (*     + rewrite <- H4; clear H4. *)
  (*       induction e0s; simpl... inv H; inv H1. *)
  (*       f_equal... *)
  (*   - (* when *) *)
  (*     econstructor... *)
  (*     + clear H H1. SolveForall. *)
  (*     + rewrite <- H1; clear H1. *)
  (*       induction es; simpl... inv H; inv H0. *)
  (*       f_equal... *)
  (*   - (* ite *) *)
  (*     econstructor... *)
  (*     + clear H H4. SolveForall. *)
  (*     + clear H1 H5. SolveForall. *)
  (*     + rewrite <- H4; clear H4. *)
  (*       induction ets; simpl... inv H; inv H0. *)
  (*       f_equal... *)
  (*     + rewrite <- H5; clear H5. *)
  (*       induction efs; simpl... inv H1; inv H2. *)
  (*       f_equal... *)
  (*   - (* merge *) *)
  (*     econstructor... *)
  (*     + clear H H4. SolveForall. *)
  (*     + clear H1 H5. SolveForall. *)
  (*     + rewrite <- H3... *)
  (*     + rewrite <- H4; clear H4. *)
  (*       induction ets; simpl... inv H; inv H0; subst. *)
  (*       f_equal... *)
  (*     + rewrite <- H5; clear H5. *)
  (*       induction efs; simpl... inv H1; inv H2; subst. *)
  (*       f_equal... *)
  (*   - (* app *) *)
  (*     econstructor... *)
  (*     + clear H H2. SolveForall. *)
  (*     + generalize dependent (n_in n). induction es; intros clocks Hfor; simpl in *. *)
  (*       * inv Hfor. constructor. *)
  (*       * inv H; inv H0. *)
  (*         apply Forall2_app_inv_l in Hfor. destruct Hfor as [n1 [n2 [Hn1 [Hn2 Hn1n2]]]]. rewrite Hn1n2; clear Hn1n2. *)
  (*         apply Forall2_app... clear IHes. *)
  (*         erewrite subst_exp_typeof... *)
  (*   - (* app (reset) *) *)
  (*     econstructor... *)
  (*     + clear H H2. SolveForall. *)
  (*     + generalize dependent (n_in n). induction es; intros clocks Hfor; simpl in *. *)
  (*       * inv Hfor. constructor. *)
  (*       * inv H; inv H0. *)
  (*         apply Forall2_app_inv_l in Hfor. destruct Hfor as [n1 [n2 [Hn1 [Hn2 Hn1n2]]]]. rewrite Hn1n2; clear Hn1n2. *)
  (*         apply Forall2_app; auto. clear IHes. *)
  (*         erewrite subst_exp_typeof... *)
  (*     + rewrite <- H5... *)
  (* Qed. *)

  (* Corollary subst_exp_typeof2: forall G vars e t et, *)
  (*     NoDupMembers vars -> *)
  (*     wt_exp G vars e -> *)
  (*     wt_equation G vars ([t], [et]) -> *)
  (*     typeof (subst_in_expr t et e) = typeof e. *)
  (* Proof. *)
  (*   intros G vars e t et Hndup Hwt1 Hwt2. *)
  (*   specialize (wt_one_equation _ _ _ _ Hwt2) as [ty [Hwt3 [Hty Hin]]]. *)
  (*   eapply subst_exp_typeof; eauto. *)
  (*   eapply subst_exp_wt; eauto. *)
  (* Qed. *)

  (* Local Hint Constructors sem_exp. *)
  (* Local Hint Resolve subst_exp_typeof2. *)
  (* Lemma subst_exp_sem1 : forall G vars H b e t et v, *)
  (*     NoDupMembers vars -> *)
  (*     wt_exp G vars e -> *)
  (*     wt_equation G vars ([t], [et]) -> *)
  (*     sem_equation G H b ([t], [et]) -> *)
  (*     sem_exp G H b e v -> *)
  (*     sem_exp G H b (subst_in_expr t et e) v. *)
  (* Proof with eauto. *)
  (*   intros G vars H b e t et v Hndup Hwt1 Hwt2 Hsemt Hsem. revert t Hwt1 Hwt2 Hsemt. *)
  (*   induction Hsem using sem_exp_ind2 with (P_equation := fun H b e => True) (P_node := fun i xs ys => True); *)
  (*     intros; simpl; auto; inv Hwt1; eauto. *)
  (*   - (* var *) *)
  (*     destruct (ident_eqb t0 x) eqn:Ht0x; auto. *)
  (*     + rewrite ident_eqb_eq in Ht0x; subst. *)
  (*       destruct H0. *)
  (*       inv Hsemt. *)
  (*       inv H10; inv H8. *)
  (*       destruct H7. *)
  (*       inv H9; inv H12. *)
  (*       unfold MapsTo in *. rewrite H0 in H2; inv H2... *)
  (*       rewrite <- H5 in H1; rewrite H1; rewrite H6; clear H1 H5 H6. *)
  (*       simpl. rewrite List.app_nil_r. assumption. *)
  (*   - (* unop *) *)
  (*     econstructor... *)
  (*     rewrite <- H0... *)
  (*   - (* binop *) *)
  (*     econstructor... *)
  (*     * rewrite <- H0... *)
  (*     * rewrite <- H1... *)
  (*   - (* fby *) *)
  (*     econstructor; eauto; clear H0 H2 H4. *)
  (*     + clear H11. induction H1; simpl... *)
  (*       inv H8... *)
  (*     + clear H10. induction H3; simpl... *)
  (*       inv H9... *)
  (*   - (* when *) *)
  (*     econstructor; eauto; clear H0 H2 H3. *)
  (*     induction H1; simpl... *)
  (*     inv H8... *)
  (*   - (* ite *) *)
  (*     econstructor; eauto; clear H0 H1 H3 H5 H12 H14. *)
  (*     + clear H4. induction H2; simpl... *)
  (*       inv H10... *)
  (*     + clear H2. induction H4; simpl... *)
  (*       inv H11... *)
  (*   - (* merge *) *)
  (*     econstructor; eauto; clear H0 H2 H4 H14. *)
  (*     + clear H3. induction H1; simpl... *)
  (*       inv H10... *)
  (*     + clear H1. induction H3; simpl... *)
  (*       inv H11... *)
  (*   - (* app *) *)
  (*     econstructor; eauto; clear H0 H2 H8. *)
  (*     induction H1; simpl... *)
  (*     inv H6... *)
  (*   - (* app (reset) *) *)
  (*     econstructor; eauto; clear H0 H10. *)
  (*     2: (intro k; destruct (H3 k); eauto). *)
  (*     clear H3. induction H1; simpl... *)
  (*     inv H8... *)
  (* Qed. *)

  (* Local Ltac rewrite_types := *)
  (*   match goal with *)
  (*   | H1 : (typeof (subst_in_expr _ _ ?e) = ?ty1), H2 : (typeof ?e = ?ty2) |- ?ty1 = ?ty2 => *)
  (*     rewrite <- H1; rewrite <- H2; eapply subst_exp_typeof2; eauto *)
  (*   | _ => idtac *)
  (*   end. *)

  (* Hypothesis sem_exp_det : forall G H b e v1 v2, *)
  (*     sem_exp G H b e v1 -> *)
  (*     sem_exp G H b e v2 -> *)
  (*     Forall2 (fun v1 v2 => Streams.EqSt v1 v2) v1 v2. *)

  (* Lemma subst_exp_sem2 : forall G vars H b e t et v, *)
  (*     NoDupMembers vars -> *)
  (*     wt_exp G vars e -> *)
  (*     wt_equation G vars ([t], [et]) -> *)
  (*     sem_equation G H b ([t], [et]) -> *)
  (*     sem_exp G H b (subst_in_expr t et e) v -> *)
  (*     sem_exp G H b e v. *)
  (* Proof with eauto. *)
  (*   intros G vars H b e t et v Hndup Hwt1 Hwt2 Hsemt Hsem. generalize dependent v. *)
  (*   induction e using exp_ind2; intros v Hsem; simpl in *; inv Hwt1; eauto. *)
  (*   - (* var *) *)
  (*     destruct (ident_eqb t x) eqn:Htx; auto. *)
  (*     rewrite ident_eqb_eq in Htx; subst. *)
  (*     destruct Hwt2 as [Hwt2 Hty2]. *)
  (*     inv Hsemt. *)
  (*     inv H7; inv H6; simpl in *; rewrite List.app_nil_r in *. *)
  (*     inv H8; inv H7. *)
  (*     specialize (sem_exp_det _ _ _ _ _ _ Hsem H4) as Hdet. *)
  (*     inv Hdet; inv H8. *)
  (*     constructor. rewrite H7. assumption. *)
  (*   - (* unop *) *)
  (*     inv Hsem. econstructor... *)
  (*     assert ([ty0] = [tye]) as Hty0e by rewrite_types. *)
  (*     inv Hty0e... *)
  (*   - (* binop *) *)
  (*     inv Hsem. econstructor... *)
  (*     assert ([ty0] = [ty1]) as Hty01 by rewrite_types. *)
  (*     assert ([ty3] = [ty2]) as Hty32 by rewrite_types. *)
  (*     inv Hty01; inv Hty32... *)
  (*   - (* fby *) *)
  (*     inv Hsem. *)
  (*     repeat take (Forall2 _ (List.map _ _) _) and rewrite Forall2_map_1 in it. *)
  (*     rewrite Forall_forall in *. *)
  (*     econstructor... *)
  (*     + apply Forall2_impl_In with (2:=it). *)
  (*       intros... *)
  (*     + apply Forall2_impl_In with (2:=it0). *)
  (*       intros... *)
  (*   - (* when *) *)
  (*     inv Hsem. *)
  (*     econstructor... *)
  (*     take (Forall2 _ (List.map _ _) _) and rewrite Forall2_map_1 in it. *)
  (*     apply Forall2_impl_In with (2:=it). *)
  (*     intros. *)
  (*     rewrite Forall_forall in *... *)
  (*   - (* ite *) *)
  (*     inv Hsem. *)
  (*     repeat take (Forall2 _ (List.map _ _) _) and rewrite Forall2_map_1 in it. *)
  (*     rewrite Forall_forall in *. *)
  (*     econstructor... *)
  (*     + apply Forall2_impl_In with (2:=it). *)
  (*       intros... *)
  (*     + apply Forall2_impl_In with (2:=it0). *)
  (*       intros... *)
  (*   - (* merge *) *)
  (*     inv Hsem. *)
  (*     repeat take (Forall2 _ (List.map _ _) _) and rewrite Forall2_map_1 in it. *)
  (*     rewrite Forall_forall in *. *)
  (*     econstructor... *)
  (*     + apply Forall2_impl_In with (2:=it). *)
  (*       intros... *)
  (*     + apply Forall2_impl_In with (2:=it0). *)
  (*       intros... *)
  (*   - (* app *) *)
  (*     inv Hsem. *)
  (*     take (Forall2 _ (List.map _ _) _) and rewrite Forall2_map_1 in it. *)
  (*     rewrite Forall_forall in *. *)
  (*     econstructor... *)
  (*     apply Forall2_impl_In with (2:=it). *)
  (*     intros... *)
  (*   - (* app (reset) *) *)
  (*     inv Hsem. *)
  (*     take (Forall2 _ (List.map _ _) _) and rewrite Forall2_map_1 in it. *)
  (*     rewrite Forall_forall in *. *)
  (*     econstructor... *)
  (*     apply Forall2_impl_In with (2:=it). *)
  (*     intros... *)
  (* Qed. *)

  (* Lemma subst_eq_sem : forall G vars H b x e t et, *)
  (*     NoDupMembers vars -> *)
  (*     wt_exp G vars e -> *)
  (*     wt_equation G vars ([t], [et]) -> *)
  (*     sem_equation G H b ([t], [et]) -> *)
  (*     (sem_equation G H b (x, [e]) <-> sem_equation G H b (x, [subst_in_expr t et e])). *)
  (* Proof. *)
  (*   intros. split; intro Hsem; inv Hsem; econstructor; eauto. *)
  (*   + inv H9; inv H8; simpl in H10; rewrite List.app_nil_r in H10. *)
  (*     constructor; eauto. eapply subst_exp_sem1; eauto. *)
  (*   + inv H9; inv H8; simpl in H10; rewrite List.app_nil_r in H10. *)
  (*     constructor; eauto. eapply subst_exp_sem2; eauto. *)
  (* Qed. *)

End NORMPROOFS.
