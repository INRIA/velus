From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common Ident.
From Velus Require Import Operators Environment.
From Velus Require Import CoindStreams.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LTyping Lustre.LSemantics.
From Velus Require Import Lustre.Normalization.Fresh Lustre.Normalization.Normalization.

(** * Correctness of the Normalization *)

Local Set Warnings "-masking-absolute-name".
Module Type CORRECTNESS
       (Import Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Str : COINDSTREAMS Op OpAux)
       (Import Syn : LSYNTAX Ids Op)
       (Import Typ : LTYPING Ids Op Syn)
       (Lord : LORDERED Ids Op Syn)
       (Import Sem : LSEMANTICS Ids Op OpAux Syn Lord Str)
       (Import Norm : NORMALIZATION Ids Op OpAux Syn Typ).
  Import List.

  Definition st_tys (st : fresh_st (ann * bool)) := idty (idty (snd st)).

  Fact st_follows_tys_incl : forall st st',
      fresh_st_follows st st' ->
      incl (st_tys st) (st_tys st').
  Proof.
    intros st st' [Hincl _].
    unfold incl in *. intros [id data] Hin.
    unfold st_tys, idty in *.
    repeat simpl_In. inv H. inv H0.
    exists (id, (data, n)). split; auto.
    repeat simpl_In.
    exists (id, (data, n, b)). eauto.
  Qed.

  Fact idents_for_anns_incl : forall anns ids st st',
      idents_for_anns anns st = (ids, st') ->
      incl ids (idty (snd st')).
  Proof.
    induction anns; intros ids st st' Hids; simpl in Hids; repeat inv_bind;
      unfold incl; intros ? Hin; inv Hin.
    - unfold fresh_ident in H; destruct st as [n l]; inv H.
      apply idents_for_anns_st_follows in H0; destruct H0 as [Hfollows _].
      unfold idty. simpl_In.
      exists (x, (a, false)); simpl. split; auto.
      apply Hfollows. simpl. auto.
    - apply IHanns in H0; auto.
  Qed.

  Ltac solve_incl :=
    match goal with
    | H : wt_clock ?l1 ?cl |- wt_clock ?l2 ?cl =>
      eapply wt_clock_incl; [| eauto]
    | H : wt_nclock ?l1 ?cl |- wt_nclock ?l2 ?cl =>
      eapply wt_nclock_incl; [| eauto]
    | H : wt_exp ?G ?l1 ?e |- wt_exp ?G ?l2 ?e =>
      eapply wt_exp_incl; [| eauto]
    | H : wt_equation ?G ?l1 ?eq |- wt_equation ?G ?l2 ?eq =>
      eapply wt_equation_incl; [| eauto]
    | |- incl ?l1 ?l1 => reflexivity
    | |- incl ?l1 (?l1 ++ ?l2) =>
      eapply incl_appl; reflexivity
    | |- incl (?l1 ++ ?l2) (?l1 ++ ?l3) =>
      eapply incl_app
    | |- incl ?l1 (?l2 ++ ?l3) =>
      eapply incl_appr
    | |- incl (st_tys ?st1) (st_tys _) =>
      eapply st_follows_tys_incl; repeat solve_st_follows
    | H : incl ?l1 ?l2 |- incl (idty ?l1) (idty ?l2) =>
      eapply incl_map; eauto
    end.

  Ltac singleton_length :=
    simpl in *;
    match goal with
    | H : length ?x = 1 |- _ =>
      destruct x; simpl in *; try congruence
    end;
    match goal with
    | H : S (length ?x) = 1 |- _ =>
      destruct x; simpl in *; try congruence;
      clear H
    end.

  Ltac subst_length :=
    match goal with
    | H: length ?x1 = length ?x2 |- context l [length ?x1] =>
      rewrite H
    | H: length ?x1 = length ?x2, H1: context l [length ?x1] |- _ =>
      rewrite H in H1
    | H: ?x1 = ?x2 |- context l [length ?x1] =>
      rewrite H
    | H: ?x1 = ?x2, H1: context l [length ?x1] |- _ =>
      rewrite H in H1
    end.

  Ltac simpl_length :=
    repeat subst_length;
    (match goal with
     | H : context c [Nat.min ?x1 ?x1] |- _ =>
       repeat rewrite PeanoNat.Nat.min_id in H
     | H : context c [length (combine _ _)] |- _ =>
       rewrite combine_length in H
     | H : context c [length (map _ _)] |- _ =>
       rewrite map_length in H
     | |- context c [Nat.min ?x1 ?x1] =>
       rewrite PeanoNat.Nat.min_id
     | |- context c [length (combine _ _)] =>
       rewrite combine_length
     | |- context c [length (map _ _)] =>
       rewrite map_length
    end).

  Ltac solve_length :=
    repeat simpl_length; solve [auto].

  Ltac simpl_nth :=
    match goal with
    | H : In ?x _ |- _ =>
      apply In_nth with (d:=x) in H; destruct H as [? [? ?]]; try simpl_nth
    | H : nth _ (combine _ _) _ = _ |- _ =>
      rewrite combine_nth in H; [inv H; try simpl_nth|repeat solve_length]
    end.

  Hint Resolve in_combine_l in_combine_r.
  Hint Resolve incl_tl incl_appl incl_appr incl_app incl_refl.

  Fact normalize_exp_numstreams : forall e is_control es' eqs' st st',
      normalize_exp is_control e st = (es', eqs', st') ->
      Forall (fun e => numstreams e = 1) es'.
  Proof.
    intros e is_control es' eqs' st st' Hnorm.
    induction e; simpl in Hnorm; repeat inv_bind; repeat constructor.
    2: destruct l0.
    3,4: destruct l1.
    3,4: destruct is_control.
    1,2,3,4,5,6,7:(repeat inv_bind; rewrite Forall_forall; intros ? Hin;
                   repeat simpl_In; reflexivity).
  Qed.

  Corollary map_bind2_normalize_exp_numstreams : forall es is_control es' eqs' st st',
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      Forall (fun e => numstreams e = 1) (concat es').
  Proof.
    intros es is_control es' eqs' st st' Hmap.
    apply map_bind2_values in Hmap.
    induction Hmap; simpl.
    - constructor.
    - apply Forall_app; split; auto.
      destruct H as [? [? H]].
      eapply normalize_exp_numstreams; eauto.
  Qed.

  Corollary normalize_exps_numstreams : forall es es' eqs' st st',
      normalize_exps es st = (es', eqs', st') ->
      Forall (fun e => numstreams e = 1) es'.
  Proof.
    intros es es' eqs' st st' Hnorm.
    unfold normalize_exps in Hnorm. repeat inv_bind.
    eapply map_bind2_normalize_exp_numstreams. eauto.
  Qed.

  Fact normalize_fby_numstreams : forall e0s es anns es' eqs' st st',
      normalize_fby e0s es anns st = (es', eqs', st') ->
      Forall (fun e => numstreams e = 1) es'.
  Proof.
    intros e0s es anns es' eqs' st st' Hnorm.
    unfold normalize_fby in Hnorm. repeat inv_bind.
    apply map_bind2_values in H.
    repeat rewrite_Forall_forall.
    eapply In_nth with (d:=x) in H2; destruct H2 as [n [? ?]].
    repeat simpl_length.
    specialize (H1 (x, x, (Op.bool_type, (Cbase, None))) x [] _ _ _ _ H2 eq_refl eq_refl eq_refl).
    destruct H1 as [st'' [st''' H1]]. destruct (nth _ _ _) as [[e0 e] [ty cl]]. rewrite <- H3.
    specialize (fby_iteexp_spec e0 e ty cl) as [[? [? Hspec]]|Hspec]; subst;
      rewrite Hspec in H1; clear Hspec; repeat inv_bind; reflexivity.
  Qed.

  (** ** Preservation of wt *)

  Fact idents_for_anns_wt : forall G vars anns ids st st',
      idents_for_anns anns st = (ids, st') ->
      Forall (fun '(ty, cl) => wt_nclock vars cl) anns ->
      Forall (wt_exp G (vars++(idty ids))) (map (fun '(x, ann) => Evar x ann) ids).
  Proof.
    induction anns; intros ids st st' Hidents Hf;
      simpl in *; repeat inv_bind.
    - constructor.
    - inv Hf. destruct a as [ty cl].
      specialize (IHanns x1 _ _ H0 H4).
      econstructor; eauto.
      + repeat constructor; simpl; auto.
        * apply in_or_app. right. constructor; auto.
        * eapply wt_nclock_incl; [| eauto]. eauto.
      + eapply Forall_impl; [| eauto].
        intros. eapply wt_exp_incl; [| eauto]. eauto.
  Qed.

  Fact hd_default_wt_exp : forall G vars es,
      Forall (wt_exp G vars) es ->
      wt_exp G vars (hd_default es).
  Proof.
    intros G vars es Hf.
    destruct es; simpl.
    - constructor.
    - inv Hf; auto.
  Qed.

  Fact map_bind2_wt_exp' {A A2 B} :
    forall G vars (k : A -> Fresh (exp * A2) B) a es' a2s st st',
      map_bind2 k a st = (es', a2s, st') ->
      (forall st st' a es a2s, k a st = (es, a2s, st') -> fresh_st_follows st st') ->
      Forall (fun a => forall e' a2s st0 st0',
                  k a st0 = (e', a2s, st0') ->
                  fresh_st_follows st st0 ->
                  fresh_st_follows st0' st' ->
                  wt_exp G vars e') a ->
      Forall (wt_exp G vars) es'.
  Proof.
    intros G vars k a.
    induction a; intros es' a2s st st' Hmap Hfollows Hforall;
      simpl in Hmap; repeat inv_bind.
    - constructor.
    - constructor.
      + rewrite Forall_forall in Hforall.
        eapply Hforall; eauto.
        * constructor. reflexivity.
        * reflexivity.
        * eapply map_bind2_st_follows in H0; eauto.
          rewrite Forall_forall; intros; eauto.
      + eapply IHa; eauto.
        rewrite Forall_forall in *; intros.
        eapply Hforall; eauto. apply in_cons; auto.
        etransitivity; eauto.
  Qed.

  Fact map_bind2_wt_exp {A A2 B} :
    forall G vars (k : A -> Fresh (list exp * A2) B) a es' a2s st st',
      map_bind2 k a st = (es', a2s, st') ->
      (forall st st' a es a2s, k a st = (es, a2s, st') -> fresh_st_follows st st') ->
      Forall (fun a => forall es' a2s st0 st0',
                  k a st0 = (es', a2s, st0') ->
                  fresh_st_follows st st0 ->
                  fresh_st_follows st0' st' ->
                  Forall (wt_exp G vars) es') a ->
      Forall (wt_exp G vars) (concat es').
  Proof.
    intros G vars k a.
    induction a; intros es' a2s st st' Hmap Hfollows Hforall;
      simpl in Hmap; repeat inv_bind.
    - constructor.
    - apply Forall_app. split; eauto.
      + rewrite Forall_forall in Hforall.
        eapply Hforall; eauto.
        * constructor. reflexivity.
        * reflexivity.
        * eapply map_bind2_st_follows in H0; eauto.
          rewrite Forall_forall; intros; eauto.
      + eapply IHa; eauto.
        rewrite Forall_forall in *; intros.
        eapply Hforall; eauto. apply in_cons; auto.
        etransitivity; eauto.
  Qed.

  Hint Constructors wt_exp.

  Fact normalize_fby_wt_exp : forall G vars e0s es anns es' eqs' st st',
      Forall (wt_exp G (vars++(st_tys st))) e0s ->
      Forall (wt_exp G (vars++(st_tys st))) es ->
      Forall2 (fun e0 a => typeof e0 = [fst a]) e0s anns ->
      Forall2 (fun e a => typeof e = [fst a]) es anns ->
      Forall (fun '(_, cl) => wt_nclock vars cl) anns ->
      normalize_fby e0s es anns st = (es', eqs', st') ->
      Forall (wt_exp G (vars++(st_tys st'))) es'.
  Proof.
    intros G vars e0s es anns es' eqs' st st' Hwt1 Hwt2 Hty1 Hty2 Hclock Hnorm.
    unfold normalize_fby in Hnorm. repeat inv_bind.
    eapply map_bind2_wt_exp' in H; eauto.
    - destruct a as [[e0 e] a]. eauto.
    - solve_forall. destruct x as [[e0 e] [ty cl]].
      specialize (fby_iteexp_spec e0 e ty cl) as [[? [? Hspec]]|Hspec]; subst;
        rewrite Hspec in H1; clear Hspec; repeat inv_bind.
      + repeat rewrite_Forall_forall.
        repeat constructor; simpl.
        * repeat simpl_In.
          apply Hwt2 in H7.
          repeat solve_incl.
        * rewrite app_nil_r.
          repeat rewrite_Forall_forall.
          simpl_nth; repeat simpl_length.
          specialize (H4 _ _ _ _ _ H0 H11 H10). simpl in H4.
          congruence.
        * f_equal. simpl_nth; repeat simpl_length.
          specialize (H6 _ _ _ _ _ H0 H8 H10); simpl in H6.
          congruence.
        * repeat simpl_In.
          apply Hclock in H0. repeat solve_incl.
      + repeat rewrite_Forall_forall.
        repeat simpl_length.
        repeat constructor; simpl.
        * unfold init_var_for_clock in H1. destruct st0.
          destruct (find _ _) eqn:Hfind.
          -- destruct p. inv H1.
             apply find_some in Hfind; destruct Hfind as [Hfind1 Hfind2].
             destruct p as [[? ?] ?].
             repeat rewrite Bool.andb_true_iff in Hfind2. destruct Hfind2 as [[_ Hfind2] _].
             rewrite equiv_decb_equiv in Hfind2.
             apply fresh_ident_st_follows in H4.
             assert (incl (idty (idty l)) (vars++(st_tys st'))) as Hincl.
             { repeat solve_incl. apply st_follows_tys_incl in H4. apply st_follows_tys_incl in H3.
               simpl in *. etransitivity; eauto. }
             apply Hincl. repeat unfold idty; repeat simpl_In.
             exists (x, (t, n)); simpl; auto. split.
             ++ repeat f_equal. apply Hfind2.
             ++ repeat simpl_In. exists (x, (t, n, b)); simpl; eauto.
          -- inv H1.
             assert (incl (idty(idty(snd (Pos.succ x, (x, (Op.bool_type, cl, true))::l)))) (vars++(st_tys st'))).
             { repeat solve_incl. apply st_follows_tys_incl. repeat solve_st_follows. }
             apply H1; simpl; auto.
        * repeat simpl_In. apply Hclock in H0. repeat solve_incl.
        * repeat simpl_In. apply Hwt1 in H10. repeat solve_incl.
        * unfold fresh_ident in H4; destruct x2 as [n l]; inv H4.
          apply st_follows_tys_incl in H3. eapply incl_appr in H3.
          eapply H3. simpl; auto.
        * repeat simpl_In. apply Hclock in H0. repeat solve_incl.
        * rewrite app_nil_r.
          simpl_nth. repeat simpl_length.
          specialize (H8 _ _ _ _ _ H0 H10 H12). simpl in H8.
          congruence.
        * repeat simpl_In. apply Hclock in H0. repeat solve_incl.
  Qed.

  Fact normalize_reset_typeof_bool : forall e e' eqs' st st',
      typeof e = [Op.bool_type] ->
      normalize_reset e st = (e', eqs', st') ->
      typeof e' = [Op.bool_type].
  Proof.
    intros e e' eqs' st st' Htyp Hnorm.
    specialize (normalize_reset_spec e) as [[? [? [? Hspec]]]|Hspec]; subst;
      rewrite Hspec in Hnorm; clear Hspec; repeat inv_bind.
    - simpl in Htyp. assumption.
    - destruct (hd _) eqn:Hann; simpl in *; repeat inv_bind;
        destruct e; simpl in *; try solve [inv Hann; auto].
      1,3,4: (destruct l1; try destruct l1; simpl in *; inv Hann; simpl in *; auto; destruct l1; congruence).
      + destruct l0. destruct l0; simpl in *; inv Hann; simpl in *; auto.
        destruct l0; congruence.
      + destruct l0; try destruct a; simpl in *; inv Hann; simpl in *; auto.
        destruct l0; congruence.
  Qed.

  Fact normalize_reset_wt_exp : forall G vars e e' eqs' st st',
      wt_exp G (vars++(st_tys st)) e ->
      normalize_reset e st = (e', eqs', st') ->
      wt_exp G (vars++(st_tys st')) e'.
  Proof.
    intros G vars e e' eqs' st st' Hwt Hnorm.
    specialize (normalize_reset_spec e) as [[? [? [? Hspec]]]|Hspec]; subst;
      rewrite Hspec in Hnorm; clear Hspec; repeat inv_bind.
    - assumption.
    - destruct (hd _) eqn:Hann; simpl in *; repeat inv_bind.
      constructor.
      + unfold fresh_ident in H. destruct st as [n l]. inv H.
        apply in_or_app. simpl. auto.
      + apply fresh_ident_st_follows in H.
        destruct e; simpl in Hann; inv Hann; inv Hwt.
        1: repeat constructor.
        1,2,3: (repeat solve_incl).
        5,6: destruct l0; simpl in *; inv H1; repeat constructor; inv H9; repeat solve_incl.
        2,3,4: destruct l; simpl in *; inv H1; repeat constructor.
        1: destruct l1; simpl in *; inv H1; repeat constructor; inv H8; repeat solve_incl.
        1: inv H5. 2: inv H5. 3: inv H6.
        1,2,3: (destruct (map _) eqn:Hmap; simpl in *; inv H2; repeat constructor;
              apply map_cons' in Hmap; destruct Hmap as [? [? [Hmap _]]]; inv Hmap; repeat solve_incl).
  Qed.

  Fact normalize_exp_wt_exp : forall G vars e is_control es' eqs' st st',
      wt_exp G vars e ->
      normalize_exp is_control e st = (es', eqs', st') ->
      Forall (wt_exp G (vars++(st_tys st'))) es'.
  Proof with eauto.
    intros G vars e is_control es' eqs' st st' Hwt;
      revert is_control eqs' es' st st'.
    induction Hwt using wt_exp_ind2;
      intros is_control eqs' es' st st' Hnorm; simpl in *.
    - (* const *)
      repeat inv_bind...
    - (* var *)
      repeat inv_bind.
      repeat constructor.
      + apply in_or_app...
      + repeat solve_incl.
    - (* unop *)
      repeat inv_bind.
      specialize (IHHwt _ _ _ _ _ H2).
      repeat constructor.
      specialize (normalize_exp_length _ _ _ _ _ _ _ _ Hwt H2) as Hlen.
      rewrite <- numstreams_length_typeof in Hlen.
      replace (typeof e) in *.
      singleton_length.
      inv IHHwt. econstructor...
      eapply normalize_exp_typeof in Hwt...
      simpl in *; rewrite app_nil_r in Hwt; rewrite Hwt...
      eapply wt_nclock_incl; [| eauto]...
    - (* binop *)
      repeat inv_bind.
      specialize (IHHwt1 _ _ _ _ _ H3).
      specialize (IHHwt2 _ _ _ _ _ H4).
      repeat constructor.
      specialize (normalize_exp_length _ _ _ _ _ _ _ _ Hwt1 H3) as Hlen1.
      specialize (normalize_exp_length _ _ _ _ _ _ _ _ Hwt2 H4) as Hlen2.
      rewrite <- numstreams_length_typeof in Hlen1.
      rewrite <- numstreams_length_typeof in Hlen2.
      replace (typeof e1) in *.
      replace (typeof e2) in *.
      repeat singleton_length.
      eapply normalize_exp_typeof in Hwt1...
      eapply normalize_exp_typeof in Hwt2...
      inv IHHwt1. inv IHHwt2. inv H8. inv H10.
      econstructor; eauto;
        simpl in *; rewrite app_nil_r in *;
          try rewrite Hwt1; try rewrite Hwt2...
      + eapply normalize_exp_st_follows in H4. repeat solve_incl.
      + repeat solve_incl.
    - (* fby *)
      repeat inv_bind.
      specialize (idents_for_anns_incl _ _ _ _ H9) as Hincl.
      apply idents_for_anns_wt with (G:=G) (vars:=vars) in H9.
      + solve_forall.
        eapply wt_exp_incl; [| eauto].
        apply incl_app... apply incl_appr. apply incl_map...
      + rewrite Forall_forall in *; intros.
        destruct x as [? [? ?]]. eapply H5.
        simpl_In.
        exists (t, (c, o)); simpl...
    - (* when *)
      repeat inv_bind.
      specialize (map_bind2_normalize_exp_length _ _ _ _ _ _ _ _ H H1) as Hlength.
      specialize (map_bind2_normalize_exp_typeof _ _ _ _ _ _ _ _ H H1) as Htypeof.
      repeat rewrite_Forall_forall.
      rewrite in_map_iff in H4; destruct H4 as [[? ?] [? Hin]]; subst.
      constructor; simpl...
      + repeat constructor. eapply map_bind2_wt_exp in H1.
        * rewrite Forall_forall in H1...
        * intros; eapply normalize_exp_st_follows...
        * rewrite Forall_forall; intros.
          eapply H0 in H5; eauto.
          solve_forall. repeat solve_incl.
      + rewrite app_nil_r.
        specialize (map_bind2_normalize_exp_numstreams _ _ _ _ _ _ H1) as Hnumstreams.
        eapply map_bind2_normalize_exp_typeof in H1; [| rewrite Forall_forall; intros; auto].
        rewrite <- Htypeof in Hin.
        repeat simpl_nth.
        unfold typesof. rewrite flat_map_concat_map.
        eapply concat_length_map_nth; solve_forall.
        * repeat solve_length.
        * rewrite numstreams_length_typeof...
      + apply in_or_app...
      + repeat solve_incl.
    - (* merge *)
      destruct is_control; repeat inv_bind.
      + rewrite Forall_forall; intros ? Hin.
        rewrite in_map_iff in Hin; destruct Hin as [[[? ?] ?] [? Hin]]; subst.
        specialize (map_bind2_normalize_exp_length _ _ _ _ _ _ _ _ H H7) as Hlength1.
        specialize (map_bind2_normalize_exp_length _ _ _ _ _ _ _ _ H1 H4) as Hlength2.
        constructor; simpl...
        * eapply map_bind2_wt_exp with (G0:=G) (vars0 := (vars++(st_tys x2))) in H7...
          -- apply map_bind2_st_follows in H4; solve_forall...
             inv H8; [| inv H9].
             repeat simpl_In.
             rewrite Forall_forall in H7. apply H7 in H9.
             repeat constructor. repeat solve_incl.
          -- solve_forall. apply H8 in H9.
             solve_forall. repeat solve_incl.
        * eapply map_bind2_wt_exp with (G0:=G) (vars0 := (vars++(st_tys st'))) in H4...
          -- repeat simpl_In.
             rewrite Forall_forall in H4. apply H4 in H8.
             repeat constructor. repeat solve_incl.
          -- solve_forall. eapply H8 in H9.
             solve_forall. repeat solve_incl.
        * apply in_or_app...
        * rewrite app_nil_r.
          specialize (map_bind2_normalize_exp_numstreams _ _ _ _ _ _ H7) as Hnumstreams.
          eapply map_bind2_normalize_exp_typeof in H7; [| rewrite Forall_forall in *; intros; auto].
          rewrite <- H7 in Hin.
          repeat simpl_nth.
          unfold typesof. rewrite flat_map_concat_map.
          eapply concat_length_map_nth; solve_forall.
          -- repeat solve_length.
          -- rewrite numstreams_length_typeof...
        * rewrite app_nil_r.
          specialize (map_bind2_normalize_exp_numstreams _ _ _ _ _ _ H4) as Hnumstreams.
          eapply map_bind2_normalize_exp_typeof in H4; [| rewrite Forall_forall in *; intros; auto].
          rewrite <- H5 in Hin. rewrite <- H4 in Hin.
          repeat simpl_nth.
          unfold typesof. rewrite flat_map_concat_map.
          eapply concat_length_map_nth; solve_forall.
          -- repeat solve_length.
          -- rewrite numstreams_length_typeof...
        * repeat solve_incl.
      + specialize (idents_for_anns_incl _ _ _ _ H9) as Hincl.
        apply idents_for_anns_wt with (G:=G) (vars:=vars) in H9.
        * solve_forall. unfold st_tys. repeat solve_incl.
        * rewrite Forall_forall; intros.
          repeat simpl_In. inv H8...
    - (* merge *)
      destruct is_control; repeat inv_bind.
      + rewrite Forall_forall; intros ? Hin.
        rewrite in_map_iff in Hin; destruct Hin as [[[? ?] ?] [? Hin]]; subst.
        specialize (map_bind2_normalize_exp_length _ _ _ _ _ _ _ _ H H8) as Hlength1.
        specialize (map_bind2_normalize_exp_length _ _ _ _ _ _ _ _ H1 H4) as Hlength2.
        constructor; simpl...
        * apply IHHwt in H7.
          apply hd_default_wt_exp. solve_forall.
          apply map_bind2_st_follows in H8; solve_forall.
          apply map_bind2_st_follows in H4; solve_forall.
          repeat solve_incl.
        * eapply map_bind2_wt_exp with (G0:=G) (vars0 := (vars++(st_tys x4))) in H8...
          -- apply map_bind2_st_follows in H4; solve_forall...
             inv H9; [| inv H10].
             repeat simpl_In.
             rewrite Forall_forall in H8. apply H8 in H10.
             repeat constructor. repeat solve_incl.
          -- solve_forall. apply H9 in H10.
             solve_forall. repeat solve_incl.
        * eapply map_bind2_wt_exp with (G0:=G) (vars0 := (vars++(st_tys st'))) in H4...
          -- repeat simpl_In.
             rewrite Forall_forall in H4. apply H4 in H9.
             repeat constructor. repeat solve_incl.
          -- solve_forall. eapply H9 in H10.
             solve_forall. repeat solve_incl.
        * specialize (normalize_exp_length _ _ _ _ _ _ _ _ Hwt H7) as Hlength.
          rewrite <- numstreams_length_typeof in Hlength.
          rewrite H3 in Hlength; simpl in Hlength.
          eapply normalize_exp_typeof in H7...
          destruct x; simpl in *; try congruence.
          destruct x; simpl in *; try congruence.
          rewrite app_nil_r in H7. congruence.
        * rewrite app_nil_r.
          specialize (map_bind2_normalize_exp_numstreams _ _ _ _ _ _ H8) as Hnumstreams.
          eapply map_bind2_normalize_exp_typeof in H8; [| rewrite Forall_forall in *; intros; auto].
          rewrite <- H8 in Hin.
          repeat simpl_nth.
          unfold typesof. rewrite flat_map_concat_map.
          eapply concat_length_map_nth; solve_forall.
          -- repeat solve_length.
          -- rewrite numstreams_length_typeof...
        * rewrite app_nil_r.
          specialize (map_bind2_normalize_exp_numstreams _ _ _ _ _ _ H4) as Hnumstreams.
          eapply map_bind2_normalize_exp_typeof in H4; [| rewrite Forall_forall in *; intros; auto].
          rewrite <- H5 in Hin. rewrite <- H4 in Hin.
          repeat simpl_nth.
          unfold typesof. rewrite flat_map_concat_map.
          eapply concat_length_map_nth; solve_forall.
          -- repeat solve_length.
          -- rewrite numstreams_length_typeof...
        * repeat solve_incl.
      + specialize (idents_for_anns_incl _ _ _ _ H10) as Hincl.
        apply idents_for_anns_wt with (G:=G) (vars:=vars) in H10.
        * solve_forall. unfold st_tys. repeat solve_incl.
        * rewrite Forall_forall; intros.
          destruct x2. repeat simpl_In. inv H9...
    - (* app *)
      repeat inv_bind.
      specialize (idents_for_anns_incl _ _ _ _ H6) as Hincl.
      apply idents_for_anns_wt with (G:=G) (vars:=vars) in H6.
      + solve_forall. unfold st_tys. repeat solve_incl.
      + rewrite Forall_forall in *; intros.
        destruct x as [? [? ?]]. specialize (H4 _ H7); simpl in H4; eauto.
    - (* app (reset) *)
      repeat inv_bind.
      specialize (idents_for_anns_incl _ _ _ _ H8) as Hincl.
      apply idents_for_anns_wt with (G:=G) (vars:=vars) in H8.
      + solve_forall. unfold st_tys. repeat solve_incl.
      + rewrite Forall_forall in *; intros.
        destruct x as [? [? ?]]. specialize (H4 _ H10); simpl in H4; eauto.
  Qed.

  Corollary map_bind2_normalize_exp_wt_exp : forall G vars is_control es es' eqs' st st',
      Forall (wt_exp G vars) es ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      Forall (wt_exp G (vars++(st_tys st'))) (concat es').
  Proof.
    intros G vars is_control es es' eqs' st st' Hwt Hmap.
    eapply map_bind2_wt_exp in Hmap; solve_forall; eauto.
    eapply normalize_exp_wt_exp in H0; eauto.
    solve_forall. repeat solve_incl.
  Qed.

  Corollary normalize_exps_wt_exp : forall G vars es es' eqs' st st',
      Forall (wt_exp G vars) es ->
      normalize_exps es st = (es', eqs', st') ->
      Forall (wt_exp G (vars++(st_tys st'))) es'.
  Proof.
    intros G vars es es' eqs' st st' Hwt Hmap.
    unfold normalize_exps in Hmap; repeat inv_bind.
    eapply map_bind2_normalize_exp_wt_exp in H; eauto.
  Qed.

  Fact normalize_rhs_wt_exp : forall G vars e keep_fby es' eqs' st st',
      wt_exp G vars e ->
      normalize_rhs keep_fby e st = (es', eqs', st') ->
      Forall (wt_exp G (vars++(st_tys st'))) es'.
  Proof with eauto.
    intros G vars e keep_fby es' eqs' st st' Hwt Hnorm.
    destruct e; unfold normalize_rhs in Hnorm;
      try (solve [eapply normalize_exp_wt_exp in Hnorm; eauto]).
    - (* fby *)
      destruct keep_fby.
      + inv Hwt. repeat inv_bind.
        eapply normalize_fby_wt_exp in H1; eauto.
        * eapply normalize_exps_wt_exp in H; eauto.
          solve_forall.
          eapply normalize_exps_st_follows in H0.
          eapply normalize_fby_st_follows in H1.
          repeat solve_incl.
        * eapply normalize_exps_wt_exp in H0; eauto.
        * specialize (normalize_exps_length _ _ _ _ _ _ _ H2 H) as Hlength.
          specialize (normalize_exps_numstreams _ _ _ _ _ H) as Hnumstreams.
          unfold normalize_exps in H; repeat inv_bind.
          eapply map_bind2_normalize_exp_typeof' in H; eauto.
          assert (Forall2 (fun tys tys' => tys = tys') (map typesof x5) (map typeof l)).
          { specialize (Forall2_map_1 (fun tys e => tys = typeof e) typesof x5 l) as [_ Hfm].
            specialize (Forall2_map_2 (fun tys tys' => tys = tys') typeof (map typesof x5) l) as [_ Hfm2].
            auto. } rewrite Forall2_eq in H7.
          repeat rewrite_Forall_forall.
          -- solve_length.
          -- rewrite (concat_length_map_nth _ _ _ _ (fst b))...
             ++ unfold typesof in *. rewrite flat_map_concat_map in H5. rewrite <- H7 in H5.
              rewrite <- (map_nth fst). rewrite <- H5.
             rewrite typeof_concat_typesof. reflexivity.
             ++ solve_forall. rewrite numstreams_length_typeof...
        * specialize (normalize_exps_length _ _ _ _ _ _ _ H3 H0) as Hlength.
          specialize (normalize_exps_numstreams _ _ _ _ _ H0) as Hnumstreams.
          unfold normalize_exps in H0; repeat inv_bind.
          eapply map_bind2_normalize_exp_typeof' in H0; eauto.
          assert (Forall2 (fun tys tys' => tys = tys') (map typesof x5) (map typeof l0)).
          { specialize (Forall2_map_1 (fun tys e => tys = typeof e) typesof x5 l0) as [_ Hfm].
            specialize (Forall2_map_2 (fun tys tys' => tys = tys') typeof (map typesof x5) l0) as [_ Hfm2].
            auto. } rewrite Forall2_eq in H7.
          repeat rewrite_Forall_forall.
          -- solve_length.
          -- rewrite (concat_length_map_nth _ _ _ _ (fst b))...
             ++ unfold typesof in *. rewrite flat_map_concat_map in H4. rewrite <- H7 in H4.
              rewrite <- (map_nth fst). rewrite <- H4.
             rewrite typeof_concat_typesof. reflexivity.
             ++ solve_forall. rewrite numstreams_length_typeof...
        * rewrite Forall_map in H6. solve_forall. destruct a...
      + eapply normalize_exp_wt_exp in Hnorm; eauto.
    - (* app *)
      inv Hwt; repeat inv_bind; repeat econstructor; eauto.
      1,4: eapply normalize_exps_wt_exp...
      2,4:solve_forall; repeat solve_incl.
      + eapply normalize_exps_typesof in H... congruence.
      + eapply normalize_exps_typesof in H0... congruence.
      + eapply normalize_exp_wt_exp in H...
        eapply hd_default_wt_exp in H.
        eapply normalize_reset_wt_exp in H1...
        apply normalize_exps_st_follows in H0.
        repeat solve_incl.
      + specialize (normalize_exp_numstreams _ _ _ _ _ _ H) as Hlength.
        eapply normalize_exp_typeof in H...
        eapply normalize_reset_typeof_bool in H1...
        rewrite H9 in H.
        destruct x4; simpl in *; try congruence.
        inv Hlength. rewrite <- numstreams_length_typeof in H11.
        destruct (typeof e); simpl in *; try congruence.
        destruct l1; simpl in *; try congruence.
  Qed.

  Corollary normalize_rhss_wt_exp : forall G vars es keep_fby es' eqs' st st',
      Forall (wt_exp G vars) es ->
      normalize_rhss keep_fby es st = (es', eqs', st') ->
      Forall (wt_exp G (vars++(st_tys st'))) es'.
  Proof with eauto.
    intros G vars es keep_fby es' eqs' st st' Hwt Hnorm.
    unfold normalize_rhss in Hnorm; repeat inv_bind.
    eapply map_bind2_wt_exp in H...
    solve_forall.
    eapply normalize_rhs_wt_exp in H1...
    solve_forall. repeat solve_incl.
  Qed.

  Fact map_bind2_wt_eq {A A1 B} :
    forall G vars (k : A -> Fresh (A1 * list equation) B) a a1s eqs' st st',
      map_bind2 k a st = (a1s, eqs', st') ->
      (forall st st' a es a2s, k a st = (es, a2s, st') -> fresh_st_follows st st') ->
      Forall (fun a => forall a1 eqs' st0 st0',
                  k a st0 = (a1, eqs', st0') ->
                  fresh_st_follows st st0 ->
                  fresh_st_follows st0' st' ->
                  Forall (wt_equation G vars) eqs') a ->
      Forall (wt_equation G vars) (concat eqs').
  Proof.
   intros G vars k a.
    induction a; intros es' a2s st st' Hmap Hfollows Hforall;
      simpl in Hmap; repeat inv_bind.
    - constructor.
    - apply Forall_app. split; eauto.
      + rewrite Forall_forall in Hforall.
        eapply Hforall; eauto.
        * constructor. reflexivity.
        * reflexivity.
        * eapply map_bind2_st_follows in H0; eauto.
          rewrite Forall_forall; intros; eauto.
      + eapply IHa; eauto.
        rewrite Forall_forall in *; intros.
        eapply Hforall; eauto. apply in_cons; auto.
        etransitivity; eauto.
  Qed.

  Fact add_whens_typeof : forall e ty cl,
      typeof e = [ty] ->
      typeof (add_whens e ty cl) = [ty].
  Proof.
    induction cl; intro Hty; simpl; auto.
  Qed.

  Fact add_whens_wt_exp : forall G vars e ty cl e',
      wt_exp G vars e ->
      typeof e = [ty] ->
      wt_clock vars cl ->
      add_whens e ty cl = e' ->
      wt_exp G vars e'.
  Proof.
    induction cl; intros e' Hwt Hty Hclock Hwhens; simpl in Hwhens; inv Hclock; subst.
    - assumption.
    - repeat constructor; simpl; auto.
      rewrite app_nil_r.
      rewrite add_whens_typeof; auto.
  Qed.

  Fact normalize_fby_wt_eq : forall G vars e0s es anns es' eqs' st st',
      Forall (wt_exp G (vars++(st_tys st))) e0s ->
      Forall (wt_exp G (vars++(st_tys st))) es ->
      Forall2 (fun e0 a => typeof e0 = [fst a]) e0s anns ->
      Forall2 (fun e a => typeof e = [fst a]) es anns ->
      Forall (fun '(_, cl) => wt_nclock vars cl) anns ->
      normalize_fby e0s es anns st = (es', eqs', st') ->
      Forall (wt_equation G (vars++(st_tys st'))) eqs'.
  Proof with eauto.
    intros G vars e0s es anns es' eqs' st st' Hwt1 Hwt2 Hty1 Hty2 Hclock Hnorm.
    unfold normalize_fby in Hnorm. repeat inv_bind.
    eapply map_bind2_wt_eq in H; eauto.
    - intros; destruct a as [[e0 e] a]...
    - repeat rewrite_Forall_forall. destruct x as [[e0 e] [ty cl]].
      specialize (fby_iteexp_spec e0 e ty cl) as [[c [? Hspec]]|Hspec]; subst;
        rewrite Hspec in H5; clear Hspec;
          repeat inv_bind; inv H8.
      + repeat constructor; simpl.
        * repeat simpl_In.
          apply Hwt2 in H8. repeat solve_incl.
        * rewrite app_nil_r.
          repeat simpl_nth. repeat simpl_length.
          specialize (H1 _ _ _ _ _ H4 H13 H12); simpl in H1. congruence.
        * f_equal. apply Op.type_init_type.
        * repeat simpl_In.
          apply Hclock in H4. repeat solve_incl.
        * destruct x3; simpl in H9; inv H9.
          apply st_follows_tys_incl in H7.
          apply in_or_app; right.
          apply H7. simpl...
      + destruct st0; simpl in H5.
        destruct (find _ _) eqn:Hfind; inv H5; [destruct p; inv H11|]; inv H10;
          repeat constructor; simpl; try rewrite app_nil_r.
        1,2: eapply add_whens_wt_exp; eauto; simpl.
        5,6: rewrite add_whens_typeof; eauto; simpl.
        1,6: f_equal; apply Op.type_true_const.
        2,4: f_equal; apply Op.type_false_const.
        1,2: repeat simpl_In; apply Hclock in H4; destruct cl; inv H4; simpl in *; repeat solve_incl.
        * simpl_In. apply Hclock in H4. repeat solve_incl.
        * apply fresh_ident_st_follows in H9. apply st_follows_tys_incl in H9.
          apply st_follows_tys_incl in H7.
          apply in_or_app. right. apply H7. apply H9.
          simpl...
        * inv H5.
  Qed.

  Fact normalize_reset_wt_eq : forall G vars e e' eqs' st st',
      wt_exp G (vars++(st_tys st)) e ->
      typeof e = [Op.bool_type] ->
      normalize_reset e st = (e', eqs', st') ->
      Forall (wt_equation G (vars++(st_tys st'))) eqs'.
  Proof.
    intros G vars e e' eqs' st st' Hwt Hty Hnorm.
    specialize (normalize_reset_spec e) as [[? [? [? Hspec]]]|Hspec]; subst;
      rewrite Hspec in Hnorm; clear Hspec; repeat inv_bind.
    - constructor.
    - destruct (hd _) eqn:Hann; simpl in *. repeat inv_bind.
      repeat constructor; simpl.
      + repeat solve_incl.
      + rewrite app_nil_r. rewrite Hty.
        repeat constructor.
        unfold fresh_ident in H.
        destruct st. inv H.
        apply in_or_app; simpl. right. left.
        f_equal.
        destruct (annot e) eqn:Hannot; simpl in Hann; inv Hann. reflexivity.
        destruct e; simpl in *; inv Hannot; inv Hty; auto;
          try destruct l2; try destruct l3; simpl in *; subst; inv H0; reflexivity.
  Qed.

  Fact normalize_exp_wt_eq : forall G vars e is_control es' eqs' st st',
      wt_exp G vars e ->
      normalize_exp is_control e st = (es', eqs', st') ->
      Forall (wt_equation G (vars++(st_tys st'))) eqs'.
  Proof with eauto.
    induction e using exp_ind2; intros is_control es' eqs' st st' Hwt Hnorm;
      simpl in Hnorm; repeat inv_bind.
    - (* const *) constructor.
    - (* var *) constructor.
    - (* unop *) inv Hwt...
    - (* binop *)
      inv Hwt.
      rewrite Forall_app.
      split; eauto.
      eapply IHe1 in H; eauto.
      solve_forall. eapply wt_equation_incl; [| eauto].
      eapply normalize_exp_st_follows in H0.
      repeat solve_incl.
    - (* fby *)
      inv Hwt.
      repeat rewrite Forall_app.
      repeat split; eauto.
      + solve_forall. destruct x.
        repeat constructor.
        * repeat simpl_In. inv H5. repeat constructor.
          eapply normalize_fby_wt_exp with (G:=G) (vars:=vars) in H3...
          -- rewrite Forall_forall in H3...
             apply H3 in H6. repeat solve_incl.
          -- eapply map_bind2_normalize_exp_wt_exp in H1...
             solve_forall. repeat solve_incl.
          -- eapply map_bind2_normalize_exp_wt_exp in H2...
          -- admit.
          -- admit.
          -- rewrite Forall_forall in *; intros [ty cl] Hin.
             apply H12. repeat simpl_In. exists (ty, cl)...
        * specialize (normalize_fby_numstreams _ _ _ _ _ _ _ H3) as Hnumstreams. rewrite Forall_forall in Hnumstreams.
          repeat simpl_In. inv H5. simpl. rewrite app_nil_r.
          specialize (Hnumstreams _ H6). rewrite <- numstreams_length_typeof in Hnumstreams.
          remember (typeof e) as ts.
          singleton_length. repeat constructor.
          apply idents_for_anns_values in H4.
          apply normalize_fby_typeof in H3; admit. (* penible *)
      + eapply map_bind2_wt_eq in H1; eauto.
        rewrite Forall_forall in *; intros.
        specialize (H _ H5 _ _ _ _ _ (H8 _ H5) H6).
        solve_forall. repeat solve_incl.
      + eapply map_bind2_wt_eq in H2; eauto.
        rewrite Forall_forall in *; intros.
        specialize (H0 _ H5 _ _ _ _ _ (H9 _ H5) H6).
        solve_forall. repeat solve_incl.
      + eapply normalize_fby_wt_eq with (G:=G) (vars:=vars) in H3...
        * solve_forall. repeat solve_incl.
        * eapply map_bind2_normalize_exp_wt_exp in H1...
          solve_forall. repeat solve_incl.
        * eapply map_bind2_normalize_exp_wt_exp in H2...
        * admit.
        * admit.
        * rewrite Forall_forall in *; intros [ty cl] Hin.
          apply H12. repeat simpl_In. exists (ty, cl)...
    - (* when *)
      inv Hwt; repeat inv_bind.
      eapply map_bind2_wt_eq; eauto.
      rewrite Forall_forall in *; intros.
      eapply H in H2; eauto.
      solve_forall.
      eapply wt_equation_incl; [| eauto]. repeat solve_incl.
    - (* merge *)
      inv Hwt.
      destruct is_control; repeat inv_bind.
      + (* control *)
        apply Forall_app; split.
        * eapply map_bind2_wt_eq in H1; eauto.
          rewrite Forall_forall in *; intros.
          eapply H in H4; eauto.
          solve_forall. repeat solve_incl.
        * eapply map_bind2_wt_eq in H2; eauto.
          rewrite Forall_forall in *; intros.
          eapply H0 in H4; eauto.
          solve_forall. repeat solve_incl.
      + (* exp *)
        repeat rewrite Forall_app; repeat split.
        * solve_forall.
          destruct x0 as [xs es].
          repeat constructor; [repeat simpl_In |]; repeat constructor; simpl.
          -- eapply map_bind2_normalize_exp_wt_exp in H1; eauto.
             rewrite Forall_forall in H1. eapply H1 in H12.
             eapply map_bind2_st_follows in H2; solve_forall.
             repeat solve_incl.
          -- eapply map_bind2_normalize_exp_wt_exp in H2; eauto.
             rewrite Forall_forall in H2. eapply H2 in H4.
             eapply idents_for_anns_st_follows in H3.
             repeat solve_incl.
          -- apply in_or_app...
          -- rewrite app_nil_r. admit.
          -- rewrite app_nil_r. admit.
          -- repeat solve_incl.
          -- admit. (* penible *)
        * eapply map_bind2_wt_eq in H1; eauto.
          rewrite Forall_forall in *; intros.
          eapply H in H4; [| eauto | eauto].
          solve_forall. repeat solve_incl.
        * eapply map_bind2_wt_eq in H2; eauto.
          rewrite Forall_forall in *; intros.
          eapply H0 in H4; [| eauto | eauto].
          solve_forall. repeat solve_incl.
    - (* ite *) admit.
    - (* app *)
      inv Hwt; repeat inv_bind; repeat econstructor; simpl; eauto.
      1,6: (eapply map_bind2_wt_exp with (vars0:=(vars++(st_tys st'))) in H2; eauto;
            solve_forall;
            try eapply normalize_exp_wt_exp in H4; try eapply normalize_exp_wt_exp in H6; eauto;
            solve_forall; repeat solve_incl).
      1,5: eapply map_bind2_normalize_exp_typeof in H2; eauto; congruence.
      1,4: (solve_forall; repeat solve_incl).
      1,5: rewrite app_nil_r.
      + clear H0 H8 H10 H11 H12.
        specialize (idents_for_anns_incl _ _ _ _ H3) as Hincl.
        apply idents_for_anns_values in H3.
        repeat rewrite_Forall_forall; repeat rewrite map_length in *...
        apply in_or_app. right.
        rewrite <- H0 in H3.
        specialize (H1 (b, (Cbase, None)) (a0, (b, (Cbase, None))) _ _ _ H3 eq_refl eq_refl).
        destruct (nth _ _ _) eqn:Hnth; subst.
        erewrite map_nth'. 2: congruence.
        rewrite H0 in H3. eapply nth_In in H3.
        rewrite Hnth in *; simpl.
        unfold st_tys. eapply Hincl in H3...
        unfold idty. repeat simpl_In.
        eexists; split; eauto; simpl. f_equal.
        replace b with (fst (b, (Cbase, @None ident))) by reflexivity.
        rewrite map_nth; reflexivity.
      + clear H H0 H8 H10 H11 H12.
        specialize (idents_for_anns_incl _ _ _ _ H3) as Hincl.
        apply idents_for_anns_values in H3.
        repeat rewrite_Forall_forall; repeat rewrite map_length in *...
        apply in_or_app. right.
        rewrite <- H in H3.
        specialize (H0 (b, (Cbase, None)) (a0, (b, (Cbase, None))) _ _ _ H3 eq_refl eq_refl).
        destruct (nth _ _ _) eqn:Hnth; subst.
        erewrite map_nth'. 2: congruence.
        rewrite H in H3. eapply nth_In in H3.
        rewrite Hnth in *; simpl.
        unfold st_tys. eapply Hincl in H3...
        unfold idty. repeat simpl_In.
        eexists; split; eauto; simpl. f_equal.
        replace b with (fst (b, (Cbase, @None ident))) by reflexivity.
        rewrite map_nth; reflexivity.
      + eapply map_bind2_wt_eq in H2; eauto.
        rewrite Forall_forall in *; intros.
        eapply H0 in H4; eauto.
        solve_forall. repeat solve_incl.
      + eapply normalize_exp_wt_exp in H1...
        eapply hd_default_wt_exp in H1...
        eapply normalize_reset_wt_exp in H4...
        eapply map_bind2_st_follows in H2; solve_forall.
        repeat solve_incl.
      + specialize (normalize_exp_numstreams _ _ _ _ _ _ H1) as Hlength.
        eapply normalize_exp_typeof in H1...
        eapply normalize_reset_typeof_bool in H4...
        rewrite H14 in H1.
        destruct x2; simpl in *; try congruence.
        inv Hlength. rewrite <- numstreams_length_typeof in H7.
        destruct (typeof e); simpl in *; try congruence.
        destruct l; simpl in *; try congruence.
      + repeat rewrite Forall_app. repeat split.
        * eapply H in H1...
          apply normalize_reset_st_follows in H4.
          apply map_bind2_st_follows in H2; solve_forall.
          apply idents_for_anns_st_follows in H3.
          solve_forall. repeat solve_incl.
        * specialize (normalize_exp_length _ _ _ _ _ _ _ _ H13 H1) as Hlength.
          specialize (normalize_exp_typeof _ _ _ _ _ _ _ _ H13 H1) as Htypeof.
          rewrite H14 in Htypeof.
          eapply normalize_exp_wt_exp in H1... eapply hd_default_wt_exp in H1...
          eapply normalize_reset_wt_eq in H4...
          -- solve_forall. repeat solve_incl.
          -- rewrite <- numstreams_length_typeof in Hlength. rewrite H14 in Hlength.
             destruct x2; simpl in *; try congruence.
             destruct x2; simpl in *; try congruence.
             rewrite app_nil_r in Htypeof...
        * eapply map_bind2_wt_eq in H2; eauto.
          rewrite Forall_forall in *; intros.
          eapply H0 in H6...
          solve_forall. repeat solve_incl.
  Admitted.

  Fact normalize_rhs_wt_eq : forall G vars e keep_fby es' eqs' st st',
      wt_exp G vars e ->
      normalize_rhs keep_fby e st = (es', eqs', st') ->
      Forall (wt_equation G (vars++(st_tys st'))) eqs'.
  Proof with eauto.
    intros G vars e keep_fby es' eqs' st st' Hwt Hnorm.
    destruct e; unfold normalize_rhs in Hnorm;
      try eapply normalize_exp_wt_eq in Hnorm; eauto;
        [destruct keep_fby|].
    - (* fby *) admit.
    - eapply normalize_exp_wt_eq...
    - (* app *) admit.
  Admitted.

  Corollary normalize_rhss_wt_eq : forall G vars es keep_fby es' eqs' st st',
      Forall (wt_exp G vars) es ->
      normalize_rhss keep_fby es st = (es', eqs', st') ->
      Forall (wt_equation G (vars++(st_tys st'))) eqs'.
  Proof with eauto.
    intros G vars es keep_fby es' eqs' st st' Hwt Hnorm.
    unfold normalize_rhss in Hnorm; repeat inv_bind.
    eapply map_bind2_wt_eq in H...
    solve_forall. eapply normalize_rhs_wt_eq in H1...
    solve_forall. repeat solve_incl.
  Qed.

  Fact normalize_equation_wt_eq : forall G vars eq to_cut eqs' st st',
      wt_equation G vars eq ->
      normalize_equation to_cut eq st = (eqs', st') ->
      Forall (wt_equation G (vars++(st_tys st'))) eqs'.
  Proof with eauto.
    intros G vars eq to_cut eqs' st st' Hwt Hnorm.
    destruct eq as [xs es]; simpl in Hnorm.
    repeat inv_bind. destruct Hwt.
    apply Forall_app. split.
    - specialize (normalize_rhss_typeof _ _ _ _ _ _ _ _ H0 H) as Htypeof.
      eapply normalize_rhss_wt_exp in H...
      rewrite <- Htypeof in H1.
      clear Htypeof. revert xs H1.
      induction x; intros xs H1; constructor; simpl in H1.
      + inv H. repeat constructor...
        simpl. rewrite app_nil_r.
        repeat rewrite_Forall_forall.
        * admit.
        * rewrite firstn_length in H2.
          rewrite PeanoNat.Nat.min_glb_lt_iff in H2; destruct H2 as [_ H2].
          admit.
      + inv H. apply IHx...
        admit.
    - eapply normalize_rhss_wt_eq in H...
  Admitted.

  Corollary normalize_equations_wt_eq : forall G vars eqs to_cut eqs' st st',
      Forall (wt_equation G vars) eqs ->
      normalize_equations to_cut eqs st = (eqs', st') ->
      Forall (wt_equation G (vars++(st_tys st'))) eqs'.
  Proof with eauto.
    induction eqs; intros to_cut eqs' st st' Hwt Hnorm;
      simpl in Hnorm; repeat inv_bind.
    - constructor.
    - inv Hwt. apply Forall_app. split...
      eapply normalize_equation_wt_eq in H...
      solve_forall. repeat solve_incl.
  Qed.

  Lemma normalize_node_wt : forall n G Hwt to_cut n',
      normalize_node to_cut n (ex_intro _ G Hwt) = n' ->
      wt_node G n'.
  Proof.
    intros n G Hwt to_cut n' Hnorm. simpl in Hwt.
    unfold normalize_node in Hnorm. subst.
    destruct Hwt as [Hclin [Hclout [Hclvars Heq]]].
    repeat constructor; simpl; auto.
    - admit. (* wt_clocks hum... *)
    - remember (normalize_equations _ (n_eqs n) (first_unused_ident n, [])) as res.
      destruct res as [eqs' st']; simpl.
      symmetry in Heqres.
      eapply normalize_equations_wt_eq in Heqres; eauto.
      solve_forall. repeat solve_incl. clear Heqres H.
      unfold st_tys, idty in *. apply incl_app.
      + apply incl_map. apply incl_app; [solve_incl|].
        apply incl_app; [| repeat solve_incl].
        apply incl_appr. apply incl_appl; solve_incl.
      + repeat rewrite map_map; simpl.
        repeat rewrite map_app; simpl.
        apply incl_appr. apply incl_appl. apply incl_appr.
        repeat rewrite map_map; simpl. reflexivity.
  Admitted.
End CORRECTNESS.

Module CorrectnessFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Str : COINDSTREAMS Op OpAux)
       (Syn : LSYNTAX Ids Op)
       (Typ : LTYPING Ids Op Syn)
       (Lord : LORDERED Ids Op Syn)
       (Sem : LSEMANTICS Ids Op OpAux Syn Lord Str)
       (Norm : NORMALIZATION Ids Op OpAux Syn Typ)
       <: CORRECTNESS Ids Op OpAux Str Syn Typ Lord Sem Norm.
  Include CORRECTNESS Ids Op OpAux Str Syn Typ Lord Sem Norm.
End CorrectnessFun.
