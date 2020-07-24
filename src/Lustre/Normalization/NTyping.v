Require Import Omega.
From Velus Require Import Common Ident.
From Velus Require Import Operators Environment.
From Coq Require Import List. Import List.ListNotations. Open Scope list_scope.
From Velus Require Import Lustre.LSyntax Lustre.LCausality Lustre.LTyping.
From Velus Require Import Lustre.Normalization.Fresh Lustre.Normalization.Normalization.

(** * Preservation of Typing through Normalization *)

Local Set Warnings "-masking-absolute-name".
Module Type NTYPING
       (Import Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Import Syn : LSYNTAX Ids Op)
       (Caus : LCAUSALITY Ids Op Syn)
       (Import Typ : LTYPING Ids Op Syn)
       (Import Norm : NORMALIZATION Ids Op OpAux Syn Caus).
  Import Fresh Facts Tactics.

  (** ** Preservation of typeof *)

  Fact normalize_exp_typeof : forall G vars e is_control es' eqs' st st',
      wt_exp G vars e ->
      normalize_exp is_control e st = (es', eqs', st')  ->
      typesof es' = typeof e.
  Proof with eauto.
    intros G vars e is_control es' eqs' st st' Hwt Hnorm.
    eapply normalize_exp_annot in Hnorm...
    rewrite typesof_annots, Hnorm, <- typeof_annot...
  Qed.

  Hint Resolve nth_In.
  Corollary map_bind2_normalize_exp_typesof' :
    forall G vars is_control es es' eqs' st st',
      Forall (wt_exp G vars) es ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      Forall2 (fun es' e => typesof es' = typeof e) es' es.
  Proof with eauto.
    intros G vars is_control es es' eqs' st st' Hwt Hmap.
    eapply map_bind2_normalize_exp_annots' in Hmap...
    clear Hwt.
    induction Hmap; constructor; eauto.
    rewrite typesof_annots, H, <- typeof_annot...
  Qed.

  Corollary map_bind2_normalize_exp_typesof'' : forall G vars is_control es es' eqs' st st',
      Forall (wt_exp G vars) es ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      Forall2 (fun e ty => typeof e = [ty]) (concat es') (typesof es).
  Proof.
    intros * Hwl Hmap.
    eapply map_bind2_normalize_exp_annots'' in Hmap; eauto.
    rewrite typesof_annots, Forall2_map_2.
    eapply Forall2_impl_In; eauto. intros; simpl in *.
    rewrite typeof_annot, H1; auto.
  Qed.

  Corollary map_bind2_normalize_exp_typesof :
    forall G vars is_control es es' eqs' st st',
      Forall (wt_exp G vars) es ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      typesof (concat es') = typesof es.
  Proof.
    intros G vars is_control es es' eqs' st st' Hwt Hmap.
    eapply map_bind2_normalize_exp_annots in Hmap; eauto.
    rewrite typesof_annots, Hmap, <- typesof_annots; eauto.
  Qed.
  Hint Resolve map_bind2_normalize_exp_typesof.

  Corollary normalize_exps_typesof : forall G vars es es' eqs' st st',
      Forall (wt_exp G vars) es ->
      normalize_exps es st = (es', eqs', st') ->
      typesof es' = typesof es.
  Proof.
    intros G vars es es' eqs' st st' Hwt Hnorm.
    unfold normalize_exps in Hnorm; repeat inv_bind.
    eapply map_bind2_normalize_exp_typesof in H; eauto.
  Qed.

  Fact fby_iteexp_typeof : forall e0 e ann e' eqs' st st',
      fby_iteexp e0 e ann st = (e', eqs', st') ->
      typeof e' = [fst ann].
  Proof.
    intros e0 e [ty cl] e' eqs' st st' Hfby.
    unfold fby_iteexp in Hfby.
    destruct (is_constant e0); repeat inv_bind; try reflexivity.
  Qed.

  Fact normalize_rhs_typeof : forall G vars e es' eqs' st st',
      wt_exp G vars e ->
      normalize_rhs e st = (es', eqs', st') ->
      typesof es' = typeof e.
  Proof with eauto.
    intros * Hwt Hnorm.
    eapply normalize_rhs_annot in Hnorm...
    rewrite typesof_annots, Hnorm, <- typeof_annot...
  Qed.

  Corollary normalize_rhss_typesof : forall G vars es es' eqs' st st',
      Forall (wt_exp G vars) es ->
      normalize_rhss es st = (es', eqs', st') ->
      typesof es' = typesof es.
  Proof with eauto.
    intros * Hwt Hnorm.
    eapply normalize_rhss_annots in Hnorm...
    rewrite typesof_annots, Hnorm, <- typesof_annots...
  Qed.

  (** ** A few additional tactics *)

  Definition st_tys (st : fresh_st (Op.type * clock)) := idty (st_anns st).
  Definition st_tys' (st : fresh_st ((Op.type * clock) * bool)) := idty (idty (st_anns st)).

  Fact st_anns_tys_In : forall st id ty,
      In (id, ty) (st_tys st) <-> (exists cl, In (id, (ty, cl)) (st_anns st)).
  Proof.
    intros st id ty.
    split; intros; unfold st_tys, idty in *.
    - repeat simpl_In; simpl in *.
      inv H.
      exists c. assumption.
    - repeat simpl_In; simpl in *.
      destruct H as [cl Hin].
      exists (id, (ty, cl)); simpl; split; auto.
  Qed.

  Fact st_follows_tys_incl : forall st st',
      st_follows st st' ->
      incl (st_tys st) (st_tys st').
  Proof.
    intros st st' Hfollows.
    apply st_follows_incl in Hfollows.
    unfold st_tys, idty.
    repeat apply incl_map.
    assumption.
  Qed.

  Fact idents_for_anns_incl_ty : forall anns ids st st',
    idents_for_anns anns st = (ids, st') ->
    incl (idty ids) (st_tys st').
  Proof.
    intros anns ids st st' Hids.
    apply idents_for_anns_incl in Hids.
    intros [id ty] Hin.
    unfold st_tys, idty in *.
    repeat simpl_In. inv H.
    exists (id, (ty, (fst n))); split; auto.
    apply Hids. repeat simpl_In.
    exists (id, (ty, n)). destruct n; auto.
  Qed.

  Fact idents_for_anns'_incl_ty : forall anns ids st st',
    idents_for_anns' anns st = (ids, st') ->
    incl (idty ids) (st_tys st').
  Proof.
    intros anns ids st st' Hids.
    apply idents_for_anns'_incl in Hids.
    intros [id ty] Hin.
    unfold st_tys, idty in *.
    repeat simpl_In. inv H.
    exists (id, (ty, c)); split; auto.
    apply Hids. repeat simpl_In.
    exists (id, (ty, (c, o))); auto.
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
    | |- incl ?l1 (?a::?l2) =>
      eapply incl_tl
    | |- incl (st_anns ?st1) (st_anns _) =>
      eapply st_follows_incl; repeat solve_st_follows
    | |- incl (st_tys ?st1) (st_tys _) =>
      eapply st_follows_tys_incl; repeat solve_st_follows
    | |- incl (st_tys' ?st1) (st_tys' _) =>
      unfold st_tys', idty; do 2 eapply incl_map; eapply st_follows_incl; repeat solve_st_follows
    | H : incl ?l1 ?l2 |- incl (idty ?l1) (idty ?l2) =>
      eapply incl_map; eauto
    end; auto.

  Hint Resolve in_combine_l in_combine_r.
  Hint Resolve incl_tl incl_appl incl_appr incl_app incl_refl.

  (** ** Preservation of wt through the first pass *)

  Fact idents_for_anns_wt : forall G vars anns ids st st',
      idents_for_anns anns st = (ids, st') ->
      Forall (fun '(ty, cl) => wt_nclock (vars++st_tys st) cl) anns ->
      Forall (wt_exp G (vars++st_tys st')) (map (fun '(x, ann) => Evar x ann) ids).
  Proof.
    induction anns; intros ids st st' Hidents Hf;
      repeat inv_bind.
    - constructor.
    - inv Hf. destruct a as [ty [cl ?]]. repeat inv_bind.
      assert (Forall (fun '(_, cl) => wt_nclock (vars ++ st_tys x0) cl) anns) as Hanns'.
      { solve_forall. repeat solve_incl. }
      rewrite Forall_map.
      eapply IHanns in Hanns'; eauto.
      econstructor.
      + repeat constructor; simpl.
        * apply in_or_app; right.
          apply fresh_ident_In in H.
          rewrite st_anns_tys_In. exists cl.
          eapply idents_for_anns_st_follows, st_follows_incl in H0; eauto.
        * inv H1. repeat solve_incl.
      + simpl_forall.
  Qed.

  Fact idents_for_anns'_wt : forall G vars anns ids st st',
      idents_for_anns' anns st = (ids, st') ->
      Forall (fun '(ty, cl) => wt_nclock (vars++(idty ids)++st_tys st) cl) anns ->
      Forall (wt_exp G (vars++(idty ids)++st_tys st')) (map (fun '(x, ann) => Evar x ann) ids).
  Proof.
    induction anns; intros ids st st' Hidents Hf;
      repeat inv_bind.
    - constructor.
    - inv Hf. destruct a as [ty [cl ?]]. repeat inv_bind.
      rewrite Forall_map.
      destruct o; repeat inv_bind; econstructor; eauto.
      + repeat constructor; simpl.
        * apply in_or_app. right. constructor; auto.
        * inv H1. destruct x; simpl in *. solve_incl.
          eapply incl_appr', incl_tl', incl_appr'. solve_incl.
      + destruct x. eapply IHanns in H0.
        * rewrite Forall_map in H0.
          solve_forall. repeat solve_incl.
        * solve_forall. solve_incl.
          rewrite Permutation.Permutation_middle.
          eapply incl_appr', incl_appr', incl_cons; repeat solve_incl.
          eapply reuse_ident_In in H. unfold st_tys, idty, idty.
          rewrite in_map_iff. exists (i, (ty, cl)); split; auto.
      + repeat constructor; simpl.
        * apply in_or_app. right. constructor; auto.
        * inv H1. solve_incl; simpl.
          eapply incl_appr', incl_tl', incl_appr'. solve_incl.
      + eapply IHanns in H0.
        * rewrite Forall_map in H0.
          solve_forall. repeat solve_incl.
        * solve_forall. solve_incl.
          rewrite Permutation.Permutation_middle.
          eapply incl_appr', incl_appr', incl_cons; try solve_incl.
          eapply fresh_ident_In in H. unfold st_tys, idty, idty.
          rewrite in_map_iff. exists (x, (ty, cl)); split; auto.
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
      (forall st st' a es a2s, k a st = (es, a2s, st') -> st_follows st st') ->
      Forall (fun a => forall e' a2s st0 st0',
                  k a st0 = (e', a2s, st0') ->
                  st_follows st st0 ->
                  st_follows st0' st' ->
                  wt_exp G vars e') a ->
      Forall (wt_exp G vars) es'.
  Proof.
    intros G vars k a.
    induction a; intros es' a2s st st' Hmap Hfollows Hforall;
      repeat inv_bind.
    - constructor.
    - constructor.
      + rewrite Forall_forall in Hforall.
        eapply Hforall. 2,3:eauto.
        * constructor. reflexivity.
        * reflexivity.
        * eapply map_bind2_st_follows in H0; eauto.
          rewrite Forall_forall; intros; eauto.
      + eapply IHa; eauto.
        rewrite Forall_forall in *; intros.
        eapply Hforall. 2,4:eauto.
        * apply in_cons; auto.
        * etransitivity; eauto.
  Qed.

  Hint Constructors wt_exp.

  Lemma idty_without_names : forall vars,
      idty (without_names' vars) = idty vars.
  Proof.
    intros vars.
    unfold idty, without_names'.
    rewrite map_map.
    eapply map_ext; intros [id [ty [cl n]]]; reflexivity.
  Qed.

  Definition idck' (vars : list (ident * ann)) : list (ident * clock) :=
    idck (without_names' vars).

  Fact map_bind2_wt_exp {A A2 B} :
    forall G vars (k : A -> Fresh (list exp * A2) B) a es' a2s st st',
      map_bind2 k a st = (es', a2s, st') ->
      (forall st st' a es a2s, k a st = (es, a2s, st') -> st_follows st st') ->
      Forall (fun a => forall es' a2s st0 st0',
                  k a st0 = (es', a2s, st0') ->
                  st_follows st st0 ->
                  st_follows st0' st' ->
                  Forall (wt_exp G vars) es') a ->
      Forall (wt_exp G vars) (concat es').
  Proof.
    intros G vars k a.
    induction a; intros es' a2s st st' Hmap Hfollows Hforall;
      repeat inv_bind.
    - constructor.
    - apply Forall_app. split; eauto.
      + rewrite Forall_forall in Hforall.
        eapply Hforall. 2:eauto.
        * constructor. reflexivity.
        * reflexivity.
        * eapply map_bind2_st_follows in H0; eauto.
          rewrite Forall_forall; intros; eauto.
      + eapply IHa; eauto.
        rewrite Forall_forall in *; intros.
        eapply Hforall. 2,4:eauto.
        * apply in_cons; auto.
        * etransitivity; eauto.
  Qed.

  Fact normalize_fby_wt_exp : forall G vars e0s es anns,
      Forall (wt_nclock vars) (map snd anns) ->
      Forall (wt_exp G vars) e0s ->
      Forall (wt_exp G vars) es ->
      Forall2 (fun e0 a => typeof e0 = [a]) e0s (map fst anns) ->
      Forall2 (fun e a => typeof e = [a]) es (map fst anns) ->
      Forall (wt_exp G vars) (normalize_fby e0s es anns).
  Proof.
    intros * Hwtc Hwt1 Hwt2 Hty1 Hty2.
    unfold normalize_fby.
    assert (length e0s = length anns) as Hlen1 by (eapply Forall2_length in Hty1; solve_length).
    assert (length es = length anns) as Hlen2 by (eapply Forall2_length in Hty2; solve_length).
    solve_forall.
    constructor; simpl; try rewrite app_nil_r; eauto.
  Qed.

  Fact normalize_when_wt_exp : forall G vars b ckid es tys ck,
      In (ckid, Op.bool_type) vars ->
      wt_nclock vars ck ->
      Forall (wt_exp G vars) es ->
      Forall2 (fun e ty => typeof e = [ty]) es tys ->
      Forall (wt_exp G vars) (normalize_when ckid b es tys ck).
  Proof.
    intros * HIn Hwtck Hwt Htys. unfold normalize_when.
    assert (length es = length tys) as Hlength by (eapply Forall2_length in Htys; eauto).
    rewrite Forall_map. apply Forall2_combine'.
    eapply Forall2_ignore2' with (ys:=tys) in Hwt; eauto.
    eapply Forall2_Forall2 in Hwt; eauto. clear Htys.
    eapply Forall2_impl_In; eauto. intros ? ? ? ? [? ?].
    repeat constructor; simpl; auto.
    rewrite app_nil_r; auto.
  Qed.

  Fact normalize_merge_wt_exp : forall G vars ckid ets efs tys ck,
      In (ckid, Op.bool_type) vars ->
      wt_nclock vars ck ->
      Forall (wt_exp G vars) ets ->
      Forall (wt_exp G vars) efs ->
      Forall2 (fun e ty => typeof e = [ty]) ets tys ->
      Forall2 (fun e ty => typeof e = [ty]) efs tys ->
      Forall (wt_exp G vars) (normalize_merge ckid ets efs tys ck).
  Proof with eauto.
    intros * HIn Hwtck Hwt1 Hwt2 Htys1 Htys2. unfold normalize_merge.
    assert (length ets = length tys) as Hlen1 by (eauto using Forall2_length).
    assert (length efs = length tys) as Hlen2 by (eauto using Forall2_length).
    solve_forall.
    repeat constructor; simpl; auto. 1,2:rewrite app_nil_r; auto.
  Qed.

  Fact normalize_ite_wt_exp : forall G vars e ets efs tys ck,
      wt_nclock vars ck ->
      wt_exp G vars e ->
      typeof e = [Op.bool_type] ->
      Forall (wt_exp G vars) ets ->
      Forall (wt_exp G vars) efs ->
      Forall2 (fun e ty => typeof e = [ty]) ets tys ->
      Forall2 (fun e ty => typeof e = [ty]) efs tys ->
      Forall (wt_exp G vars) (normalize_ite e ets efs tys ck).
  Proof with eauto.
    intros * Hwtck Hwt Htye Hwt1 Hwt2 Htys1 Htys2. unfold normalize_ite.
    assert (length ets = length tys) as Hlen1 by (eauto using Forall2_length).
    assert (length efs = length tys) as Hlen2 by (eauto using Forall2_length).
    solve_forall.
    repeat constructor; simpl; auto. 1,2:rewrite app_nil_r; auto.
  Qed.

  Lemma normalize_exp_wt_exp : forall G vars e is_control es' eqs' st st',
      wt_exp G (vars++st_tys st) e ->
      normalize_exp is_control e st = (es', eqs', st') ->
      Forall (wt_exp G (vars++st_tys st')) es'.
  Proof with eauto.
    induction e using exp_ind2; intros * Hwt Hnorm; inv Hwt; simpl in *.
    - (* const *)
      repeat inv_bind...
    - (* var *)
      repeat inv_bind.
      repeat constructor...
    - (* unop *)
      repeat inv_bind.
      assert (length x = numstreams e) as Hlen by eauto.
      rewrite <- length_typeof_numstreams, H3 in Hlen; simpl in Hlen.
      singleton_length.
      assert (Hnorm:=H); eapply IHe in H; eauto.
      repeat econstructor...
      + inv H; eauto.
      + eapply normalize_exp_typeof in Hnorm; simpl in Hnorm; eauto.
        rewrite app_nil_r, H3 in Hnorm...
      + repeat solve_incl.
    - (* binop *)
      repeat inv_bind.
      assert (length x = numstreams e1) as Hlen1 by eauto.
      rewrite <- length_typeof_numstreams, H5 in Hlen1; simpl in Hlen1.
      assert (length x2 = numstreams e2) as Hlen2 by eauto.
      rewrite <- length_typeof_numstreams, H6 in Hlen2; simpl in Hlen2. repeat singleton_length.
      assert (Hnorm1:=H); eapply IHe1 in H; eauto.
      assert (Hnorm2:=H0); eapply IHe2 in H0; eauto. 2:repeat solve_incl.
      repeat econstructor...
      + inv H. repeat solve_incl.
      + inv H0...
      + eapply normalize_exp_typeof in Hnorm1; simpl in Hnorm1; eauto.
        rewrite app_nil_r, H5 in Hnorm1...
      + eapply normalize_exp_typeof in Hnorm2; simpl in Hnorm2; eauto.
        rewrite app_nil_r, H6 in Hnorm2...
      + repeat solve_incl.
    - (* fby *)
      repeat inv_bind.
      eapply idents_for_anns_wt in H3...
      solve_forall. repeat solve_incl.
    - (* when *)
      repeat inv_bind.
      eapply normalize_when_wt_exp; eauto.
      + assert (incl (vars ++ st_tys st) (vars ++ st_tys st')) as Hincl by repeat solve_incl...
      + repeat solve_incl.
      + eapply map_bind2_wt_exp in H0; eauto.
        solve_forall. eapply H5 in H2...
        solve_forall. 1,2:repeat solve_incl.
      + eapply map_bind2_normalize_exp_typesof'' in H0; eauto.
    - (* merge *)
      repeat inv_bind.
      assert (Forall (wt_exp G (vars ++ st_tys x2)) (concat x3)) as Hwt1.
      { eapply map_bind2_wt_exp in H1; eauto.
        eapply Forall_Forall in H; eauto.
        eapply Forall_impl; eauto.
        intros ? [? ?] ? ? ? ? ? ? ?. eapply H8 in H11; eauto.
        solve_forall; eauto. 1,2:repeat solve_incl. }
      assert (Forall (wt_exp G (vars ++ st_tys x5)) (concat x6)) as Hwt2.
      { eapply map_bind2_wt_exp in H2; eauto.
        solve_forall. eapply H11 in H5...
        solve_forall. 1,2:repeat solve_incl. } clear H H0.
      destruct is_control; repeat inv_bind.
      + eapply normalize_merge_wt_exp; auto.
        * assert (incl (vars ++ st_tys st) (vars ++ st_tys st')) as Hincl by repeat solve_incl...
        * repeat solve_incl.
        * solve_forall. repeat solve_incl.
        * eapply map_bind2_normalize_exp_typesof'' in H1...
        * eapply map_bind2_normalize_exp_typesof'' in H2... congruence.
      + specialize (idents_for_anns_incl_ty _ _ _ _ H) as Hincl.
        apply idents_for_anns_wt with (G:=G) (vars:=vars) in H...
        rewrite Forall_forall; intros.
        repeat simpl_In. inv H0... repeat solve_incl.
    - (* ite *)
      repeat inv_bind.
      assert (length x = 1) as Hlen.
      { eapply normalize_exp_length in H1...
        rewrite H1, <- length_typeof_numstreams, H8... } singleton_length.
      assert (typeof e0 = [Op.bool_type]) as Htyp.
      { eapply normalize_exp_typeof in H1; simpl in H1...
        rewrite app_nil_r in H1; congruence. }
      assert (wt_exp G (vars ++ st_tys x1) e0) as Hwt'.
      { eapply IHe in H1... inv H1... }
      assert (Forall (wt_exp G (vars ++ st_tys x4)) (concat x5)) as Hwt1.
      { eapply map_bind2_wt_exp in H2; eauto.
        solve_forall. eapply H13 in H7...
        solve_forall. 1,2:repeat solve_incl. }
      assert (Forall (wt_exp G (vars ++ st_tys x7)) (concat x8)) as Hwt2.
      { eapply map_bind2_wt_exp in H3; eauto.
        solve_forall. eapply H13 in H7...
        solve_forall. 1,2:repeat solve_incl. } clear H H0.
      destruct is_control; repeat inv_bind.
      + eapply normalize_ite_wt_exp; auto.
        * repeat solve_incl.
        * repeat solve_incl.
        * solve_forall. repeat solve_incl.
        * eapply map_bind2_normalize_exp_typesof'' in H2...
        * eapply map_bind2_normalize_exp_typesof'' in H3... congruence.
      + specialize (idents_for_anns_incl_ty _ _ _ _ H) as Hincl.
        apply idents_for_anns_wt with (G:=G) (vars:=vars) in H...
        rewrite Forall_forall; intros.
        repeat simpl_In. inv H0... repeat solve_incl.
    - (* app *)
      repeat inv_bind.
      specialize (idents_for_anns'_incl_ty _ _ _ _ H2) as Hincl.
      eapply idents_for_anns'_wt with (G:=G) (vars:=vars) in H2...
      + solve_forall. repeat solve_incl.
      + solve_forall. simpl in *...
        solve_incl. unfold idty. rewrite map_app, <- app_assoc.
        apply incl_appr', incl_app; [repeat solve_incl|apply incl_app;[apply incl_appr|apply incl_appl]].
        * eapply map_bind2_normalize_exp_fresh_incl in H1.
          unfold st_tys, idty in *. apply incl_map...
        * eapply idents_for_anns'_anon_streams_incl, incl_map in H2.
          etransitivity. eapply H2.
          replace (map _ (without_names' x1)) with (map (fun xtc => (fst xtc, fst (snd xtc))) x1); auto.
          unfold without_names'; rewrite map_map; simpl.
          apply map_ext; intros [? [? [? ?]]]; auto.
    - (* app (reset) *)
      repeat inv_bind.
      specialize (idents_for_anns'_incl_ty _ _ _ _ H3) as Hincl.
      eapply idents_for_anns'_wt with (G:=G) (vars:=vars) in H3...
      + solve_forall. repeat solve_incl.
      + solve_forall; simpl in *...
        solve_incl. unfold idty. rewrite map_app, <- app_assoc.
        apply incl_appr', incl_app; [repeat solve_incl|apply incl_app;[apply incl_appr|apply incl_appl]].
        * eapply map_bind2_normalize_exp_fresh_incl in H1.
          unfold st_tys, idty in *. eapply incl_map.
          assert (st_follows x1 x4) by repeat solve_st_follows.
          etransitivity...
        * eapply idents_for_anns'_anon_streams_incl, incl_map in H3.
          etransitivity. eapply H3.
          replace (map _ (without_names' x5)) with (map (fun xtc => (fst xtc, fst (snd xtc))) x5); auto.
          unfold without_names'; rewrite map_map; simpl.
          apply map_ext; intros [? [? [? ?]]]; auto.
  Qed.

  Corollary map_bind2_normalize_exp_wt_exp : forall G vars is_control es es' eqs' st st',
      Forall (wt_exp G (vars++st_tys st)) es ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      Forall (wt_exp G (vars++st_tys st')) (concat es').
  Proof.
    intros G vars is_control es es' eqs' st st' Hwt Hmap.
    eapply map_bind2_wt_exp in Hmap; solve_forall; eauto.
    eapply normalize_exp_wt_exp with (G:=G) (vars:=vars) in H1; eauto.
    solve_forall. 1,2:repeat solve_incl.
  Qed.

  Corollary normalize_exps_wt_exp : forall G vars es es' eqs' st st',
      Forall (wt_exp G (vars++st_tys st)) es ->
      normalize_exps es st = (es', eqs', st') ->
      Forall (wt_exp G (vars++st_tys st')) es'.
  Proof.
    intros G vars es es' eqs' st st' Hwt Hmap.
    unfold normalize_exps in Hmap; repeat inv_bind.
    eapply map_bind2_normalize_exp_wt_exp in H; eauto.
  Qed.

  Fact normalize_reset_typeof_bool : forall e e' eqs' st st',
      typeof e = [Op.bool_type] ->
      normalize_reset e st = (e', eqs', st') ->
      typeof e' = [Op.bool_type].
  Proof with eauto.
    intros e e' eqs' st st' Htyp Hnorm.
    specialize (normalize_reset_spec e) as [[? [? [? Hspec]]]|Hspec]; subst;
      rewrite Hspec in Hnorm; clear Hspec; repeat inv_bind; simpl in *...
    destruct (hd _) as [? [? ?]] eqn:Hann; repeat inv_bind.
    rewrite typeof_annot in Htyp.
    destruct (annot e); simpl in *; try congruence.
    inv Hann.
    destruct l; simpl in *; try congruence.
  Qed.

  Fact normalize_reset_wt_exp : forall G vars e e' eqs' st st',
      incl (fresh_in e) (st_anns st') ->
      wt_exp G (vars++(st_tys st)) e ->
      normalize_reset e st = (e', eqs', st') ->
      wt_exp G (vars++(st_tys st')) e'.
  Proof.
    intros G vars e e' eqs' st st' Hincl Hwt Hnorm.
    assert (st_follows st st') as Hfollows by eauto.
    specialize (normalize_reset_spec e) as [[? [? [? Hspec]]]|Hspec]; subst;
      rewrite Hspec in Hnorm; clear Hspec; repeat inv_bind.
    - assumption.
    - destruct (hd _) as [? [? ?]] eqn:Hann; repeat inv_bind.
      constructor.
      + apply fresh_ident_In in H.
        apply in_or_app; right.
        rewrite st_anns_tys_In. exists c. assumption.
      + constructor. destruct (annot e) eqn:Hann'; simpl in Hann.
        * inv Hann. constructor.
        * subst. eapply wt_exp_clockof in Hwt.
          rewrite Forall_forall in Hwt.
          eapply wt_clock_incl; [| eapply Hwt].
          -- rewrite <- app_assoc.
             eapply incl_appr'. eapply incl_app.
             ++ eapply st_follows_tys_incl; auto.
             ++ apply incl_map; auto.
          -- rewrite clockof_annot. rewrite Hann'; simpl. left; auto.
  Qed.

  Fact normalize_rhs_wt_exp : forall G vars e es' eqs' st st',
      wt_exp G (vars++st_tys st) e ->
      normalize_rhs e st = (es', eqs', st') ->
      Forall (wt_exp G (vars++st_tys st')) es'.
  Proof with eauto.
    intros * Hwt Hnorm.
    destruct e; unfold normalize_rhs in Hnorm;
      try (solve [eapply normalize_exp_wt_exp in Hnorm; eauto]).
    - (* fby *)
      inv Hwt. repeat inv_bind.
      eapply normalize_fby_wt_exp.
      + solve_forall; repeat solve_incl.
      + eapply normalize_exps_wt_exp in H... solve_forall; repeat solve_incl.
      + eapply normalize_exps_wt_exp in H0... solve_forall; repeat solve_incl.
      + unfold normalize_exps in H; repeat inv_bind.
        eapply map_bind2_normalize_exp_typesof'' in H... congruence.
      + unfold normalize_exps in H0; repeat inv_bind.
        eapply map_bind2_normalize_exp_typesof'' in H0... congruence.
    - (* app *)
      inv Hwt; repeat inv_bind; repeat econstructor; eauto.
      1,4: eapply normalize_exps_wt_exp in H...
      1,3,5:solve_forall. repeat solve_incl.
      1,2:replace (fresh_ins x) with (@nil (ident * (Op.type * clock))); simpl. 2,4:(eapply normalize_exps_no_fresh in H; eauto).
      3,4: (eapply normalize_exps_typesof in H; eauto; congruence).
      + unfold idty in *. rewrite <- app_assoc, map_app in *.
        solve_incl. eapply incl_appr', incl_app; [apply incl_appl; repeat solve_incl|apply incl_app]; auto.
        apply normalize_exps_fresh_incl in H.
        unfold st_tys, idty. apply incl_appl, incl_map...
      + unfold idty in *. rewrite <- app_assoc, map_app in *.
        solve_incl. eapply incl_appr', incl_app; [apply incl_appl; repeat solve_incl|apply incl_app]; auto.
        apply normalize_exps_fresh_incl in H.
        assert (st_follows x1 st') by repeat solve_st_follows.
        unfold st_tys, idty. eapply incl_appl, incl_map.
        etransitivity...
      + specialize (normalize_exp_no_fresh _ _ _ _ _ _ H0) as Hincl.
        eapply normalize_exp_wt_exp with (G:=G) (vars:=vars) in H0... 2:repeat solve_incl.
        eapply hd_default_wt_exp in H0.
        eapply normalize_reset_wt_exp in H1...
        destruct x4; simpl; try apply incl_nil'.
        apply fresh_ins_nil in Hincl; rewrite Hincl; apply incl_nil'.
      + specialize (normalize_exp_numstreams _ _ _ _ _ _ H0) as Hlength.
        eapply normalize_exp_typeof in H0...
        eapply normalize_reset_typeof_bool in H1...
        rewrite H9 in H0.
        destruct x4; simpl in *; try congruence.
        inv Hlength. rewrite <- length_typeof_numstreams in H11.
        destruct (typeof e); simpl in *; try congruence.
        destruct l1; simpl in *; try congruence.
  Qed.

  Corollary normalize_rhss_wt_exp : forall G vars es es' eqs' st st',
      Forall (wt_exp G (vars++st_tys st)) es ->
      normalize_rhss es st = (es', eqs', st') ->
      Forall (wt_exp G (vars++st_tys st')) es'.
  Proof with eauto.
    intros * Hwt Hnorm.
    unfold normalize_rhss in Hnorm; repeat inv_bind.
    eapply map_bind2_wt_exp in H...
    solve_forall.
    eapply normalize_rhs_wt_exp with (G:=G) (vars:=vars) in H2...
    solve_forall. 1,2:repeat solve_incl.
  Qed.

  Fact map_bind2_wt_eq {A A1 B} :
    forall G vars (k : A -> Fresh (A1 * list equation) B) a a1s eqs' st st',
      map_bind2 k a st = (a1s, eqs', st') ->
      (forall st st' a es a2s, k a st = (es, a2s, st') -> st_follows st st') ->
      Forall (fun a => forall a1 eqs' st0 st0',
                  k a st0 = (a1, eqs', st0') ->
                  st_follows st st0 ->
                  st_follows st0' st' ->
                  Forall (wt_equation G vars) eqs') a ->
      Forall (wt_equation G vars) (concat eqs').
  Proof.
   intros G vars k a.
    induction a; intros es' a2s st st' Hmap Hfollows Hforall;
      repeat inv_bind.
    - constructor.
    - apply Forall_app. split; eauto.
      + rewrite Forall_forall in Hforall.
        eapply Hforall. 2:eauto.
        * constructor. reflexivity.
        * reflexivity.
        * eapply map_bind2_st_follows in H0; eauto.
          rewrite Forall_forall; intros; eauto.
      + eapply IHa; eauto.
        rewrite Forall_forall in *; intros.
        eapply Hforall. 2,4:eauto.
        * apply in_cons; auto.
        * etransitivity; eauto.
  Qed.

  Fact normalize_reset_wt_eq : forall G vars e e' eqs' st st',
      wt_exp G (vars++(st_tys st)) e ->
      typeof e = [Op.bool_type] ->
      normalize_reset e st = (e', eqs', st') ->
      Forall (wt_equation G (vars++(st_tys st'))) eqs'.
  Proof.
    intros G vars e e' eqs' st st' Hwt Hty Hnorm.
    specialize (normalize_reset_spec e) as [[? [? [? Hspec]]]|Hspec]; subst;
      rewrite Hspec in Hnorm; clear Hspec; repeat inv_bind; auto.
    destruct (hd _) as [? [? ?]] eqn:Hann; repeat inv_bind.
    repeat constructor; simpl.
    - repeat solve_incl.
    - rewrite app_nil_r. rewrite Hty.
      repeat constructor.
      apply fresh_ident_In in H.
      apply in_or_app; right.
      unfold st_tys, idty.
      repeat simpl_In.
      exists (x, (t, c)); simpl; split; auto.
      destruct (annot e) eqn:Hannot; simpl in Hann; inv Hann. reflexivity.
      destruct e; simpl in *; inv Hannot; inv Hty; auto;
        try destruct l1; try destruct l2; simpl in *; subst; inv H1; reflexivity.
  Qed.

  Definition default_ann : ann := (Op.bool_type, (Cbase, None)).

  Fact idents_for_anns'_wt_nclock : forall vars anns ids st st',
      idents_for_anns' anns st = (ids, st') ->
      Forall (fun '(ty, cl) => wt_nclock (vars++idty (anon_streams anns)++st_tys st) cl) anns ->
      Forall (wt_nclock (vars++idty (anon_streams (map snd ids))++st_tys st')) (map snd (map snd ids)).
  Proof with eauto.
    induction anns; intros ids st st' Hidents Hf;
      repeat inv_bind; simpl; auto.
    inv Hf. destruct a as [ty [cl ?]].
    destruct o; repeat inv_bind; simpl; constructor.
    - repeat constructor; simpl.
      inv H1. destruct x; simpl in *. solve_incl.
      eapply incl_appr', incl_tl', incl_app.
      + apply incl_appl.
        eapply idents_for_anns'_anon_streams, incl_map in H0...
      + apply incl_appr. solve_incl.
    - eapply IHanns in H0.
      + solve_forall. repeat solve_incl.
      + solve_forall. destruct x. solve_incl.
        rewrite Permutation.Permutation_middle.
        eapply incl_appr', incl_appr', incl_cons; try solve_incl.
        eapply reuse_ident_In in H. unfold st_tys, idty, idty.
        rewrite in_map_iff. exists (i, (ty, cl)); split; auto.
    - repeat constructor; simpl.
      inv H1. solve_incl.
      eapply incl_appr', incl_app.
      + apply incl_appl.
        eapply idents_for_anns'_anon_streams, incl_map in H0...
      + apply incl_appr. solve_incl.
    - eapply IHanns in H0.
      + solve_forall.
      + solve_forall. solve_incl.
        eapply incl_appr', incl_appr'. solve_incl.
  Qed.

  Import Permutation.
  Fact normalize_exp_wt_eq : forall G vars e is_control es' eqs' st st',
      wt_exp G (vars++st_tys st) e ->
      normalize_exp is_control e st = (es', eqs', st') ->
      Forall (wt_equation G (vars++(st_tys st'))) eqs'.
  Proof with eauto.
    induction e using exp_ind2; intros is_control es' eqs' st st' Hwt Hnorm;
      repeat inv_bind.
    - (* const *) constructor.
    - (* var *) constructor.
    - (* unop *) inv Hwt...
    - (* binop *)
      inv Hwt.
      rewrite Forall_app.
      split.
      + eapply IHe1 in H; eauto.
        solve_forall. eapply wt_equation_incl; [| eauto].
        eapply normalize_exp_st_follows in H0.
        repeat solve_incl.
      + eapply IHe2 in H0; eauto.
        repeat solve_incl.
    - (* fby *)
      inv Hwt.
      repeat rewrite Forall_app.
      repeat split.
      + assert (Forall (wt_exp G (vars++st_tys st')) (normalize_fby (concat x2) (concat x6) a)) as Hwcfby.
        { eapply normalize_fby_wt_exp...
          + solve_forall; repeat solve_incl.
          + eapply map_bind2_normalize_exp_wt_exp in H1... solve_forall; repeat solve_incl.
          + eapply map_bind2_normalize_exp_wt_exp with (G:=G) (vars:=vars) in H2... 1,2:solve_forall; repeat solve_incl.
          + eapply map_bind2_normalize_exp_typesof'' in H1... congruence.
          + eapply map_bind2_normalize_exp_typesof'' in H2... congruence. }
        remember (normalize_fby _ _ _) as fby.
        assert (length (concat x2) = length a) as Hlen1.
        { eapply map_bind2_normalize_exp_length in H1...
          repeat simpl_length. erewrite <- map_length, H10; solve_length. }
        assert (length (concat x6) = length a) as Hlen2.
        { eapply map_bind2_normalize_exp_length in H2...
          repeat simpl_length. erewrite <- map_length, H9; solve_length. }
        assert (length fby = length x5).
        { rewrite Heqfby, normalize_fby_length...
          eapply idents_for_anns_length in H3... }
        assert (Forall2 (fun '(ty, _) e => typeof e = [ty]) (map snd x5) fby) as Htys.
        { eapply idents_for_anns_values in H3; subst.
          specialize (normalize_fby_annot' _ _ _ Hlen1 Hlen2) as Hanns; eauto. clear - Hanns.
          eapply Forall2_swap_args. solve_forall.
          destruct a0 as [ty ck]; simpl in *. rewrite typeof_annot, H1; auto. }
        solve_forall.
        repeat constructor; eauto.
        destruct a0 as [ty ck]; simpl in *. rewrite app_nil_r, H7.
        constructor; auto. eapply idents_for_anns_incl_ty in H3.
        apply in_or_app, or_intror, H3. unfold idty; simpl_In. exists (i, (ty, ck)); auto.
      + eapply map_bind2_wt_eq in H1; eauto.
        solve_forall. eapply H8 in H5; eauto.
        solve_forall. 1,2:repeat solve_incl.
      + eapply map_bind2_wt_eq in H2; eauto.
        solve_forall. eapply H8 in H5; eauto.
        solve_forall. 1,2:repeat solve_incl.
    - (* when *)
      inv Hwt; repeat inv_bind.
      eapply map_bind2_wt_eq; eauto.
      solve_forall. eapply H5 in H2...
      solve_forall. 1,2:repeat solve_incl.
    - (* merge *)
      inv Hwt.
      simpl_forall.
      destruct is_control; repeat inv_bind; repeat rewrite Forall_app; repeat split.
      1,4: eapply map_bind2_wt_eq in H1... 3,5: eapply map_bind2_wt_eq in H2...
      1,2,3,4:(eapply Forall_impl; eauto;
               intros ? [Hwt Hf] ? ? ? ? Hnorm ? ?; simpl in *; eapply Hf in Hnorm; [solve_forall|]; repeat solve_incl).
      simpl_forall.
      remember (normalize_merge x (concat x3) (concat x7) (typesof ets) nck) as merges.
      assert (Forall (wt_exp G (vars++st_tys st')) merges).
      { subst. apply normalize_merge_wt_exp; auto.
        - assert (incl (vars ++ st_tys st) (vars ++ st_tys st')) by repeat solve_incl; eauto.
        - repeat solve_incl.
        - eapply map_bind2_normalize_exp_wt_exp with (G:=G) (vars:=vars) in H1...
          1,2:solve_forall; repeat solve_incl.
        - eapply map_bind2_normalize_exp_wt_exp with (G:=G) (vars:=vars) in H2...
          1,2:solve_forall; repeat solve_incl.
        - eapply map_bind2_normalize_exp_typesof'' in H1...
          solve_forall.
        - eapply map_bind2_normalize_exp_typesof'' in H2... congruence.
          solve_forall.
      }
      assert (length (concat x3) = length (typesof ets)) as Hlen1.
      { eapply map_bind2_normalize_exp_length in H1; eauto; solve_length. solve_forall. }
      assert (length (concat x7) = length (typesof efs)) as Hlen2.
      { clear H9. eapply map_bind2_normalize_exp_length in H2; eauto; solve_length. solve_forall. }
      assert (Forall2 (fun '(ty, _) e => annot e = [(ty, nck)]) (map snd x6) merges) as Htys.
      { eapply idents_for_anns_values in H3. rewrite H3, Forall2_map_1.
        subst; eapply normalize_merge_annot; eauto. congruence. } rewrite Forall2_map_1 in Htys.
      eapply Forall2_ignore1' with (xs:=x6) in H4.
      2:{ subst. apply idents_for_anns_length in H3. rewrite map_length in H3.
          rewrite normalize_merge_length... congruence. }
      solve_forall.
      repeat constructor... destruct a; simpl in *.
      rewrite typeof_annot, H6, app_nil_r; simpl.
      constructor; auto.
      assert (In (i, t) (idty x6)).
      { unfold idty. rewrite in_map_iff. exists (i, (t, n)); eauto. }
      eapply idents_for_anns_incl_ty in H3.
      eapply in_or_app, or_intror...
    - (* ite *)
      inv Hwt.
      eapply Forall_Forall in H; eauto.
      eapply Forall_Forall in H0; eauto.
      destruct is_control; repeat inv_bind; repeat rewrite Forall_app; repeat split.
      1,5:eapply IHe in H1; eauto; solve_forall; repeat solve_incl...
      1,4: eapply map_bind2_wt_eq in H2... 3,5: eapply map_bind2_wt_eq in H3...
      1,2,3,4:(eapply Forall_impl; eauto;
               intros ? [Hwt Hf] ? ? ? ? Hnorm ? ?; simpl in *; eapply Hf in Hnorm; [solve_forall|]; repeat solve_incl).
      clear IHe.
      assert (length x = 1) as Hlen.
      { eapply normalize_exp_length in H1...
        rewrite H1, <- length_typeof_numstreams, H8; auto. } singleton_length.
      apply Forall2_combine', Forall2_map_1, Forall2_map_2.
      remember (normalize_ite e0 (concat x5) (concat x9) (typesof ets) nck) as ites.
      assert (Forall (wt_exp G (vars++st_tys st')) ites).
      { subst. apply normalize_ite_wt_exp; auto.
        - repeat solve_incl.
        - eapply normalize_exp_wt_exp in H1... inv H1. repeat solve_incl.
        - eapply normalize_exp_typeof in H1... simpl in H1; rewrite app_nil_r in H1; congruence.
        - eapply map_bind2_normalize_exp_wt_exp with (G:=G) (vars:=vars) in H2...
          1,2:solve_forall; repeat solve_incl.
        - eapply map_bind2_normalize_exp_wt_exp with (G:=G) (vars:=vars) in H3...
          1,2:solve_forall; repeat solve_incl.
        - eapply map_bind2_normalize_exp_typesof'' in H2...
        - eapply map_bind2_normalize_exp_typesof'' in H3... congruence.
      }
      assert (length (concat x5) = length (typesof ets)) as Hlen1.
      { eapply map_bind2_normalize_exp_length in H2; eauto; solve_length. }
      assert (length (concat x9) = length (typesof efs)) as Hlen2.
      { clear H10. eapply map_bind2_normalize_exp_length in H3; eauto; solve_length. }
      assert (Forall2 (fun '(ty, _) e => annot e = [(ty, nck)]) (map snd x8) ites) as Htys.
      { eapply idents_for_anns_values in H4. rewrite H4, Forall2_map_1.
        subst; eapply normalize_ite_annot; eauto. congruence. } rewrite Forall2_map_1 in Htys.
      eapply Forall2_ignore1' with (xs:=x8) in H9.
      2:{ subst. apply idents_for_anns_length in H4. rewrite map_length in H4.
          rewrite normalize_ite_length... congruence. }
      solve_forall.
      repeat constructor...
      destruct a; simpl in *.
      rewrite typeof_annot, app_nil_r, H9; simpl.
      constructor; auto.
      assert (In (i, t) (idty x8)).
      { unfold idty. rewrite in_map_iff. exists (i, (t, n)); eauto. }
      eapply idents_for_anns_incl_ty in H4.
      eapply in_or_app, or_intror...
    - (* app *)
      inv Hwt; repeat inv_bind; repeat econstructor; simpl; eauto.
      1,7: (eapply map_bind2_normalize_exp_wt_exp in H1; eauto;
            solve_forall; repeat solve_incl).
      1,6: (eapply map_bind2_normalize_exp_typesof in H1; eauto; congruence).
      3,4,9: rewrite app_nil_r.
      + clear H0 H8 H10 H12.
        eapply idents_for_anns'_values in H3; subst. assumption.
      + eapply idents_for_anns'_wt_nclock with (vars:=vars) in H3.
        * rewrite Forall_map in H3. solve_forall.
          solve_incl.
          rewrite <- app_assoc. apply incl_appr'.
          rewrite Permutation_app_comm. apply incl_appr'.
          unfold idty. rewrite map_app. apply incl_appr, incl_refl.
        * solve_forall.
          solve_incl. rewrite <- app_assoc. apply incl_appr'.
          unfold idty. rewrite map_app.
          apply incl_app; [repeat solve_incl|].
          apply incl_app; [apply incl_appr|apply incl_appl; auto].
          apply map_bind2_normalize_exp_fresh_incl in H1. eapply incl_map in H1; eauto.
      + simpl_forall.
        eapply idents_for_anns'_incl_ty in H3.
        eapply Forall_forall; intros [id [ty [cl name]]] Hin; simpl.
        apply in_or_app; right. apply H3.
        unfold idty. rewrite in_map_iff. eexists; split; eauto...
      + eapply map_bind2_wt_eq in H1...
        rewrite Forall_forall in *; intros.
        eapply H0 in H4...
        solve_forall; repeat solve_incl. apply H8 in H2; repeat solve_incl.
      + simpl_forall.
        eapply idents_for_anns'_incl_ty in H3.
        eapply Forall_forall; intros [id [ty [cl name]]] Hin; simpl.
        apply in_or_app; right. apply H3.
        unfold idty. rewrite in_map_iff. eexists; split; eauto...
      + clear H0 H8 H10 H12.
        eapply idents_for_anns'_values in H3; subst. assumption.
      + eapply idents_for_anns'_wt_nclock with (vars:=vars) in H3.
        * rewrite Forall_map in H3. solve_forall.
          solve_incl.
          rewrite <- app_assoc. apply incl_appr'.
          rewrite Permutation_app_comm. apply incl_appr'.
          unfold idty. rewrite map_app. apply incl_appr, incl_refl.
        * solve_forall; simpl in *.
          solve_incl. rewrite <- app_assoc. apply incl_appr'.
          unfold idty. rewrite map_app. apply incl_app; [repeat solve_incl|].
          apply incl_app; [apply incl_appr|apply incl_appl]...
          apply map_bind2_normalize_exp_fresh_incl in H1.
          assert (st_follows x1 x8) by eauto. eapply st_follows_incl in H7.
          assert (st_follows x8 x4) by eauto. eapply st_follows_incl in H8.
          assert (incl (fresh_ins es) (st_anns x4)) by (repeat (etransitivity; eauto)).
          eapply incl_map...
      + specialize (normalize_exp_no_fresh _ _ _ _ _ _ H2) as Hnofresh.
        eapply normalize_exp_wt_exp with (G:=G) (vars:=vars) in H2... 2:repeat solve_incl.
        eapply hd_default_wt_exp in H2...
        eapply normalize_reset_wt_exp in H4...
        2:{ destruct x; simpl. apply incl_nil'.
            apply fresh_ins_nil in Hnofresh; rewrite Hnofresh; apply incl_nil'. }
        eapply map_bind2_st_follows in H1; solve_forall.
        repeat solve_incl.
      + specialize (normalize_exp_numstreams _ _ _ _ _ _ H2) as Hlength.
        eapply normalize_exp_typeof in H2...
        eapply normalize_reset_typeof_bool in H4...
        rewrite H14 in H2.
        destruct x; simpl in *; try congruence.
        inv Hlength. rewrite <- length_typeof_numstreams in H7.
        destruct (typeof e); simpl in *; try congruence.
        destruct l; simpl in *; try congruence.
      + repeat rewrite Forall_app. repeat split.
        * eapply map_bind2_wt_eq in H1; eauto.
          rewrite Forall_forall in *; intros.
          eapply H0 in H6...
          solve_forall; repeat solve_incl. eapply H8 in H5; repeat solve_incl.
        * eapply H in H2...
          apply normalize_reset_st_follows in H4.
          apply idents_for_anns'_st_follows in H3.
          solve_forall. 1,2:repeat solve_incl.
        * assert (length x = numstreams r) as Hlength by eauto.
          specialize (normalize_exp_typeof _ _ _ _ _ _ _ _ H13 H2) as Htypeof.
          rewrite H14 in Htypeof.
          eapply normalize_exp_wt_exp with (G:=G) (vars:=vars) in H2... 2:repeat solve_incl.
          eapply hd_default_wt_exp in H2...
          eapply normalize_reset_wt_eq in H4...
          -- solve_forall. repeat solve_incl.
          -- rewrite <- length_typeof_numstreams in Hlength. rewrite H14 in Hlength; simpl in Hlength.
             singleton_length...
  Qed.

  Corollary normalize_exps_wt_eq : forall G vars es es' eqs' st st',
      Forall (wt_exp G (vars++st_tys st)) es ->
      normalize_exps es st = (es', eqs', st') ->
      Forall (wt_equation G (vars++(st_tys st'))) eqs'.
  Proof with eauto.
    intros G vars es es' eqs' st st' Hwt Hnorm.
    unfold normalize_exps in Hnorm. repeat inv_bind.
    eapply map_bind2_wt_eq in H...
    solve_forall.
    eapply normalize_exp_wt_eq with (G:=G) (vars:=vars) in H2...
    solve_forall. 1,2:repeat solve_incl.
  Qed.

  Fact normalize_rhs_wt_eq : forall G vars e es' eqs' st st',
      wt_exp G (vars++st_tys st) e ->
      normalize_rhs e st = (es', eqs', st') ->
      Forall (wt_equation G (vars++(st_tys st'))) eqs'.
  Proof with eauto.
    intros * Hwt Hnorm.
    destruct e; unfold normalize_rhs in Hnorm;
      try eapply normalize_exp_wt_eq in Hnorm; eauto.
    - (* fby *)
      inv Hwt. repeat inv_bind.
      repeat rewrite Forall_app. repeat split.
      + eapply normalize_exps_wt_eq in H...
        solve_forall. repeat solve_incl.
      + eapply normalize_exps_wt_eq with (G:=G) (vars:=vars) in H0...
        1,2:solve_forall; repeat solve_incl.
    - (* app *)
      repeat inv_bind.
      apply Forall_app. split.
      + inv Hwt; repeat inv_bind; eapply normalize_exps_wt_eq in H...
        solve_forall. repeat solve_incl.
      + inv Hwt; repeat inv_bind; try constructor.
        apply Forall_app. split.
        * eapply normalize_exp_wt_eq with (G:=G) (vars:=vars) in H0...
          solve_forall. 1,2:repeat solve_incl.
        * eapply normalize_reset_wt_eq with (G:=G) (vars:=vars) in H1...
          -- eapply hd_default_wt_exp.
             eapply normalize_exp_wt_exp in H0...
             repeat solve_incl.
          -- specialize (normalize_exp_numstreams _ _ _ _ _ _ H0) as Hnumstreams.
             eapply normalize_exp_typeof in H0...
             rewrite H11 in H0.
             destruct x4; simpl in *; try congruence.
             inv Hnumstreams. rewrite <- length_typeof_numstreams in H4. singleton_length.
  Qed.

  Corollary normalize_rhss_wt_eq : forall G vars es es' eqs' st st',
      Forall (wt_exp G (vars++st_tys st)) es ->
      normalize_rhss es st = (es', eqs', st') ->
      Forall (wt_equation G (vars++(st_tys st'))) eqs'.
  Proof with eauto.
    intros * Hwt Hnorm.
    unfold normalize_rhss in Hnorm; repeat inv_bind.
    eapply map_bind2_wt_eq in H...
    solve_forall. eapply normalize_rhs_wt_eq with (G:=G) (vars:=vars) in H2...
    solve_forall. 1,2:repeat solve_incl.
  Qed.

  Fact untuple_equation_wt_eq : forall G vars eq eqs' st st',
      wt_equation G (vars++st_tys st) eq ->
      untuple_equation eq st = (eqs', st') ->
      Forall (wt_equation G (vars++st_tys st')) eqs'.
  Proof with eauto.
    intros * Hwt Hnorm.
    destruct eq as [xs es]; simpl in Hnorm.
    repeat inv_bind. destruct Hwt.
    apply Forall_app. split.
    - specialize (normalize_rhss_typesof _ _ _ _ _ _ _ H0 H) as Htypeof.
      assert (st_follows st st') as Hfollows by eauto.
      eapply normalize_rhss_wt_exp in H...
      rewrite <- Htypeof in H1.
      clear Htypeof. revert xs H1.
      induction x; intros xs H1; constructor; simpl in H1.
      + inv H. repeat constructor...
        simpl. rewrite app_nil_r.
        repeat rewrite_Forall_forall.
        * rewrite app_length in H.
          rewrite firstn_length. rewrite H.
          rewrite length_typeof_numstreams.
          apply Nat.min_l. omega.
        * rewrite firstn_length in H2.
          rewrite PeanoNat.Nat.min_glb_lt_iff in H2; destruct H2 as [Hlen1 Hlen2].
          specialize (H1 a0 b _ _ _ Hlen2 eq_refl eq_refl).
          rewrite app_nth1 in H1. 2: rewrite length_typeof_numstreams.
          rewrite nth_firstn_1. 2,3:eauto.
          rewrite in_app_iff in *. destruct H1; auto.
          right. eapply st_follows_tys_incl...
      + inv H. apply IHx...
        repeat rewrite_Forall_forall.
        * rewrite app_length in H.
          rewrite skipn_length. rewrite H.
          rewrite length_typeof_numstreams. omega.
        * rewrite skipn_length in H2.
          rewrite nth_skipn.
          assert (n + numstreams a < length xs) as Hlen by omega.
          specialize (H1 a0 b _ _ _ Hlen eq_refl eq_refl).
          rewrite app_nth2 in H1. 2: rewrite length_typeof_numstreams; omega.
          rewrite length_typeof_numstreams in H1.
          replace (n + numstreams a - numstreams a) with n in H1 by omega...
    - eapply normalize_rhss_wt_eq in H...
  Qed.

  Corollary untuple_equations_wt_eq : forall G vars eqs eqs' st st',
      Forall (wt_equation G (vars++st_tys st)) eqs ->
      untuple_equations eqs st = (eqs', st') ->
      Forall (wt_equation G (vars++st_tys st')) eqs'.
  Proof with eauto.
    induction eqs; intros * Hwt Hnorm;
      unfold untuple_equations in Hnorm;
      repeat inv_bind; auto.
    inv Hwt. apply Forall_app. split.
    - eapply untuple_equation_wt_eq in H...
      solve_forall; repeat solve_incl.
    - assert (untuple_equations eqs x1 = (concat x2, st')) as Hnorm.
      { unfold untuple_equations; repeat inv_bind. repeat eexists; eauto. inv_bind; eauto. }
      eapply IHeqs in Hnorm...
      solve_forall; repeat solve_incl.
  Qed.

  (** ** Preservation of wt_clock *)

  Definition st_clocks (st : fresh_st (Op.type * clock)) : list clock :=
    map (fun '(_, (_, cl)) => cl) (st_anns st).
  Definition st_clocks' (st : fresh_st (Op.type * clock * bool)) : list clock :=
    map (fun '(_, (_, cl, _)) => cl) (st_anns st).

  Fact fresh_ident_wt_clock : forall vars ty cl id st st',
      Forall (wt_clock vars) (st_clocks st) ->
      wt_clock vars cl ->
      fresh_ident (ty, cl) st = (id, st') ->
      Forall (wt_clock vars) (st_clocks st').
  Proof.
    intros * Hclocks Hwt Hfresh.
    apply fresh_ident_anns in Hfresh.
    unfold st_clocks in *. setoid_rewrite Hfresh; simpl.
    constructor; auto.
  Qed.

  Corollary idents_for_anns_wt_clock : forall vars anns ids st st',
      Forall (wt_clock vars) (st_clocks st) ->
      Forall (wt_nclock vars) (map snd anns) ->
      idents_for_anns anns st = (ids, st') ->
      Forall (wt_clock vars) (st_clocks st').
  Proof.
    induction anns; intros ids st st' Hclocks Hwt Hidents;
      repeat inv_bind.
    - assumption.
    - inv Hwt. destruct a as [ty [cl ?]]. repeat inv_bind.
      eapply IHanns in H0; eauto.
      inv H1.
      eapply fresh_ident_wt_clock; eauto.
  Qed.

  Fact reuse_ident_wt_clock : forall vars ty cl id st st',
      Forall (wt_clock vars) (st_clocks st) ->
      wt_clock vars cl ->
      reuse_ident id (ty, cl) st = (tt, st') ->
      Forall (wt_clock vars) (st_clocks st').
  Proof.
    intros * Hclocks Hwt Hfresh.
    apply reuse_ident_anns in Hfresh.
    unfold st_clocks in *. setoid_rewrite Hfresh; simpl.
    constructor; auto.
  Qed.

  Corollary idents_for_anns'_wt_clock : forall vars anns ids st st',
      Forall (wt_clock vars) (st_clocks st) ->
      Forall (wt_nclock vars) (map snd anns) ->
      idents_for_anns' anns st = (ids, st') ->
      Forall (wt_clock vars) (st_clocks st').
  Proof.
    induction anns; intros ids st st' Hclocks Hwt Hidents;
      repeat inv_bind.
    - assumption.
    - inv Hwt. destruct a as [ty [cl ?]]. destruct o; repeat inv_bind.
      + eapply IHanns in H0; eauto.
        inv H1.
        destruct x. eapply reuse_ident_wt_clock; eauto.
      + eapply IHanns in H0; eauto.
        inv H1.
        eapply fresh_ident_wt_clock; eauto.
  Qed.

  Fact map_bind2_wt_clock {A A1 A2 : Type} :
    forall vars (k : A -> Untuple.FreshAnn (A1 * A2)) a a1s a2s st st',
      Forall (wt_clock (vars++st_tys st)) (st_clocks st) ->
      map_bind2 k a st = (a1s, a2s, st') ->
      (forall st st' a es a2s, k a st = (es, a2s, st') -> st_follows st st') ->
      Forall (fun a => forall a1s a2s st0 st0',
                  Forall (wt_clock (vars++st_tys st0)) (st_clocks st0) ->
                  k a st0 = (a1s, a2s, st0') ->
                  st_follows st st0 ->
                  st_follows st0' st' ->
                  Forall (wt_clock (vars++st_tys st0')) (st_clocks st0')) a ->
      Forall (wt_clock (vars++st_tys st')) (st_clocks st').
  Proof with eauto.
    induction a; intros a1s a2s st st' Hclocks Hmap Hfollows Hf;
      repeat inv_bind...
    inv Hf.
    specialize (H3 _ _ _ _ Hclocks H).
    eapply IHa in H3...
    - reflexivity.
    - eapply map_bind2_st_follows...
      solve_forall...
    - solve_forall.
      eapply H2 in H5...
      etransitivity...
  Qed.

  Fact normalize_reset_wt_clock : forall vars e e' eqs' st st',
      Forall (wt_clock vars) (clockof e) ->
      Forall (wt_clock vars) (st_clocks st) ->
      normalize_reset e st = (e', eqs', st') ->
      Forall (wt_clock vars) (st_clocks st').
  Proof with eauto.
  intros vars e e' eqs' st st' Hwt Hclocks Hnorm.
    specialize (normalize_reset_spec e) as [[? [? [? Hspec]]]|Hspec]; subst;
      rewrite Hspec in Hnorm; clear Hspec; repeat inv_bind...
    destruct (hd _) as [? [? ?]] eqn:Hhd.
    repeat inv_bind.
    eapply fresh_ident_wt_clock in H...
    rewrite clockof_annot in Hwt.
    destruct (annot e); simpl in *; inv Hhd.
    - constructor.
    - simpl in Hwt. inv Hwt...
  Qed.

  Fact normalize_exp_wt_clock : forall G vars e is_control es' eqs' st st',
      wt_exp G (vars++st_tys st) e ->
      Forall (wt_clock (vars++st_tys st)) (st_clocks st) ->
      normalize_exp is_control e st = (es', eqs', st') ->
      Forall (wt_clock (vars++st_tys st')) (st_clocks st').
  Proof with eauto.
    induction e using exp_ind2; intros is_control es' eqs' st st' Hwt Hclocks Hnorm;
      inv Hwt; repeat inv_bind; eauto.
    Ltac solve_map_bind2 :=
      solve_forall;
      match goal with
      | Hnorm : normalize_exp _ _ _ = _, Hf : forall (_ : bool), _ |- Forall _ ?l =>
        eapply Hf in Hnorm; eauto
      end; repeat solve_incl.
    - (* binop *)
      eapply IHe2 in H0...
      repeat solve_incl.
    - (* fby *)
      eapply idents_for_anns_wt_clock in H3... 2:solve_forall; repeat solve_incl.
      eapply map_bind2_wt_clock with (vars0:=vars) in H2... solve_forall; repeat solve_incl.
      eapply map_bind2_wt_clock in H1...
      1,2:solve_map_bind2.
    - (* when *)
      eapply map_bind2_wt_clock in H0...
      rewrite Forall_forall in *; intros...
      eapply H in H3... eapply H4 in H1... repeat solve_incl.
    - (* merge *)
      eapply Forall_Forall in H; eauto. clear H5. eapply Forall_Forall in H0; eauto. clear H6.
      destruct is_control; repeat inv_bind.
      + eapply map_bind2_wt_clock in H2...
        eapply map_bind2_wt_clock in H1... 1,2:solve_map_bind2.
      + eapply idents_for_anns_wt_clock in H3...
        2:{ rewrite map_map; simpl. solve_forall. repeat solve_incl. }
        eapply map_bind2_wt_clock with (vars0:=vars) in H2... 3:solve_map_bind2. solve_forall; repeat solve_incl.
        eapply map_bind2_wt_clock in H1... solve_map_bind2.
    - (* ite *)
      eapply Forall_Forall in H; eauto. clear H6. eapply Forall_Forall in H0; eauto. clear H7.
      destruct is_control; repeat inv_bind.
      + eapply map_bind2_wt_clock in H3...
        eapply map_bind2_wt_clock in H2... 1,2:solve_map_bind2.
      + eapply idents_for_anns_wt_clock in H4...
        2:{ rewrite map_map; simpl. solve_forall. repeat solve_incl. }
        eapply map_bind2_wt_clock with (vars0:=vars) in H3... 3:solve_map_bind2. solve_forall; repeat solve_incl.
        eapply map_bind2_wt_clock in H2... solve_map_bind2.
    - (* app *)
      eapply Forall_Forall in H0; eauto; clear H5.
      assert (st_follows st st') as Hfollows by repeat solve_st_follows.
      assert (incl (fresh_ins es) (st_anns x4)) as Hincl by (apply map_bind2_normalize_exp_fresh_incl in H1; auto).
      eapply map_bind2_wt_clock in H1... 2:solve_map_bind2.
      eapply idents_for_anns'_wt_clock in H2...
      1: solve_forall; repeat solve_incl.
      rewrite Forall_map. solve_forall; solve_incl.
      rewrite <- app_assoc. apply incl_appr', incl_app; repeat solve_incl.
      unfold st_tys, idty; rewrite map_app; apply incl_app; apply incl_map.
      + etransitivity...
      + apply idents_for_anns'_fresh_incl in H2...
    - (* app (reset) *)
      eapply Forall_Forall in H0; eauto; clear H5.
      assert (st_follows st x1) by repeat solve_st_follows. assert (st_follows x1 st') by repeat solve_st_follows.
      assert (st_follows x1 x8) by eauto. assert (st_follows x8 st') by repeat solve_st_follows.
      assert (incl (fresh_in r) (st_anns x8)) as Hincl1 by (apply normalize_exp_fresh_incl in H2; auto).
      assert (incl (fresh_ins es) (st_anns x1)) as Hincl2 by (apply map_bind2_normalize_exp_fresh_incl in H1; auto).
      assert (length x6 = numstreams r) as Hlength by eauto.
      assert (clocksof x6 = clockof r) as Hannot by eauto.
      eapply map_bind2_wt_clock in H1... 2:solve_map_bind2.
      eapply H in H2... 2:repeat solve_incl.
      eapply normalize_reset_wt_clock in H4...
      2: { apply wt_exp_clockof in H10. rewrite <- Hannot in H10.
           rewrite <- length_typeof_numstreams, H11 in Hlength; simpl in Hlength.
           singleton_length.
           solve_forall. solve_incl.
           rewrite <- app_assoc. apply incl_appr', incl_app...
           1: apply st_follows_tys_incl; repeat solve_st_follows.
           unfold st_tys, idty; apply incl_map... }
      eapply idents_for_anns'_wt_clock in H3...
      1: solve_forall; repeat solve_incl.
      rewrite Forall_map. solve_forall. solve_incl.
      rewrite <- app_assoc. apply incl_appr', incl_app; repeat solve_incl.
      unfold st_tys, idty; apply incl_map, incl_app.
      + etransitivity...
      + apply idents_for_anns'_fresh_incl in H3...
  Qed.

  Corollary normalize_exps_wt_clock : forall G vars es es' eqs' st st',
      Forall (wt_exp G (vars++st_tys st)) es ->
      Forall (wt_clock (vars++st_tys st)) (st_clocks st) ->
      normalize_exps es st = (es', eqs', st') ->
      Forall (wt_clock (vars++st_tys st')) (st_clocks st').
  Proof.
    intros G vars es es' eqs' st st' Hwt Hclocks Hnorm.
    unfold normalize_exps in Hnorm. repeat inv_bind.
    eapply map_bind2_wt_clock in H; eauto.
    solve_forall.
    assert (st_follows st0 st0') by eauto.
    eapply normalize_exp_wt_clock with (G:=G) (vars:=vars) in H3; repeat solve_incl.
    - solve_forall; solve_incl.
    - solve_forall; solve_incl.
  Qed.

  Corollary normalize_rhs_wt_clock : forall G vars e es' eqs' st st',
      wt_exp G (vars++st_tys st) e ->
      Forall (wt_clock (vars++st_tys st)) (st_clocks st) ->
      normalize_rhs e st = (es', eqs', st') ->
      Forall (wt_clock (vars++st_tys st')) (st_clocks st').
  Proof with eauto.
    intros * Hwt Hclocks Hnorm.
    destruct e; unfold normalize_rhs in Hnorm;
      try eapply normalize_exp_wt_clock in Hnorm; eauto;
        inv Hwt.
    - (* fby (keep) *)
      repeat inv_bind.
      assert (st_follows st x1) by repeat solve_st_follows. assert (st_follows st st') by repeat solve_st_follows.
      eapply normalize_exps_wt_clock with (G:=G) in H...
      eapply normalize_exps_wt_clock with (G:=G) in H0...
      solve_forall; do 3 solve_incl; apply st_follows_tys_incl; auto.
    - (* app *)
      repeat inv_bind.
      eapply normalize_exps_wt_clock with (G:=G) in H...
    - (* app (reset) *)
      repeat inv_bind.
      assert (incl (fresh_in r) (st_anns x6)) as Hincl by (eapply normalize_exp_fresh_incl; eauto).
      assert (st_follows x6 st') as Hfollows2 by repeat solve_st_follows.
      assert (length x4 = numstreams r) as Hlength by eauto.
      assert (clocksof x4 = clockof r) as Hclockof by eauto.
      assert (wt_exp G (vars ++ st_tys x1) r) as Hwt' by repeat solve_incl.
      assert (st_follows st st') as Hfollows by repeat solve_st_follows.
      specialize (normalize_exp_wt_exp _ _ _ _ _ _ _ _ Hwt' H0) as Hwt.
      eapply normalize_exps_wt_clock with (G:=G) in H...
      eapply normalize_exp_wt_clock with (G:=G) in H0...
      eapply normalize_reset_wt_clock in H1... 2:solve_forall; repeat solve_incl.
      assert (length x4 = 1).
      { rewrite Hlength. rewrite typeof_annot in H9. rewrite <- length_annot_numstreams.
        erewrite <- map_length. rewrite H9. reflexivity. }
      singleton_length.
      rewrite Hclockof.
      eapply wt_exp_clockof in H8.
      solve_forall; solve_incl.
      rewrite <- app_assoc. apply incl_appr'; repeat solve_incl.
      apply incl_app; repeat solve_incl. unfold st_tys, idty.
      apply incl_map; etransitivity...
  Qed.

  Corollary normalize_rhss_wt_clock : forall G vars es es' eqs' st st',
      Forall (wt_exp G (vars++st_tys st)) es ->
      Forall (wt_clock (vars++st_tys st)) (st_clocks st) ->
      normalize_rhss es st = (es', eqs', st') ->
      Forall (wt_clock (vars++st_tys st')) (st_clocks st').
  Proof.
    intros * Hwt Hclocks Hnorm.
    unfold normalize_rhss in Hnorm. repeat inv_bind.
    eapply map_bind2_wt_clock in H; eauto.
    solve_forall. eapply normalize_rhs_wt_clock with (G:=G) in H3; eauto.
    repeat solve_incl.
  Qed.

  Fact untuple_equation_wt_clock : forall G vars eq eqs' st st',
      wt_equation G (vars++st_tys st) eq ->
      Forall (wt_clock (vars++st_tys st)) (st_clocks st) ->
      untuple_equation eq st = (eqs', st') ->
      Forall (wt_clock (vars++st_tys st')) (st_clocks st').
  Proof.
    intros * Hwt Hclocks Hnorm.
    destruct eq; repeat inv_bind.
    destruct Hwt.
    eapply normalize_rhss_wt_clock in H; eauto.
  Qed.

  Corollary untuple_equations_wt_clock : forall G vars eqs eqs' st st',
      Forall (wt_equation G (vars++st_tys st)) eqs ->
      Forall (wt_clock (vars++st_tys st)) (st_clocks st) ->
      untuple_equations eqs st = (eqs', st') ->
      Forall (wt_clock (vars++st_tys st')) (st_clocks st').
  Proof.
    induction eqs; intros * Hwt Hclocks Hnorm;
      unfold untuple_equations in Hnorm; repeat inv_bind.
    - assumption.
    - inv Hwt.
      assert (st_follows st x1) by repeat solve_st_follows.
      eapply untuple_equation_wt_clock in H; eauto.
      assert (untuple_equations eqs x1 = (concat x2, st')) as Hnorm.
      { unfold untuple_equations; repeat inv_bind.
        repeat eexists; eauto. inv_bind; auto. }
      eapply IHeqs in Hnorm; eauto.
      solve_forall; repeat solve_incl.
  Qed.

  Lemma untuple_node_wt : forall G n Hwl,
      wt_node G n ->
      wt_node G (untuple_node n Hwl).
  Proof.
    intros * [Hclin [Hclout [Hclvars Heq]]].
    unfold untuple_node.
    repeat constructor; simpl; auto.
    - unfold wt_clocks in *.
      apply Forall_app. split.
      + solve_forall. unfold idty in *.
        solve_incl. repeat rewrite map_app. repeat solve_incl.
      + remember (untuple_equations _ _) as res.
        destruct res as [eqs st']. symmetry in Heqres.
        eapply untuple_equations_wt_clock with (G:=G) in Heqres; eauto.
        * simpl. unfold st_clocks in Heqres.
          unfold idty. solve_forall.
          repeat solve_incl.
          repeat rewrite map_app, app_assoc.
          eapply incl_appr'. reflexivity.
        * unfold st_clocks. unfold st_tys. rewrite init_st_anns, app_nil_r.
          repeat rewrite <- app_assoc. repeat rewrite <- map_app.
          solve_forall; repeat solve_incl. apply incl_map, incl_appr'. rewrite Permutation_app_comm; auto.
        * unfold st_clocks. rewrite init_st_anns; simpl; constructor.
    - remember (untuple_equations _ _) as res.
      destruct res as [eqs' st']; simpl.
      symmetry in Heqres.
      eapply untuple_equations_wt_eq with (G:=G) (vars:=(idty (n_in n ++ n_vars n ++ n_out n))) in Heqres; eauto.
      + solve_forall; solve_incl.
        unfold st_tys; rewrite <- idty_app. apply incl_map.
        repeat rewrite <- app_assoc. apply incl_appr', incl_appr'.
        rewrite Permutation_app_comm. reflexivity.
      + solve_forall; repeat solve_incl.
  Qed.

  Lemma untuple_global_wt : forall G Hwl,
      wt_global G ->
      wt_global (untuple_global G Hwl).
  Proof.
    induction G; intros * Hwt; simpl; inv Hwt.
    - constructor.
    - constructor.
      + eapply IHG; eauto.
      + remember (untuple_node _ _) as n'. symmetry in Heqn'.
        subst.
        eapply untuple_node_wt; eauto.
        eapply iface_eq_wt_node; eauto.
        eapply untuple_global_eq.
      + eapply untuple_global_names; eauto.
  Qed.

  (** ** Preservation of wt through the second pass *)

  Fact fby_iteexp_wt_exp : forall G vars e0 e ty ck name e' eqs' st st',
      wt_clock (vars++st_tys' st) ck ->
      wt_exp G (vars++st_tys' st) e0 ->
      wt_exp G (vars++st_tys' st) e ->
      typeof e0 = [ty] ->
      typeof e = [ty] ->
      fby_iteexp e0 e (ty, (ck, name)) st = (e', eqs', st') ->
      wt_exp G (vars++st_tys' st') e'.
  Proof.
    intros * Hwtc Hwt1 Hwt2 Hty1 Hty2 Hfby.
    unfold fby_iteexp in Hfby. destruct (is_constant e0); repeat inv_bind.
    - repeat constructor; simpl; try rewrite app_nil_r; auto.
    - repeat constructor; simpl; try rewrite app_nil_r; auto.
      2,3,5,6:repeat solve_incl; eapply init_var_for_clock_st_follows in H; repeat solve_st_follows.
      + apply init_var_for_clock_In in H.
        apply in_or_app, or_intror. unfold st_tys', idty.
        simpl_In. exists (x, (Op.bool_type, ck)); split; auto.
        simpl_In. exists (x, (Op.bool_type, ck, true)); split; auto.
        eapply st_follows_incl; eauto.
      + apply fresh_ident_In in H0.
        apply in_or_app, or_intror. unfold st_tys', idty.
        simpl_In. exists (x2, (ty, ck)); split; auto.
        simpl_In. exists (x2, (ty, ck, false)); split; auto.
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

  Fact fby_iteexp_wt_eq : forall G vars e0 e ty ck name e' eqs' st st',
      wt_clock (vars++st_tys' st) ck ->
      wt_exp G (vars++st_tys' st) e0 ->
      wt_exp G (vars++st_tys' st) e ->
      typeof e0 = [ty] ->
      typeof e = [ty] ->
      fby_iteexp e0 e (ty, (ck, name)) st = (e', eqs', st') ->
      Forall (wt_equation G (vars++st_tys' st')) eqs'.
  Proof.
    intros * Hwtc Hwt1 Hwt2 Hty1 Hty2 Hfby.
    unfold fby_iteexp in Hfby. destruct (is_constant e0); repeat inv_bind; auto.
    assert (wt_clock (vars ++ st_tys' st') ck) as Hwtck'.
    { repeat solve_incl; eapply init_var_for_clock_st_follows in H; repeat solve_st_follows. }
    constructor.
    - repeat constructor; simpl; try rewrite app_nil_r; auto.
      2:repeat solve_incl; eapply init_var_for_clock_st_follows in H; repeat solve_st_follows.
      + eapply add_whens_wt_exp; eauto.
        simpl. rewrite Op.type_init_type; auto.
      + eapply add_whens_typeof.
        simpl. rewrite Op.type_init_type; auto.
      + apply fresh_ident_In in H0.
        apply in_or_app, or_intror. unfold st_tys', idty.
        simpl_In. exists (x2, (ty, ck)); split; auto.
        simpl_In. exists (x2, (ty, ck, false)); split; auto.
    - unfold init_var_for_clock in H. destruct (find _ _) eqn:Hfind.
      + destruct p; inv H; auto.
      + destruct (fresh_ident _ _) eqn:Hfresh; inv H.
        repeat constructor; auto.
        * eapply add_whens_wt_exp; eauto.
          simpl. rewrite Op.type_true_const; auto.
        * eapply add_whens_wt_exp; eauto.
          simpl. rewrite Op.type_false_const; auto.
        * simpl. rewrite app_nil_r, add_whens_typeof; auto.
          simpl. rewrite Op.type_false_const; auto.
        * simpl. rewrite app_nil_r, add_whens_typeof; auto.
          simpl. rewrite Op.type_true_const; auto.
        * eapply fresh_ident_In in Hfresh.
          apply in_or_app, or_intror. unfold st_tys', idty.
          simpl_In. exists (x, (Op.bool_type, ck)); split; auto.
          simpl_In. exists (x, (Op.bool_type, ck, true)); split; auto.
          eapply st_follows_incl; eauto.
  Qed.

  Fact fby_equation_wt_eq : forall G vars to_cut eq eqs' st st',
      wt_equation G (vars++st_tys' st) eq ->
      fby_equation to_cut eq st = (eqs', st') ->
      Forall (wt_equation G (vars++st_tys' st')) eqs'.
  Proof.
    intros * Hwt Hfby.
    inv_fby_equation Hfby to_cut eq.
    destruct x2 as [ty [ck name]]; repeat inv_bind.
    assert (st_follows st x4) as Hfollows by (eapply fby_iteexp_st_follows with (ann:=(ty, (ck, name))) in H; eauto).
    destruct Hwt as [Hwt Hins]; inv Hwt; clear H4.
    inv H3; simpl in *; rewrite app_nil_r in *.
    inv H5; clear H4. inv H6; clear H5. inv H9; clear H6. inv H5.
    inv Hins; clear H11.
    assert (H':=H). eapply fby_iteexp_wt_eq in H; eauto.
    destruct (PS.mem _ _); repeat inv_bind; repeat constructor; simpl; auto.
    5,8:rewrite app_nil_r.
    - eapply fresh_ident_In in H0.
      apply in_or_app, or_intror. unfold st_tys', idty.
      simpl_In. exists (x5, (ty, ck)); split; auto.
      simpl_In. exists (x5, (ty, ck, false)); split; auto.
    - repeat solve_incl.
    - assert (incl (vars ++ st_tys' st) (vars ++ st_tys' st')) by repeat solve_incl; eauto.
    - eapply fby_iteexp_wt_exp in H'; eauto. repeat solve_incl.
    - eapply fby_iteexp_typeof with (ann:=(ty, (ck, name))) in H'.
      rewrite H'; simpl. constructor; auto.
      eapply fresh_ident_In in H0.
      apply in_or_app, or_intror. unfold st_tys', idty.
      simpl_In. exists (x5, (ty, ck)); split; auto.
      simpl_In. exists (x5, (ty, ck, false)); split; auto.
    - eapply fby_iteexp_typeof with (ann:=(ty, (ck, name))) in H'.
      rewrite H'; simpl. constructor; auto.
      assert (incl (vars ++ st_tys' st) (vars ++ st_tys' st')) by repeat solve_incl; eauto.
    - solve_forall; repeat solve_incl.
    - eapply fby_iteexp_wt_exp in H'; eauto.
  Qed.

  Fact fby_equations_wt_eq : forall G vars to_cut eqs eqs' st st',
      Forall (wt_equation G (vars++st_tys' st)) eqs ->
      fby_equations to_cut eqs st = (eqs', st') ->
      Forall (wt_equation G (vars++st_tys' st')) eqs'.
  Proof.
    induction eqs; intros * Hwt Hfby;
      unfold fby_equations in *; repeat inv_bind; simpl; auto.
    inv Hwt.
    apply Forall_app; split.
    - eapply fby_equation_wt_eq in H; eauto. solve_forall; repeat solve_incl.
    - assert (fby_equations to_cut eqs x1 = (concat x2, st')) as Hnorm.
      { unfold fby_equations. repeat inv_bind. repeat eexists; eauto.
        inv_bind; auto. }
      eapply IHeqs in Hnorm; eauto. solve_forall; repeat solve_incl; eauto.
  Qed.

  Fact fresh_ident_wt_clock' : forall vars ty cl b id st st',
      Forall (wt_clock vars) (st_clocks' st) ->
      wt_clock vars cl ->
      fresh_ident (ty, cl, b) st = (id, st') ->
      Forall (wt_clock vars) (st_clocks' st').
  Proof.
    intros * Hclocks Hwt Hfresh.
    apply fresh_ident_anns in Hfresh.
    unfold st_clocks' in *. rewrite Hfresh; simpl.
    constructor; auto.
  Qed.

  Fact fby_iteexp_wt_clock : forall vars e0 e ty ck name e' eqs' st st',
      wt_clock (vars++st_tys' st) ck ->
      Forall (wt_clock (vars ++ st_tys' st)) (st_clocks' st) ->
      fby_iteexp e0 e (ty, (ck, name)) st = (e', eqs', st') ->
      Forall (wt_clock (vars ++ st_tys' st')) (st_clocks' st').
  Proof.
    intros * Hwtc1 Hwtc2 Hfby.
    unfold fby_iteexp in Hfby. destruct (is_constant e0); repeat inv_bind; auto.
    assert (st_follows st x1) as Hfollows1 by (eapply init_var_for_clock_st_follows in H; eauto).
    assert (st_follows x1 st') as Hfollows2 by eauto.
    eapply fresh_ident_wt_clock' in H0; eauto. 2:repeat solve_incl.
    unfold init_var_for_clock in H. destruct (find _ _) eqn:Hfind.
    - destruct p; inv H. solve_forall; repeat solve_incl.
    - destruct (fresh_ident _ _) eqn:Hfresh.
      inv H.
      eapply fresh_ident_wt_clock' in Hfresh; eauto. solve_forall. 1,2:repeat solve_incl.
  Qed.

  Fact fby_equation_wt_clock : forall G vars to_cut eq eqs' st st',
      wt_equation G (vars++st_tys' st) eq ->
      Forall (wt_clock (vars ++ st_tys' st)) (st_clocks' st) ->
      fby_equation to_cut eq st = (eqs', st') ->
      Forall (wt_clock (vars ++ st_tys' st')) (st_clocks' st').
  Proof.
    intros * Hwt Hwtck Hfby.
    inv_fby_equation Hfby to_cut eq.
    destruct x2 as [ty [ck name]]; repeat inv_bind.
    assert (st_follows st x4) as Hfollows by (eapply fby_iteexp_st_follows with (ann:=(ty, (ck, name))) in H; eauto).
    assert (wt_clock (vars ++ st_tys' st) ck) as Hwtc.
    { destruct Hwt as [Hwt _]. inv Hwt; inv H3; inv H10; inv H3; auto. }
    eapply fby_iteexp_wt_clock in H; eauto.
    destruct (PS.mem _ _); repeat inv_bind; auto.
    eapply fresh_ident_wt_clock' in H0; eauto. solve_forall. 1,2:repeat solve_incl.
  Qed.

  Fact fby_equations_wt_clock : forall G vars to_cut eqs eqs' st st',
      Forall (wt_equation G (vars++st_tys' st)) eqs ->
      Forall (wt_clock (vars ++ st_tys' st)) (st_clocks' st) ->
      fby_equations to_cut eqs st = (eqs', st') ->
      Forall (wt_clock (vars ++ st_tys' st')) (st_clocks' st').
  Proof.
    induction eqs; intros * Hwt Hwtck Hfby;
      unfold fby_equations in *; repeat inv_bind; simpl; auto.
    inv Hwt.
    assert (H':=H). eapply fby_equation_wt_clock in H; eauto.
    assert (fby_equations to_cut eqs x1 = (concat x2, st')) as Hnorm.
    { unfold fby_equations. repeat inv_bind. repeat eexists; eauto.
      inv_bind; auto. }
      eapply IHeqs in Hnorm; eauto. solve_forall; repeat solve_incl; eauto.
  Qed.

  Lemma normfby_node_wt : forall G to_cut n Hunt,
      wt_node G n ->
      wt_node G (normfby_node to_cut n Hunt).
  Proof.
    intros * [Hclin [Hclout [Hclvars Heq]]].
    unfold normfby_node.
    repeat constructor; simpl; auto.
    - unfold wt_clocks in *.
      apply Forall_app. split.
      + solve_forall. unfold idty in *.
        solve_incl. repeat rewrite map_app. repeat solve_incl.
      + remember (fby_equations _ _ _) as res. symmetry in Heqres. destruct res as [eqs' st'].
        eapply fby_equations_wt_clock with (G:=G) in Heqres; eauto.
        * simpl. unfold st_clocks' in Heqres.
          unfold idty. solve_forall; simpl.
          repeat solve_incl.
          repeat rewrite map_app, app_assoc.
          eapply incl_appr'. reflexivity.
        * unfold st_clocks'. unfold st_tys'. rewrite init_st_anns, app_nil_r.
          repeat rewrite <- app_assoc. repeat rewrite <- map_app.
          solve_forall; repeat solve_incl. apply incl_map, incl_appr'. rewrite Permutation_app_comm; auto.
        * unfold st_clocks'. rewrite init_st_anns; simpl; constructor.
    - remember (fby_equations _ _ _) as res. symmetry in Heqres. destruct res as [eqs' st'].
      eapply fby_equations_wt_eq with (G:=G) (vars:=(idty (n_in n ++ n_vars n ++ n_out n))) in Heqres; eauto.
      + solve_forall; solve_incl.
        unfold st_tys'; repeat rewrite <- idty_app. apply incl_map.
        repeat rewrite <- app_assoc. apply incl_appr', incl_appr'.
        rewrite Permutation_app_comm. reflexivity.
      + solve_forall; repeat solve_incl.
  Qed.

  Lemma normfby_global_wt : forall G Hunt,
      wt_global G ->
      wt_global (normfby_global G Hunt).
  Proof.
    induction G; intros * Hwt; simpl; inv Hwt.
    - constructor.
    - constructor.
      + eapply IHG; eauto.
      + remember (normfby_node _ _) as n'. symmetry in Heqn'.
        subst.
        eapply normfby_node_wt; eauto.
        eapply iface_eq_wt_node; eauto.
        eapply normfby_global_eq.
      + eapply normfby_global_names; eauto.
  Qed.

  (** ** Conclusion *)

  Lemma normalize_global_wt : forall G Hwl G',
      wt_global G ->
      normalize_global G Hwl = Errors.OK G' ->
      wt_global G'.
  Proof.
    intros * Hwt Hnorm.
    unfold normalize_global in Hnorm.
    destruct (Caus.check_causality _); inv Hnorm.
    eapply normfby_global_wt, untuple_global_wt, Hwt.
  Qed.

End NTYPING.

Module NTypingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Syn : LSYNTAX Ids Op)
       (Caus : LCAUSALITY Ids Op Syn)
       (Typ : LTYPING Ids Op Syn)
       (Norm : NORMALIZATION Ids Op OpAux Syn Caus)
       <: NTYPING Ids Op OpAux Syn Caus Typ Norm.
  Include NTYPING Ids Op OpAux Syn Caus Typ Norm.
End NTypingFun.
