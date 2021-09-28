Require Import Omega.
From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import Fresh.
From Coq Require Import List. Import List.ListNotations. Open Scope list_scope.
From Velus Require Import Lustre.LSyntax Lustre.LTyping.
From Velus Require Import Lustre.Normalization.Normalization.

(** * Preservation of Typing through Normalization *)

Module Type NTYPING
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Syn : LSYNTAX Ids Op OpAux Cks)
       (Import Typ : LTYPING Ids Op OpAux Cks Syn)
       (Import Norm : NORMALIZATION Ids Op OpAux Cks Syn).
  Import Fresh Facts Tactics.

  (** ** Preservation of typeof *)

  Fact unnest_noops_exps_typesof: forall cks es es' eqs' st st',
      length cks = length es ->
      Forall (fun e => numstreams e = 1) es ->
      unnest_noops_exps cks es st = (es', eqs', st') ->
      typesof es' = typesof es.
  Proof.
    intros.
    repeat rewrite typesof_annots.
    erewrite unnest_noops_exps_annots; eauto.
  Qed.

  Fact unnest_exp_typeof : forall G e is_control es' eqs' st st',
      wl_exp G e ->
      unnest_exp G is_control e st = (es', eqs', st')  ->
      typesof es' = typeof e.
  Proof with eauto.
    intros * Hwl Hnorm.
    eapply unnest_exp_annot in Hnorm...
    rewrite typesof_annots, Hnorm, <- typeof_annot...
  Qed.

  Hint Resolve nth_In.
  Corollary mmap2_unnest_exp_typesof' :
    forall G is_control es es' eqs' st st',
      Forall (wl_exp G) es ->
      mmap2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      Forall2 (fun es' e => typesof es' = typeof e) es' es.
  Proof with eauto.
    intros * Hwl Hmap.
    eapply mmap2_unnest_exp_annots' in Hmap...
    clear Hwl.
    induction Hmap; constructor; eauto.
    rewrite typesof_annots, H, <- typeof_annot...
  Qed.

  Corollary mmap2_unnest_exp_typesof'' : forall G is_control es es' eqs' st st',
      Forall (wl_exp G) es ->
      mmap2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      Forall2 (fun e ty => typeof e = [ty]) (concat es') (typesof es).
  Proof.
    intros * Hwl Hmap.
    eapply mmap2_unnest_exp_annots'' in Hmap; eauto.
    rewrite typesof_annots, Forall2_map_2.
    eapply Forall2_impl_In; eauto. intros; simpl in *.
    rewrite typeof_annot, H1; auto.
  Qed.

  Corollary mmap2_mmap2_unnest_exp_typesof : forall G is_control tys (es : list (enumtag * list exp)) es' eqs' st st',
      Forall (fun es => Forall (wl_exp G) (snd es)) es ->
      Forall (fun es => typesof (snd es) = tys) es ->
      mmap2 (fun '(i, es) => bind2 (mmap2 (unnest_exp G is_control) es)
                                  (fun es' eqs' => ret (i, concat es', concat eqs'))) es st = (es', eqs', st') ->
      Forall (fun es0 => Forall2 (fun e ty => typeof e = [ty]) (snd es0) tys) es'.
  Proof.
    intros * Hwl Htys Hmap.
    eapply mmap2_values in Hmap.
    induction Hmap; inv Hwl; inv Htys; constructor; auto.
    destruct x, y, H as (?&?&?); repeat inv_bind.
    eapply mmap2_unnest_exp_typesof'' in H; eauto.
  Qed.

  (* Corollary mmap2_mmap2_unnest_exp_typesof' : forall G is_control tys es es' eqs' st st', *)
  (*     Forall (LiftO True (Forall (wl_exp G))) es -> *)
  (*     Forall (LiftO True (fun es => typesof es = tys)) es -> *)
  (*     mmap2 *)
  (*       (or_default_with *)
  (*          (ret (None, [])) *)
  (*          (fun es => bind2 *)
  (*                    (bind2 (mmap2 (unnest_exp G is_control) es) (fun es0 eqs => ret (concat es0, concat eqs))) *)
  (*                    (fun es' eqs'  => ret (Some es', eqs')))) es st = (es', eqs', st') -> *)
  (*     Forall (LiftO True (fun es0 => Forall2 (fun e ty => typeof e = [ty]) es0 tys)) es'. *)
  (* Proof. *)
  (*   intros * Hwl Htys Hmap. *)
  (*   eapply mmap2_values in Hmap. *)
  (*   induction Hmap; inv Hwl; inv Htys; constructor; auto. *)
  (*   destruct H as (?&?&?); repeat inv_bind. *)
  (*   destruct x; simpl in *; repeat inv_bind; simpl; auto. *)
  (*   eapply mmap2_unnest_exp_typesof'' in H; eauto. *)
  (* Qed. *)

  Corollary mmap2_unnest_exp_typesof :
    forall G is_control es es' eqs' st st',
      Forall (wl_exp G) es ->
      mmap2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      typesof (concat es') = typesof es.
  Proof.
    intros * Hwl Hmap.
    eapply mmap2_unnest_exp_annots in Hmap; eauto.
    rewrite typesof_annots, Hmap, <- typesof_annots; eauto.
  Qed.
  Hint Resolve mmap2_unnest_exp_typesof.

  Corollary unnest_exps_typesof : forall G es es' eqs' st st',
      Forall (wl_exp G) es ->
      unnest_exps G es st = (es', eqs', st') ->
      typesof es' = typesof es.
  Proof.
    intros * Hwl Hnorm.
    unfold unnest_exps in Hnorm; repeat inv_bind.
    eapply mmap2_unnest_exp_typesof in H; eauto.
  Qed.

  Fact fby_iteexp_typeof : forall e0 e ann e' eqs' st st',
      fby_iteexp e0 e ann st = (e', eqs', st') ->
      typeof e' = [fst ann].
  Proof.
    intros ?? [ty [ck name]] e' eqs' st st' Hfby.
    unfold fby_iteexp in Hfby.
    destruct (is_constant e0); repeat inv_bind; try reflexivity.
  Qed.

  Fact unnest_rhs_typeof : forall G e es' eqs' st st',
      wl_exp G e ->
      unnest_rhs G e st = (es', eqs', st') ->
      typesof es' = typeof e.
  Proof with eauto.
    intros * Hwl Hnorm.
    eapply unnest_rhs_annot in Hnorm...
    rewrite typesof_annots, Hnorm, <- typeof_annot...
  Qed.

  Corollary unnest_rhss_typesof : forall G es es' eqs' st st',
      Forall (wl_exp G) es ->
      unnest_rhss G es st = (es', eqs', st') ->
      typesof es' = typesof es.
  Proof with eauto.
    intros * Hwl Hnorm.
    eapply unnest_rhss_annots in Hnorm...
    rewrite typesof_annots, Hnorm, <- typesof_annots...
  Qed.

  (** ** A few additional tactics *)

  Definition st_tys (st : fresh_st (Op.type * clock)) := idty (st_anns st).

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
    | Hiface : global_iface_eq ?G1 ?G2, H : wt_clock (enums ?G1) _ ?ck |- wt_clock (enums ?G2) _ ?ck =>
      eapply iface_eq_wt_clock; eauto
    | H : wt_clock _ ?l1 ?cl |- wt_clock _ ?l2 ?cl =>
      eapply wt_clock_incl; [| eauto]
    | Hiface : global_iface_eq ?G1 ?G2, H : wt_nclock (enums ?G1) _ ?ck |- wt_nclock (enums ?G2) _ ?ck =>
      eapply iface_eq_wt_nclock; eauto
    | H : wt_nclock _ ?l1 ?cl |- wt_nclock _ ?l2 ?cl =>
      eapply wt_nclock_incl; [| eauto]
    | Hiface : global_iface_eq ?G1 ?G2, H : wt_exp ?G1 _ ?e |- wt_exp ?G2 _ ?e =>
      eapply iface_eq_wt_exp; eauto
    | H : wt_exp ?G ?l1 ?e |- wt_exp ?G ?l2 ?e =>
      eapply wt_exp_incl; [| eauto]
    | H : wt_equation ?G ?l1 ?eq |- wt_equation ?G ?l2 ?eq =>
      eapply wt_equation_incl; [| eauto]
    | Hiface : global_iface_eq ?G1 ?G2, H : wt_block ?G1 _ ?e |- wt_block ?G2 _ ?e =>
      eapply iface_eq_wt_block; eauto
    | H : wt_block ?G ?l1 ?eq |- wt_block ?G ?l2 ?eq =>
      eapply wt_block_incl; [| eauto]
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
    | H : incl ?l1 ?l2 |- incl (idty ?l1) (idty ?l2) =>
      eapply incl_map; eauto
    | H : In ?x ?l1 |- In ?x ?l2 =>
      assert (incl l1 l2); eauto
    end; auto.

  Hint Resolve in_combine_l in_combine_r.
  Hint Resolve incl_tl incl_appl incl_appr incl_app incl_refl.

  (** ** Preservation of wt through the first pass *)

  Section unnest_node_wt.
    Variable G1 : @global nolocal_top_block local_prefs.
    Variable G2 : @global nolocal_top_block norm1_prefs.

    Hypothesis Hiface : global_iface_eq G1 G2.

    Fact idents_for_anns_wt : forall vars anns ids st st',
        idents_for_anns anns st = (ids, st') ->
        Forall (fun '(ty, cl) => wt_nclock G2.(enums) (vars++st_tys st) cl) anns ->
        Forall (wt_exp G2 (vars++st_tys st')) (map (fun '(x, ann) => Evar x ann) ids).
    Proof.
      induction anns; intros ids st st' Hidents Hf;
        repeat inv_bind.
      - constructor.
      - inv Hf. destruct a as [ty [cl ?]]. repeat inv_bind.
        assert (Forall (fun '(_, cl) => wt_nclock G2.(enums) (vars ++ st_tys x0) cl) anns) as Hanns'.
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

    Fact idents_for_anns'_wt : forall vars anns ids st st',
        idents_for_anns' anns st = (ids, st') ->
        Forall (fun '(ty, cl) => wt_nclock G2.(enums) (vars++(idty ids)++st_tys st) cl) anns ->
        Forall (wt_exp G2 (vars++(idty ids)++st_tys st')) (map (fun '(x, ann) => Evar x ann) ids).
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

    Fact idents_for_anns'_wt_nclock : forall enums vars anns ids st st',
        idents_for_anns' anns st = (ids, st') ->
        Forall (fun '(ty, cl) => wt_nclock enums (vars++idty (anon_streams anns)++st_tys st) cl) anns ->
        Forall (wt_nclock enums (vars++idty (anon_streams (map snd ids))++st_tys st')) (map snd (map snd ids)).
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

    Fact unnest_fby_wt_exp : forall vars e0s es anns,
        Forall (wt_nclock G2.(enums) vars) (map snd anns) ->
        Forall (wt_exp G2 vars) e0s ->
        Forall (wt_exp G2 vars) es ->
        Forall2 (fun e0 a => typeof e0 = [a]) e0s (map fst anns) ->
        Forall2 (fun e a => typeof e = [a]) es (map fst anns) ->
        Forall (wt_exp G2 vars) (unnest_fby e0s es anns).
    Proof.
      intros * Hwtc Hwt1 Hwt2 Hty1 Hty2.
      unfold unnest_fby.
      assert (length e0s = length anns) as Hlen1 by (eapply Forall2_length in Hty1; solve_length).
      assert (length es = length anns) as Hlen2 by (eapply Forall2_length in Hty2; solve_length).
      solve_forall.
      constructor; simpl; try rewrite app_nil_r; eauto.
    Qed.

    Fact unnest_arrow_wt_exp : forall vars e0s es anns,
        Forall (wt_nclock G2.(enums) vars) (map snd anns) ->
        Forall (wt_exp G2 vars) e0s ->
        Forall (wt_exp G2 vars) es ->
        Forall2 (fun e0 a => typeof e0 = [a]) e0s (map fst anns) ->
        Forall2 (fun e a => typeof e = [a]) es (map fst anns) ->
        Forall (wt_exp G2 vars) (unnest_arrow e0s es anns).
    Proof.
      intros * Hwtc Hwt1 Hwt2 Hty1 Hty2.
      unfold unnest_arrow.
      assert (length e0s = length anns) as Hlen1 by (eapply Forall2_length in Hty1; solve_length).
      assert (length es = length anns) as Hlen2 by (eapply Forall2_length in Hty2; solve_length).
      solve_forall.
      constructor; simpl; try rewrite app_nil_r; eauto.
    Qed.

    Fact unnest_when_wt_exp : forall vars k ckid ty n es tys ck,
        In (ty, n) G2.(enums) ->
        In (ckid, Op.Tenum (ty, n)) vars ->
        k < n ->
        wt_nclock G2.(enums) vars ck ->
        Forall (wt_exp G2 vars) es ->
        Forall2 (fun e ty => typeof e = [ty]) es tys ->
        Forall (wt_exp G2 vars) (unnest_when ckid k es tys ck).
    Proof.
      intros * InE InV Hlt Hwtck Hwt Htys. unfold unnest_when.
      assert (length es = length tys) as Hlength by (eapply Forall2_length in Htys; eauto).
      rewrite Forall_map. apply Forall2_combine'.
      eapply Forall2_ignore2' with (ys:=tys) in Hwt; eauto.
      eapply Forall2_Forall2 in Hwt; eauto. clear Htys.
      eapply Forall2_impl_In; eauto. intros ? ? ? ? [? ?].
      repeat econstructor; simpl; eauto.
      rewrite app_nil_r; auto.
    Qed.

    Import Permutation.

    Fact unnest_merge_wt_exp : forall vars ckid ty n es tys ck,
        In (ty, n) G2.(enums) ->
        In (ckid, Op.Tenum (ty, n)) vars ->
        Permutation (map fst es) (seq 0 n) ->
        es <> [] ->
        wt_nclock G2.(enums) vars ck ->
        Forall (fun es => Forall (wt_exp G2 vars) (snd es)) es ->
        Forall (fun es => Forall2 (fun e ty => typeof e = [ty]) (snd es) tys) es ->
        Forall (wt_exp G2 vars) (unnest_merge (ckid, Op.Tenum (ty, n)) es tys ck).
    Proof with eauto.
      intros *; revert es. induction tys; intros * InE InV Perm Hnnil Hwtck Hwt Htys; simpl; constructor.
      - constructor; auto; try rewrite Forall_map.
        + erewrite map_map, map_ext; eauto. intros (?&?); auto.
        + contradict Hnnil. apply map_eq_nil in Hnnil; auto.
        + clear - Htys Hwt.
          rewrite Forall_forall in *; intros (?&?) Hin.
          specialize (Hwt _ Hin). specialize (Htys _ Hin). simpl in *. inv Htys; inv Hwt; simpl.
          constructor; auto.
        + clear - Htys.
          eapply Forall_impl; [|eauto]; intros (?&?) ?.
          inv H; simpl in *; subst; simpl. now rewrite app_nil_r.
      - eapply IHtys; eauto; try rewrite Forall_map.
        + erewrite map_map, map_ext; eauto. intros (?&?); auto.
        + contradict Hnnil. apply map_eq_nil in Hnnil; auto.
        + clear - Hwt. eapply Forall_impl; [|eauto]; intros (?&?) ?; simpl in *.
          inv H; simpl; auto.
        + clear - Htys. eapply Forall_impl; [|eauto]; intros (?&?) ?; simpl in *.
          inv H; auto.
    Qed.

    Fact unnest_case_Total_wt_exp : forall vars e ty n es tys ck,
        wt_exp G2 vars e ->
        typeof e = [Op.Tenum (ty, n)] ->
        In (ty, n) G2.(enums) ->
        Permutation (map fst es) (seq 0 n) ->
        es <> [] ->
        wt_nclock G2.(enums) vars ck ->
        Forall (fun es => Forall (wt_exp G2 vars) (snd es)) es ->
        Forall (fun es => Forall2 (fun e ty => typeof e = [ty]) (snd es) tys) es ->
        Forall (wt_exp G2 vars) (unnest_case e es None tys ck).
    Proof with eauto.
      intros *; revert es. induction tys; intros * WtE TypE InE Perm Hnnil Hwtck Hwt Htys; simpl; constructor.
      - econstructor; eauto; try rewrite Forall_map.
        + erewrite map_map, map_ext; eauto. intros (?&?); auto.
        + contradict Hnnil. apply map_eq_nil in Hnnil; auto.
        + clear - Htys Hwt.
          rewrite Forall_forall in *; intros (?&?) Hin.
          specialize (Hwt _ Hin). specialize (Htys _ Hin). simpl in *. inv Htys; inv Hwt; simpl.
          constructor; auto.
        + clear - Htys.
          eapply Forall_impl; [|eauto]; intros (?&?) ?.
          inv H; simpl in *; subst; simpl. now rewrite app_nil_r.
      - eapply IHtys; eauto; try rewrite Forall_map.
        + erewrite map_map, map_ext; eauto. intros (?&?); auto.
        + contradict Hnnil. apply map_eq_nil in Hnnil; auto.
        + clear - Hwt. eapply Forall_impl; [|eauto]; intros (?&?) ?; simpl in *.
          inv H; simpl; auto.
        + clear - Htys. eapply Forall_impl; [|eauto]; intros (?&?) ?; simpl in *.
          inv H; auto.
    Qed.

    Fact unnest_case_Default_wt_exp : forall vars e ty n es d tys ck,
        wt_exp G2 vars e ->
        typeof e = [Op.Tenum (ty, n)] ->
        In (ty, n) G2.(enums) ->
        incl (map fst es) (seq 0 n) ->
        NoDupMembers es ->
        es <> [] ->
        wt_nclock G2.(enums) vars ck ->
        Forall (fun es => Forall (wt_exp G2 vars) (snd es)) es ->
        Forall (fun es => Forall2 (fun e ty => typeof e = [ty]) (snd es) tys) es ->
        Forall (wt_exp G2 vars) d ->
        Forall2 (fun d ty => typeof d = [ty]) d tys ->
        Forall (wt_exp G2 vars) (unnest_case e es (Some d) tys ck).
    Proof with eauto.
      intros *; revert es d. induction tys; intros * WtE TypE InE Incl NoDup Hnnil Hwtck Hwt Htys Hwd Htyd; simpl; constructor.
      - eapply wt_EcaseDefault; eauto; try rewrite Forall_map.
        + erewrite map_map, map_ext; eauto. intros (?&?); auto.
        + erewrite fst_NoDupMembers, map_map, map_ext, <-fst_NoDupMembers; eauto. intros (?&?); auto.
        + contradict Hnnil. apply map_eq_nil in Hnnil; auto.
        + clear - Htys Hwt.
          rewrite Forall_forall in *; intros (?&?) Hin.
          specialize (Hwt _ Hin). specialize (Htys _ Hin). simpl in *. inv Htys; inv Hwt; simpl.
          constructor; auto.
        + clear - Htys.
          eapply Forall_impl; [|eauto]; intros (?&?) ?.
          inv H; simpl in *; subst; simpl. now rewrite app_nil_r.
        + inv Htyd; inv Hwd; auto.
        + inv Htyd; simpl. now rewrite app_nil_r.
      - eapply IHtys; eauto; try rewrite Forall_map.
        + erewrite map_map, map_ext; eauto. intros (?&?); auto.
        + erewrite fst_NoDupMembers, map_map, map_ext, <-fst_NoDupMembers; eauto. intros (?&?); auto.
        + contradict Hnnil. apply map_eq_nil in Hnnil; auto.
        + clear - Hwt. eapply Forall_impl; [|eauto]; intros (?&?) ?; simpl in *.
          inv H; simpl; auto.
        + clear - Htys. eapply Forall_impl; [|eauto]; intros (?&?) ?; simpl in *.
          inv H; auto.
        + inv Htyd; inv Hwd; auto.
        + inv Htyd; auto.
    Qed.

    Lemma unnest_noops_exps_wt : forall vars cks es es' eqs' st st' ,
        length es = length cks ->
        Forall normalized_lexp es ->
        Forall (fun e => numstreams e = 1) es ->
        Forall (wt_exp G2 (vars++st_tys st)) es ->
        unnest_noops_exps cks es st = (es', eqs', st') ->
        Forall (wt_exp G2 (vars++st_tys st')) es' /\
        Forall (wt_equation G2 (vars++st_tys st')) eqs'.
    Proof.
      unfold unnest_noops_exps.
      induction cks; intros * Hlen Hnormed Hnums Hwt Hunt; repeat inv_bind; simpl; auto.
      destruct es; simpl in *; inv Hlen; repeat inv_bind.
      inv Hwt. inv Hnums. inv Hnormed.
      assert (Forall (wt_exp G2 (vars ++ st_tys x2)) es) as Hes.
      { solve_forall. repeat solve_incl; eauto. }
      eapply IHcks in Hes as (Hes'&Heqs'). 2-4:eauto.
      2:repeat inv_bind; repeat eexists; eauto; inv_bind; eauto.
      unfold unnest_noops_exp in H.
      rewrite <-length_annot_numstreams in H6. singleton_length.
      destruct p as (?&?&?).
      split; simpl; try constructor; try (rewrite Forall_app; split); auto.
      1,2:destruct (is_noops_exp); repeat inv_bind; auto.
      + repeat solve_incl.
      + constructor. eapply fresh_ident_In in H.
        eapply in_or_app. right. rewrite st_anns_tys_In.
        eapply st_follows_incl in H; eauto. repeat solve_st_follows.
        constructor. eapply wt_exp_clockof in H4.
        rewrite normalized_lexp_no_fresh in H4; simpl in *; auto. repeat rewrite app_nil_r in H4.
        rewrite clockof_annot, Hsingl in H4. apply Forall_singl in H4.
        repeat solve_incl.
      + repeat constructor; auto; simpl; try rewrite app_nil_r.
        * repeat solve_incl.
        * rewrite typeof_annot, Hsingl; simpl.
          constructor; auto.
          eapply fresh_ident_In in H.
          eapply in_or_app. right. rewrite st_anns_tys_In.
          eapply st_follows_incl in H; eauto. repeat solve_st_follows.
    Qed.

    Fact mmap2_wt {A B} :
      forall vars (k : A -> Fresh (list exp * list equation) B) a es' eqs' st st',
        mmap2 k a st = (es', eqs', st') ->
        (forall st st' a es eqs', k a st = (es, eqs', st') -> st_follows st st') ->
        Forall (fun a => forall es' eqs' st0 st0',
                    k a st0 = (es', eqs', st0') ->
                    st_follows st st0 ->
                    st_follows st0' st' ->
                    Forall (wt_exp G2 vars) es' /\
                    Forall (wt_equation G2 vars) eqs') a ->
        Forall (wt_exp G2 vars) (concat es') /\
        Forall (wt_equation G2 vars) (concat eqs').
    Proof.
      intros vars k a.
      induction a; intros es' a2s st st' Hmap Hfollows Hforall;
        repeat inv_bind.
      - simpl; auto.
      - simpl. repeat rewrite Forall_app.
        inv Hforall. assert (Hk:=H). eapply H3 in H as [Hwt1 Hwt1'].
        2:reflexivity.
        2:eapply mmap2_st_follows; eauto; solve_forall.
        eapply IHa in H0 as [Hwt2 Hwt2']; eauto.
        solve_forall. eapply H1; eauto.
        etransitivity; eauto.
    Qed.

    Fact mmap2_wt' {A B} :
      forall vars (k : A -> Fresh (enumtag * list exp * list equation) B) a es' eqs' st st',
        mmap2 k a st = (es', eqs', st') ->
        (forall st st' a es eqs', k a st = (es, eqs', st') -> st_follows st st') ->
        Forall (fun a => forall n es' eqs' st0 st0',
                    k a st0 = (n, es', eqs', st0') ->
                    st_follows st st0 ->
                    st_follows st0' st' ->
                    Forall (wt_exp G2 vars) es' /\
                    Forall (wt_equation G2 vars) eqs') a ->
        Forall (wt_exp G2 vars) (concat (map snd es')) /\
        Forall (wt_equation G2 vars) (concat eqs').
    Proof with eauto.
      intros vars k a.
      induction a; intros es' a2s st st' Hmap Hfollows Hforall;
        repeat inv_bind; simpl; auto.
      inv Hforall.
      assert (H':=H). destruct x. eapply H3 in H' as [Hwc1 Hwc1']... 2,3:repeat solve_st_follows.
      eapply IHa in H0 as [Hwc2 Hwc2']...
      2:{ solve_forall. eapply H2 in H4... etransitivity... }
      repeat rewrite Forall_app. repeat split; eauto.
    Qed.

    Import Permutation.

    Hint Resolve iface_eq_wt_clock iface_eq_wt_exp.

    Fact unnest_reset_wt : forall vars e e' eqs' st st' ,
        (forall es' eqs' st0',
            st_follows st0' st' ->
            unnest_exp G1 true e st = (es', eqs', st0') ->
            Forall (wt_exp G2 (vars++st_tys st0')) es' /\
            Forall (wt_equation G2 (vars++st_tys st0')) eqs') ->
        wt_exp G1 (vars++st_tys st) e ->
        typeof e = [OpAux.bool_velus_type] ->
        unnest_reset (unnest_exp G1 true) e st = (e', eqs', st') ->
        typeof e' = [OpAux.bool_velus_type] /\
        wt_exp G2 (vars++st_tys st') e' /\
        Forall (wt_equation G2 (vars++st_tys st')) eqs'.
    Proof.
      intros * Hunwt Hwt Hty Hnorm.
      assert (st_follows st st') as Hfollows.
      { repeat solve_st_follows; destruct e; simpl; intros; eauto. }
      unnest_reset_spec; simpl in *; auto.
      1,2:assert (length l = 1).
      1,3:(eapply unnest_exp_length in Hk0; eauto;
           rewrite <- length_typeof_numstreams, Hty in Hk0; auto).
      1,2:singleton_length.
      - assert (Hk:=Hk0). eapply unnest_exp_typeof in Hk0; eauto; simpl in Hk0.
        specialize (Hunwt _ _ _ (Ker.st_follows_refl _) eq_refl) as (He&Heq); inv He; eauto.
        repeat split; eauto. congruence.
      - assert (Hk:=Hk0). eapply unnest_exp_annot in Hk0; eauto. simpl in Hk0. rewrite app_nil_r in Hk0.
        assert (Hk1:=Hk). eapply unnest_exp_fresh_incl in Hk1.
        assert (x = OpAux.bool_velus_type) as Hbool; subst.
        { rewrite Hk0 in Hhd.
          rewrite typeof_annot in *.
          destruct (annot e); simpl in *. inv Hty.
          subst; simpl in *. destruct l; try congruence.
        }
        assert (st_follows f st') as Hfollows1 by repeat solve_st_follows.
        specialize (Hunwt _ _ _ Hfollows1 eq_refl) as (He&Heq).
        repeat constructor.
        + eapply fresh_ident_In in Hfresh.
          apply in_or_app; right.
          rewrite st_anns_tys_In. exists x0. assumption.
        + apply wt_exp_clockof in Hwt.
          rewrite Hk0 in Hhd.
          rewrite clockof_annot in Hwt.
          rewrite typeof_annot in Hty.
          destruct (annot e); simpl in *. inv Hty.
          inv Hwt; simpl in *. do 2 solve_incl.
          rewrite <- app_assoc. apply incl_appr'.
          apply incl_app; repeat solve_incl.
          eapply fresh_ident_st_follows, st_follows_incl in Hfresh.
          unfold st_tys, idty. apply incl_map. etransitivity; eauto.
        + inv He; repeat solve_incl.
        + simpl; rewrite app_nil_r, typeof_annot, Hk0, <- typeof_annot, Hty.
          repeat constructor.
          eapply fresh_ident_In in Hfresh.
          apply in_or_app; right.
          unfold st_tys, idty. simpl_In; eexists; split; eauto. simpl. f_equal.
        + solve_forall; repeat solve_incl.
    Qed.

    Corollary unnest_resets_wt : forall vars es es' eqs' st st' ,
        Forall (fun e => forall es' eqs' st0 st0',
                    unnest_exp G1 true e st0 = (es', eqs', st0') ->
                    st_follows st st0 ->
                    st_follows st0' st' ->
                    Forall (wt_exp G2 (vars++st_tys st0')) es' /\
                    Forall (wt_equation G2 (vars++st_tys st0')) eqs') es ->
        Forall (wt_exp G1 (vars++st_tys st)) es ->
        Forall (fun e => typeof e = [OpAux.bool_velus_type]) es ->
        mmap2 (unnest_reset (unnest_exp G1 true)) es st = (es', eqs', st') ->
        Forall (fun e => typeof e = [OpAux.bool_velus_type]) es' /\
        Forall (wt_exp G2 (vars++st_tys st')) es' /\
        Forall (wt_equation G2 (vars++st_tys st')) (concat eqs').
    Proof.
      induction es; intros * F Wt Tys Map; inv F; inv Wt; inv Tys;
        repeat inv_bind; simpl in *; auto.
      assert (Hmap:=H0). eapply IHes in H0 as (Tys1&Wt1&Wt2); eauto.
      3:solve_forall; repeat solve_incl.
      2:{ eapply Forall_impl; [|eapply H2].
          intros. eapply H7 in H8; eauto.
          repeat solve_st_follows. }
      eapply unnest_reset_wt in H as (Tys2&Wt3&Wt4); eauto.
      repeat split; try constructor; auto.
      - repeat solve_incl.
      - apply Forall_app; split; auto.
        solve_forall; repeat solve_incl.
      - intros * Follows Un. eapply H1 in Un; eauto. 1,2:repeat solve_st_follows.
    Qed.

    Hint Resolve iface_eq_wt_enum.

    Fact unnest_controls_fst : forall (es : list (enumtag * list exp)) es' eqs' st st',
        mmap2 (fun '(i, es) => bind2 (mmap2 (unnest_exp G1 true) es)
                                  (fun es' eqs' => ret (i, concat es', concat eqs'))) es st = (es', eqs', st') ->
        map fst es' = map fst es.
    Proof.
      induction es as [|(?&?)]; intros * Hmmap;
        repeat inv_bind; simpl; f_equal; eauto.
    Qed.

    Lemma unnest_exp_wt : forall vars e is_control es' eqs' st st',
        wt_exp G1 (vars++st_tys st) e ->
        unnest_exp G1 is_control e st = (es', eqs', st') ->
        Forall (wt_exp G2 (vars++st_tys st')) es' /\
        Forall (wt_equation G2 (vars++st_tys st')) eqs'.
    Proof with eauto.
      Local Ltac solve_mmap2 :=
        solve_forall;
        match goal with
        | Hnorm : unnest_exp _ _ _ _ = _, H : context [unnest_exp _ _ _ _ = _ -> _] |- _ =>
          eapply H in Hnorm as [? ?]; eauto;
          [split|]; try solve_forall; repeat solve_incl
        end.

      induction e using exp_ind2; intros * Hwt Hnorm; simpl in *. 4-11:inv Hwt.
      - (* const *)
        repeat inv_bind...
      - (* enum *)
        repeat inv_bind...
      - (* var *)
        repeat inv_bind.
        repeat constructor...
      - (* unop *)
        repeat inv_bind.
        assert (length x = numstreams e) as Hlen by eauto.
        rewrite <- length_typeof_numstreams, H3 in Hlen; simpl in Hlen.
        singleton_length.
        assert (Hnorm:=H); eapply IHe in H as [Hwt1 Hwt1']; eauto.
        repeat econstructor...
        + inv Hwt1; eauto.
        + eapply unnest_exp_typeof in Hnorm; simpl in Hnorm; eauto.
          rewrite app_nil_r, H3 in Hnorm...
        + repeat solve_incl.
      - (* binop *)
        repeat inv_bind.
        assert (length x = numstreams e1) as Hlen1 by eauto.
        rewrite <- length_typeof_numstreams, H5 in Hlen1; simpl in Hlen1.
        assert (length x2 = numstreams e2) as Hlen2 by eauto.
        rewrite <- length_typeof_numstreams, H6 in Hlen2; simpl in Hlen2. repeat singleton_length.
        assert (Hnorm1:=H); eapply IHe1 in H as [Hwt1 Hwt1']; eauto.
        assert (Hnorm2:=H0); eapply IHe2 in H0 as [Hwt2 Hwt2']; eauto. 2:repeat solve_incl.
        repeat econstructor...
        + inv Hwt1. repeat solve_incl.
        + inv Hwt2...
        + eapply unnest_exp_typeof in Hnorm1; simpl in Hnorm1; eauto.
          rewrite app_nil_r, H5 in Hnorm1...
        + eapply unnest_exp_typeof in Hnorm2; simpl in Hnorm2; eauto.
          rewrite app_nil_r, H6 in Hnorm2...
        + repeat solve_incl.
        + apply Forall_app; split; auto.
          solve_forall. repeat solve_incl.
      - (* fby *)
        repeat inv_bind.
        assert (Hnorm1:=H1). eapply mmap2_wt with (vars0:=vars++st_tys x1) in H1 as [Hwt1 Hwt1']...
        assert (Hnorm2:=H2). eapply mmap2_wt with (vars0:=vars++st_tys x4) in H2 as [Hwt2 Hwt2']...
        2,3:solve_mmap2.
        repeat rewrite Forall_app. repeat split.
        3-4:solve_forall; repeat solve_incl.
        + eapply idents_for_anns_wt in H3...
          solve_forall; repeat solve_incl.
        + assert (Forall (wt_exp G2 (vars++st_tys st')) (unnest_fby (concat x2) (concat x6) a)) as Hwcfby.
          { eapply unnest_fby_wt_exp...
            1-3:solve_forall; repeat solve_incl.
            + eapply mmap2_unnest_exp_typesof'' in Hnorm1... 1,2:congruence.
            + eapply mmap2_unnest_exp_typesof'' in Hnorm2... 1,2:congruence. }
          remember (unnest_fby _ _ _) as fby.
          assert (length (concat x2) = length a) as Hlen1.
          { eapply mmap2_unnest_exp_length in Hnorm1...
            repeat simpl_length; erewrite <- map_length, <- typesof_annots; solve_length. }
          assert (length (concat x6) = length a) as Hlen2.
          { eapply mmap2_unnest_exp_length in Hnorm2...
            repeat simpl_length; erewrite <- map_length, <- typesof_annots; solve_length. }
          assert (length fby = length x5).
          { rewrite Heqfby, unnest_fby_length...
            eapply idents_for_anns_length in H3... }
          assert (Forall2 (fun '(ty, _) e => typeof e = [ty]) (map snd x5) fby) as Htys.
          { eapply idents_for_anns_values in H3; subst.
            specialize (unnest_fby_annot' _ _ _ Hlen1 Hlen2) as Hanns; eauto. clear - Hanns.
            eapply Forall2_swap_args. solve_forall.
            destruct a0 as [ty ck]; simpl in *. rewrite typeof_annot, H1; auto. }
          eapply mk_equations_Forall; solve_forall.
          repeat constructor; eauto.
          destruct a0 as [ty ck]; simpl in *. rewrite app_nil_r, H5.
          constructor; auto. eapply idents_for_anns_incl_ty in H3.
          apply in_or_app, or_intror, H3. unfold idty; simpl_In. exists (i, (ty, ck)); auto.
      - (* arrow *)
        repeat inv_bind.
        assert (Hnorm1:=H1). eapply mmap2_wt with (vars0:=vars++st_tys x1) in H1 as [Hwt1 Hwt1']...
        assert (Hnorm2:=H2). eapply mmap2_wt with (vars0:=vars++st_tys x4) in H2 as [Hwt2 Hwt2']...
        2,3:solve_mmap2.
        repeat rewrite Forall_app. repeat split.
        3-4:solve_forall; repeat solve_incl.
        + eapply idents_for_anns_wt in H3...
          solve_forall; repeat solve_incl.
        + assert (Forall (wt_exp G2 (vars++st_tys st')) (unnest_arrow (concat x2) (concat x6) a)) as Hwcfby.
          { eapply unnest_arrow_wt_exp...
            1-3:solve_forall; repeat solve_incl.
            + eapply mmap2_unnest_exp_typesof'' in Hnorm1... 1,2:congruence.
            + eapply mmap2_unnest_exp_typesof'' in Hnorm2... 1,2:congruence. }
          remember (unnest_arrow _ _ _) as fby.
          assert (length (concat x2) = length a) as Hlen1.
          { eapply mmap2_unnest_exp_length in Hnorm1...
            repeat simpl_length; erewrite <- map_length, <- typesof_annots; solve_length. }
          assert (length (concat x6) = length a) as Hlen2.
          { eapply mmap2_unnest_exp_length in Hnorm2...
            repeat simpl_length; erewrite <- map_length, <- typesof_annots; solve_length. }
          assert (length fby = length x5).
          { rewrite Heqfby, unnest_arrow_length...
            eapply idents_for_anns_length in H3... }
          assert (Forall2 (fun '(ty, _) e => typeof e = [ty]) (map snd x5) fby) as Htys.
          { eapply idents_for_anns_values in H3; subst.
            specialize (unnest_arrow_annot' _ _ _ Hlen1 Hlen2) as Hanns; eauto. clear - Hanns.
            eapply Forall2_swap_args. solve_forall.
            destruct a0 as [ty ck]; simpl in *. rewrite typeof_annot, H1; auto. }
          eapply mk_equations_Forall; solve_forall.
          repeat constructor; eauto.
          destruct a0 as [ty ck]; simpl in *. rewrite app_nil_r, H5.
          constructor; auto. eapply idents_for_anns_incl_ty in H3.
          apply in_or_app, or_intror, H3. unfold idty; simpl_In. exists (i, (ty, ck)); auto.
      - (* when *)
        destruct tn. repeat inv_bind.
        assert (Hnorm:=H0). eapply mmap2_wt with (vars0:=vars++st_tys st') in H0 as [Hwt1 Hwt1']; eauto.
        2:solve_mmap2.
        split; eauto.
        eapply unnest_when_wt_exp; eauto.
        + destruct Hiface as (Heq&_); rewrite <-Heq; eauto.
        + assert (incl (vars ++ st_tys st) (vars ++ st_tys st')) as Hincl by repeat solve_incl...
        + repeat solve_incl.
        + eapply mmap2_unnest_exp_typesof'' in Hnorm; eauto.
      - (* merge *)
        destruct tn. repeat inv_bind.
        assert (Hnorm1:=H0). eapply mmap2_wt' with (vars0:=vars++st_tys x2) in H0 as [Hwt1 Hwt1']; eauto.
        2:(intros; destruct a; repeat solve_st_follows).
        2:{ solve_forall. repeat inv_bind. eapply mmap2_wt in H7; eauto.
            solve_mmap2. }
        remember (unnest_merge _ _ _ _) as merges.
        assert (Forall (wt_exp G2 (vars++st_tys x2)) merges) as Hwt'.
        { subst. apply unnest_merge_wt_exp; auto.
          - destruct Hiface as (Heq&_); rewrite <-Heq; auto.
          - assert (incl (vars ++ st_tys st) (vars ++ st_tys x2)) by repeat solve_incl; eauto.
          - erewrite unnest_controls_fst; eauto.
          - apply mmap2_length_1 in Hnorm1.
            intro contra; subst. destruct es; simpl in *; try congruence.
            exfalso; eauto.
          - repeat solve_incl.
          - eapply Forall_concat in Hwt1; rewrite Forall_map in Hwt1; eauto.
          - eapply mmap2_mmap2_unnest_exp_typesof in Hnorm1...
            solve_forall.
        }
        destruct is_control; repeat inv_bind; repeat rewrite Forall_app; repeat split.
        1,2,5:solve_forall; repeat solve_incl.
        + specialize (idents_for_anns_incl_ty _ _ _ _ H0) as Hincl.
          apply idents_for_anns_wt with (vars:=vars) in H0...
          rewrite Forall_forall; intros.
          repeat simpl_In. inv H1... repeat solve_incl.
        + remember (unnest_merge _ _ _ _) as merges.
          assert (Forall2 (fun '(ty, _) e => annot e = [(ty, nck)]) (map snd x3) merges) as Htys.
          { eapply idents_for_anns_values in H0. rewrite H0, Forall2_map_1.
            subst; eapply unnest_merge_annot; eauto. } rewrite Forall2_map_1 in Htys.
          eapply Forall2_ignore1' with (xs:=x3) in Hwt'.
          2:{ subst. apply idents_for_anns_length in H0. rewrite map_length in H0.
              rewrite unnest_merge_length... }
          apply mk_equations_Forall; solve_forall; destruct a; simpl in *.
          repeat constructor... 1:repeat solve_incl.
          rewrite typeof_annot, H7, app_nil_r; simpl.
          constructor; auto.
          assert (In (i0, t) (idty x3)).
          { unfold idty. rewrite in_map_iff. exists (i0, (t, n0)); eauto. }
          eapply idents_for_anns_incl_ty in H0.
          eapply in_or_app, or_intror...
      - (* case (total) *)
        destruct tn. repeat inv_bind.
        assert (Hnorm0:=H1). eapply IHe in H1 as (Hwt1&Hwt1'); eauto.
        assert (Hnorm1:=H2). eapply mmap2_wt' with (vars0:=vars++st_tys x7) in H2 as (Hwt2&Hwt2'); eauto.
        2:(intros; destruct a; repeat solve_st_follows).
        2:{ solve_forall. repeat inv_bind. eapply mmap2_wt in H3; eauto.
            solve_mmap2. }
        remember (unnest_case _ _ _ _ _) as cases.
        assert (Forall (wt_exp G2 (vars++st_tys x7)) cases) as Hwt'.
        { assert (Hnorm0':=Hnorm0). eapply unnest_exp_length in Hnorm0'...
          rewrite <-length_typeof_numstreams, H6 in Hnorm0'; simpl in Hnorm0'.
          singleton_length. apply Forall_singl in Hwt1.
          subst. eapply unnest_case_Total_wt_exp; auto.
          - repeat solve_incl.
          - eapply unnest_exp_typeof in Hnorm0; eauto; simpl in *; rewrite app_nil_r in *.
            rewrite Hnorm0; eauto.
          - destruct Hiface as (Heq&_); rewrite <-Heq; auto.
          - erewrite unnest_controls_fst; eauto.
          - apply mmap2_length_1 in Hnorm1.
            intro contra; subst. destruct es; simpl in *; try congruence.
            exfalso; eauto.
          - repeat solve_incl.
          - eapply Forall_concat in Hwt2; rewrite Forall_map in Hwt2; eauto.
          - eapply mmap2_mmap2_unnest_exp_typesof in Hnorm1...
            solve_forall.
        }
        destruct is_control; repeat inv_bind; repeat rewrite Forall_app; repeat split; auto.
        1,4,5:solve_forall; repeat solve_incl.
        + specialize (idents_for_anns_incl_ty _ _ _ _ H1) as Hincl.
          apply idents_for_anns_wt with (vars:=vars) in H1...
          rewrite Forall_forall; intros.
          repeat simpl_In. inv H2... repeat solve_incl.
        + remember (unnest_case _ _ _ _ _) as cases.
          assert (Forall2 (fun '(ty, _) e => annot e = [(ty, nck)]) (map snd x4) cases) as Htys.
          { eapply idents_for_anns_values in H1. rewrite H1, Forall2_map_1.
            subst; eapply unnest_case_annot; eauto. } rewrite Forall2_map_1 in Htys.
          eapply Forall2_ignore1' with (xs:=x4) in Hwt'.
          2:{ subst. apply idents_for_anns_length in H1. rewrite map_length in H1.
              rewrite unnest_case_length... }
          apply mk_equations_Forall; solve_forall; destruct a; simpl in *.
          repeat constructor... 1:repeat solve_incl.
          rewrite typeof_annot, H4, app_nil_r; simpl.
          constructor; auto.
          assert (In (i0, t) (idty x4)).
          { unfold idty. rewrite in_map_iff. exists (i0, (t, n0)); eauto. }
          eapply idents_for_anns_incl_ty in H1.
          eapply in_or_app, or_intror...
      - (* case (default) *)
        destruct tn. repeat inv_bind.
        assert (Hnorm0:=H1). eapply IHe in H1 as (Hwt1&Hwt1')...
        assert (Hnorm1:=H2). eapply mmap2_wt' with (vars0:=vars++st_tys x7) in H2 as (Hwt2&Hwt2')...
        2:(intros; destruct a; repeat solve_st_follows).
        2:{ solve_forall. repeat inv_bind. eapply mmap2_wt in H11...
            solve_mmap2. }
        assert (Hnorm2:=H3). eapply mmap2_wt with (vars0:=vars++st_tys x7) in H3 as (Hwt3&Hwt3')...
        2:solve_mmap2.
        remember (unnest_case _ _ _ _ _) as cases.
        assert (Forall (wt_exp G2 (vars++st_tys x7)) cases) as Hwt'.
        { assert (Hnorm0':=Hnorm0). eapply unnest_exp_length in Hnorm0'...
          rewrite <-length_typeof_numstreams, H6 in Hnorm0'; simpl in Hnorm0'.
          singleton_length. apply Forall_singl in Hwt1.
          subst. eapply unnest_case_Default_wt_exp; auto.
          - repeat solve_incl.
          - eapply unnest_exp_typeof in Hnorm0; eauto; simpl in *; rewrite app_nil_r in *.
            rewrite Hnorm0; eauto.
          - destruct Hiface as (Heq&_); rewrite <-Heq; auto.
          - erewrite unnest_controls_fst; eauto.
          - erewrite fst_NoDupMembers, unnest_controls_fst, <-fst_NoDupMembers; eauto.
          - apply mmap2_length_1 in Hnorm1.
            intro contra; subst. destruct es; simpl in *; try congruence.
            exfalso; eauto.
          - repeat solve_incl.
          - eapply Forall_concat in Hwt2; rewrite Forall_map in Hwt2; eauto.
          - eapply mmap2_mmap2_unnest_exp_typesof in Hnorm1...
            solve_forall.
          - eapply mmap2_unnest_exp_typesof'' in Hnorm2; eauto.
        }
        destruct is_control; repeat inv_bind; repeat rewrite Forall_app; repeat split; auto.
        1,4-6:solve_forall; repeat solve_incl.
        + specialize (idents_for_anns_incl_ty _ _ _ _ H1) as Hincl.
          apply idents_for_anns_wt with (vars:=vars) in H1...
          rewrite Forall_forall; intros.
          repeat simpl_In. inv H2... repeat solve_incl.
        + remember (unnest_case _ _ _ _ _) as cases.
          assert (Forall2 (fun '(ty, _) e => annot e = [(ty, nck)]) (map snd x6) cases) as Htys.
          { eapply idents_for_anns_values in H1. rewrite H1, Forall2_map_1.
            subst; eapply unnest_case_annot; eauto. } rewrite Forall2_map_1 in Htys.
          eapply Forall2_ignore1' with (xs:=x6) in Hwt'.
          2:{ subst. apply idents_for_anns_length in H1. rewrite map_length in H1.
              rewrite unnest_case_length... }
          apply mk_equations_Forall; solve_forall; destruct a; simpl in *.
          repeat constructor... 1:repeat solve_incl.
          rewrite typeof_annot, H4, app_nil_r; simpl.
          constructor; auto.
          assert (In (i0, t) (idty x6)).
          { unfold idty. rewrite in_map_iff. exists (i0, (t, n0)); eauto. }
          eapply idents_for_anns_incl_ty in H1.
          eapply in_or_app, or_intror...
      - (* app *)
        repeat inv_bind.
        assert (st_follows x4 x7) as Hfollows by repeat solve_st_follows.
        eapply unnest_resets_wt in H3 as [Hwt2 [Hwt2' Hwt2'']]; simpl...
        2,3:solve_forall. 2:eapply H13 in H6; eauto. 2,3:repeat solve_incl.

        assert (Hnorm:=H1). eapply mmap2_wt with (vars0:=vars++st_tys x1) in H1 as [Hwt1 Hwt1']...
        2:solve_mmap2. clear H0.

        assert (length (find_node_incks G1 f) = length (concat x6)) as Hlen1.
        { unfold find_node_incks. rewrite H7.
          eapply Forall2_length in H8. rewrite map_length.
          eapply mmap2_unnest_exp_length in Hnorm; eauto. rewrite length_typesof_annots in H8.
          congruence. }
        assert (Forall (fun e : exp => numstreams e = 1) (concat x6)) as Hnum.
        { eapply mmap2_unnest_exp_numstreams; eauto. }

        split; [|constructor]; repeat rewrite Forall_app; repeat split.
        4,6:solve_forall; repeat solve_incl.
        + specialize (idents_for_anns'_incl_ty _ _ _ _ H4) as Hincl.
          eapply idents_for_anns'_wt with (vars:=vars) in H4... 1:solve_forall; repeat solve_incl.
          solve_forall; simpl in *...
          do 2 solve_incl. unfold idty. rewrite map_app, <- app_assoc.
          apply incl_appr', incl_app; [repeat solve_incl|apply incl_app;[apply incl_appr|apply incl_appl]].
          * eapply mmap2_unnest_exp_fresh_incl in Hnorm.
            unfold st_tys, idty in *. eapply incl_map; eauto.
            assert (incl (st_anns x1) (st_anns x4)) by repeat solve_incl.
            do 2 etransitivity...
          * eapply idents_for_anns'_anon_streams_incl, incl_map in H4.
            etransitivity. eapply H4.
            replace (map _ (without_names' x8)) with (map (fun xtc => (fst xtc, fst (snd xtc))) x8); auto.
            unfold without_names'; rewrite map_map; simpl.
            apply map_ext; intros [? [? [? ?]]]; auto.
        + destruct Hiface as (_&Hiface'). specialize (Hiface' f).
          rewrite H7 in Hiface'. inv Hiface'. destruct H3 as (?&?&Hin&Hout).
          repeat econstructor; eauto.
          * eapply unnest_noops_exps_wt with (vars:=vars) in H2 as (?&?); eauto.
            solve_forall; repeat solve_incl.
          * solve_forall; repeat solve_incl.
          * erewrite <-Hin, unnest_noops_exps_typesof, mmap2_unnest_exp_typesof; eauto.
          * eapply idents_for_anns'_values in H4. congruence.
          * eapply idents_for_anns'_wt_nclock with (vars:=vars) in H4.
            -- rewrite Forall_map in H4. solve_forall.
               solve_incl.
               rewrite <- app_assoc. apply incl_appr'.
               rewrite Permutation_app_comm. apply incl_appr'.
               unfold idty. rewrite map_app. apply incl_appr, incl_refl.
            -- assert (incl ((vars ++ st_tys st) ++ idty (fresh_ins es ++ anon_streams a)) (vars ++ idty (anon_streams a) ++ st_tys x7)).
               { rewrite <- app_assoc. apply incl_appr'.
                 unfold idty. rewrite map_app. apply incl_app; [repeat solve_incl|].
                 apply incl_app; [apply incl_appr|apply incl_appl]...
                 apply mmap2_unnest_exp_fresh_incl in Hnorm.
                 assert (incl (fresh_ins es) (st_anns x4)) by (repeat (etransitivity; eauto)).
                 eapply incl_map... etransitivity... }
               solve_forall; simpl in *; do 2 solve_incl.
        + simpl. rewrite app_nil_r.
          eapply idents_for_anns'_incl_ty in H4.
          clear - H4. solve_forall; simpl.
          apply in_or_app, or_intror, H4. unfold idty. simpl_In.
          exists (i, (t, (c, o))); auto.
        + eapply unnest_noops_exps_wt in H2 as (?&?); eauto.
          solve_forall; repeat solve_incl.
    Qed.

    Corollary mmap2_unnest_exp_wt : forall vars is_control es es' eqs' st st' ,
        Forall (wt_exp G1 (vars++st_tys st)) es ->
        mmap2 (unnest_exp G1 is_control) es st = (es', eqs', st') ->
        Forall (wt_exp G2 (vars++st_tys st')) (concat es') /\
        Forall (wt_equation G2 (vars++st_tys st')) (concat eqs').
    Proof.
      intros * Hwt Hmap.
      eapply mmap2_wt in Hmap; solve_forall; eauto.
      eapply unnest_exp_wt with (vars:=vars) in H1 as [? ?]; eauto.
      split. 1,2:solve_forall. 1,2,3:repeat solve_incl.
    Qed.

    Corollary unnest_exps_wt : forall vars es es' eqs' st st' ,
        Forall (wt_exp G1 (vars++st_tys st)) es ->
        unnest_exps G1 es st = (es', eqs', st') ->
        Forall (wt_exp G2 (vars++st_tys st')) es' /\
        Forall (wt_equation G2 (vars++st_tys st')) eqs'.
    Proof.
      intros * Hwt Hmap.
      unfold unnest_exps in Hmap; repeat inv_bind.
      eapply mmap2_unnest_exp_wt in H; eauto.
    Qed.

    Fact unnest_rhs_wt : forall vars e es' eqs' st st' ,
        wt_exp G1 (vars++st_tys st) e ->
        unnest_rhs G1 e st = (es', eqs', st') ->
        Forall (wt_exp G2 (vars++st_tys st')) es' /\
        Forall (wt_equation G2 (vars++st_tys st')) eqs'.
    Proof with eauto.
      intros * Hwt Hnorm.
      destruct e; unfold unnest_rhs in Hnorm;
        try (solve [eapply unnest_exp_wt in Hnorm; eauto]); inv Hwt.
      - (* fby *)
        repeat inv_bind.
        assert (Hnorm1:=H). eapply unnest_exps_wt in H as [Hwt1 Hwt1']...
        assert (Hnorm2:=H0). eapply unnest_exps_wt with (vars:=vars) in H0 as [Hwt2 Hwt2']...
        2:solve_forall; repeat solve_incl.
        repeat rewrite Forall_app; repeat split... 2,3:solve_forall; repeat solve_incl.
        eapply unnest_fby_wt_exp; eauto.
        1-2:solve_forall; repeat solve_incl.
        + unfold unnest_exps in Hnorm1; repeat inv_bind.
          eapply mmap2_unnest_exp_typesof'' in H... 1,2:congruence.
        + unfold unnest_exps in Hnorm2; repeat inv_bind.
          eapply mmap2_unnest_exp_typesof'' in H... 1,2:congruence.
      - (* arrow *)
        repeat inv_bind.
        assert (Hnorm1:=H). eapply unnest_exps_wt in H as [Hwt1 Hwt1']...
        assert (Hnorm2:=H0). eapply unnest_exps_wt with (vars:=vars) in H0 as [Hwt2 Hwt2']...
        2:solve_forall; repeat solve_incl.
        repeat rewrite Forall_app; repeat split... 2,3:solve_forall; repeat solve_incl.
        eapply unnest_arrow_wt_exp; eauto.
        1-2:solve_forall; repeat solve_incl.
        + unfold unnest_exps in Hnorm1; repeat inv_bind.
          eapply mmap2_unnest_exp_typesof'' in H... 1,2:congruence.
        + unfold unnest_exps in Hnorm2; repeat inv_bind.
          eapply mmap2_unnest_exp_typesof'' in H... 1,2:congruence.
      - (* app *)
        repeat inv_bind.
        assert (st_follows st x4) as Hfollows1 by repeat solve_st_follows.
        assert (st_follows x4 st') as Hfollows2 by repeat solve_st_follows.
        eapply unnest_resets_wt with (vars:=vars) in H1 as [Hwt3 [Hwt3' Hwt3'']]...
        2,3:solve_forall. 2:eapply unnest_exp_wt in H8; eauto. 2,3:repeat solve_incl.

        assert (Hnorm:=H). eapply unnest_exps_wt in H as [Hwt1 Hwt1']; eauto.
        rewrite Forall_app.

        assert (length (find_node_incks G1 i) = length x) as Hlen1.
        { unfold find_node_incks. rewrite H5.
          eapply Forall2_length in H6. rewrite map_length.
          eapply unnest_exps_length in Hnorm; eauto. rewrite length_typesof_annots in H6.
          congruence. }
        assert (Forall (fun e : exp => numstreams e = 1) x) as Hnum.
        { eapply unnest_exps_numstreams; eauto. }

        repeat split; auto.
        2:solve_forall; repeat solve_incl.
        repeat constructor.
        destruct Hiface as (_&Hiface'). specialize (Hiface' i).
        rewrite H5 in Hiface'. inv Hiface'. destruct H2 as (?&?&Hin&Hout).
        repeat econstructor; eauto.
        + eapply unnest_noops_exps_wt in H0 as (?&?); eauto.
          solve_forall; repeat solve_incl.
        + erewrite <-Hin, unnest_noops_exps_typesof, unnest_exps_typesof; eauto.
        + congruence.
        + eapply unnest_exps_fresh_incl in Hnorm.
          solve_forall; do 2 solve_incl.
          repeat rewrite idty_app; repeat rewrite <- app_assoc.
          repeat apply incl_app; auto.
          1,2:apply incl_appr, incl_appl; repeat solve_incl.
          unfold st_tys, idty; rewrite incl_map; do 2 etransitivity...
          eapply st_follows_incl; eauto. etransitivity; eauto.
        + apply Forall_app; split. 2:solve_forall; repeat solve_incl.
          eapply unnest_noops_exps_wt in H0 as (?&?); eauto.
          solve_forall; repeat solve_incl.
    Qed.

    Corollary unnest_rhss_wt : forall vars es es' eqs' st st' ,
        Forall (wt_exp G1 (vars++st_tys st)) es ->
        unnest_rhss G1 es st = (es', eqs', st') ->
        Forall (wt_exp G2 (vars++st_tys st')) es' /\
        Forall (wt_equation G2 (vars++st_tys st')) eqs'.
    Proof with eauto.
      intros * Hwt Hnorm.
      unfold unnest_rhss in Hnorm; repeat inv_bind.
      eapply mmap2_wt in H...
      solve_forall.
      eapply unnest_rhs_wt with (vars:=vars) in H2 as [? ?]...
      split. 1,2:solve_forall. 1,2,3:repeat solve_incl.
    Qed.

    Fact unnest_equation_wt_eq : forall vars eq eqs' st st' ,
        wt_equation G1 (vars++st_tys st) eq ->
        unnest_equation G1 eq st = (eqs', st') ->
        Forall (wt_equation G2 (vars++st_tys st')) eqs'.
    Proof with eauto.
      intros * Hwt Hnorm.
      destruct eq as [xs es]; simpl in Hnorm.
      repeat inv_bind. destruct Hwt.
      assert (Hnorm:=H). eapply unnest_rhss_wt in H as [Hwt Hwt']...
      apply Forall_app. split; eauto.
      assert (st_follows st st') as Hfollows by eauto.
      eapply unnest_rhss_typesof in Hnorm...
      rewrite <- Hnorm in H1.
      clear Hnorm. revert xs H1.
      induction x; intros xs H1; try constructor; simpl in H1.
      + inv H1; simpl; auto.
      + inv Hwt. repeat constructor...
        simpl. rewrite app_nil_r.
        repeat rewrite_Forall_forall.
        * rewrite app_length in H.
          rewrite firstn_length. rewrite H.
          rewrite length_typeof_numstreams.
          apply Nat.min_l. omega.
        * rewrite firstn_length in H2.
          rewrite PeanoNat.Nat.min_glb_lt_iff in H2; destruct H2 as [Hlen1 Hlen2].
          specialize (H1 a0 b _ _ _ Hlen2 eq_refl eq_refl).
          rewrite app_nth1 in H1. 2: rewrite length_typeof_numstreams...
          rewrite nth_firstn_1. 2,3:eauto.
          rewrite in_app_iff in *. destruct H1; auto.
          right. eapply st_follows_tys_incl...
      + inv Hwt. apply IHx...
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
    Qed.

    Lemma unnest_block_wt : forall vars d blocks' st st',
        wt_block G1 (vars++st_tys st) d ->
        unnest_block G1 d st = (blocks', st') ->
        Forall (wt_block G2 (vars++st_tys st')) blocks'.
    Proof.
      induction d using block_ind2; intros * Hwt Hun; inv Hwt; repeat inv_bind.
      - eapply unnest_equation_wt_eq in H; eauto.
        clear - H. rewrite Forall_map.
        eapply Forall_impl; [|eauto]; intros.
        constructor; auto.
      - assert (st_follows x0 st') as Hfollows by (repeat solve_st_follows).
        eapply unnest_reset_wt with (vars:=vars) in H1 as (Hty1&Hwt1&Hwt1'); eauto.
        2:{ intros. eapply unnest_exp_wt in H6; eauto; repeat solve_incl. }
        2:repeat solve_incl.
        apply Forall_app; split.
        + clear - H H2 H0 H4 Hty1 Hwt1 Hfollows.
          revert st x x0 Hfollows H H0 H2 H4.
          induction blocks; intros * Hfollows Hf Hmap Hwt; repeat inv_bind; simpl; auto;
            inv Hf; inv Hwt.
          rewrite map_app, Forall_app; split.
          * eapply H3 in H; eauto.
            rewrite Forall_map. eapply Forall_impl; [|eauto]; intros.
            econstructor; eauto.
            constructor; auto. repeat solve_incl.
          * eapply IHblocks; eauto. 2:repeat solve_incl.
            clear - H6 H. solve_forall; repeat solve_incl.
        + rewrite Forall_map.
          eapply Forall_impl; [|eauto]; intros; constructor; auto.
      - repeat (constructor; auto).
        + solve_forall. eapply iface_eq_wt_block; eauto.
        + eapply Forall_impl; [|eauto]. intros (?&(?&?)&?) ?. eapply iface_eq_wt_clock; eauto.
        + solve_forall.
    Qed.

    Corollary unnest_blocks_wt_block : forall vars blocks blocks' st st' ,
        Forall (wt_block G1 (vars++st_tys st)) blocks ->
        unnest_blocks G1 blocks st = (blocks', st') ->
        Forall (wt_block G2 (vars++st_tys st')) blocks'.
    Proof with eauto.
      induction blocks; intros * Hwt Hnorm;
        unfold unnest_blocks in Hnorm;
        repeat inv_bind; simpl; auto.
      inv Hwt; apply Forall_app. split.
      - eapply unnest_block_wt in H...
        solve_forall; repeat solve_incl.
      - assert (unnest_blocks G1 blocks x1 = (concat x2, st')) as Hnorm.
        { unfold unnest_blocks; repeat inv_bind; eauto. }
        eapply IHblocks in Hnorm...
        solve_forall; repeat solve_incl.
    Qed.

    (** ** Preservation of wt_clock *)

    Definition st_clocks (st : fresh_st (Op.type * clock)) : list clock :=
      map (fun '(_, (_, cl)) => cl) (st_anns st).

    Fact fresh_ident_wt_clock : forall enums pref hint vars ty cl id st st',
        Forall (wt_clock enums vars) (st_clocks st) ->
        wt_clock enums vars cl ->
        fresh_ident pref hint (ty, cl) st = (id, st') ->
        Forall (wt_clock enums vars) (st_clocks st').
    Proof.
      intros * Hclocks Hwt Hfresh.
      apply fresh_ident_anns in Hfresh.
      unfold st_clocks in *. setoid_rewrite Hfresh; simpl.
      constructor; auto.
    Qed.

    Corollary idents_for_anns_wt_clock : forall enums vars anns ids st st',
        Forall (wt_clock enums vars) (st_clocks st) ->
        Forall (wt_nclock enums vars) (map snd anns) ->
        idents_for_anns anns st = (ids, st') ->
        Forall (wt_clock enums vars) (st_clocks st').
    Proof.
      induction anns; intros ids st st' Hclocks Hwt Hidents;
        repeat inv_bind.
      - assumption.
      - inv Hwt. destruct a as [ty [cl ?]]. repeat inv_bind.
        eapply IHanns in H0; eauto.
        inv H1.
        eapply fresh_ident_wt_clock; eauto.
    Qed.

    Fact reuse_ident_wt_clock : forall enums vars ty cl id st st',
        Forall (wt_clock enums vars) (st_clocks st) ->
        wt_clock enums vars cl ->
        reuse_ident id (ty, cl) st = (tt, st') ->
        Forall (wt_clock enums vars) (st_clocks st').
    Proof.
      intros * Hclocks Hwt Hfresh.
      apply reuse_ident_anns in Hfresh.
      unfold st_clocks in *. setoid_rewrite Hfresh; simpl.
      constructor; auto.
    Qed.

    Corollary idents_for_anns'_wt_clock : forall enums vars anns ids st st' ,
        Forall (wt_clock enums vars) (st_clocks st) ->
        Forall (wt_nclock enums vars) (map snd anns) ->
        idents_for_anns' anns st = (ids, st') ->
        Forall (wt_clock enums vars) (st_clocks st').
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

    Fact mmap2_wt_clock {A A1 A2 : Type} :
      forall enums vars (k : A -> Unnesting.FreshAnn (A1 * A2)) a a1s a2s st st',
        Forall (wt_clock enums (vars++st_tys st)) (st_clocks st) ->
        mmap2 k a st = (a1s, a2s, st') ->
        (forall st st' a es a2s, k a st = (es, a2s, st') -> st_follows st st') ->
        Forall (fun a => forall a1s a2s st0 st0',
                    Forall (wt_clock enums (vars++st_tys st0)) (st_clocks st0) ->
                    k a st0 = (a1s, a2s, st0') ->
                    st_follows st st0 ->
                    st_follows st0' st' ->
                    Forall (wt_clock enums (vars++st_tys st0')) (st_clocks st0')) a ->
        Forall (wt_clock enums (vars++st_tys st')) (st_clocks st').
    Proof with eauto.
      induction a; intros a1s a2s st st' Hclocks Hmap Hfollows Hf;
        repeat inv_bind...
      inv Hf.
      specialize (H3 _ _ _ _ Hclocks H).
      eapply IHa in H3...
      - reflexivity.
      - eapply mmap2_st_follows...
        solve_forall...
      - solve_forall.
        eapply H2 in H5...
        etransitivity...
    Qed.

    Fact unnest_reset_wt_clock : forall vars e e' eqs' st st' ,
        (forall es' eqs' st0',
            st_follows st0' st' ->
            unnest_exp G1 true e st = (es', eqs', st0') ->
            Forall (wt_clock G2.(enums) (vars++st_tys st0')) (st_clocks st0')) ->
        wt_exp G1 (vars++st_tys st) e ->
        Forall (wt_clock G2.(enums) (vars++st_tys st)) (st_clocks st) ->
        unnest_reset (unnest_exp G1 true) e st = (e', eqs', st') ->
        Forall (wt_clock G2.(enums) (vars++st_tys st')) (st_clocks st').
    Proof with eauto.
      intros * Hkck Hwt Hclocks Hnorm.
      unnest_reset_spec; simpl in *; eauto. eapply Hkck; eauto; reflexivity.
      assert (Forall (wt_clock G2.(enums) (vars++st_tys st')) (clockof e)) as Hwtck.
      { eapply wt_exp_clockof in Hwt.
        assert (Hk:=Hk0). eapply unnest_exp_fresh_incl in Hk0.
        solve_forall; do 2 solve_incl. rewrite <- app_assoc.
        apply incl_app; [repeat solve_incl|apply incl_appr, incl_app].
        repeat solve_incl. unfold st_tys, idty. apply incl_map.
        etransitivity; eauto. }
      eapply fresh_ident_wt_clock in Hfresh...
      - assert (st_follows f st') as Hfollows by repeat solve_st_follows.
        specialize (Hkck _ _ _ Hfollows eq_refl).
        solve_forall; repeat solve_incl.
      - assert (Hk:=Hk0). eapply unnest_exp_annot in Hk0; eauto.
        rewrite clockof_annot, <- Hk0 in Hwtck.
        destruct l; simpl in *. 1:inv Hhd; constructor.
        destruct (annot e0); simpl in *. inv Hhd; constructor.
        subst; simpl in *.
        inv Hwtck. repeat solve_incl.
    Qed.

    Fact unnest_resets_wt_clock : forall vars es es' eqs' st st' ,
        Forall (fun e => forall es' eqs' st0 st0',
                    Forall (wt_clock G2.(enums) (vars++st_tys st0)) (st_clocks st0) ->
                    unnest_exp G1 true e st0 = (es', eqs', st0') ->
                    st_follows st st0 ->
                    st_follows st0' st' ->
                    Forall (wt_clock G2.(enums) (vars++st_tys st0')) (st_clocks st0')) es ->
        Forall (wt_exp G1 (vars++st_tys st)) es ->
        Forall (wt_clock G2.(enums) (vars++st_tys st)) (st_clocks st) ->
        mmap2 (unnest_reset (unnest_exp G1 true)) es st = (es', eqs', st') ->
        Forall (wt_clock G2.(enums) (vars++st_tys st')) (st_clocks st').
    Proof.
      induction es; intros * F Wt WtC Map; simpl in *;
        inv F; inv Wt; repeat inv_bind; auto.
      assert (Res:=H). eapply unnest_reset_wt_clock in H; eauto.
      2:intros * Follows Un; eapply H1; eauto; repeat solve_st_follows.
      eapply IHes in H; eauto; solve_forall; repeat solve_incl.
      eapply H9 in H6; eauto. repeat solve_st_follows.
    Qed.

    Lemma unnest_noops_exps_wt_clock : forall vars cks es es' eqs' st st' ,
        length es = length cks ->
        Forall normalized_lexp es ->
        Forall (fun e => numstreams e = 1) es ->
        Forall (wt_exp G2 (vars++st_tys st)) es ->
        Forall (wt_clock G2.(enums) (vars++st_tys st)) (st_clocks st) ->
        unnest_noops_exps cks es st = (es', eqs', st') ->
        Forall (wt_clock G2.(enums) (vars++st_tys st')) (st_clocks st').
    Proof.
      unfold unnest_noops_exps.
      induction cks; intros * Hlen Hnormed Hnum Hwt1 Hwt2 Hunt; repeat inv_bind; simpl; auto.
      destruct es; simpl in *; inv Hlen; repeat inv_bind.
      inv Hnormed. inv Hnum. inv Hwt1.
      eapply IHcks with (st:=x2); eauto.
      solve_forall; repeat solve_incl; eapply unnest_noops_exp_st_follows in H; eauto.
      2:repeat inv_bind; repeat eexists; eauto; inv_bind; eauto.
      clear H0 H1.
      rewrite <-length_annot_numstreams in H6. singleton_length. destruct p as (?&?&?).
      unfold unnest_noops_exp in H. rewrite Hsingl in H; simpl in H.
      destruct (is_noops_exp a e); simpl in *; repeat inv_bind; auto.
      eapply fresh_ident_wt_clock; eauto. solve_forall; repeat solve_incl.
      eapply wt_exp_clockof in H8.
      rewrite normalized_lexp_no_fresh in H8; auto. simpl in H8; rewrite app_nil_r in H8.
      rewrite clockof_annot, Hsingl in H8; inv H8.
      repeat solve_incl.
    Qed.

    Fact unnest_exp_wt_clock : forall vars e is_control es' eqs' st st' ,
        wt_exp G1 (vars++st_tys st) e ->
        Forall (wt_clock G2.(enums) (vars++st_tys st)) (st_clocks st) ->
        unnest_exp G1 is_control e st = (es', eqs', st') ->
        Forall (wt_clock G2.(enums) (vars++st_tys st')) (st_clocks st').
    Proof with eauto.
      induction e using exp_ind2; intros is_control es' eqs' st st' Hwt Hclocks Hnorm;
        repeat inv_bind; inv Hwt; eauto.
      Ltac solve_mmap2' :=
        solve_forall;
        match goal with
        | Hnorm : unnest_exp _ _ _ _ = _, Hf : forall (_ : bool), _ |- Forall _ ?l =>
          eapply Hf in Hnorm; eauto
        end; repeat solve_incl.
      - (* binop *)
        eapply IHe2 in H0...
        repeat solve_incl.
      - (* fby *)
        assert (st_follows x4 st') as Hfollows by repeat solve_st_follows.
        assert (Hnorm:=H1). eapply mmap2_wt_clock in H1... 2:solve_mmap2'.
        assert (Hnorm1:=H2). eapply mmap2_wt_clock in H2... 2:solve_mmap2'.
        eapply idents_for_anns_wt_clock in H3... 2:solve_forall; repeat solve_incl.
        solve_forall; repeat solve_incl.
      - (* arrow *)
        assert (st_follows x4 st') as Hfollows by repeat solve_st_follows.
        assert (Hnorm:=H1). eapply mmap2_wt_clock in H1... 2:solve_mmap2'.
        assert (Hnorm1:=H2). eapply mmap2_wt_clock in H2... 2:solve_mmap2'.
        eapply idents_for_anns_wt_clock in H3... 2:solve_forall; repeat solve_incl.
        solve_forall; repeat solve_incl.
      - (* when *)
        repeat inv_bind.
        eapply mmap2_wt_clock in H0...
        rewrite Forall_forall in *; intros...
        eapply H in H3... eapply H7 in H1... repeat solve_incl.
      - (* merge *)
        repeat inv_bind.
        assert (Hnorm1:=H0). eapply mmap2_wt_clock in H0... 2:(intros; destruct a; repeat solve_st_follows).
        2:{ solve_forall; repeat inv_bind. eapply mmap2_wt_clock in H8... solve_mmap2'. }
        destruct is_control; repeat inv_bind...
        eapply idents_for_anns_wt_clock in H1...
        2:{ rewrite map_map; simpl. solve_forall; repeat solve_incl. }
        solve_forall; repeat solve_incl.
      - (* case (total) *)
        repeat inv_bind.
        assert (Hnorm0:=H1). eapply IHe in H1...
        assert (Hnorm1:=H2). eapply mmap2_wt_clock in H2... 2:(intros; destruct a; repeat solve_st_follows).
        2:{ solve_forall; repeat inv_bind. eapply mmap2_wt_clock in H11... solve_mmap2'. }
        destruct is_control; repeat inv_bind...
        eapply idents_for_anns_wt_clock in H3...
        2:{ rewrite map_map; simpl. solve_forall; repeat solve_incl. }
        solve_forall; repeat solve_incl.
      - (* case (default) *)
        repeat inv_bind.
        assert (Hnorm0:=H1). eapply IHe in H1...
        assert (Hnorm1:=H2). eapply mmap2_wt_clock in H2... 2:(intros; destruct a; repeat solve_st_follows).
        2:{ solve_forall; repeat inv_bind. eapply mmap2_wt_clock in H13... solve_mmap2'. }
        assert (Hnorm2:=H3). eapply mmap2_wt_clock in H3... 2:solve_mmap2'.
        destruct is_control; repeat inv_bind...
        eapply idents_for_anns_wt_clock in H4...
        2:{ rewrite map_map; simpl. solve_forall; repeat solve_incl. }
        solve_forall; repeat solve_incl.
      - (* app *)
        assert (st_follows x4 x7) as Hfollows by repeat solve_st_follows.
        assert (Forall (wt_clock G2.(enums) (vars ++ st_tys x1)) (st_clocks x1)) as Hck1.
        { repeat inv_bind. eapply mmap2_wt_clock in H1... solve_mmap2'. }
        assert (Forall (wt_clock G2.(enums) (vars ++ st_tys x4)) (st_clocks x4)) as Hck2.
        { eapply unnest_noops_exps_wt_clock in H2; eauto.
          + unfold find_node_incks. rewrite H11.
            eapply Forall2_length in H12. rewrite map_length.
            eapply mmap2_unnest_exp_length in H1; eauto. rewrite length_typesof_annots in H12.
            congruence.
          + eapply mmap2_unnest_exp_numstreams; eauto.
          + eapply mmap2_unnest_exp_wt. 2:eauto. eauto.
        }

        eapply unnest_resets_wt_clock in H3; simpl; eauto. 2:solve_mmap2'.
        2:solve_forall; repeat solve_incl.
        eapply idents_for_anns'_wt_clock in H4...
        solve_forall; repeat solve_incl.
        rewrite Forall_map. solve_forall; do 2 solve_incl.
        rewrite <- app_assoc. apply incl_appr', incl_app; repeat solve_incl.
        unfold st_tys, idty; apply incl_map, incl_app.
        + eapply mmap2_unnest_exp_fresh_incl in H1.
          etransitivity... repeat solve_incl.
        + apply idents_for_anns'_fresh_incl in H4...
    Qed.

    Corollary unnest_exps_wt_clock : forall vars es es' eqs' st st' ,
        Forall (wt_exp G1 (vars++st_tys st)) es ->
        Forall (wt_clock G2.(enums) (vars++st_tys st)) (st_clocks st) ->
        unnest_exps G1 es st = (es', eqs', st') ->
        Forall (wt_clock G2.(enums) (vars++st_tys st')) (st_clocks st').
    Proof.
      intros vars es es' eqs' st st' Hwt Hclocks Hnorm.
      unfold unnest_exps in Hnorm. repeat inv_bind.
      eapply mmap2_wt_clock in H; eauto.
      solve_forall.
      assert (st_follows st0 st0') by eauto.
      eapply unnest_exp_wt_clock with (vars:=vars) in H3; repeat solve_incl.
      - solve_forall; solve_incl.
      - solve_forall; solve_incl.
    Qed.

    Fact unnest_rhs_wt_clock : forall vars e es' eqs' st st' ,
        wt_exp G1 (vars++st_tys st) e ->
        Forall (wt_clock G2.(enums) (vars++st_tys st)) (st_clocks st) ->
        unnest_rhs G1 e st = (es', eqs', st') ->
        Forall (wt_clock G2.(enums) (vars++st_tys st')) (st_clocks st').
    Proof with eauto.
      intros * Hwt Hclocks Hnorm.
      destruct e; unfold unnest_rhs in Hnorm;
        try eapply unnest_exp_wt_clock in Hnorm; eauto; repeat inv_bind. 3:inv Hwt.
      - (* fby *)
        inv Hwt.
        assert (Hnorm:=H). eapply unnest_exps_wt_clock in H...
        assert (Hnorm1:=H0). eapply unnest_exps_wt_clock in H0...
        solve_forall; repeat solve_incl.
      - (* arrow *)
        inv Hwt.
        assert (Hnorm:=H). eapply unnest_exps_wt_clock in H...
        assert (Hnorm1:=H0). eapply unnest_exps_wt_clock in H0...
        solve_forall; repeat solve_incl.
      - (* app *)
        assert (st_follows x4 st') as Hfollows by repeat solve_st_follows.
        assert (Forall (wt_clock G2.(enums) (vars ++ st_tys x1)) (st_clocks x1)) as Hck1.
        { repeat inv_bind. eapply unnest_exps_wt_clock in H... }
        assert (Forall (wt_clock G2.(enums) (vars ++ st_tys x4)) (st_clocks x4)) as Hck2.
        { clear H1. repeat inv_bind.
          eapply unnest_noops_exps_wt_clock in H0; eauto.
          + unfold find_node_incks. rewrite H8.
            eapply Forall2_length in H9. rewrite map_length.
            eapply unnest_exps_length in H; eauto. rewrite length_typesof_annots in H9.
            congruence.
          + eapply unnest_exps_numstreams; eauto.
          + eapply unnest_exps_wt in H as (?&?); eauto.
        }
        eapply unnest_resets_wt_clock in H1; eauto. 2:solve_forall; repeat solve_incl.
        eapply Forall_forall. intros. eapply unnest_exp_wt_clock in H4; eauto.
        eapply Forall_forall in H7; eauto. repeat solve_incl.
    Qed.

    Corollary unnest_rhss_wt_clock : forall vars es es' eqs' st st' ,
        Forall (wt_exp G1 (vars++st_tys st)) es ->
        Forall (wt_clock G2.(enums) (vars++st_tys st)) (st_clocks st) ->
        unnest_rhss G1 es st = (es', eqs', st') ->
        Forall (wt_clock G2.(enums) (vars++st_tys st')) (st_clocks st').
    Proof.
      intros * Hwt Hclocks Hnorm.
      unfold unnest_rhss in Hnorm. repeat inv_bind.
      eapply mmap2_wt_clock in H; eauto.
      solve_forall. eapply unnest_rhs_wt_clock in H3; eauto.
      repeat solve_incl.
    Qed.

    Fact unnest_equation_wt_clock : forall vars eq eqs' st st' ,
        wt_equation G1 (vars++st_tys st) eq ->
        Forall (wt_clock G2.(enums) (vars++st_tys st)) (st_clocks st) ->
        unnest_equation G1 eq st = (eqs', st') ->
        Forall (wt_clock G2.(enums) (vars++st_tys st')) (st_clocks st').
    Proof.
      intros * Hwt Hclocks Hnorm.
      destruct eq; repeat inv_bind.
      destruct Hwt.
      eapply unnest_rhss_wt_clock in H; eauto.
    Qed.

    Fact unnest_block_wt_clock : forall vars d blocks' st st' ,
        wt_block G1 (vars++st_tys st) d ->
        Forall (wt_clock G2.(enums) (vars++st_tys st)) (st_clocks st) ->
        unnest_block G1 d st = (blocks', st') ->
        Forall (wt_clock G2.(enums) (vars++st_tys st')) (st_clocks st').
    Proof.
      induction d using block_ind2; intros * Hwt Hcks Hnorm; inv Hwt;
        repeat inv_bind.
      - eapply unnest_equation_wt_clock; eauto.
      - assert (Forall (wt_clock G2.(enums) (vars ++ st_tys x0)) (st_clocks x0)) as Hcks'.
        { clear - Hcks H H0 H2. revert st x x0 H Hcks H0 H2.
          induction blocks; intros; inv H; inv H2; repeat inv_bind; auto.
          eapply IHblocks in H0; eauto. solve_forall; repeat solve_incl.
        }
        eapply unnest_reset_wt_clock in H1; eauto.
        2:repeat solve_incl.
        intros; eapply unnest_exp_wt_clock in H6; eauto. repeat solve_incl.
      - solve_forall.
    Qed.

    Corollary unnest_blocks_wt_clock : forall vars blocks blocks' st st' ,
        Forall (wt_block G1 (vars++st_tys st)) blocks ->
        Forall (wt_clock G2.(enums) (vars++st_tys st)) (st_clocks st) ->
        unnest_blocks G1 blocks st = (blocks', st') ->
        Forall (wt_clock G2.(enums) (vars++st_tys st')) (st_clocks st').
    Proof.
      induction blocks; intros * Hwt Hclocks Hnorm;
        unfold unnest_blocks in Hnorm; repeat inv_bind.
      - assumption.
      - inv Hwt.
        assert (st_follows st x1) by repeat solve_st_follows.
        eapply unnest_block_wt_clock in H; eauto.
        assert (unnest_blocks G1 blocks x1 = (concat x2, st')) as Hnorm.
        { unfold unnest_blocks; repeat inv_bind; eauto. }
        eapply IHblocks in Hnorm; eauto.
        solve_forall; repeat solve_incl.
    Qed.

    (** The enum types used in the new variables are also correct *)

    Lemma fresh_ident_wt_enum : forall vars pref hint ty ck id st st',
        wt_enum G2 ty ->
        Forall (wt_enum G2) (map snd (vars++st_tys st)) ->
        fresh_ident pref hint (ty, ck) st = (id, st') ->
        Forall (wt_enum G2) (map snd (vars++st_tys st')).
    Proof.
      unfold st_tys.
      intros * Hty Henums Hfresh.
      apply Ker.fresh_ident_anns in Hfresh. rewrite Hfresh; simpl.
      rewrite <-Permutation_middle; simpl; eauto.
    Qed.

    Corollary idents_for_anns_wt_enum : forall vars anns ids st st',
        Forall (wt_enum G2) (map fst anns) ->
        Forall (wt_enum G2) (map snd (vars++st_tys st)) ->
        idents_for_anns anns st = (ids, st') ->
        Forall (wt_enum G2) (map snd (vars++st_tys st')).
    Proof.
      induction anns as [|(?&?&?)]; intros * Hwt Henums Hids;
        inv Hwt; simpl in *; repeat inv_bind; auto.
      eapply IHanns in H0; eauto using fresh_ident_wt_enum.
    Qed.

    Lemma reuse_ident_wt_enum : forall vars ty ck id st st',
        wt_enum G2 ty ->
        Forall (wt_enum G2) (map snd (vars++st_tys st)) ->
        reuse_ident id (ty, ck) st = (tt, st') ->
        Forall (wt_enum G2) (map snd (vars++st_tys st')).
    Proof.
      unfold st_tys.
      intros * Hty Henums Hfresh.
      apply Ker.reuse_ident_anns in Hfresh. rewrite Hfresh; simpl.
      rewrite <-Permutation_middle; simpl; eauto.
    Qed.

    Corollary idents_for_anns'_wt_enum : forall vars anns ids st st',
        Forall (wt_enum G2) (map fst anns) ->
        Forall (wt_enum G2) (map snd (vars++st_tys st)) ->
        idents_for_anns' anns st = (ids, st') ->
        Forall (wt_enum G2) (map snd (vars++st_tys st')).
    Proof.
      induction anns as [|(?&?&[?|])]; intros * Hwt Henums Hids;
        inv Hwt; simpl in *; repeat inv_bind; auto.
      1,2:eapply IHanns in H0; eauto using fresh_ident_wt_enum.
      destruct x. eauto using reuse_ident_wt_enum.
    Qed.

    Fact mmap2_wt_enum {A A1 A2 : Type} :
      forall vars (k : A -> Unnesting.FreshAnn (A1 * A2)) a a1s a2s st st',
        Forall (wt_enum G2) (map snd (vars++st_tys st)) ->
        mmap2 k a st = (a1s, a2s, st') ->
        (forall st st' a es a2s, k a st = (es, a2s, st') -> st_follows st st') ->
        Forall (fun a => forall a1s a2s st0 st0',
                    Forall (wt_enum G2) (map snd (vars++st_tys st0)) ->
                    k a st0 = (a1s, a2s, st0') ->
                    st_follows st st0 ->
                    st_follows st0' st' ->
                    Forall (wt_enum G2) (map snd (vars++st_tys st0'))) a ->
        Forall (wt_enum G2) (map snd (vars++st_tys st')).
    Proof with eauto.
      induction a; intros a1s a2s st st' Hclocks Hmap Hfollows Hf;
        repeat inv_bind...
      inv Hf.
      specialize (H3 _ _ _ _ Hclocks H).
      eapply IHa in H3...
      - reflexivity.
      - eapply mmap2_st_follows...
        solve_forall...
      - solve_forall.
        eapply H2 in H5...
        etransitivity...
    Qed.

    Hypothesis WtG1 : wt_global G1.
    Hypothesis WtG2 : wt_global G2.

    Fact unnest_reset_wt_enum : forall vars e e' eqs' st st' ,
        (forall es' eqs' st0',
            st_follows st0' st' ->
            unnest_exp G1 true e st = (es', eqs', st0') ->
            Forall (wt_enum G2) (map snd (vars++st_tys st0'))) ->
        wt_exp G1 (vars++st_tys st) e ->
        typeof e = [OpAux.bool_velus_type] ->
        Forall (wt_enum G2) (map snd (vars++st_tys st)) ->
        unnest_reset (unnest_exp G1 true) e st = (e', eqs', st') ->
        Forall (wt_enum G2) (map snd (vars++st_tys st')).
    Proof with eauto.
      intros * Hkck Hwt Hty Henums Hnorm.
      unnest_reset_spec; simpl in *; eauto. eapply Hkck; eauto; reflexivity.
      eapply fresh_ident_wt_enum in Hfresh; eauto.
      assert (length l = 1). 2:singleton_length.
      { eapply unnest_exp_length in Hk0; eauto.
        now rewrite <-length_typeof_numstreams, Hty in Hk0. }
      eapply unnest_exp_annot in Hk0; eauto; simpl in Hk0; rewrite app_nil_r in Hk0.
      eapply iface_eq_wt_exp, wt_exp_wt_enum in Hwt; eauto.
      rewrite typeof_annot in *. rewrite Hk0 in Hhd.
      rewrite Forall_map in Hwt. destruct (annot e); inv Hwt; simpl in *; try congruence.
      subst; auto.
    Qed.

    Corollary unnest_resets_wt_enum : forall vars es es' eqs' st st' ,
        Forall (fun e => forall es' eqs' st0 st0',
                    Forall (wt_enum G2) (map snd (vars++st_tys st0)) ->
                    unnest_exp G1 true e st0 = (es', eqs', st0') ->
                    st_follows st st0 ->
                    st_follows st0' st' ->
                    Forall (wt_enum G2) (map snd (vars++st_tys st0'))) es ->
        Forall (wt_exp G1 (vars++st_tys st)) es ->
        Forall (fun e => typeof e = [OpAux.bool_velus_type]) es ->
        Forall (wt_enum G2) (map snd (vars++st_tys st)) ->
        mmap2 (unnest_reset (unnest_exp G1 true)) es st = (es', eqs', st') ->
        Forall (wt_enum G2) (map snd (vars++st_tys st')).
    Proof.
      intros * F Wt Tys WtE Map.
      eapply mmap2_wt_enum in Map; eauto.
      rewrite Forall_forall in *. intros.
      eapply unnest_reset_wt_enum in H1; eauto.
      - intros. eapply F; eauto. etransitivity; eauto.
      - eapply Wt in H. repeat solve_incl.
    Qed.

    Fact unnest_noops_exps_wt_enum : forall vars cks es es' eqs' st st' ,
        length es = length cks ->
        Forall (fun e => numstreams e = 1) es ->
        Forall (wt_exp G2 (vars++st_tys st)) es ->
        Forall (wt_enum G2) (map snd (vars++st_tys st)) ->
        unnest_noops_exps cks es st = (es', eqs', st') ->
        Forall (wt_enum G2) (map snd (vars++st_tys st')).
    Proof.
      unfold unnest_noops_exps.
      intros * Hlen Hnum Hwt1 Hwt2 Hunt. repeat inv_bind.
      eapply mmap2_wt_enum in H; eauto. intros ?? (?&?) ???; eauto using unnest_noops_exp_st_follows.
      solve_forall.
      unfold unnest_noops_exp in H4.
      rewrite <-length_annot_numstreams in H7. singleton_length.
      destruct p as (?&?&?).
      destruct (is_noops_exp _ _); repeat inv_bind; auto.
      eapply fresh_ident_wt_enum; eauto.
      eapply wt_exp_wt_enum in H2; eauto. 2:solve_forall.
      rewrite typeof_annot, Hsingl in H2. inv H2; auto.
    Qed.

    Lemma unnest_exp_wt_enum : forall vars e is_control es' eqs' st st' ,
        wt_exp G1 (vars++st_tys st) e ->
        Forall (wt_enum G2) (map snd (vars++st_tys st)) ->
        unnest_exp G1 is_control e st = (es', eqs', st') ->
        Forall (wt_enum G2) (map snd (vars++st_tys st')).
    Proof.
      induction e using exp_ind2; intros * Hwt Henums Hun;
        inv Hwt; simpl in Hun; repeat inv_bind; auto.
      - (* unop *)
        eapply IHe; eauto.
      - (* binop *)
        eapply IHe2 in H0; eauto. repeat solve_incl.
      - (* fby *)
        eapply idents_for_anns_wt_enum in H3; eauto.
        1:{ rewrite <-H6. eapply wt_exps_wt_enum; eauto. solve_forall. }
        eapply mmap2_wt_enum in H2; eauto. 2:solve_mmap2'.
        eapply mmap2_wt_enum in H1; eauto. solve_mmap2'.
      - (* arrow *)
        eapply idents_for_anns_wt_enum in H3; eauto.
        1:{ rewrite <-H6. eapply wt_exps_wt_enum; eauto. solve_forall. }
        eapply mmap2_wt_enum in H2; eauto. 2:solve_mmap2'.
        eapply mmap2_wt_enum in H1; eauto. solve_mmap2'.
      - (* when *)
        eapply mmap2_wt_enum in H0; eauto. solve_mmap2'.
      - (* merge *)
        assert (Hnorm1:=H0). eapply mmap2_wt_enum in H0; eauto.
        2:(intros; destruct a; repeat solve_st_follows).
        2:{ solve_forall. repeat inv_bind. eapply mmap2_wt_enum in H8; eauto.
            solve_mmap2'. }
        destruct is_control; repeat inv_bind; eauto.
        eapply idents_for_anns_wt_enum; eauto.
        rewrite map_map, map_id; simpl.
        inv H8; simpl in *; subst; try congruence.
        inv H7. eapply wt_exps_wt_enum; eauto. solve_forall; repeat solve_incl.
      - (* case (total) *)
        assert (Hnorm0:=H1). eapply IHe in H1; eauto.
        assert (Hnorm1:=H2). eapply mmap2_wt_enum in H2; eauto.
        2:(intros; destruct a; repeat solve_st_follows).
        2:{ solve_forall. repeat inv_bind. eapply mmap2_wt_enum in H11; eauto.
            solve_mmap2'. }
        destruct is_control; repeat inv_bind; eauto.
        eapply idents_for_anns_wt_enum; eauto.
        rewrite map_map, map_id; simpl.
        inv H11; simpl in *; subst; try congruence.
        inv H10. eapply wt_exps_wt_enum; eauto. solve_forall; repeat solve_incl.
      - (* case (default) *)
        assert (Hnorm0:=H1). eapply IHe in H1; eauto.
        assert (Hnorm1:=H2). eapply mmap2_wt_enum in H2; eauto.
        2:(intros; destruct a; repeat solve_st_follows).
        2:{ solve_forall. repeat inv_bind. eapply mmap2_wt_enum in H13; eauto.
            solve_mmap2'. }
        assert (Hnorm2:=H3). eapply mmap2_wt_enum in H3; eauto. 2:solve_mmap2'.
        destruct is_control; repeat inv_bind; eauto.
        eapply idents_for_anns_wt_enum; eauto.
        rewrite map_map, map_id; simpl.
        inv H12; simpl in *; subst; try congruence.
        inv H11. eapply wt_exps_wt_enum; eauto. solve_forall; repeat solve_incl.
      - (* app *)
        eapply idents_for_anns'_wt_enum in H4; eauto.
        + eapply wt_find_node in H7 as (G'&(_&_&Henums'&_)&Heq); eauto.
          rewrite 2 idty_app, map_app, Forall_app in Henums'.
          unfold idty in Henums'. rewrite map_map, Forall_map in Henums'. destruct Henums' as (_&Henums').
          clear - H9 Henums' Heq Hiface. destruct Hiface as (Heq2&_).
          rewrite Forall_map. induction H9; inv Henums'; constructor; auto.
          destruct x as (?&?), y as (?&(?&?)&?); subst; simpl in *. destruct t; simpl in *; auto.
          destruct H2; split; auto. congruence.
        + eapply unnest_resets_wt_enum in H3; eauto. solve_mmap2'.
          solve_forall; repeat solve_incl.
          eapply unnest_noops_exps_wt_enum in H2; eauto.
          * unfold find_node_incks. rewrite H7.
            eapply Forall2_length in H8. rewrite map_length.
            eapply mmap2_unnest_exp_length in H1; eauto. rewrite length_typesof_annots in H8.
            congruence.
          * eapply mmap2_unnest_exp_numstreams; eauto.
          * eapply mmap2_unnest_exp_wt. 2:eauto. eauto.
          * eapply mmap2_wt_enum; eauto. solve_mmap2'.
    Qed.

    Corollary unnest_exps_wt_enum : forall vars es es' eqs' st st' ,
        Forall (wt_exp G1 (vars++st_tys st)) es ->
        Forall (wt_enum G2) (map snd (vars++st_tys st)) ->
        unnest_exps G1 es st = (es', eqs', st') ->
        Forall (wt_enum G2) (map snd (vars++st_tys st')).
    Proof.
      intros vars es es' eqs' st st' Hwt Hclocks Hnorm.
      unfold unnest_exps in Hnorm. repeat inv_bind.
      eapply mmap2_wt_enum in H; eauto.
      solve_forall.
      assert (st_follows st0 st0') by eauto.
      eapply unnest_exp_wt_enum with (vars:=vars) in H3; repeat solve_incl.
      - solve_forall; solve_incl.
      - solve_forall; solve_incl.
    Qed.

    Fact unnest_rhs_wt_enum : forall vars e es' eqs' st st' ,
        wt_exp G1 (vars++st_tys st) e ->
        Forall (wt_enum G2) (map snd (vars++st_tys st)) ->
        unnest_rhs G1 e st = (es', eqs', st') ->
        Forall (wt_enum G2) (map snd (vars++st_tys st')).
    Proof with eauto.
      intros * Hwt Hclocks Hnorm.
      destruct e; unfold unnest_rhs in Hnorm;
        try eapply unnest_exp_wt_enum in Hnorm; eauto; repeat inv_bind; inv Hwt.
      - (* fby *)
        eapply unnest_exps_wt_enum in H0... solve_forall; repeat solve_incl.
        eapply unnest_exps_wt_enum in H...
      - (* arrow *)
        eapply unnest_exps_wt_enum in H0... solve_forall; repeat solve_incl.
        eapply unnest_exps_wt_enum in H...
      - (* app *)
        eapply unnest_resets_wt_enum in H1... 2:solve_forall; repeat solve_incl.
        { eapply Forall_forall. intros. eapply unnest_exp_wt_enum in H4; eauto.
          eapply Forall_forall in H7; eauto. repeat solve_incl. }
        eapply unnest_noops_exps_wt_enum in H0...
        + unfold find_node_incks. rewrite H8.
          eapply Forall2_length in H9. rewrite map_length.
          eapply unnest_exps_length in H; eauto. rewrite length_typesof_annots in H9.
          congruence.
        + eapply unnest_exps_numstreams; eauto.
        + eapply unnest_exps_wt. 2:eauto. eauto.
        + eapply unnest_exps_wt_enum in H; eauto.
    Qed.

    Corollary unnest_rhss_wt_enum : forall vars es es' eqs' st st' ,
        Forall (wt_exp G1 (vars++st_tys st)) es ->
        Forall (wt_enum G2) (map snd (vars++st_tys st)) ->
        unnest_rhss G1 es st = (es', eqs', st') ->
        Forall (wt_enum G2) (map snd (vars++st_tys st')).
    Proof.
      intros * Hwt Hclocks Hnorm.
      unfold unnest_rhss in Hnorm. repeat inv_bind.
      eapply mmap2_wt_enum in H; eauto.
      solve_forall. eapply unnest_rhs_wt_enum in H3; eauto.
      repeat solve_incl.
    Qed.

    Fact unnest_equation_wt_enum : forall vars eq eqs' st st' ,
        wt_equation G1 (vars++st_tys st) eq ->
        Forall (wt_enum G2) (map snd (vars++st_tys st)) ->
        unnest_equation G1 eq st = (eqs', st') ->
        Forall (wt_enum G2) (map snd (vars++st_tys st')).
    Proof.
      intros * Hwt Henums Hnorm.
      destruct eq; repeat inv_bind.
      destruct Hwt.
      eapply unnest_rhss_wt_enum in H; eauto.
    Qed.

    Fact unnest_block_wt_enum : forall vars d blocks' st st' ,
        wt_block G1 (vars++st_tys st) d ->
        Forall (wt_enum G2) (map snd (vars++st_tys st)) ->
        unnest_block G1 d st = (blocks', st') ->
        Forall (wt_enum G2) (map snd (vars++st_tys st')).
    Proof.
      induction d using block_ind2; intros * Hwt Henums Hnorm;
        inv Hwt; repeat inv_bind.
      - eapply unnest_equation_wt_enum; eauto.
      - assert (Forall (wt_enum G2) (map snd (vars ++ st_tys x0))) as Henums'.
        { clear - H H0 H2 Henums.
          revert st x0 x H2 Henums H0.
          induction H; intros * Hwt Henums Hmap; inv Hwt; repeat inv_bind; auto.
          eapply IHForall in H2; eauto.
          solve_forall; repeat solve_incl.
        }
        eapply unnest_reset_wt_enum in H1; eauto.
        intros. eapply unnest_exp_wt_enum in H6; eauto.
        1,2:repeat solve_incl.
      - solve_forall.
    Qed.

    Corollary unnest_blocks_wt_enum : forall vars blocks blocks' st st' ,
        Forall (wt_block G1 (vars++st_tys st)) blocks ->
        Forall (wt_enum G2) (map snd (vars++st_tys st)) ->
        unnest_blocks G1 blocks st = (blocks', st') ->
        Forall (wt_enum G2) (map snd (vars++st_tys st')).
    Proof.
      induction blocks; intros * Hwt Hclocks Hnorm;
        unfold unnest_blocks in Hnorm; repeat inv_bind.
      - assumption.
      - inv Hwt.
        assert (st_follows st x1) by repeat solve_st_follows.
        eapply unnest_block_wt_enum in H; eauto.
        assert (unnest_blocks G1 blocks x1 = (concat x2, st')) as Hnorm.
        { unfold unnest_blocks; repeat inv_bind; eauto. }
        eapply IHblocks in Hnorm; eauto.
        solve_forall; repeat solve_incl.
    Qed.

    (** Finally, we can prove that the node is properly normalized *)

    Lemma unnest_node_wt : forall n,
        wt_node G1 n ->
        wt_node G2 (unnest_node G1 n).
    Proof.
      intros * [Hclin [Hclout [Hvars Heq]]].
      unfold unnest_node.
      destruct Hiface as (Henums&_).
      split; [|split;[|split]]; simpl; try solve [rewrite <- Henums; auto]. solve_forall.
      destruct (n_block n); simpl; eauto using iface_eq_wt_block. inv Heq. constructor.
      - destruct (unnest_blocks _ _ _) as (blocks'&st') eqn:Heqres; simpl.
        eapply unnest_blocks_wt_block in Heqres; eauto. 2:unfold st_tys; rewrite init_st_anns, app_nil_r; eauto.
        unfold st_tys, idty in *. repeat rewrite map_app in *. repeat rewrite <-app_assoc in *.
        repeat rewrite map_map in *; eauto.
      - unfold wt_clocks in *.
        apply Forall_app. split.
        + solve_forall. unfold idty in *.
          do 2 solve_incl. repeat rewrite map_app. repeat solve_incl.
        + destruct (unnest_blocks _ _ _) as (blocks&st') eqn:Heqres.
          eapply unnest_blocks_wt_clock with (vars:=idty (idty (n_in n ++ n_out n)) ++ idty (idty l)) in Heqres; eauto.
          * simpl. unfold st_clocks in Heqres.
            unfold st_tys, idty in *. solve_forall.
            repeat rewrite map_app in *. repeat rewrite map_map in *; simpl.
            repeat solve_incl.
          * unfold st_clocks. unfold st_tys. rewrite init_st_anns, app_nil_r. assumption.
          * unfold st_clocks. rewrite init_st_anns; simpl; constructor.
      - destruct (unnest_blocks _ _ _) as (blocks'&st') eqn:Heqres; simpl.
        eapply unnest_blocks_wt_enum with (vars:=idty (idty (n_in n ++ n_out n)) ++ idty (idty l)) in Heqres; eauto.
        + rewrite 2 map_app, 2 Forall_app in Heqres. destruct Heqres as ((?&?)&?).
          unfold st_tys, idty in *.
          repeat rewrite map_app in *. repeat rewrite map_map in *; simpl in *.
          apply Forall_app; auto.
        + unfold st_tys. now rewrite init_st_anns, app_nil_r.
        + unfold st_tys. rewrite init_st_anns, app_nil_r.
          rewrite map_app, Forall_app; split; solve_forall.
    Qed.

  End unnest_node_wt.

  Lemma unnest_global_wt : forall G,
      wt_global G ->
      wt_global (unnest_global G).
  Proof.
    intros (enums&nds) (Henums&Hwt). unfold CommonTyping.wt_program in Hwt; simpl.
    induction nds; inv Hwt; split; simpl; auto. constructor.
    destruct H1.
    constructor; [constructor|].
    - eapply unnest_node_wt; eauto. 2:split; auto.
      eapply unnest_nodes_eq.
    - eapply unnest_nodes_names; eauto.
    - eapply IHnds; eauto.
  Qed.

  (** ** Preservation of wt through the second pass *)

  Section normfby_node_wt.
    Variable G1 : @global nolocal_top_block norm1_prefs.
    Variable G2 : @global nolocal_top_block norm2_prefs.

    Hypothesis Hiface : global_iface_eq G1 G2.
    Hypothesis Hbool : In (bool_id, 2) G1.(enums).
    Hint Resolve iface_eq_wt_clock iface_eq_wt_exp.

    Fact add_whens_typeof : forall e ty ck,
        typeof e = [ty] ->
        typeof (add_whens e ty ck) = [ty].
    Proof.
      induction ck; [|destruct p]; intro Hty; simpl; auto.
    Qed.

    Fact add_whens_wt_exp : forall vars e ty cl e' ,
        wt_exp G1 vars e ->
        typeof e = [ty] ->
        wt_clock G1.(enums) vars cl ->
        add_whens e ty cl = e' ->
        wt_exp G2 vars e'.
    Proof.
      induction cl; intros e' Hwt Hty Hclock Hwhens; simpl in Hwhens; inv Hclock; subst.
      - eauto.
      - destruct Hiface as (Henums&_).
        repeat econstructor; simpl; try rewrite <-Henums; eauto.
        rewrite app_nil_r.
        rewrite add_whens_typeof; auto.
    Qed.

    Fact init_var_for_clock_wt_eq : forall vars ck id eqs' st st' ,
        wt_clock G1.(enums) (vars++st_tys st) ck ->
        init_var_for_clock ck st = (id, eqs', st') ->
        Forall (wt_equation G2 (vars++st_tys st')) eqs'.
    Proof with eauto.
      intros * Hck Hinit.
      unfold init_var_for_clock in Hinit.
      destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit.
        repeat constructor; simpl; repeat rewrite app_nil_r; auto.
        1,2:eapply add_whens_wt_exp; [| | |eauto]; eauto.
        1,3:constructor; simpl; auto.
        3,4:eapply add_whens_typeof; simpl; auto.
        1,2,3:repeat solve_incl.
        eapply fresh_ident_In in Hfresh.
        eapply in_or_app; right; unfold st_tys, idty; simpl_In;
          eexists; split; eauto; eauto.
    Qed.

    Fact fby_iteexp_wt_exp : forall vars e0 e ty ck name e' eqs' st st' ,
        wt_clock G1.(enums) (vars++st_tys st) ck ->
        wt_exp G1 (vars++st_tys st) e0 ->
        wt_exp G1 (vars++st_tys st) e ->
        typeof e0 = [ty] ->
        typeof e = [ty] ->
        fby_iteexp e0 e (ty, (ck, name)) st = (e', eqs', st') ->
        wt_exp G2 (vars++st_tys st') e'.
    Proof.
      intros * Hwtc Hwt1 Hwt2 Hty1 Hty2 Hfby.
      unfold fby_iteexp in Hfby; repeat inv_bind.
      repeat econstructor; simpl in *; try rewrite app_nil_r; auto.
      2,5,6,7,8:repeat solve_incl; eapply init_var_for_clock_st_follows in H; repeat solve_st_follows.
      - apply init_var_for_clock_In in H as In.
        apply in_or_app, or_intror; unfold st_tys, idty.
        simpl_In; exists (x, (OpAux.bool_velus_type, ck)); split; auto.
        repeat solve_incl.
      - apply fresh_ident_In in H0.
        apply in_or_app, or_intror; unfold st_tys, idty.
        simpl_In; exists (x2, (ty, ck)); split; auto.
      - destruct Hiface as (Henums&_). congruence.
      - congruence.
    Qed.

    Fact arrow_iteexp_wt_exp : forall vars e0 e ty ck name e' eqs' st st' ,
        wt_clock G1.(enums) (vars++st_tys st) ck ->
        wt_exp G1 (vars++st_tys st) e0 ->
        wt_exp G1 (vars++st_tys st) e ->
        typeof e0 = [ty] ->
        typeof e = [ty] ->
        arrow_iteexp e0 e (ty, (ck, name)) st = (e', eqs', st') ->
        wt_exp G2 (vars++st_tys st') e'.
    Proof.
      intros * Hwtc Hwt1 Hwt2 Hty1 Hty2 Hfby.
      unfold arrow_iteexp in Hfby; repeat inv_bind.
      repeat econstructor; simpl in *; try rewrite app_nil_r; auto.
      2,5,6,7:repeat solve_incl; eapply init_var_for_clock_st_follows in H; repeat solve_st_follows.
      - apply init_var_for_clock_In in H as In.
        apply in_or_app, or_intror; unfold st_tys, idty.
        simpl_In; exists (x, (OpAux.bool_velus_type, ck)); split; auto.
      - destruct Hiface as (Henums&_). congruence.
      - congruence.
    Qed.

    Hypothesis HwtG1 : wt_global G1.

    Fact fby_iteexp_wt_eq : forall vars e0 e ty ck name e' eqs' st st' ,
        Forall (wt_enum G1) (map snd vars) ->
        wt_clock G1.(enums) (vars++st_tys st) ck ->
        wt_exp G1 vars e0 ->
        wt_exp G1 vars e ->
        typeof e0 = [ty] ->
        typeof e = [ty] ->
        fby_iteexp e0 e (ty, (ck, name)) st = (e', eqs', st') ->
        Forall (wt_equation G2 (vars++st_tys st')) eqs'.
    Proof.
      intros * Henums Hwtc Hwt1 Hwt2 Hty1 Hty2 Hfby.
      unfold fby_iteexp in Hfby; repeat inv_bind; auto.
      assert (wt_clock G1.(enums) (vars ++ st_tys st') ck) as Hwtck'.
      { repeat solve_incl; eapply init_var_for_clock_st_follows in H; repeat solve_st_follows. }
      constructor.
      - repeat constructor; simpl; try rewrite app_nil_r; eauto.
        + eapply add_whens_wt_exp; [| | |eauto]; auto.
          * destruct ty; simpl; [constructor|]; auto.
            eapply wt_exp_wt_enum in Hwt1; eauto.
            rewrite Hty1 in Hwt1. apply Forall_singl in Hwt1. destruct Hwt1.
            constructor; auto.
          * destruct ty; simpl; auto.
            now rewrite Op.ctype_init_ctype.
        + repeat solve_incl; eapply init_var_for_clock_st_follows in H; repeat solve_st_follows.
        + eapply add_whens_typeof.
          destruct ty; simpl; auto. now rewrite Op.ctype_init_ctype.
        + apply fresh_ident_In in H0.
          apply in_or_app, or_intror. unfold st_tys, idty.
          simpl_In. exists (x2, (ty, ck)); split; auto.
      - eapply init_var_for_clock_wt_eq with (vars:=vars) in H; eauto.
        solve_forall; repeat solve_incl.
    Qed.

    Fact arrow_iteexp_wt_eq : forall vars e0 e ty ck name e' eqs' st st' ,
        wt_clock G1.(enums) (vars++st_tys st) ck ->
        arrow_iteexp e0 e (ty, (ck, name)) st = (e', eqs', st') ->
        Forall (wt_equation G2 (vars++st_tys st')) eqs'.
    Proof.
      intros * Hwtc Hfby.
      unfold arrow_iteexp in Hfby. repeat inv_bind.
      eapply init_var_for_clock_wt_eq in H; eauto.
    Qed.

    Fact normfby_equation_wt_eq : forall vars to_cut eq eqs' st st' ,
        Forall (wt_enum G1) (map snd vars) ->
        wt_equation G1 vars eq ->
        normfby_equation to_cut eq st = (eqs', st') ->
        Forall (wt_equation G2 (vars++st_tys st')) eqs'.
    Proof.
      intros * Henums Hwt Hfby.
      inv_normfby_equation Hfby to_cut eq.
      - (* constant fby *)
        destruct x2 as (?&?&?). destruct (PS.mem x to_cut); repeat inv_bind; auto.
        destruct Hwt as [Hwt Hin]. apply Forall_singl in Hwt. apply Forall2_singl in Hin.
        inv Hwt. apply Forall_singl in H4. apply Forall_singl in H3.
        apply Forall_singl in H7. inv H7.
        repeat (constructor; auto).
        2,4,5,6:repeat solve_incl.
        + apply fresh_ident_In in H. apply in_or_app, or_intror.
          unfold st_tys, idty. repeat simpl_In. exists (x2, (t, c)); split; auto.
        + solve_forall; repeat solve_incl.
        + apply fresh_ident_In in H. apply in_or_app, or_intror.
          unfold st_tys, idty. repeat simpl_In. exists (x2, (t, c)); split; auto.
        + destruct Hwt. constructor; eauto.
          eapply iface_eq_wt_equation; eauto.
          constructor; auto. solve_forall; repeat solve_incl.
          simpl. solve_forall. apply in_app_iff; auto.
      - (* fby *)
        destruct x2 as (ty&ck&name).
        assert (st_follows st st') as Hfollows by (eapply fby_iteexp_st_follows with (ann:=(ty, (ck, name))) in H; eauto).
        destruct Hwt as [Hwt Hins]. apply Forall_singl in Hwt. apply Forall2_singl in Hins.
        inv Hwt.
        simpl in *; rewrite app_nil_r in *.
        apply Forall_singl in H3; apply Forall_singl in H4.
        apply Forall_singl in H7; inv H7.
        assert (Hwte:=H). eapply fby_iteexp_wt_exp with (vars:=vars) in Hwte; eauto.
        assert (Hty:=H). eapply (fby_iteexp_typeof _ _ (ty, (ck, name))) in Hty; eauto.
        assert (Hwteq:=H). eapply fby_iteexp_wt_eq in Hwteq; eauto.
        repeat constructor; auto.
        simpl; rewrite app_nil_r, Hty. repeat constructor. 1-5:repeat solve_incl.
      - (* arrow *)
        destruct x2 as [ty [ck name]].
        destruct Hwt as [Hwt Hins]. apply Forall_singl in Hwt. apply Forall2_singl in Hins.
        inv Hwt.
        simpl in *; rewrite app_nil_r in *.
        apply Forall_singl in H3; apply Forall_singl in H4.
        apply Forall_singl in H7; inv H7.
        assert (Hwte:=H). eapply arrow_iteexp_wt_exp with (vars:=vars) in Hwte; eauto. 2-4:repeat solve_incl.
        assert (Hwteq:=H). eapply arrow_iteexp_wt_eq with (vars:=vars) in Hwteq; eauto. 2:repeat solve_incl.
        assert (st_follows st st') as Hfollows.
        { repeat inv_bind. eapply init_var_for_clock_st_follows; eauto. }
        repeat inv_bind.
        repeat (econstructor; auto); try congruence.
        apply in_or_app; auto.
      - destruct Hwt. constructor; auto. constructor; auto.
        solve_forall. repeat solve_incl.
        solve_forall. apply in_app_iff; auto.
    Qed.

    Fact normfby_block_wt : forall vars to_cut d blocks' st st' ,
        Forall (wt_enum G1) (map snd vars) ->
        wt_block G1 vars d ->
        normfby_block to_cut d st = (blocks', st') ->
        Forall (wt_block G2 (vars++st_tys st')) blocks'.
    Proof.
      induction d using block_ind2; intros * Henums Hwt Hnorm.
      - (* equation *)
        inv Hwt; repeat inv_bind.
        eapply normfby_equation_wt_eq in H; eauto.
        rewrite Forall_map. eapply Forall_impl; [|eauto].
        intros; constructor; auto.
      - (* reset *)
        simpl in Hnorm.
        cases; repeat inv_bind;
          try (constructor; auto; repeat solve_incl).
        inv Hwt; simpl in *. inv H6. apply Forall_singl in H3.
        apply Forall_singl in H. apply H in H0; eauto.
        rewrite Forall_map. solve_forall.
        constructor; auto. repeat solve_incl.
      - (* locals *)
        repeat inv_bind. constructor; auto.
        repeat solve_incl.
    Qed.

    Corollary normfby_blocks_wt : forall vars to_cut blocks blocks' st st' ,
        Forall (wt_enum G1) (map snd vars) ->
        Forall (wt_block G1 vars) blocks ->
        normfby_blocks to_cut blocks st = (blocks', st') ->
        Forall (wt_block G2 (vars++st_tys st')) blocks'.
    Proof.
      induction blocks; intros * Henums Hwt Hfby;
        unfold normfby_blocks in *; repeat inv_bind; simpl; auto.
      inv Hwt.
      apply Forall_app; split.
      - eapply normfby_block_wt in H; eauto. solve_forall; repeat solve_incl.
      - assert (normfby_blocks to_cut blocks x1 = (concat x2, st')) as Hnorm.
        { unfold normfby_blocks. repeat inv_bind; eauto. }
        eapply IHblocks in Hnorm; eauto.
    Qed.

    (** wt_clock *)

    Fact init_var_for_clock_wt_clock : forall enums vars ck x eqs' st st' ,
        wt_clock enums (vars++st_tys st) ck ->
        Forall (wt_clock enums (vars ++ st_tys st)) (st_clocks st) ->
        init_var_for_clock ck st = (x, eqs', st') ->
        Forall (wt_clock enums (vars ++ st_tys st')) (st_clocks st').
    Proof.
      intros * Hwtc1 Hwtc2 Hfby.
      unfold init_var_for_clock in Hfby.
      destruct (fresh_ident _ _) eqn:Hfresh.
      inv Hfby.
      eapply fresh_ident_wt_clock in Hfresh; eauto. solve_forall. 1,2:repeat solve_incl.
    Qed.

    Fact fby_iteexp_wt_clock : forall enums vars e0 e ty ck name e' eqs' st st' ,
        wt_clock enums (vars++st_tys st) ck ->
        Forall (wt_clock enums (vars ++ st_tys st)) (st_clocks st) ->
        fby_iteexp e0 e (ty, (ck, name)) st = (e', eqs', st') ->
        Forall (wt_clock enums (vars ++ st_tys st')) (st_clocks st').
    Proof.
      intros * Hwtc1 Hwtc2 Hfby.
      unfold fby_iteexp in Hfby; repeat inv_bind; auto.
      assert (st_follows st x1) as Hfollows1 by (eapply init_var_for_clock_st_follows in H; eauto).
      assert (st_follows x1 st') as Hfollows2 by eauto.
      eapply fresh_ident_wt_clock in H0; eauto. 2:repeat solve_incl.
      eapply init_var_for_clock_wt_clock in H; eauto.
      solve_forall; repeat solve_incl.
    Qed.

    Fact arrow_iteexp_wt_clock : forall enums vars e0 e ty ck name e' eqs' st st' ,
        wt_clock enums (vars++st_tys st) ck ->
        Forall (wt_clock enums (vars ++ st_tys st)) (st_clocks st) ->
        arrow_iteexp e0 e (ty, (ck, name)) st = (e', eqs', st') ->
        Forall (wt_clock enums (vars ++ st_tys st')) (st_clocks st').
    Proof.
      intros * Hwtc1 Hwtc2 Hfby.
      unfold arrow_iteexp in Hfby. repeat inv_bind.
      eapply init_var_for_clock_wt_clock in H; eauto.
    Qed.

    Fact normfby_equation_wt_clock : forall vars to_cut eq eqs' st st' ,
        wt_equation G1 (vars++st_tys st) eq ->
        Forall (wt_clock G2.(enums) (vars ++ st_tys st)) (st_clocks st) ->
        normfby_equation to_cut eq st = (eqs', st') ->
        Forall (wt_clock G2.(enums) (vars ++ st_tys st')) (st_clocks st').
    Proof.
      intros * Hwt Hwtck Hfby.
      inv_normfby_equation Hfby to_cut eq; destruct x2 as (ty&ck&name).
      - (* fby (constant) *)
        destruct PS.mem; repeat inv_bind; auto.
        destruct Hwt as [Hwt _]. apply Forall_singl in Hwt.
        inv Hwt. apply Forall_singl in H7; inv H7.
        eapply fresh_ident_wt_clock in H; eauto.
        1:solve_forall. 1,2:repeat solve_incl.
      - (* fby *)
        eapply fby_iteexp_wt_clock in H; eauto.
        destruct Hwt as [Hwt _]. apply Forall_singl in Hwt.
        inv Hwt. apply Forall_singl in H7; inv H7; auto.
        solve_incl.
      - (* arrow *)
        destruct Hwt as [Hwt _]. apply Forall_singl in Hwt.
        inv Hwt. apply Forall_singl in H7; inv H7; auto.
        eapply arrow_iteexp_wt_clock in H; eauto.
    Qed.

    Fact normfby_block_wt_clock : forall vars to_cut d blocks' st st' ,
        wt_block G1 (vars++st_tys st) d ->
        Forall (wt_clock G2.(enums) (vars ++ st_tys st)) (st_clocks st) ->
        normfby_block to_cut d st = (blocks', st') ->
        Forall (wt_clock G2.(enums) (vars ++ st_tys st')) (st_clocks st').
    Proof.
      induction d using block_ind2; intros * Hwt Hwtck Hnorm.
      - (* equation *)
        inv Hwt; repeat inv_bind.
        eapply normfby_equation_wt_clock; eauto.
      - (* reset *)
        simpl in Hnorm.
        cases; repeat inv_bind; auto.
        inv Hwt. apply Forall_singl in H3.
        apply Forall_singl in H; eauto.
      - (* locals *)
        repeat inv_bind; auto.
    Qed.

    Corollary normfby_blocks_wt_clock : forall vars to_cut blocks blocks' st st' ,
        Forall (wt_block G1 (vars++st_tys st)) blocks ->
        Forall (wt_clock G2.(enums) (vars ++ st_tys st)) (st_clocks st) ->
        normfby_blocks to_cut blocks st = (blocks', st') ->
        Forall (wt_clock G2.(enums) (vars ++ st_tys st')) (st_clocks st').
    Proof.
      induction blocks; intros * Hwt Hwtck Hfby;
        unfold normfby_blocks in *; repeat inv_bind; simpl; auto.
      inv Hwt.
      assert (H':=H). eapply normfby_block_wt_clock in H; eauto.
      assert (normfby_blocks to_cut blocks x1 = (concat x2, st')) as Hnorm.
      { unfold normfby_blocks. repeat inv_bind; eauto. }
      eapply IHblocks in Hnorm; eauto. solve_forall; repeat solve_incl; eauto.
    Qed.

    (** wt_enum *)

    Lemma fresh_ident_wt_enum' : forall vars pref hint ty ck id st st',
        wt_enum G2 ty ->
        Forall (wt_enum G2) (map snd (vars++st_tys st)) ->
        fresh_ident pref hint (ty, ck) st = (id, st') ->
        Forall (wt_enum G2) (map snd (vars++st_tys st')).
    Proof.
      unfold st_tys.
      intros * Hty Henums Hfresh.
      apply Ker.fresh_ident_anns in Hfresh. rewrite Hfresh; simpl.
      rewrite <-Permutation.Permutation_middle; simpl; eauto.
    Qed.

    Fact init_var_for_clock_wt_enum : forall vars ck x eqs' st st' ,
        Forall (wt_enum G2) (map snd (vars ++ st_tys st)) ->
        init_var_for_clock ck st = (x, eqs', st') ->
        Forall (wt_enum G2) (map snd (vars ++ st_tys st')).
    Proof.
      intros * Hwtc2 Hfby.
      unfold init_var_for_clock in Hfby.
      destruct (fresh_ident _ _) eqn:Hfresh.
      inv Hfby.
      eapply fresh_ident_wt_enum' in Hfresh; eauto.
      constructor; simpl; auto.
      destruct Hiface; congruence.
    Qed.

    Fact fby_iteexp_wt_enum : forall vars e0 e ty ck name e' eqs' st st' ,
        wt_enum G2 ty ->
        Forall (wt_enum G2) (map snd (vars ++ st_tys st)) ->
        fby_iteexp e0 e (ty, (ck, name)) st = (e', eqs', st') ->
        Forall (wt_enum G2) (map snd (vars ++ st_tys st')).
    Proof.
      intros * Hwt1 Hwt2 Hfby.
      unfold fby_iteexp in Hfby; repeat inv_bind; auto.
      assert (st_follows st x1) as Hfollows1 by (eapply init_var_for_clock_st_follows in H; eauto).
      assert (st_follows x1 st') as Hfollows2 by eauto.
      eapply fresh_ident_wt_enum' in H0; eauto.
      eapply init_var_for_clock_wt_enum in H; eauto.
    Qed.

    Fact arrow_iteexp_wt_enum : forall vars e0 e ty ck name e' eqs' st st' ,
        wt_enum G2 ty ->
        Forall (wt_enum G2) (map snd (vars ++ st_tys st)) ->
        arrow_iteexp e0 e (ty, (ck, name)) st = (e', eqs', st') ->
        Forall (wt_enum G2) (map snd (vars ++ st_tys st')).
    Proof.
      intros * Hwtc1 Hwtc2 Hfby.
      unfold arrow_iteexp in Hfby. repeat inv_bind.
      eapply init_var_for_clock_wt_enum in H; eauto.
    Qed.

    Hypothesis HwtG2 : wt_global G2.

    Fact normfby_equation_wt_enum : forall vars to_cut eq eqs' st st' ,
        wt_equation G1 (vars++st_tys st) eq ->
        Forall (wt_enum G2) (map snd (vars ++ st_tys st)) ->
        normfby_equation to_cut eq st = (eqs', st') ->
        Forall (wt_enum G2) (map snd (vars ++ st_tys st')).
    Proof.
      intros * Hwt Hwtck Hfby.
      inv_normfby_equation Hfby to_cut eq; destruct x2 as (ty&ck&name).
      - (* fby (constant) *)
        destruct PS.mem; repeat inv_bind; auto.
        destruct Hwt as [Hwt _]. apply Forall_singl in Hwt.
        inv Hwt. apply Forall_singl in H7; inv H7.
        eapply fresh_ident_wt_enum' in H; eauto. simpl in *.
        eapply Forall_singl, iface_eq_wt_exp in H4; eauto. eapply wt_exp_wt_enum in H4; eauto.
        rewrite app_nil_r in H5. rewrite H5 in H4. apply Forall_singl in H4; eauto.
      - (* fby *)
        eapply fby_iteexp_wt_enum in H; eauto.
        destruct Hwt as [Hwt _]. apply Forall_singl in Hwt.
        inv Hwt. apply Forall_singl in H7; inv H7; auto. simpl in *.
        eapply Forall_singl, iface_eq_wt_exp in H4; eauto. eapply wt_exp_wt_enum in H4; eauto.
        rewrite app_nil_r in H5. rewrite H5 in H4. apply Forall_singl in H4; eauto.
      - (* arrow *)
        destruct Hwt as [Hwt _]. apply Forall_singl in Hwt.
        inv Hwt. apply Forall_singl in H7; inv H7; auto. simpl in *.
        eapply arrow_iteexp_wt_enum in H; eauto.
        eapply Forall_singl, iface_eq_wt_exp in H4; eauto. eapply wt_exp_wt_enum in H4; eauto.
        rewrite app_nil_r in H5. rewrite H5 in H4. apply Forall_singl in H4; eauto.
    Qed.

    Fact normfby_block_wt_enum : forall vars to_cut d blocks' st st' ,
        wt_block G1 (vars++st_tys st) d ->
        Forall (wt_enum G2) (map snd (vars ++ st_tys st)) ->
        normfby_block to_cut d st = (blocks', st') ->
        Forall (wt_enum G2) (map snd (vars ++ st_tys st')).
    Proof.
      induction d using block_ind2; intros * Hwt Henums Hnorm.
      - (* equation *)
        inv Hwt. repeat inv_bind.
        eapply normfby_equation_wt_enum in H; eauto.
      - (* reset *)
        simpl in Hnorm. cases; repeat inv_bind; auto.
        inv Hwt. apply Forall_singl in H3.
        apply Forall_singl in H; eauto.
      - (* locals *)
        repeat inv_bind; auto.
    Qed.

    Corollary normfby_blocks_wt_enum : forall vars to_cut blocks blocks' st st' ,
        Forall (wt_block G1 (vars++st_tys st)) blocks ->
        Forall (wt_enum G2) (map snd (vars ++ st_tys st)) ->
        normfby_blocks to_cut blocks st = (blocks', st') ->
        Forall (wt_enum G2) (map snd (vars ++ st_tys st')).
    Proof.
      induction blocks; intros * Hwt Hwtck Hfby;
        unfold normfby_blocks in *; repeat inv_bind; simpl; auto.
      inv Hwt.
      assert (H':=H). eapply normfby_block_wt_enum in H; eauto.
      assert (normfby_blocks to_cut blocks x1 = (concat x2, st')) as Hnorm.
      { unfold normfby_blocks. repeat inv_bind; eauto. }
      eapply IHblocks in Hnorm; eauto. solve_forall; repeat solve_incl; eauto.
    Qed.

    (** Finally, typing of a node *)

    Hint Resolve iface_eq_wt_enum.

    Lemma normfby_node_wt : forall n,
        wt_node G1 n ->
        wt_node G2 (normfby_node n).
    Proof.
      intros * [Hclin [Hclout [Hvars Heq]]].
      unfold normfby_node.
      destruct Hiface as (Henums&_).
      split; [|split; [|split]]; simpl; try solve [rewrite <- Henums; auto]. solve_forall.
      destruct (n_block n); simpl; eauto using iface_eq_wt_block. inv Heq. constructor.
      - destruct (normfby_blocks _ _ _) as (blocks'&st') eqn:Heqres; simpl.
        eapply normfby_blocks_wt in Heqres. 3:eauto. 2:rewrite map_app, Forall_app; split; eauto.
        unfold st_tys, idty in *. repeat rewrite map_app in *. repeat rewrite <-app_assoc in *.
        repeat rewrite map_map in *; eauto.
      - unfold wt_clocks in *.
        apply Forall_app. split.
        + solve_forall. unfold idty in *.
          do 2 solve_incl. repeat rewrite map_app. repeat solve_incl.
        + destruct (normfby_blocks _ _ _) as (blocks&st') eqn:Heqres.
          eapply normfby_blocks_wt_clock with (vars:=idty (idty (n_in n ++ n_out n)) ++ idty (idty l)) in Heqres; eauto.
          * simpl. unfold st_clocks in Heqres.
            unfold st_tys, idty in *. solve_forall.
            repeat rewrite map_app in *. repeat rewrite map_map in *; simpl.
            repeat solve_incl.
          * unfold st_clocks. unfold st_tys. rewrite init_st_anns, app_nil_r. assumption.
          * unfold st_clocks. rewrite init_st_anns; simpl; constructor.
      - destruct (normfby_blocks _ _ _) as (blocks'&st') eqn:Heqres; simpl.
        eapply normfby_blocks_wt_enum with (vars:=idty (idty (n_in n ++ n_out n)) ++ idty (idty l)) in Heqres; eauto.
        + rewrite 2 map_app, 2 Forall_app in Heqres. destruct Heqres as ((?&?)&?).
          unfold st_tys, idty in *.
          repeat rewrite map_app in *. repeat rewrite map_map in *; simpl in *.
          apply Forall_app; auto.
        + unfold st_tys. now rewrite init_st_anns, app_nil_r.
        + unfold st_tys. rewrite init_st_anns, app_nil_r.
          rewrite map_app, Forall_app; split; solve_forall.
    Qed.

  End normfby_node_wt.

  Lemma normfby_global_wt : forall G,
      wt_global G ->
      wt_global (normfby_global G).
  Proof.
    intros (enums&nds) (?&Hwt). unfold CommonTyping.wt_program in Hwt; simpl.
    induction nds; simpl; inv Hwt; split; simpl; auto. constructor.
    destruct H2. constructor; [constructor|]; simpl in *.
    - eapply normfby_node_wt; eauto; simpl; auto. 2:split; auto.
      eapply normfby_global_eq.
    - eapply normfby_nodes_names; eauto.
    - eapply IHnds; eauto.
  Qed.

  (** ** Conclusion *)

  Lemma normalize_global_wt : forall G,
      wt_global G ->
      wt_global (normalize_global G).
  Proof.
    intros * Hwt.
    eapply normfby_global_wt, unnest_global_wt, Hwt.
  Qed.

End NTYPING.

Module NTypingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Syn : LSYNTAX Ids Op OpAux Cks)
       (Typ : LTYPING Ids Op OpAux Cks Syn)
       (Norm : NORMALIZATION Ids Op OpAux Cks Syn)
       <: NTYPING Ids Op OpAux Cks Syn Typ Norm.
  Include NTYPING Ids Op OpAux Cks Syn Typ Norm.
End NTypingFun.
