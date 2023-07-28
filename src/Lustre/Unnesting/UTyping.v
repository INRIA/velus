From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import Fresh.
From Coq Require Import List. Import List.ListNotations. Open Scope list_scope.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LTyping.
From Velus Require Import Lustre.Unnesting.Unnesting.

(** * Preservation of Typing through Unnesting *)

Module Type UTYPING
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Typ : LTYPING Ids Op OpAux Cks Senv Syn)
       (Import Un  : UNNESTING Ids Op OpAux Cks Senv Syn).

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
  Local Hint Resolve mmap2_unnest_exp_typesof : norm.

  Corollary unnest_exps_typesof : forall G es es' eqs' st st',
      Forall (wl_exp G) es ->
      unnest_exps G es st = (es', eqs', st') ->
      typesof es' = typesof es.
  Proof.
    intros * Hwl Hnorm.
    unfold unnest_exps in Hnorm; repeat inv_bind.
    eapply mmap2_unnest_exp_typesof in H; eauto.
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

  Fact idents_for_anns_incl_ty : forall anns ids st st',
    idents_for_anns anns st = (ids, st') ->
    forall x ty ck, In (x, (ty, ck)) ids -> HasType (st_senv st') x ty.
  Proof.
    intros * Hids * Hin.
    apply idents_for_anns_incl in Hids.
    apply Hids in Hin.
    econstructor. solve_In. auto.
  Qed.

  Ltac solve_incl :=
    match goal with
    | Hiface : global_iface_incl ?G1 ?G2, H : wt_clock (types ?G1) _ ?ck |- wt_clock (types ?G2) _ ?ck =>
        eapply iface_incl_wt_clock; eauto
    | H : wt_clock _ ?l1 ?cl |- wt_clock _ ?l2 ?cl =>
        eapply wt_clock_incl; [|eauto]; intros
    | Hiface : global_iface_incl ?G1 ?G2, H : wt_exp ?G1 _ ?e |- wt_exp ?G2 _ ?e =>
        eapply iface_incl_wt_exp; eauto
    | H : wt_exp ?G ?l1 ?e |- wt_exp ?G ?l2 ?e =>
        eapply wt_exp_incl; [| |eauto]; intros
    | H : wt_equation ?G ?l1 ?eq |- wt_equation ?G ?l2 ?eq =>
        eapply wt_equation_incl; [| |eauto]; intros
    | Hiface : global_iface_incl ?G1 ?G2, H : wt_block ?G1 _ ?e |- wt_block ?G2 _ ?e =>
        eapply iface_incl_wt_block; eauto
    | H : wt_block ?G ?l1 ?eq |- wt_block ?G ?l2 ?eq =>
        eapply wt_block_incl; [| |eauto]; intros
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
    | |- incl (st_senv ?st1) (st_senv _) =>
        apply incl_map; repeat solve_st_follows
    | H : In ?x ?l1 |- In ?x ?l2 =>
        assert (incl l1 l2); eauto
    | H : HasType ?l1 ?x ?ty |- HasType ?l2 ?x ?ty =>
        eapply HasType_incl; [|eauto]
    | H : IsLast ?l1 ?x |- IsLast ?l2 ?x =>
        eapply IsLast_incl; [|eauto]
    end; auto with datatypes.

  Local Hint Resolve in_combine_l in_combine_r : datatypes.
  Local Hint Resolve incl_tl incl_appl incl_appr incl_app incl_refl : datatypes.

  (** ** Preservation of wt through the first pass *)

  Section unnest_node_wt.
    Variable G1 : @global nolocal local_prefs.
    Variable G2 : @global unnested norm1_prefs.

    Hypothesis Hiface : global_iface_incl G1 G2.

    Fact idents_for_anns_wt : forall vars anns ids st st',
        idents_for_anns anns st = (ids, st') ->
        Forall (fun '(ty, cl) => wt_clock G2.(types) (vars++st_senv st) cl) anns ->
        Forall (wt_exp G2 (vars++st_senv st')) (map (fun '(x, ann) => Evar x ann) ids).
    Proof.
      induction anns; intros ids st st' Hidents Hf;
        repeat inv_bind.
      - constructor.
      - inv Hf. destruct a as [ty cl]. repeat inv_bind.
        assert (Forall (fun '(_, cl) => wt_clock G2.(types) (vars ++ st_senv x0) cl) anns) as Hanns'.
        { simpl_Forall. repeat solve_incl. }
        rewrite Forall_map.
        eapply IHanns in Hanns'; eauto.
        econstructor.
        + repeat constructor; simpl.
          * apply HasType_app; right.
            apply fresh_ident_In in H.
            econstructor; solve_In; eauto.
            2:eapply idents_for_anns_st_follows, st_follows_incl in H0; eauto.
            1,2:reflexivity.
          * repeat solve_incl.
        + simpl_Forall. auto.
    Qed.

    Fact unnest_fby_wt_exp : forall vars e0s es anns,
        Forall (wt_clock G2.(types) vars) (map snd anns) ->
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
      apply Forall_map, Forall2_combine', Forall3_combine'1.
      solve_forall.
      constructor; simpl; try rewrite app_nil_r; eauto.
    Qed.

    Fact unnest_arrow_wt_exp : forall vars e0s es anns,
        Forall (wt_clock G2.(types) vars) (map snd anns) ->
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

    Fact unnest_when_wt_exp : forall vars k ckid tx tn es tys ck,
        In (Tenum tx tn) G2.(types) ->
        HasType vars ckid (Tenum tx tn) ->
        k < length tn ->
        wt_clock G2.(types) vars ck ->
        Forall (wt_exp G2 vars) es ->
        Forall2 (fun e ty => typeof e = [ty]) es tys ->
        Forall (wt_exp G2 vars) (unnest_when (ckid, Tenum tx tn) k es tys ck).
    Proof.
      intros * InE InV Hlt Hwtck Hwt Htys. unfold unnest_when.
      assert (length es = length tys) as Hlength by (eapply Forall2_length in Htys; eauto).
      rewrite Forall_map. apply Forall2_combine'.
      eapply Forall2_ignore2' with (ys:=tys) in Hwt; eauto.
      simpl_Forall.
      repeat (econstructor; simpl; eauto).
      rewrite app_nil_r; auto.
    Qed.

    Import Permutation.

    Fact unnest_merge_wt_exp : forall vars ckid tx tn es tys ck,
        In (Tenum tx tn) G2.(types) ->
        HasType vars ckid (Op.Tenum tx tn) ->
        Permutation (map fst es) (seq 0 (length tn)) ->
        es <> [] ->
        wt_clock G2.(types) vars ck ->
        Forall (fun es => Forall (wt_exp G2 vars) (snd es)) es ->
        Forall (fun es => Forall2 (fun e ty => typeof e = [ty]) (snd es) tys) es ->
        Forall (wt_exp G2 vars) (unnest_merge (ckid, Tenum tx tn) es tys ck).
    Proof with eauto.
      intros *; revert es. induction tys; intros * InE InV Perm Hnnil Hwtck Hwt Htys; simpl; constructor.
      - constructor; auto; try rewrite Forall_map.
        + erewrite map_map, map_ext; eauto. intros (?&?); auto.
        + contradict Hnnil. apply map_eq_nil in Hnnil; auto.
        + clear - Htys Hwt.
          simpl_Forall. destruct l; simpl_Forall; auto.
        + clear - Htys.
          simpl_Forall. inv Htys. now rewrite app_nil_r.
      - eapply IHtys; eauto; try rewrite Forall_map.
        + erewrite map_map, map_ext; eauto. intros (?&?); auto.
        + contradict Hnnil. apply map_eq_nil in Hnnil; auto.
        + clear - Hwt. eapply Forall_impl; [|eauto]; intros (?&?) ?; simpl in *.
          inv H; simpl; auto.
        + clear - Htys. simpl_Forall. inv Htys; auto.
    Qed.

    Fact unnest_case_Total_wt_exp : forall vars e tx tn es tys ck,
        wt_exp G2 vars e ->
        typeof e = [Tenum tx tn] ->
        In (Tenum tx tn) G2.(types) ->
        Permutation (map fst es) (seq 0 (length tn)) ->
        es <> [] ->
        wt_clock G2.(types) vars ck ->
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
        + clear - Htys. simpl_Forall. inv Htys; auto.
    Qed.

    Fact unnest_case_Default_wt_exp : forall vars e tx tn es d tys ck,
        wt_exp G2 vars e ->
        typeof e = [Tenum tx tn] ->
        In (Tenum tx tn) G2.(types) ->
        incl (map fst es) (seq 0 (length tn)) ->
        NoDupMembers es ->
        es <> [] ->
        wt_clock G2.(types) vars ck ->
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
        Forall (wt_exp G2 (vars++st_senv st)) es ->
        unnest_noops_exps cks es st = (es', eqs', st') ->
        Forall (wt_exp G2 (vars++st_senv st')) es' /\
        Forall (wt_equation G2 (vars++st_senv st')) eqs'.
    Proof.
      unfold unnest_noops_exps.
      induction cks; intros * Hlen Hnormed Hnums Hwt Hunt; repeat inv_bind; simpl; auto.
      destruct es; simpl in *; inv Hlen; repeat inv_bind.
      inv Hwt. inv Hnums. inv Hnormed.
      assert (Forall (wt_exp G2 (vars ++ st_senv x2)) es) as Hes.
      { simpl_Forall. repeat solve_incl; eauto with norm. }
      eapply IHcks in Hes as (Hes'&Heqs'). 2-4:eauto.
      2:repeat inv_bind; repeat eexists; eauto; inv_bind; eauto.
      unfold unnest_noops_exp in H.
      rewrite <-length_annot_numstreams in H6. singleton_length.
      destruct p as (?&?).
      split; simpl; try constructor; try (rewrite Forall_app; split); auto.
      1,2:destruct (is_noops_exp); repeat inv_bind; auto.
      + repeat solve_incl.
      + constructor. eapply fresh_ident_In in H.
        eapply HasType_app. right. econstructor; solve_In; eauto.
        2:eapply st_follows_incl in H; eauto; repeat solve_st_follows.
        1,2:reflexivity.
        eapply wt_exp_clockof in H4.
        rewrite clockof_annot, Hsingl in H4. apply Forall_singl in H4.
        repeat solve_incl.
      + repeat constructor; auto; simpl; try rewrite app_nil_r.
        * repeat solve_incl.
        * rewrite typeof_annot, Hsingl; simpl.
          constructor; auto.
          eapply fresh_ident_In in H.
          eapply HasType_app. right. econstructor; solve_In.
          2:eapply st_follows_incl in H; eauto; repeat solve_st_follows.
          1,2:reflexivity.
    Qed.

    Fact mmap2_wt {pref A B} :
      forall vars (k : A -> Fresh pref (list exp * list equation) B) a es' eqs' st st',
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
        2:eapply mmap2_st_follows; eauto; simpl_Forall; eauto.
        eapply IHa in H0 as [Hwt2 Hwt2']; eauto.
        simpl_Forall. take (forall es' eqs' st st', _ -> _ -> _ -> _ /\ _) and eapply it; eauto.
        etransitivity; eauto.
    Qed.

    Fact mmap2_wt' {pref A B} :
      forall vars (k : A -> Fresh pref (enumtag * list exp * list equation) B) a es' eqs' st st',
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
      2:{ simpl_Forall. eapply H4 in H2... etransitivity... }
      repeat rewrite Forall_app. repeat split; eauto.
    Qed.

    Import Permutation.

    Local Hint Resolve iface_incl_wt_clock iface_incl_wt_exp : norm.

    Fact unnest_reset_wt : forall vars e e' eqs' st st' ,
        (forall es' eqs' st0',
            st_follows st0' st' ->
            unnest_exp G1 true e st = (es', eqs', st0') ->
            Forall (wt_exp G2 (vars++st_senv st0')) es' /\
            Forall (wt_equation G2 (vars++st_senv st0')) eqs') ->
        wt_exp G1 (vars++st_senv st) e ->
        typeof e = [OpAux.bool_velus_type] ->
        unnest_reset (unnest_exp G1 true) e st = (e', eqs', st') ->
        typeof e' = [OpAux.bool_velus_type] /\
        wt_exp G2 (vars++st_senv st') e' /\
        Forall (wt_equation G2 (vars++st_senv st')) eqs'.
    Proof.
      intros * Hunwt Hwt Hty Hnorm.
      assert (st_follows st st') as Hfollows.
      { repeat solve_st_follows; destruct e; simpl; intros; eauto. }
      unnest_reset_spec; simpl in *; auto.
      1,2:assert (length l = 1).
      1,3:(eapply unnest_exp_length in Hk0; eauto with norm ltyping;
           rewrite <- length_typeof_numstreams, Hty in Hk0; auto).
      1,2:singleton_length.
      - assert (Hk:=Hk0). eapply unnest_exp_typeof in Hk0; eauto with ltyping; simpl in Hk0.
        specialize (Hunwt _ _ _ (Ker.st_follows_refl _) eq_refl) as (He&Heq); inv He; eauto.
        repeat split; eauto. congruence.
      - assert (Hk:=Hk0). eapply unnest_exp_annot in Hk0; eauto with ltyping. simpl in Hk0. rewrite app_nil_r in Hk0.
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
          apply HasType_app; right. econstructor; solve_In. auto.
        + apply wt_exp_clockof in Hwt.
          rewrite Hk0 in Hhd.
          rewrite clockof_annot in Hwt.
          rewrite typeof_annot in Hty.
          destruct (annot e); simpl in *. inv Hty.
          inv Hwt; simpl in *. do 2 solve_incl.
          repeat solve_incl.
        + inv He; repeat solve_incl.
        + simpl; rewrite app_nil_r, typeof_annot, Hk0, <- typeof_annot, Hty.
          repeat constructor.
          eapply fresh_ident_In in Hfresh.
          apply HasType_app; right. econstructor; solve_In. auto.
        + eapply Forall_impl; [|eauto]; intros; repeat solve_incl.
    Qed.

    Corollary unnest_resets_wt : forall vars es es' eqs' st st' ,
        Forall (fun e => forall es' eqs' st0 st0',
                    unnest_exp G1 true e st0 = (es', eqs', st0') ->
                    st_follows st st0 ->
                    st_follows st0' st' ->
                    Forall (wt_exp G2 (vars++st_senv st0')) es' /\
                    Forall (wt_equation G2 (vars++st_senv st0')) eqs') es ->
        Forall (wt_exp G1 (vars++st_senv st)) es ->
        Forall (fun e => typeof e = [OpAux.bool_velus_type]) es ->
        mmap2 (unnest_reset (unnest_exp G1 true)) es st = (es', eqs', st') ->
        Forall (fun e => typeof e = [OpAux.bool_velus_type]) es' /\
        Forall (wt_exp G2 (vars++st_senv st')) es' /\
        Forall (wt_equation G2 (vars++st_senv st')) (concat eqs').
    Proof.
      induction es; intros * F Wt Tys Map; inv F; inv Wt; inv Tys;
        repeat inv_bind; simpl in *; auto.
      assert (Hmap:=H0). eapply IHes in H0 as (Tys1&Wt1&Wt2); eauto.
      3:simpl_Forall; repeat solve_incl.
      2:{ simpl_Forall.
          take (forall es' eqs' st st', _ -> _ -> _ -> _ /\ _) and eapply it in H8; eauto.
          repeat solve_st_follows. }
      eapply unnest_reset_wt in H as (Tys2&Wt3&Wt4); eauto.
      repeat split; try constructor; auto.
      - repeat solve_incl.
      - apply Forall_app; split; auto.
        simpl_Forall; repeat solve_incl.
      - intros * Follows Un. eapply H1 in Un; eauto. 1,2:repeat solve_st_follows.
    Qed.

    Local Hint Resolve iface_incl_wt_type : norm.

    Fact unnest_controls_fst : forall (es : list (enumtag * list exp)) es' eqs' st st',
        mmap2 (fun '(i, es) => bind2 (mmap2 (unnest_exp G1 true) es)
                                  (fun es' eqs' => ret (i, concat es', concat eqs'))) es st = (es', eqs', st') ->
        map fst es' = map fst es.
    Proof.
      induction es as [|(?&?)]; intros * Hmmap;
        repeat inv_bind; simpl; f_equal; eauto.
    Qed.

    Lemma unnest_exp_wt : forall vars e is_control es' eqs' st st',
        wt_exp G1 (vars++st_senv st) e ->
        unnest_exp G1 is_control e st = (es', eqs', st') ->
        Forall (wt_exp G2 (vars++st_senv st')) es' /\
        Forall (wt_equation G2 (vars++st_senv st')) eqs'.
    Proof with eauto with norm ltyping.
      Local Ltac solve_mmap2 :=
        simpl_Forall;
        match goal with
        | Hnorm : unnest_exp _ _ _ _ = _, H : context [unnest_exp _ _ _ _ = _ -> _] |- _ =>
          eapply H in Hnorm as [? ?]; eauto;
          [split|]; try simpl_Forall; repeat solve_incl
        end.

      induction e using exp_ind2; intros * Hwt Hnorm; simpl in *; inv Hwt.
      - (* const *)
        repeat inv_bind...
      - (* enum *)
        repeat inv_bind...
      - (* var *)
        repeat inv_bind.
        repeat constructor...
      - (* last *)
        repeat inv_bind.
        repeat constructor...
      - (* unop *)
        repeat inv_bind.
        assert (length x = numstreams e) as Hlen by eauto with norm ltyping.
        rewrite <- length_typeof_numstreams, H3 in Hlen; simpl in Hlen.
        singleton_length.
        assert (Hnorm:=H); eapply IHe in H as [Hwt1 Hwt1']; eauto.
        repeat econstructor...
        + inv Hwt1; eauto.
        + eapply unnest_exp_typeof in Hnorm; simpl in Hnorm; eauto with ltyping.
          rewrite app_nil_r, H3 in Hnorm...
        + repeat solve_incl.
      - (* binop *)
        repeat inv_bind.
        assert (length x = numstreams e1) as Hlen1 by eauto with norm ltyping.
        rewrite <- length_typeof_numstreams, H5 in Hlen1; simpl in Hlen1.
        assert (length x2 = numstreams e2) as Hlen2 by eauto with norm ltyping.
        rewrite <- length_typeof_numstreams, H6 in Hlen2; simpl in Hlen2. repeat singleton_length.
        assert (Hnorm1:=H); eapply IHe1 in H as [Hwt1 Hwt1']; eauto.
        assert (Hnorm2:=H0); eapply IHe2 in H0 as [Hwt2 Hwt2']; eauto. 2:repeat solve_incl.
        repeat econstructor...
        + inv Hwt1. repeat solve_incl.
        + inv Hwt2...
        + eapply unnest_exp_typeof in Hnorm1; simpl in Hnorm1; eauto with ltyping.
          rewrite app_nil_r, H5 in Hnorm1...
        + eapply unnest_exp_typeof in Hnorm2; simpl in Hnorm2; eauto with ltyping.
          rewrite app_nil_r, H6 in Hnorm2...
        + repeat solve_incl.
        + apply Forall_app; split; auto.
          simpl_Forall. repeat solve_incl.
      - (* extcall *)
        repeat inv_bind.
        assert (Hnorm1:=H0). eapply mmap2_wt with (vars:=vars++st_senv x1) in H0 as [Hwt1 Hwt1']...
        2:solve_mmap2.
        apply mmap2_unnest_exp_typesof in Hnorm1 as Htys; eauto with ltyping.
        assert (HasType (vars ++ st_senv st') x2 (Tprimitive tyout)) as Hty.
        { take (fresh_ident _ _ _ = _) and apply fresh_ident_In in it.
          apply HasType_app, or_intror.
          econstructor; solve_In. auto. }
        repeat constructor; auto.
        3:eapply Forall_impl; [|eauto]; intros. 1,3:repeat solve_incl.
        econstructor; simpl_Forall; repeat solve_incl.
        1-3:try rewrite Htys; eauto.
        destruct Hiface as (?&?&?); eauto.
      - (* fby *)
        repeat inv_bind.
        assert (Hnorm1:=H1). eapply mmap2_wt with (vars:=vars++st_senv x1) in H1 as [Hwt1 Hwt1']...
        assert (Hnorm2:=H2). eapply mmap2_wt with (vars:=vars++st_senv x4) in H2 as [Hwt2 Hwt2']...
        2,3:solve_mmap2.
        repeat rewrite Forall_app. repeat split.
        3-4:simpl_Forall; repeat solve_incl.
        + eapply idents_for_anns_wt in H3...
          simpl_Forall; repeat solve_incl.
        + assert (Forall (wt_exp G2 (vars++st_senv st')) (unnest_fby (concat x2) (concat x6) a)) as Hwcfby.
          { eapply unnest_fby_wt_exp...
            1-3:simpl_Forall; repeat solve_incl.
            + eapply mmap2_unnest_exp_typesof'' in Hnorm1... congruence.
            + eapply mmap2_unnest_exp_typesof'' in Hnorm2... congruence. }
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
            eapply Forall2_swap_args. simpl_Forall.
            rewrite typeof_annot, H1; auto. }
          eapply mk_equations_Forall; simpl_Forall.
          repeat constructor; eauto.
          rewrite app_nil_r, H10.
          constructor; auto. eapply idents_for_anns_incl_ty in H3; eauto.
          apply HasType_app; auto.
      - (* arrow *)
        repeat inv_bind.
        assert (Hnorm1:=H1). eapply mmap2_wt with (vars:=vars++st_senv x1) in H1 as [Hwt1 Hwt1']...
        assert (Hnorm2:=H2). eapply mmap2_wt with (vars:=vars++st_senv x4) in H2 as [Hwt2 Hwt2']...
        2,3:solve_mmap2.
        repeat rewrite Forall_app. repeat split.
        3-4:simpl_Forall; repeat solve_incl.
        + eapply idents_for_anns_wt in H3...
          simpl_Forall; repeat solve_incl.
        + assert (Forall (wt_exp G2 (vars++st_senv st')) (unnest_arrow (concat x2) (concat x6) a)) as Hwcfby.
          { eapply unnest_arrow_wt_exp...
            1-3:simpl_Forall; repeat solve_incl.
            + eapply mmap2_unnest_exp_typesof'' in Hnorm1... congruence.
            + eapply mmap2_unnest_exp_typesof'' in Hnorm2... congruence. }
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
            eapply Forall2_swap_args. simpl_Forall.
            rewrite typeof_annot, H1; auto. }
          eapply mk_equations_Forall; simpl_Forall.
          repeat constructor; eauto.
          take (typeof _ = _) and rewrite app_nil_r, it.
          constructor; auto. eapply idents_for_anns_incl_ty in H3; eauto.
          apply HasType_app; auto.
      - (* when *)
        repeat inv_bind.
        assert (Hnorm:=H0). eapply mmap2_wt with (vars:=vars++st_senv st') in H0 as [Hwt1 Hwt1']; eauto with norm.
        2:solve_mmap2.
        split; eauto.
        eapply unnest_when_wt_exp; eauto.
        + apply Hiface; eauto.
        + repeat solve_incl.
        + repeat solve_incl.
        + eapply mmap2_unnest_exp_typesof'' in Hnorm; eauto with ltyping.
      - (* merge *)
        repeat inv_bind.
        assert (Hnorm1:=H0). eapply mmap2_wt' with (vars:=vars++st_senv x2) in H0 as [Hwt1 Hwt1']; eauto.
        2:(intros; destruct a; repeat solve_st_follows).
        2:{ simpl_Forall. repeat inv_bind. eapply mmap2_wt in H10; eauto with norm.
            solve_mmap2. }
        remember (unnest_merge _ _ _ _) as merges.
        assert (Forall (wt_exp G2 (vars++st_senv x2)) merges) as Hwt'.
        { subst. apply unnest_merge_wt_exp; auto.
          - apply Hiface; eauto.
          - repeat solve_incl.
          - erewrite unnest_controls_fst; eauto.
          - apply mmap2_length_1 in Hnorm1.
            intro contra; subst. destruct es; simpl in *; try congruence.
            exfalso; eauto.
          - repeat solve_incl.
          - eapply Forall_concat in Hwt1; rewrite Forall_map in Hwt1; eauto.
          - eapply mmap2_mmap2_unnest_exp_typesof in Hnorm1...
            simpl_Forall...
        }
        destruct is_control; repeat inv_bind; repeat rewrite Forall_app; repeat split.
        1,2,5:simpl_Forall; repeat solve_incl.
        + specialize (idents_for_anns_incl_ty _ _ _ _ H0) as Hincl.
          apply idents_for_anns_wt with (vars:=vars) in H0...
          rewrite Forall_forall; intros.
          simpl_In. repeat solve_incl.
        + remember (unnest_merge _ _ _ _) as merges.
          assert (Forall2 (fun '(ty, _) e => annot e = [(ty, nck)]) (map snd x3) merges) as Htys.
          { eapply idents_for_anns_values in H0. rewrite H0, Forall2_map_1.
            subst; eapply unnest_merge_annot; eauto. } rewrite Forall2_map_1 in Htys.
          eapply Forall2_ignore1' with (xs:=x3) in Hwt'.
          2:{ subst. apply idents_for_anns_length in H0. rewrite map_length in H0.
              rewrite unnest_merge_length... }
          apply mk_equations_Forall; simpl_Forall; simpl in *.
          repeat constructor... 1:repeat solve_incl.
          take (annot _ = _) and rewrite typeof_annot, it, app_nil_r; simpl.
          constructor; auto.
          eapply idents_for_anns_incl_ty in H0; eauto.
          apply HasType_app; auto.
      - (* case (total) *)
        repeat inv_bind.
        assert (Hnorm0:=H1). eapply IHe in H1 as (Hwt1&Hwt1'); eauto.
        assert (Hnorm1:=H2). eapply mmap2_wt' with (vars:=vars++st_senv x7) in H2 as (Hwt2&Hwt2'); eauto.
        2:(intros; destruct a; repeat solve_st_follows).
        2:{ simpl_Forall. repeat inv_bind. eapply mmap2_wt in H3...
            solve_mmap2. }
        remember (unnest_case _ _ _ _ _) as cases.
        assert (Forall (wt_exp G2 (vars++st_senv x7)) cases) as Hwt'.
        { assert (Hnorm0':=Hnorm0). eapply unnest_exp_length in Hnorm0'...
          rewrite <-length_typeof_numstreams, H6 in Hnorm0'; simpl in Hnorm0'.
          singleton_length. apply Forall_singl in Hwt1.
          subst. eapply unnest_case_Total_wt_exp; auto.
          - repeat solve_incl.
          - eapply unnest_exp_typeof in Hnorm0; eauto with ltyping; simpl in *; rewrite app_nil_r in *.
            rewrite Hnorm0; eauto.
          - apply Hiface; eauto.
          - erewrite unnest_controls_fst; eauto.
          - apply mmap2_length_1 in Hnorm1.
            intro contra; subst. destruct es; simpl in *; try congruence.
            exfalso; eauto.
          - repeat solve_incl.
          - eapply Forall_concat in Hwt2; rewrite Forall_map in Hwt2; eauto.
          - eapply mmap2_mmap2_unnest_exp_typesof in Hnorm1...
            simpl_Forall...
        }
        destruct is_control; repeat inv_bind; repeat rewrite Forall_app; repeat split; auto.
        1,4,5:simpl_Forall; repeat solve_incl.
        + specialize (idents_for_anns_incl_ty _ _ _ _ H1) as Hincl.
          apply idents_for_anns_wt with (vars:=vars) in H1...
          rewrite Forall_forall; intros.
          simpl_In. repeat solve_incl.
        + remember (unnest_case _ _ _ _ _) as cases.
          assert (Forall2 (fun '(ty, _) e => annot e = [(ty, nck)]) (map snd x4) cases) as Htys.
          { eapply idents_for_anns_values in H1. rewrite H1, Forall2_map_1.
            subst; eapply unnest_case_annot; eauto. } rewrite Forall2_map_1 in Htys.
          eapply Forall2_ignore1' with (xs:=x4) in Hwt'.
          2:{ subst. apply idents_for_anns_length in H1. rewrite map_length in H1.
              rewrite unnest_case_length... }
          apply mk_equations_Forall; simpl_Forall.
          repeat constructor... 1:repeat solve_incl.
          take (annot _ = _) and rewrite typeof_annot, it, app_nil_r; simpl.
          constructor; auto.
          eapply idents_for_anns_incl_ty in H1; eauto.
          apply HasType_app; auto.
      - (* case (default) *)
        repeat inv_bind.
        assert (Hnorm0:=H1). eapply IHe in H1 as (Hwt1&Hwt1')...
        assert (Hnorm1:=H2). eapply mmap2_wt' with (vars:=vars++st_senv x7) in H2 as (Hwt2&Hwt2')...
        2:(intros; destruct a; repeat solve_st_follows).
        2:{ simpl_Forall. repeat inv_bind. take (mmap2 _ _ _ = _) and eapply mmap2_wt in it...
            solve_mmap2. }
        assert (Hnorm2:=H3). eapply mmap2_wt with (vars:=vars++st_senv x7) in H3 as (Hwt3&Hwt3')...
        2:solve_mmap2.
        remember (unnest_case _ _ _ _ _) as cases.
        assert (Forall (wt_exp G2 (vars++st_senv x7)) cases) as Hwt'.
        { assert (Hnorm0':=Hnorm0). eapply unnest_exp_length in Hnorm0'...
          rewrite <-length_typeof_numstreams, H6 in Hnorm0'; simpl in Hnorm0'.
          singleton_length. apply Forall_singl in Hwt1.
          subst. eapply unnest_case_Default_wt_exp; auto.
          - repeat solve_incl.
          - eapply unnest_exp_typeof in Hnorm0; eauto with ltyping; simpl in *; rewrite app_nil_r in *.
            rewrite Hnorm0; eauto.
          - apply Hiface; eauto.
          - erewrite unnest_controls_fst; eauto.
          - erewrite fst_NoDupMembers, unnest_controls_fst, <-fst_NoDupMembers; eauto.
          - apply mmap2_length_1 in Hnorm1.
            intro contra; subst. destruct es; simpl in *; try congruence.
            exfalso; eauto.
          - repeat solve_incl.
          - eapply Forall_concat in Hwt2; rewrite Forall_map in Hwt2; eauto.
          - eapply mmap2_mmap2_unnest_exp_typesof in Hnorm1...
            simpl_Forall...
          - eapply mmap2_unnest_exp_typesof'' in Hnorm2...
        }
        destruct is_control; repeat inv_bind; repeat rewrite Forall_app; repeat split; auto.
        1,4-6:simpl_Forall; repeat solve_incl.
        + specialize (idents_for_anns_incl_ty _ _ _ _ H1) as Hincl.
          apply idents_for_anns_wt with (vars:=vars) in H1...
          rewrite Forall_forall; intros.
          simpl_In. repeat solve_incl.
        + remember (unnest_case _ _ _ _ _) as cases.
          assert (Forall2 (fun '(ty, _) e => annot e = [(ty, nck)]) (map snd x6) cases) as Htys.
          { eapply idents_for_anns_values in H1. rewrite H1, Forall2_map_1.
            subst; eapply unnest_case_annot; eauto. } rewrite Forall2_map_1 in Htys.
          eapply Forall2_ignore1' with (xs:=x6) in Hwt'.
          2:{ subst. apply idents_for_anns_length in H1. rewrite map_length in H1.
              rewrite unnest_case_length... }
          apply mk_equations_Forall; simpl_Forall.
          repeat constructor... 1:repeat solve_incl.
          take (annot _ = _) and rewrite typeof_annot, it, app_nil_r; simpl.
          constructor; auto.
          eapply idents_for_anns_incl_ty in H1; eauto.
          apply HasType_app; auto.
      - (* app *)
        repeat inv_bind.
        assert (Hun:=H3). eapply unnest_resets_wt in H3 as [Hwt2 [Hwt2' Hwt2'']]; simpl...
        2,3:simpl_Forall. 2:eapply H0 in H13; eauto. 2,3:repeat solve_incl.

        assert (Hnorm:=H1). eapply mmap2_wt with (vars:=vars++st_senv x1) in H1 as [Hwt1 Hwt1']...
        2:solve_mmap2. clear H0.

        assert (length (find_node_incks G1 f) = length (concat x6)) as Hlen1.
        { unfold find_node_incks. rewrite H7.
          eapply Forall2_length in H8. rewrite map_length.
          eapply mmap2_unnest_exp_length in Hnorm; eauto with ltyping. rewrite length_typesof_annots in H8.
          congruence. }
        assert (Forall (fun e : exp => numstreams e = 1) (concat x6)) as Hnum.
        { eapply mmap2_unnest_exp_numstreams; eauto. }

        split; [|constructor]; repeat rewrite Forall_app; repeat split.
        4,6:eapply Forall_impl; [|eauto]; intros; repeat solve_incl.
        + specialize (idents_for_anns_incl_ty _ _ _ _ H4) as Hincl.
          eapply idents_for_anns_wt with (vars:=vars) in H4... simpl_Forall; repeat solve_incl.
        + apply Hiface in H7 as (?&?&?&?&Hin&Hout).
          repeat econstructor; eauto.
          * eapply unnest_noops_exps_wt with (vars:=vars) in H2 as (?&?); eauto.
            simpl_Forall; repeat solve_incl.
            eapply mmap2_normalized_lexp in Hnorm; eauto.
          * simpl_Forall; repeat solve_incl.
          * erewrite unnest_noops_exps_typesof, mmap2_unnest_exp_typesof. 3-6:eauto. 2:eauto with ltyping.
            eapply Forall2_eq in Hin. simpl_Forall.
            eapply Forall2_trans_ex in Hin; [|eauto]. simpl_Forall. inv_equalities. auto.
          * eapply idents_for_anns_values in H4; subst.
            eapply Forall2_eq in Hout. simpl_Forall.
            eapply Forall2_trans_ex in Hout; [|eauto]. simpl_Forall. inv_equalities. auto.
          * eapply idents_for_anns_wt with (vars:=vars) in H4.
            -- simpl_Forall. inv H4. solve_incl.
            -- simpl_Forall; simpl in *; repeat solve_incl.
        + simpl. rewrite app_nil_r. simpl_Forall.
          eapply idents_for_anns_incl_ty in H4; eauto. solve_incl.
        + assert (Hun2:=H2). eapply unnest_noops_exps_wt in H2 as (?&?); eauto.
          eapply Forall_impl; [|eauto]; intros; repeat solve_incl.
          eapply mmap2_normalized_lexp in Hnorm; eauto.
    Qed.

    Corollary mmap2_unnest_exp_wt : forall vars is_control es es' eqs' st st' ,
        Forall (wt_exp G1 (vars++st_senv st)) es ->
        mmap2 (unnest_exp G1 is_control) es st = (es', eqs', st') ->
        Forall (wt_exp G2 (vars++st_senv st')) (concat es') /\
        Forall (wt_equation G2 (vars++st_senv st')) (concat eqs').
    Proof.
      intros * Hwt Hmap.
      eapply mmap2_wt in Hmap; eauto using unnest_exp_st_follows.
      simpl_Forall.
      eapply unnest_exp_wt with (vars:=vars) in H0 as [? ?]; eauto.
      split. 1,2:simpl_Forall. all:repeat solve_incl.
    Qed.

    Corollary unnest_exps_wt : forall vars es es' eqs' st st' ,
        Forall (wt_exp G1 (vars++st_senv st)) es ->
        unnest_exps G1 es st = (es', eqs', st') ->
        Forall (wt_exp G2 (vars++st_senv st')) es' /\
        Forall (wt_equation G2 (vars++st_senv st')) eqs'.
    Proof.
      intros * Hwt Hmap.
      unfold unnest_exps in Hmap; repeat inv_bind.
      eapply mmap2_unnest_exp_wt in H; eauto.
    Qed.

    Fact unnest_rhs_wt : forall vars e es' eqs' st st' ,
        wt_exp G1 (vars++st_senv st) e ->
        unnest_rhs G1 e st = (es', eqs', st') ->
        Forall (wt_exp G2 (vars++st_senv st')) es' /\
        Forall (wt_equation G2 (vars++st_senv st')) eqs'.
    Proof with eauto with norm ltyping.
      intros * Hwt Hnorm.
      destruct e; unfold unnest_rhs in Hnorm;
        try (solve [eapply unnest_exp_wt in Hnorm; eauto]); inv Hwt.
      - (* extcall *)
        repeat inv_bind.
        assert (Hnorm1:=H). eapply unnest_exps_wt in H as [Hwt1 Hwt1']...
        eapply unnest_exps_typesof in Hnorm1 as Htys; eauto with ltyping.
        repeat econstructor; eauto. 4:repeat solve_incl.
        1-3:try erewrite Htys; eauto.
        destruct Hiface as (?&?&?); eauto.
      - (* fby *)
        repeat inv_bind.
        assert (Hnorm1:=H). eapply unnest_exps_wt in H as [Hwt1 Hwt1']...
        assert (Hnorm2:=H0). eapply unnest_exps_wt with (vars:=vars) in H0 as [Hwt2 Hwt2']...
        2:simpl_Forall; repeat solve_incl.
        repeat rewrite Forall_app; repeat split... 2:simpl_Forall; repeat solve_incl.
        eapply unnest_fby_wt_exp; eauto.
        1-2:simpl_Forall; repeat solve_incl.
        + unfold unnest_exps in Hnorm1; repeat inv_bind.
          eapply mmap2_unnest_exp_typesof'' in H... congruence.
        + unfold unnest_exps in Hnorm2; repeat inv_bind.
          eapply mmap2_unnest_exp_typesof'' in H... congruence.
      - (* arrow *)
        repeat inv_bind.
        assert (Hnorm1:=H). eapply unnest_exps_wt in H as [Hwt1 Hwt1']...
        assert (Hnorm2:=H0). eapply unnest_exps_wt with (vars:=vars) in H0 as [Hwt2 Hwt2']...
        2:simpl_Forall; repeat solve_incl.
        repeat rewrite Forall_app; repeat split... 2:simpl_Forall; repeat solve_incl.
        eapply unnest_arrow_wt_exp; eauto.
        1-2:simpl_Forall; repeat solve_incl.
        + unfold unnest_exps in Hnorm1; repeat inv_bind.
          eapply mmap2_unnest_exp_typesof'' in H... congruence.
        + unfold unnest_exps in Hnorm2; repeat inv_bind.
          eapply mmap2_unnest_exp_typesof'' in H... congruence.
      - (* app *)
        repeat inv_bind.
        assert (st_follows st x4) as Hfollows1 by repeat solve_st_follows.
        assert (st_follows x4 st') as Hfollows2 by repeat solve_st_follows.
        eapply unnest_resets_wt with (vars:=vars) in H1 as [Hwt3 [Hwt3' Hwt3'']]...
        2,3:simpl_Forall. 2:take (unnest_exp _ _ _ _ = _) and eapply unnest_exp_wt in it; eauto.
        2,3:repeat solve_incl.

        assert (Hnorm:=H). eapply unnest_exps_wt in H as [Hwt1 Hwt1']; eauto.
        rewrite Forall_app.

        assert (length (find_node_incks G1 i) = length x) as Hlen1.
        { unfold find_node_incks. rewrite H5.
          eapply Forall2_length in H6. rewrite map_length.
          eapply unnest_exps_length in Hnorm... rewrite length_typesof_annots in H6.
          congruence. }
        assert (Forall (fun e : exp => numstreams e = 1) x) as Hnum.
        { eapply unnest_exps_numstreams; eauto. }

        repeat split; auto.
        2:simpl_Forall; repeat solve_incl.
        repeat constructor.
        apply Hiface in H5 as (?&?&?&?&Hin&Hout).
        repeat econstructor; eauto.
        + eapply unnest_noops_exps_wt with (vars:=vars) in H0 as (?&?); auto.
          simpl_Forall; repeat solve_incl.
          eapply unnest_exps_normalized_lexp in Hnorm; eauto.
        + erewrite unnest_noops_exps_typesof, unnest_exps_typesof. 3-6:eauto. 2:eauto with ltyping.
          eapply Forall2_eq in Hin. simpl_Forall.
          eapply Forall2_trans_ex in Hin; [|eauto]. simpl_Forall. inv_equalities. auto.
        + eapply Forall2_eq in Hout. simpl_Forall.
          eapply Forall2_trans_ex in Hout; [|eauto]. simpl_Forall. inv_equalities. auto.
        + simpl_Forall; repeat solve_incl.
        + apply Forall_app; split. 2:simpl_Forall; repeat solve_incl.
          eapply unnest_noops_exps_wt with (vars:=vars) in H0 as (?&?); auto.
          simpl_Forall; repeat solve_incl.
          eapply unnest_exps_normalized_lexp in Hnorm; eauto.
    Qed.

    Corollary unnest_rhss_wt : forall vars es es' eqs' st st' ,
        Forall (wt_exp G1 (vars++st_senv st)) es ->
        unnest_rhss G1 es st = (es', eqs', st') ->
        Forall (wt_exp G2 (vars++st_senv st')) es' /\
        Forall (wt_equation G2 (vars++st_senv st')) eqs'.
    Proof with eauto with norm.
      intros * Hwt Hnorm.
      unfold unnest_rhss in Hnorm; repeat inv_bind.
      eapply mmap2_wt in H...
      simpl_Forall.
      eapply unnest_rhs_wt with (vars:=vars) in H1 as [? ?]...
      split. 1,2:simpl_Forall. 1,2,3:repeat solve_incl.
    Qed.

    Fact unnest_equation_wt_eq : forall vars eq eqs' st st' ,
        wt_equation G1 (vars++st_senv st) eq ->
        unnest_equation G1 eq st = (eqs', st') ->
        Forall (wt_equation G2 (vars++st_senv st')) eqs'.
    Proof with eauto with norm ltyping.
      intros * Hwt Hnorm.
      destruct eq as [xs es]; simpl in Hnorm.
      repeat inv_bind. destruct Hwt.
      assert (Hnorm:=H). eapply unnest_rhss_wt in H as [Hwt Hwt']...
      apply Forall_app. split; eauto.
      assert (st_follows st st') as Hfollows by eauto with norm.
      eapply unnest_rhss_typesof in Hnorm...
      rewrite <- Hnorm in H1.
      clear Hnorm. revert xs H1.
      induction x; intros xs H1; simpl in *.
      + simpl_Forall. inv H.
      + inv Hwt.
        apply Forall2_length in H1 as Hlen.
        erewrite <-firstn_skipn with (n:=numstreams a) (l:=xs) in H1. apply Forall2_app_split in H1 as (Hf1&Hf2).
        2:{ rewrite app_length in Hlen.
            rewrite firstn_length. rewrite Hlen.
            rewrite length_typeof_numstreams.
            apply Nat.min_l. lia. }
        destruct xs; repeat constructor; simpl; try rewrite app_nil_r...
        simpl_Forall. repeat solve_incl.
    Qed.

    Lemma unnest_block_wt : forall vars d blocks' st st',
        wt_block G1 (vars++st_senv st) d ->
        unnest_block G1 d st = (blocks', st') ->
        Forall (wt_block G2 (vars++st_senv st')) blocks'.
    Proof.
      induction d using block_ind2; intros * Hwt Hun; repeat inv_bind;
        eauto using iface_incl_wt_block.
      - inv Hwt.
        eapply unnest_equation_wt_eq in H; eauto.
        simpl_Forall. constructor; auto.
      - inv Hwt.
        eapply unnest_exp_wt in H as Wt; eauto. destruct Wt as (Wt1&Wt2).
        apply unnest_exp_length in H as Len; eauto with ltyping.
        rewrite <-length_typeof_numstreams, H6 in Len. simpl in *. singleton_length.
        repeat constructor. 2:simpl_Forall; constructor; repeat solve_incl.
        eapply wt_Blast with (ty:=ty); repeat solve_incl.
        + simpl_Forall. auto.
        + apply unnest_exp_typeof in H; eauto with ltyping.
          simpl in *. rewrite app_nil_r in *. congruence.
      - inv Hwt.
        assert (st_follows x0 st') as Hfollows by (repeat solve_st_follows).
        eapply unnest_reset_wt with (vars:=vars) in H1 as (Hty1&Hwt1&Hwt1'); eauto.
        2:{ intros. eapply unnest_exp_wt in H3; eauto; repeat solve_incl. }
        2:repeat solve_incl.
        apply Forall_app; split.
        + clear - H H0 H4 Hty1 Hwt1 Hfollows.
          revert st x x0 Hfollows H H0 H4.
          induction blocks; intros * Hfollows Hf Hmap Hwt; repeat inv_bind; simpl; auto;
            inv Hf; inv Hwt.
          rewrite map_app, Forall_app; split.
          * eapply H3 in H; eauto.
            rewrite Forall_map. eapply Forall_impl; [|eauto]; intros.
            econstructor; eauto.
            constructor; auto. repeat solve_incl.
          * eapply IHblocks; eauto.
            simpl_Forall; repeat solve_incl.
        + simpl_Forall. constructor; auto.
    Qed.

    Corollary unnest_blocks_wt_block : forall vars blocks blocks' st st' ,
        Forall (wt_block G1 (vars++st_senv st)) blocks ->
        unnest_blocks G1 blocks st = (blocks', st') ->
        Forall (wt_block G2 (vars++st_senv st')) blocks'.
    Proof with eauto.
      induction blocks; intros * Hwt Hnorm;
        unfold unnest_blocks in Hnorm;
        repeat inv_bind; simpl; auto.
      inv Hwt; apply Forall_app. split.
      - eapply unnest_block_wt in H...
        simpl_Forall; repeat solve_incl.
      - assert (unnest_blocks G1 blocks x1 = (concat x2, st')) as Hnorm.
        { unfold unnest_blocks; repeat inv_bind; eauto. }
        eapply IHblocks in Hnorm...
        simpl_Forall; repeat solve_incl.
    Qed.

    (** ** Preservation of wt_clock *)

    Definition st_clocks {pref} (st : fresh_st pref (Op.type * clock)) : list clock :=
      map (fun '(_, (_, cl)) => cl) (st_anns st).

    Fact fresh_ident_wt_clock : forall types pref hint vars ty cl id (st st' : fresh_st pref _),
        Forall (wt_clock types vars) (st_clocks st) ->
        wt_clock types vars cl ->
        fresh_ident hint (ty, cl) st = (id, st') ->
        Forall (wt_clock types vars) (st_clocks st').
    Proof.
      intros * Hclocks Hwt Hfresh.
      apply fresh_ident_anns in Hfresh.
      unfold st_clocks in *. setoid_rewrite Hfresh; simpl.
      constructor; auto.
    Qed.

    Corollary idents_for_anns_wt_clock : forall types vars anns ids st st',
        Forall (wt_clock types vars) (st_clocks st) ->
        Forall (wt_clock types vars) (map snd anns) ->
        idents_for_anns anns st = (ids, st') ->
        Forall (wt_clock types vars) (st_clocks st').
    Proof.
      induction anns; intros ids st st' Hclocks Hwt Hidents;
        repeat inv_bind.
      - assumption.
      - inv Hwt. destruct a as [ty cl]. repeat inv_bind.
        eapply IHanns in H0; eauto.
        eapply fresh_ident_wt_clock; eauto.
    Qed.

    Fact mmap2_wt_clock {A A1 A2 : Type} :
      forall types vars (k : A -> FreshAnn (A1 * A2)) a a1s a2s st st',
        Forall (wt_clock types (vars++st_senv st)) (st_clocks st) ->
        mmap2 k a st = (a1s, a2s, st') ->
        (forall st st' a es a2s, k a st = (es, a2s, st') -> st_follows st st') ->
        Forall (fun a => forall a1s a2s st0 st0',
                    Forall (wt_clock types (vars++st_senv st0)) (st_clocks st0) ->
                    k a st0 = (a1s, a2s, st0') ->
                    st_follows st st0 ->
                    st_follows st0' st' ->
                    Forall (wt_clock types (vars++st_senv st0')) (st_clocks st0')) a ->
        Forall (wt_clock types (vars++st_senv st')) (st_clocks st').
    Proof with eauto.
      induction a; intros a1s a2s st st' Hclocks Hmap Hfollows Hf;
        repeat inv_bind...
      inv Hf.
      specialize (H3 _ _ _ _ Hclocks H).
      eapply IHa in H3...
      - reflexivity.
      - eapply mmap2_st_follows...
        simpl_Forall...
      - solve_forall.
        eapply H2 in H5...
        etransitivity...
    Qed.

    Fact unnest_reset_wt_clock : forall vars e e' eqs' st st' ,
        (forall es' eqs' st0',
            st_follows st0' st' ->
            unnest_exp G1 true e st = (es', eqs', st0') ->
            Forall (wt_clock G2.(types) (vars++st_senv st0')) (st_clocks st0')) ->
        wt_exp G1 (vars++st_senv st) e ->
        Forall (wt_clock G2.(types) (vars++st_senv st)) (st_clocks st) ->
        unnest_reset (unnest_exp G1 true) e st = (e', eqs', st') ->
        Forall (wt_clock G2.(types) (vars++st_senv st')) (st_clocks st').
    Proof with eauto.
      intros * Hkck Hwt Hclocks Hnorm.
      unnest_reset_spec; simpl in *; eauto. eapply Hkck; eauto; reflexivity.
      assert (Forall (wt_clock G2.(types) (vars++st_senv st')) (clockof e)) as Hwtck.
      { eapply wt_exp_clockof in Hwt.
        simpl_Forall; repeat solve_incl. }
      eapply fresh_ident_wt_clock in Hfresh...
      - assert (st_follows f st') as Hfollows by repeat solve_st_follows.
        specialize (Hkck _ _ _ Hfollows eq_refl).
        simpl_Forall; repeat solve_incl.
      - assert (Hk:=Hk0). eapply unnest_exp_annot in Hk0; eauto with ltyping.
        rewrite clockof_annot, <- Hk0 in Hwtck.
        destruct l; simpl in *. 1:inv Hhd; constructor.
        destruct (annot e0); simpl in *. inv Hhd; constructor.
        subst; simpl in *.
        inv Hwtck. repeat solve_incl.
    Qed.

    Fact unnest_resets_wt_clock : forall vars es es' eqs' st st' ,
        Forall (fun e => forall es' eqs' st0 st0',
                    Forall (wt_clock G2.(types) (vars++st_senv st0)) (st_clocks st0) ->
                    unnest_exp G1 true e st0 = (es', eqs', st0') ->
                    st_follows st st0 ->
                    st_follows st0' st' ->
                    Forall (wt_clock G2.(types) (vars++st_senv st0')) (st_clocks st0')) es ->
        Forall (wt_exp G1 (vars++st_senv st)) es ->
        Forall (wt_clock G2.(types) (vars++st_senv st)) (st_clocks st) ->
        mmap2 (unnest_reset (unnest_exp G1 true)) es st = (es', eqs', st') ->
        Forall (wt_clock G2.(types) (vars++st_senv st')) (st_clocks st').
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
        Forall (wt_exp G2 (vars++st_senv st)) es ->
        Forall (wt_clock G2.(types) (vars++st_senv st)) (st_clocks st) ->
        unnest_noops_exps cks es st = (es', eqs', st') ->
        Forall (wt_clock G2.(types) (vars++st_senv st')) (st_clocks st').
    Proof.
      unfold unnest_noops_exps.
      induction cks; intros * Hlen Hnormed Hnum Hwt1 Hwt2 Hunt; repeat inv_bind; simpl; auto.
      destruct es; simpl in *; inv Hlen; repeat inv_bind.
      inv Hnormed. inv Hnum. inv Hwt1.
      eapply IHcks with (st:=x2); eauto.
      simpl_Forall; repeat solve_incl; eapply unnest_noops_exp_st_follows in H; eauto.
      2:repeat inv_bind; repeat eexists; eauto; inv_bind; eauto.
      clear H0 H1.
      rewrite <-length_annot_numstreams in H6. singleton_length. destruct p as (?&?).
      unfold unnest_noops_exp in H. rewrite Hsingl in H; simpl in H.
      destruct (is_noops_exp a e); simpl in *; repeat inv_bind; auto.
      eapply fresh_ident_wt_clock; eauto. simpl_Forall; repeat solve_incl.
      eapply wt_exp_clockof in H8.
      rewrite clockof_annot, Hsingl in H8; inv H8.
      repeat solve_incl.
    Qed.

    Fact unnest_exp_wt_clock : forall vars e is_control es' eqs' st st' ,
        wt_exp G1 (vars++st_senv st) e ->
        Forall (wt_clock G2.(types) (vars++st_senv st)) (st_clocks st) ->
        unnest_exp G1 is_control e st = (es', eqs', st') ->
        Forall (wt_clock G2.(types) (vars++st_senv st')) (st_clocks st').
    Proof with eauto with norm ltyping.
      induction e using exp_ind2; intros * Hwt Hclocks Hnorm;
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
      - (* extcall *)
        destruct_conjs; repeat inv_bind.
        assert (Hnorm:=H0). eapply mmap2_wt_clock in H0... 2:solve_mmap2'.
        eapply fresh_ident_wt_clock in H1... 2:repeat solve_incl.
        simpl_Forall; repeat solve_incl.
      - (* fby *)
        assert (st_follows x4 st') as Hfollows by repeat solve_st_follows.
        assert (Hnorm:=H1). eapply mmap2_wt_clock in H1... 2:solve_mmap2'.
        assert (Hnorm1:=H2). eapply mmap2_wt_clock in H2... 2:solve_mmap2'.
        eapply idents_for_anns_wt_clock in H3... all:simpl_Forall; repeat solve_incl.
      - (* arrow *)
        assert (st_follows x4 st') as Hfollows by repeat solve_st_follows.
        assert (Hnorm:=H1). eapply mmap2_wt_clock in H1... 2:solve_mmap2'.
        assert (Hnorm1:=H2). eapply mmap2_wt_clock in H2... 2:solve_mmap2'.
        eapply idents_for_anns_wt_clock in H3... all:simpl_Forall; repeat solve_incl.
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
        2:rewrite map_map; simpl. all:simpl_Forall; repeat solve_incl.
      - (* case (total) *)
        repeat inv_bind.
        assert (Hnorm0:=H1). eapply IHe in H1...
        assert (Hnorm1:=H2). eapply mmap2_wt_clock in H2... 2:(intros; destruct a; repeat solve_st_follows).
        2:{ solve_forall; repeat inv_bind. eapply mmap2_wt_clock in H11... solve_mmap2'. }
        destruct is_control; repeat inv_bind...
        eapply idents_for_anns_wt_clock in H3...
        2:rewrite map_map; simpl. all:simpl_Forall; repeat solve_incl.
      - (* case (default) *)
        repeat inv_bind.
        assert (Hnorm0:=H1). eapply IHe in H1...
        assert (Hnorm1:=H2). eapply mmap2_wt_clock in H2... 2:(intros; destruct a; repeat solve_st_follows).
        2:{ solve_forall; repeat inv_bind. eapply mmap2_wt_clock in H13... solve_mmap2'. }
        assert (Hnorm2:=H3). eapply mmap2_wt_clock in H3... 2:solve_mmap2'.
        destruct is_control; repeat inv_bind...
        eapply idents_for_anns_wt_clock in H4...
        2:rewrite map_map; simpl. all:simpl_Forall; repeat solve_incl.
      - (* app *)
        assert (st_follows x4 x7) as Hfollows by repeat solve_st_follows.
        assert (Forall (wt_clock G2.(types) (vars ++ st_senv x1)) (st_clocks x1)) as Hck1.
        { repeat inv_bind. eapply mmap2_wt_clock in H1... solve_mmap2'. }
        assert (Forall (wt_clock G2.(types) (vars ++ st_senv x4)) (st_clocks x4)) as Hck2.
        { eapply unnest_noops_exps_wt_clock in H2...
          + unfold find_node_incks. rewrite H11.
            eapply Forall2_length in H12. rewrite map_length.
            eapply mmap2_unnest_exp_length in H1; eauto with ltyping.
            rewrite length_typesof_annots in H12.
            congruence.
          + eapply mmap2_unnest_exp_numstreams; eauto.
          + eapply mmap2_unnest_exp_wt. 2:eauto. eauto.
        }

        eapply unnest_resets_wt_clock in H3; simpl; eauto. 2:solve_mmap2'.
        eapply idents_for_anns_wt_clock in H4...
        all:simpl_Forall; repeat solve_incl.
    Qed.

    Corollary unnest_exps_wt_clock : forall vars es es' eqs' st st' ,
        Forall (wt_exp G1 (vars++st_senv st)) es ->
        Forall (wt_clock G2.(types) (vars++st_senv st)) (st_clocks st) ->
        unnest_exps G1 es st = (es', eqs', st') ->
        Forall (wt_clock G2.(types) (vars++st_senv st')) (st_clocks st').
    Proof.
      intros * Hwt Hclocks Hnorm.
      unfold unnest_exps in Hnorm. repeat inv_bind.
      eapply mmap2_wt_clock in H; eauto with norm.
      solve_forall.
      assert (st_follows st0 st0') by eauto with norm.
      eapply unnest_exp_wt_clock with (vars:=vars) in H3; auto; repeat solve_incl.
    Qed.

    Fact unnest_rhs_wt_clock : forall vars e es' eqs' st st' ,
        wt_exp G1 (vars++st_senv st) e ->
        Forall (wt_clock G2.(types) (vars++st_senv st)) (st_clocks st) ->
        unnest_rhs G1 e st = (es', eqs', st') ->
        Forall (wt_clock G2.(types) (vars++st_senv st')) (st_clocks st').
    Proof with eauto.
      intros * Hwt Hclocks Hnorm.
      destruct e; unfold unnest_rhs in Hnorm;
        try eapply unnest_exp_wt_clock in Hnorm; eauto; repeat inv_bind; inv Hwt.
      - (* extcall *)
        assert (Hnorm:=H). eapply unnest_exps_wt_clock in H...
      - (* fby *)
        assert (Hnorm:=H). eapply unnest_exps_wt_clock in H...
        assert (Hnorm1:=H0). eapply unnest_exps_wt_clock in H0...
        simpl_Forall; repeat solve_incl.
      - (* arrow *)
        assert (Hnorm:=H). eapply unnest_exps_wt_clock in H...
        assert (Hnorm1:=H0). eapply unnest_exps_wt_clock in H0...
        simpl_Forall; repeat solve_incl.
      - (* app *)
        assert (st_follows x4 st') as Hfollows by repeat solve_st_follows.
        assert (Forall (wt_clock G2.(types) (vars ++ st_senv x1)) (st_clocks x1)) as Hck1.
        { repeat inv_bind. eapply unnest_exps_wt_clock in H... }
        assert (Forall (wt_clock G2.(types) (vars ++ st_senv x4)) (st_clocks x4)) as Hck2.
        { clear H1. repeat inv_bind.
          eapply unnest_noops_exps_wt_clock in H0; eauto with norm.
          + unfold find_node_incks. rewrite H8.
            eapply Forall2_length in H9. rewrite map_length.
            eapply unnest_exps_length in H; eauto with ltyping. rewrite length_typesof_annots in H9.
            congruence.
          + eapply unnest_exps_numstreams; eauto.
          + eapply unnest_exps_wt in H as (?&?); eauto.
        }
        eapply unnest_resets_wt_clock in H1; eauto. 2:solve_forall; repeat solve_incl.
        eapply Forall_forall. intros. eapply unnest_exp_wt_clock in H4; eauto.
        simpl_Forall; repeat solve_incl.
    Qed.

    Corollary unnest_rhss_wt_clock : forall vars es es' eqs' st st' ,
        Forall (wt_exp G1 (vars++st_senv st)) es ->
        Forall (wt_clock G2.(types) (vars++st_senv st)) (st_clocks st) ->
        unnest_rhss G1 es st = (es', eqs', st') ->
        Forall (wt_clock G2.(types) (vars++st_senv st')) (st_clocks st').
    Proof.
      intros * Hwt Hclocks Hnorm.
      unfold unnest_rhss in Hnorm. repeat inv_bind.
      eapply mmap2_wt_clock in H; eauto with norm.
      solve_forall. eapply unnest_rhs_wt_clock in H3; eauto.
      repeat solve_incl.
    Qed.

    Fact unnest_equation_wt_clock : forall vars eq eqs' st st' ,
        wt_equation G1 (vars++st_senv st) eq ->
        Forall (wt_clock G2.(types) (vars++st_senv st)) (st_clocks st) ->
        unnest_equation G1 eq st = (eqs', st') ->
        Forall (wt_clock G2.(types) (vars++st_senv st')) (st_clocks st').
    Proof.
      intros * Hwt Hclocks Hnorm.
      destruct eq; repeat inv_bind.
      destruct Hwt.
      eapply unnest_rhss_wt_clock in H; eauto.
    Qed.

    Fact unnest_block_wt_clock : forall vars d blocks' st st' ,
        wt_block G1 (vars++st_senv st) d ->
        Forall (wt_clock G2.(types) (vars++st_senv st)) (st_clocks st) ->
        unnest_block G1 d st = (blocks', st') ->
        Forall (wt_clock G2.(types) (vars++st_senv st')) (st_clocks st').
    Proof.
      induction d using block_ind2; intros * Hwt Hcks Hnorm; inv Hwt;
        repeat inv_bind; auto.
      - eapply unnest_equation_wt_clock; eauto.
      - eapply unnest_exp_wt_clock; eauto.
      - assert (Forall (wt_clock G2.(types) (vars ++ st_senv x0)) (st_clocks x0)) as Hcks'.
        { clear - Hcks H H0 H2. revert st x x0 H Hcks H0 H2.
          induction blocks; intros; inv H; inv H2; repeat inv_bind; auto.
          eapply IHblocks in H0; eauto. simpl_Forall; repeat solve_incl.
        }
        eapply unnest_reset_wt_clock in H1; eauto.
        2:repeat solve_incl.
        intros; eapply unnest_exp_wt_clock in H6; eauto. repeat solve_incl.
    Qed.

    Corollary unnest_blocks_wt_clock : forall vars blocks blocks' st st' ,
        Forall (wt_block G1 (vars++st_senv st)) blocks ->
        Forall (wt_clock G2.(types) (vars++st_senv st)) (st_clocks st) ->
        unnest_blocks G1 blocks st = (blocks', st') ->
        Forall (wt_clock G2.(types) (vars++st_senv st')) (st_clocks st').
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
        simpl_Forall; repeat solve_incl.
    Qed.

    (** The enum types used in the new variables are also correct *)

    Lemma fresh_ident_wt_type : forall vars pref hint ty ck id (st st': fresh_st pref _),
        wt_type G2.(types) ty ->
        Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars++st_senv st)) ->
        fresh_ident hint (ty, ck) st = (id, st') ->
        Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars++st_senv st')).
    Proof.
      unfold st_senv.
      intros * Hty Htypes Hfresh.
      apply Ker.fresh_ident_anns in Hfresh. rewrite Hfresh; simpl.
      rewrite <-Permutation_middle; simpl; eauto.
    Qed.

    Corollary idents_for_anns_wt_type : forall vars anns ids st st',
        Forall (wt_type G2.(types)) (map fst anns) ->
        Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars++st_senv st)) ->
        idents_for_anns anns st = (ids, st') ->
        Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars++st_senv st')).
    Proof.
      induction anns as [|(?&?)]; intros * Hwt Htypes Hids;
        inv Hwt; simpl in *; repeat inv_bind; auto.
      eapply IHanns in H0; eauto using fresh_ident_wt_type.
    Qed.

    Fact mmap2_wt_type {A A1 A2 : Type} :
      forall vars (k : A -> FreshAnn (A1 * A2)) a a1s a2s st st',
        Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars++st_senv st)) ->
        mmap2 k a st = (a1s, a2s, st') ->
        (forall st st' a es a2s, k a st = (es, a2s, st') -> st_follows st st') ->
        Forall (fun a => forall a1s a2s st0 st0',
                    Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars++st_senv st0)) ->
                    k a st0 = (a1s, a2s, st0') ->
                    st_follows st st0 ->
                    st_follows st0' st' ->
                    Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars++st_senv st0'))) a ->
        Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars++st_senv st')).
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

    Fact unnest_reset_wt_type : forall vars e e' eqs' st st' ,
        (forall es' eqs' st0',
            st_follows st0' st' ->
            unnest_exp G1 true e st = (es', eqs', st0') ->
            Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars++st_senv st0'))) ->
        wt_exp G1 (vars++st_senv st) e ->
        typeof e = [OpAux.bool_velus_type] ->
        Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars++st_senv st)) ->
        unnest_reset (unnest_exp G1 true) e st = (e', eqs', st') ->
        Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars++st_senv st')).
    Proof with eauto.
      intros * Hkck Hwt Hty Htypes Hnorm.
      unnest_reset_spec; simpl in *; eauto. eapply Hkck; eauto; reflexivity.
      eapply fresh_ident_wt_type in Hfresh; eauto with fresh.
      assert (length l = 1). 2:singleton_length.
      { eapply unnest_exp_length in Hk0; eauto with ltyping.
        now rewrite <-length_typeof_numstreams, Hty in Hk0. }
      eapply unnest_exp_annot in Hk0; eauto with ltyping; simpl in Hk0; rewrite app_nil_r in Hk0.
      eapply iface_incl_wt_exp, wt_exp_wt_type in Hwt; eauto.
      rewrite typeof_annot in *. rewrite Hk0 in Hhd.
      rewrite Forall_map in Hwt. destruct (annot e); inv Hwt; simpl in *; try congruence.
      subst; auto.
    Qed.

    Corollary unnest_resets_wt_type : forall vars es es' eqs' st st' ,
        Forall (fun e => forall es' eqs' st0 st0',
                    Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars++st_senv st0)) ->
                    unnest_exp G1 true e st0 = (es', eqs', st0') ->
                    st_follows st st0 ->
                    st_follows st0' st' ->
                    Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars++st_senv st0'))) es ->
        Forall (wt_exp G1 (vars++st_senv st)) es ->
        Forall (fun e => typeof e = [OpAux.bool_velus_type]) es ->
        Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars++st_senv st)) ->
        mmap2 (unnest_reset (unnest_exp G1 true)) es st = (es', eqs', st') ->
        Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars++st_senv st')).
    Proof.
      intros * F Wt Tys WtE Map.
      eapply mmap2_wt_type in Map; eauto with norm.
      rewrite Forall_forall in *. intros.
      eapply unnest_reset_wt_type in H1; eauto.
      - intros. eapply F; eauto. etransitivity; eauto.
      - eapply Wt in H. repeat solve_incl.
    Qed.

    Fact unnest_noops_exps_wt_type : forall vars cks es es' eqs' st st' ,
        length es = length cks ->
        Forall (fun e => numstreams e = 1) es ->
        Forall (wt_exp G2 (vars++st_senv st)) es ->
        Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars++st_senv st)) ->
        unnest_noops_exps cks es st = (es', eqs', st') ->
        Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars++st_senv st')).
    Proof.
      unfold unnest_noops_exps.
      intros * Hlen Hnum Hwt1 Hwt2 Hunt. repeat inv_bind.
      eapply mmap2_wt_type in H; eauto. intros ?? (?&?) ???; eauto using unnest_noops_exp_st_follows.
      solve_forall.
      unfold unnest_noops_exp in H4.
      rewrite <-length_annot_numstreams in H7. singleton_length.
      destruct p as (?&?).
      destruct (is_noops_exp _ _); repeat inv_bind; auto.
      eapply fresh_ident_wt_type; eauto.
      eapply wt_exp_wt_type in H2; eauto. 2:solve_forall.
      rewrite typeof_annot, Hsingl in H2. inv H2; auto.
    Qed.

    Lemma unnest_exp_wt_type : forall vars e is_control es' eqs' st st' ,
        wt_exp G1 (vars++st_senv st) e ->
        Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars++st_senv st)) ->
        unnest_exp G1 is_control e st = (es', eqs', st') ->
        Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars++st_senv st')).
    Proof.
      induction e using exp_ind2; intros * Hwt Htypes Hun;
        inv Hwt; simpl in Hun; repeat inv_bind; auto.
      - (* unop *)
        eapply IHe; eauto.
      - (* binop *)
        eapply IHe2 in H0; eauto. repeat solve_incl.
      - (* extcall *)
        eapply fresh_ident_wt_type in H1; eauto. constructor.
        eapply mmap2_wt_type in H0; eauto with norm. solve_mmap2'.
      - (* fby *)
        eapply idents_for_anns_wt_type in H3; eauto.
        1:{ rewrite <-H6. eapply wt_exps_wt_type; eauto. solve_forall. }
        eapply mmap2_wt_type in H2; eauto with norm. 2:solve_mmap2'.
        eapply mmap2_wt_type in H1; eauto with norm. solve_mmap2'.
      - (* arrow *)
        eapply idents_for_anns_wt_type in H3; eauto.
        1:{ rewrite <-H6. eapply wt_exps_wt_type; eauto. solve_forall. }
        eapply mmap2_wt_type in H2; eauto with norm. 2:solve_mmap2'.
        eapply mmap2_wt_type in H1; eauto with norm. solve_mmap2'.
      - (* when *)
        eapply mmap2_wt_type in H0; eauto with norm. solve_mmap2'.
      - (* merge *)
        assert (Hnorm1:=H0). eapply mmap2_wt_type in H0; eauto.
        2:(intros; destruct a; repeat solve_st_follows).
        2:{ solve_forall. repeat inv_bind. eapply mmap2_wt_type in H8; eauto with norm.
            solve_mmap2'. }
        destruct is_control; repeat inv_bind; eauto.
        eapply idents_for_anns_wt_type; eauto.
        rewrite map_map, map_id; simpl.
        inv H8; simpl in *; subst; try congruence.
        inv H7. eapply wt_exps_wt_type; eauto. simpl_Forall; repeat solve_incl.
      - (* case (total) *)
        assert (Hnorm0:=H1). eapply IHe in H1; eauto.
        assert (Hnorm1:=H2). eapply mmap2_wt_type in H2; eauto.
        2:(intros; destruct a; repeat solve_st_follows).
        2:{ solve_forall. repeat inv_bind. eapply mmap2_wt_type in H11; eauto with norm.
            solve_mmap2'. }
        destruct is_control; repeat inv_bind; eauto.
        eapply idents_for_anns_wt_type; eauto.
        rewrite map_map, map_id; simpl.
        inv H11; simpl in *; subst; try congruence.
        inv H10. eapply wt_exps_wt_type; eauto. simpl_Forall; repeat solve_incl.
      - (* case (default) *)
        assert (Hnorm0:=H1). eapply IHe in H1; eauto.
        assert (Hnorm1:=H2). eapply mmap2_wt_type in H2; eauto.
        2:(intros; destruct a; repeat solve_st_follows).
        2:{ solve_forall. repeat inv_bind. eapply mmap2_wt_type in H13; eauto with norm.
            solve_mmap2'. }
        assert (Hnorm2:=H3). eapply mmap2_wt_type in H3; eauto with norm. 2:solve_mmap2'.
        destruct is_control; repeat inv_bind; eauto.
        eapply idents_for_anns_wt_type; eauto.
        rewrite map_map, map_id; simpl.
        inv H12; simpl in *; subst; try congruence.
        inv H11. eapply wt_exps_wt_type; eauto. simpl_Forall; repeat solve_incl.
      - (* app *)
        eapply idents_for_anns_wt_type in H4; eauto.
        + eapply wt_find_node in H7 as (G'&Hwt&Heq); eauto. inversion_clear Hwt as [?? _ _ Htypes' _]; subst Γ.
          apply Forall_app in Htypes' as (_&Htypes').
          eapply Forall2_ignore2 in H9. unfold senv_of_decls in *. simpl_Forall. subst.
          eapply iface_incl_wt_type; eauto.
          congruence.
        + eapply unnest_resets_wt_type in H3; eauto. solve_mmap2'.
          simpl_Forall; repeat solve_incl.
          eapply unnest_noops_exps_wt_type in H2; eauto.
          * unfold find_node_incks. rewrite H7.
            eapply Forall2_length in H8. rewrite map_length.
            eapply mmap2_unnest_exp_length in H1; eauto with ltyping. rewrite length_typesof_annots in H8.
            congruence.
          * eapply mmap2_unnest_exp_numstreams; eauto.
          * eapply mmap2_unnest_exp_wt. 2:eauto. eauto.
          * eapply mmap2_wt_type; eauto with norm. solve_mmap2'.
    Qed.

    Corollary unnest_exps_wt_type : forall vars es es' eqs' st st' ,
        Forall (wt_exp G1 (vars++st_senv st)) es ->
        Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars++st_senv st)) ->
        unnest_exps G1 es st = (es', eqs', st') ->
        Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars++st_senv st')).
    Proof.
      intros * Hwt Hclocks Hnorm.
      unfold unnest_exps in Hnorm. repeat inv_bind.
      eapply mmap2_wt_type in H; eauto with norm.
      solve_forall.
      assert (st_follows st0 st0') by eauto with norm.
      eapply unnest_exp_wt_type with (vars:=vars) in H3; repeat solve_incl; auto.
    Qed.

    Fact unnest_rhs_wt_type : forall vars e es' eqs' st st' ,
        wt_exp G1 (vars++st_senv st) e ->
        Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars++st_senv st)) ->
        unnest_rhs G1 e st = (es', eqs', st') ->
        Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars++st_senv st')).
    Proof with eauto.
      intros * Hwt Hclocks Hnorm.
      destruct e; unfold unnest_rhs in Hnorm;
        try eapply unnest_exp_wt_type in Hnorm; eauto; repeat inv_bind; inv Hwt.
      - (* extcall *)
        eapply unnest_exps_wt_type in H...
      - (* fby *)
        eapply unnest_exps_wt_type in H0... simpl_Forall; repeat solve_incl.
        eapply unnest_exps_wt_type in H...
      - (* arrow *)
        eapply unnest_exps_wt_type in H0... simpl_Forall; repeat solve_incl.
        eapply unnest_exps_wt_type in H...
      - (* app *)
        eapply unnest_resets_wt_type in H1... 2:simpl_Forall; repeat solve_incl.
        { eapply Forall_forall. intros. eapply unnest_exp_wt_type in H4; eauto.
          eapply Forall_forall in H7; eauto. repeat solve_incl. }
        eapply unnest_noops_exps_wt_type in H0...
        + unfold find_node_incks. rewrite H8.
          eapply Forall2_length in H9. rewrite map_length.
          eapply unnest_exps_length in H; eauto with ltyping. rewrite length_typesof_annots in H9.
          congruence.
        + eapply unnest_exps_numstreams; eauto.
        + eapply unnest_exps_wt. 2:eauto. eauto.
        + eapply unnest_exps_wt_type in H; eauto.
    Qed.

    Corollary unnest_rhss_wt_type : forall vars es es' eqs' st st' ,
        Forall (wt_exp G1 (vars++st_senv st)) es ->
        Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars++st_senv st)) ->
        unnest_rhss G1 es st = (es', eqs', st') ->
        Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars++st_senv st')).
    Proof.
      intros * Hwt Hclocks Hnorm.
      unfold unnest_rhss in Hnorm. repeat inv_bind.
      eapply mmap2_wt_type in H; eauto with norm.
      solve_forall. eapply unnest_rhs_wt_type in H3; eauto.
      repeat solve_incl.
    Qed.

    Fact unnest_equation_wt_type : forall vars eq eqs' st st' ,
        wt_equation G1 (vars++st_senv st) eq ->
        Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars++st_senv st)) ->
        unnest_equation G1 eq st = (eqs', st') ->
        Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars++st_senv st')).
    Proof.
      intros * Hwt Htypes Hnorm.
      destruct eq; repeat inv_bind.
      destruct Hwt.
      eapply unnest_rhss_wt_type in H; eauto.
    Qed.

    Fact unnest_block_wt_type : forall vars d blocks' st st' ,
        wt_block G1 (vars++st_senv st) d ->
        Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars++st_senv st)) ->
        unnest_block G1 d st = (blocks', st') ->
        Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars++st_senv st')).
    Proof.
      induction d using block_ind2; intros * Hwt Htypes Hnorm;
        inv Hwt; repeat inv_bind; auto.
      - eapply unnest_equation_wt_type; eauto.
      - eapply unnest_exp_wt_type; eauto.
      - assert (Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars ++ st_senv x0))) as Htypes'.
        { clear - H H0 H2 Htypes.
          revert st x0 x H2 Htypes H0.
          induction H; intros * Hwt Htypes Hmap; inv Hwt; repeat inv_bind; auto.
          eapply IHForall in H2; eauto.
          simpl_Forall; repeat solve_incl.
        }
        eapply unnest_reset_wt_type in H1; eauto.
        intros. eapply unnest_exp_wt_type in H6; eauto.
        1,2:repeat solve_incl.
    Qed.

    Corollary unnest_blocks_wt_type : forall vars blocks blocks' st st' ,
        Forall (wt_block G1 (vars++st_senv st)) blocks ->
        Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars++st_senv st)) ->
        unnest_blocks G1 blocks st = (blocks', st') ->
        Forall (wt_type G2.(types)) (map (fun '(_, ann) => ann.(typ)) (vars++st_senv st')).
    Proof.
      induction blocks; intros * Hwt Hclocks Hnorm;
        unfold unnest_blocks in Hnorm; repeat inv_bind.
      - assumption.
      - inv Hwt.
        assert (st_follows st x1) by repeat solve_st_follows.
        eapply unnest_block_wt_type in H; eauto.
        assert (unnest_blocks G1 blocks x1 = (concat x2, st')) as Hnorm.
        { unfold unnest_blocks; repeat inv_bind; eauto. }
        eapply IHblocks in Hnorm; eauto.
        simpl_Forall; repeat solve_incl.
    Qed.

    (** Finally, we can prove that the node is properly normalized *)

    Lemma unnest_node_wt : forall n,
        wt_node G1 n ->
        wt_node G2 (unnest_node G1 n).
    Proof.
      intros * Wt. inversion_clear Wt as [??? Hclin Hclout Heq].
      unfold unnest_node.
      pose proof (n_syn n) as Hsyn. inversion_clear Hsyn as [?? Hsyn2 _]. inv Hsyn2.
      destruct Hiface as (Htypes&_).
      econstructor; simpl; eauto.
      1-3:unfold wt_clocks in *; simpl_Forall; eauto with ltyping.
      rewrite <-H0 in *; simpl in *. inv Heq.
      inv_scope; subst Γ Γ'. do 2 econstructor; eauto.
      - unfold wt_clocks in *. setoid_rewrite senv_of_decls_app. rewrite <-st_senv_senv_of_decls. apply Forall_app; split; simpl_Forall.
        + eapply wt_clock_incl; [|eauto with ltyping].
          intros. eapply HasType_incl; [|eauto]. setoid_rewrite senv_of_decls_app. solve_incl_app.
        + destruct (unnest_blocks _ _ _) as (blocks&st') eqn:Heqres.
          eapply unnest_blocks_wt_clock with (vars:=senv_of_ins (n_in n) ++ senv_of_decls (n_out n) ++ senv_of_decls locs) in Heqres; eauto.
          * unfold st_clocks in *. simpl_In. simpl_Forall.
            simpl_app. erewrite map_map, map_ext with (l:=st_anns _); eauto. intros; destruct_conjs; auto.
          * unfold st_clocks, st_senv. rewrite init_st_anns, app_nil_r. simpl_app; auto.
          * unfold st_clocks. rewrite init_st_anns; simpl; constructor.
      - destruct (unnest_blocks _ _ _) as (blocks'&st') eqn:Heqres; simpl.
        eapply unnest_blocks_wt_type with (vars:=senv_of_ins (n_in n) ++ senv_of_decls (n_out n) ++ senv_of_decls locs) in Heqres; eauto.
        + rewrite 2 map_app, 2 Forall_app in Heqres. destruct Heqres as ((?&?)&?).
          unfold st_senv, idfst in *. simpl_app.
          apply Forall_app; auto; split; simpl_Forall; eauto with ltyping.
        + unfold st_senv. rewrite init_st_anns, app_nil_r. simpl_app; auto.
        + unfold st_senv. rewrite init_st_anns, app_nil_r.
          rewrite app_assoc, map_app, Forall_app; split; simpl_Forall; simpl_In; simpl_Forall; eauto with ltyping.
      - destruct (unnest_blocks _ _ _) as (blocks'&st') eqn:Heqres; simpl.
        eapply unnest_blocks_wt_block in Heqres; eauto. 2:unfold st_senv; rewrite init_st_anns, app_nil_r; simpl_app; eauto.
        simpl_app. auto. erewrite map_map, map_ext with (l:=st_anns _); eauto. intros; destruct_conjs; auto.
    Qed.

  End unnest_node_wt.

  Lemma unnest_global_wt : forall G,
      wt_global G ->
      wt_global (unnest_global G).
  Proof.
    intros [] (Htypes&Hwt). unfold CommonTyping.wt_program in Hwt; simpl.
    induction nodes0; inv Hwt; split; simpl; auto. constructor.
    destruct H1.
    constructor; [constructor|].
    - eapply unnest_node_wt; eauto. 2:split; auto.
      eapply iface_eq_iface_incl, unnest_nodes_eq.
    - eapply unnest_nodes_names; eauto.
    - eapply IHnodes0; eauto.
  Qed.

End UTYPING.

Module UTypingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Typ : LTYPING Ids Op OpAux Cks Senv Syn)
       (Un  : UNNESTING Ids Op OpAux Cks Senv Syn)
       <: UTYPING Ids Op OpAux Cks Senv Syn Typ Un.
  Include UTYPING Ids Op OpAux Cks Senv Syn Typ Un.
End UTypingFun.
