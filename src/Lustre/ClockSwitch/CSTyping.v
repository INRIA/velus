From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import CommonTyping.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Fresh.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import Lustre.LTyping.
From Velus Require Import Lustre.ClockSwitch.ClockSwitch.

Module Type CSTYPING
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Syn : LSYNTAX Ids Op OpAux Cks)
       (Import Typ : LTYPING Ids Op OpAux Cks Syn)
       (Import CS : CLOCKSWITCH Ids Op OpAux Cks Syn).

  Section subclock.
    Variable bck : clock.
    Variable sub : Env.t ident.

    Variable vars vars' : list (ident * type).

    Hypothesis Hsub : forall x y ty,
        Env.find x sub = Some y ->
        In (x, ty) vars ->
        In (y, ty) vars'.

    Hypothesis Hnsub : forall x ty,
        Env.find x sub = None ->
        In (x, ty) vars ->
        In (x, ty) vars'.

    Lemma rename_var_wt : forall x ty,
        In (x, ty) vars ->
        In (rename_var sub x, ty) vars'.
    Proof.
      unfold rename_var.
      intros * Hin.
      destruct (Env.find _ _) eqn:Hfind; simpl in *; eauto.
    Qed.

    Context {PSyn : block -> Prop} {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Hypothesis Hwbck : wt_clock G.(enums) vars' bck.

    Lemma subclock_clock_wt : forall ck,
        wt_clock G.(enums) vars ck ->
        wt_clock G.(enums) vars' (subclock_clock bck sub ck).
    Proof.
      induction ck; intros * Hwt; inv Hwt; simpl; auto.
      constructor; eauto using rename_var_wt.
    Qed.
    Local Hint Resolve subclock_clock_wt : ltyping.

    Lemma add_whens_wt : forall e ty,
        typeof e = [ty] ->
        wt_exp G vars' e ->
        wt_exp G vars' (add_whens e ty bck).
    Proof.
      clear Hsub Hnsub.
      induction bck as [|??? (?&?)]; intros * Hbase Hwt; inv Hwbck;
        simpl in *; auto.
      econstructor; eauto; simpl.
      - rewrite add_whens_typeof; auto.
      - constructor; auto.
    Qed.

    Lemma subclock_exp_wt : forall e,
        wt_exp G vars e ->
        wt_exp G vars' (subclock_exp bck sub e).
    Proof with auto with ltyping.
      induction e using exp_ind2; intros * Hwt; inv Hwt; simpl in *.
      3-12:econstructor; simpl in *; eauto using rename_var_wt, subclock_clock_wt.
      1-40:try solve [rewrite Forall_map, Forall_forall in *; intros; eauto].
      1-32:try rewrite subclock_exp_typeof.
      1-32:try rewrite subclock_exp_typesof.
      1-32:try (rewrite map_subclock_ann_clock; auto). 1-32:try (rewrite map_subclock_ann_type; auto). 1-28:auto.
      - apply add_whens_wt...
      - apply add_whens_wt...
      - rewrite Forall_map. eapply Forall_impl; [|eauto]; intros ??; subst...
      - rewrite Forall_map. eapply Forall_impl; [|eauto]; intros ??; subst...
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
      - rewrite Forall_map. rewrite Forall_forall; intros (?&?) Hin; simpl.
        rewrite subclock_exp_typesof.
        eapply Forall_forall in H11; eauto; auto.
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
        wt_equation G vars eq ->
        wt_equation G vars' (subclock_equation bck sub eq).
    Proof.
      intros (?&?) (Hwt1&Hwt2). constructor.
      - rewrite Forall_map.
        eapply Forall_impl; [|eauto]; eauto using subclock_exp_wt.
      - rewrite Forall2_map_1, subclock_exp_typesof.
        eapply Forall2_impl_In; [|eauto]; intros; eauto using rename_var_wt.
    Qed.

  End subclock.

  Import Fresh Facts Tactics.

  Section switch_block.

    Context {PSyn : block -> Prop} {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Import Permutation.

    Lemma cond_eq_wt vars : forall e ty ck x xcs eqs' st st',
        wt_exp G vars e ->
        typeof e = [ty] ->
        cond_eq e ty ck st = (x, xcs, eqs', st') ->
        Forall (wt_equation G (vars++idty xcs)) eqs'.
    Proof.
      intros * Hwt Hck Hcond; destruct e; repeat inv_bind.
      3:destruct a; repeat inv_bind; auto.
      1-10:constructor; auto; rewrite Permutation_app_comm; simpl.
      1-10:(constructor; [constructor; auto; eapply wt_exp_incl; eauto; eauto with datatypes|]).
      1-10:take (_ = [_]) and rewrite it; try rewrite app_nil_r; eauto.
    Qed.

    Lemma cond_eq_wt_clock vars : forall e ty ck x xcs eqs' st st',
        wt_clock G.(enums) vars ck ->
        cond_eq e ty ck st = (x, xcs, eqs', st') ->
        Forall (wt_clock G.(enums) vars) (map snd (idck xcs)).
    Proof.
      intros * Hck Hcond; destruct e; repeat inv_bind; simpl; auto.
      destruct a; repeat inv_bind; simpl; auto.
    Qed.

    Lemma cond_eq_wt_enum : forall e ty ck x xcs eqs' st st',
        wt_enum G ty ->
        cond_eq e ty ck st = (x, xcs, eqs', st') ->
        Forall (wt_enum G) (map snd (idty xcs)).
    Proof.
      intros * Hck Hcond; destruct e; repeat inv_bind; simpl; auto.
      destruct a; repeat inv_bind; simpl; auto.
    Qed.

    Lemma cond_eq_In vars : forall e ty ck x xcs eqs' st st',
        wt_exp G vars e ->
        typeof e = [ty] ->
        cond_eq e ty ck st = (x, xcs, eqs', st') ->
        In (x, ty) (vars ++ idty xcs).
    Proof.
      intros * Hwt Hck Hcond; destruct e; repeat inv_bind; simpl in *; auto with datatypes.
      inv Hwt. repeat inv_bind.
      inv Hck; auto with datatypes.
    Qed.

    Lemma new_idents_wt_clock vars' : forall ck x tn k ids ids' st st',
        In tn G.(enums) ->
        k < snd tn ->
        wt_clock G.(enums) vars' ck ->
        In (x, Tenum tn) vars' ->
        new_idents ck x (Tenum tn) k ids st = (ids', st') ->
        Forall (wt_clock G.(enums) vars') (map snd (idck (idty (map (fun '(_, x1, (ty, ck0)) => (x1, (ty, ck0, xH))) ids')))).
    Proof.
      intros * Hen Hk Hck Hin Hni.
      unfold new_idents in *. eapply mmap_values, Forall2_ignore1 in Hni.
      repeat setoid_rewrite Forall_map.
      eapply Forall_impl; [|eauto]; intros ((?&?)&?&?) ((?&?&?)&?&?&?&?); repeat inv_bind.
      econstructor; eauto.
    Qed.

    Lemma new_idents_wt_enum : forall ck x tn k ids ids' st st',
        Forall (wt_enum G) (map snd (idty ids)) ->
        new_idents ck x (Tenum tn) k ids st = (ids', st') ->
        Forall (wt_enum G) (map snd (idty (idty (map (fun '(_, x1, (ty, ck0)) => (x1, (ty, ck0, xH))) ids')))).
    Proof.
      intros * Hwt Hni.
      unfold new_idents in *. eapply mmap_values, Forall2_ignore1 in Hni.
      repeat setoid_rewrite Forall_map.
      eapply Forall_impl_In; [|eauto]; intros ((?&?)&?&?) Hin ((?&?&?)&?&?&?&?); repeat inv_bind.
      unfold idty in Hwt. rewrite 2 Forall_map in Hwt. eapply Forall_forall in Hwt; eauto.
      simpl; auto.
    Qed.

    Lemma when_free_wt vars : forall x y ty ck cx tn k,
        In (x, ty) vars ->
        In (y, ty) vars ->
        In (cx, Tenum tn) vars ->
        k < snd tn ->
        In tn G.(enums) ->
        wt_clock G.(enums) vars ck ->
        wt_block G vars (when_free x y ty ck cx (Tenum tn) k).
    Proof.
      intros.
      repeat econstructor; simpl; eauto.
    Qed.

    Lemma merge_defs_wt vars : forall sub y ty ck x tn xcs,
        In (x, Tenum tn) vars ->
        In tn G.(enums) ->
        In (rename_var sub y, ty) vars ->
        wt_clock G.(enums) vars ck ->
        xcs <> [] ->
        Permutation (map fst xcs) (seq 0 (snd tn)) ->
        Forall (fun '(k, sub) => In (rename_var sub y, ty) vars) xcs ->
        wt_block G vars (merge_defs sub y ty ck x (Tenum tn) xcs).
    Proof.
      intros * Hin1 Htn Hin2 Hck Hnnil Hperm Hf.
      repeat constructor; auto.
      - erewrite map_map, map_ext; eauto. intros (?&?); auto.
      - contradict Hnnil. apply map_eq_nil in Hnnil; auto.
      - rewrite Forall_map. eapply Forall_impl_In; [|eauto]; intros (?&?) Hin ?.
        repeat constructor; auto.
        eapply In_InMembers, fst_InMembers in Hin. rewrite Hperm in Hin.
        apply in_seq in Hin as (?&?); auto.
      - rewrite Forall_map. eapply Forall_forall; intros (?&?) Hin; simpl; auto.
    Qed.

    Lemma new_idents_In : forall x ty ck cx tx k ids1 ids2 nids1 nids2 st1 st2 st3 st4,
        NoDupMembers (ids1++ids2) ->
        In (x, ty) (idty (ids1++ids2)) ->
        new_idents ck cx tx k ids1 st1 = (nids1, st2) ->
        new_idents ck cx tx k ids2 st3 = (nids2, st4) ->
        In (rename_var (Env.from_list (map (fun '(x, y, _) => (x, y)) (nids1 ++ nids2))) x, ty)
           (map (fun '(_, x, (ty, _)) => (x, ty)) (nids1++nids2)).
    Proof.
      intros * Hnd Hinm Hni1 Hni2.
      assert (NoDupMembers (map (fun '(x, y, _) => (x, y)) (nids1 ++ nids2))) as Hnd'.
      { erewrite fst_NoDupMembers, map_map, map_ext, map_app, 2 new_idents_old; eauto.
        rewrite <-map_app, <-fst_NoDupMembers; auto.
        intros ((?&?)&?&?); auto. }
      eapply mmap_values, Forall2_ignore2 in Hni1.
      eapply mmap_values, Forall2_ignore2 in Hni2. simpl_In.
      apply in_app_iff in Hin as [Hin|Hin]; eapply Forall_forall in Hin; eauto; simpl in *.
      1,2:destruct Hin as (((?&?)&?&?)&Hin&?&?&?); repeat inv_bind.
      - solve_In; eauto with datatypes.
        f_equal; auto.
        unfold rename_var. erewrite Env.find_In_from_list; eauto.
        2:solve_In; eauto with datatypes. 1,2:reflexivity.
      - solve_In; eauto with datatypes.
        f_equal; auto.
        unfold rename_var. erewrite Env.find_In_from_list; eauto.
        2:solve_In; eauto with datatypes. 1,2:reflexivity.
    Qed.

    Fact switch_blocks_wt' : forall bck sub envck envty envty' blks blks' st st',
        Forall
          (fun blk => forall bck sub envck envty envty' blk' st st',
               (forall x, Env.In x sub -> InMembers x envck) ->
               (forall x y ty, Env.find x sub = Some y -> In (x, ty) envty -> In (y, ty) envty') ->
               (forall x ty, In (x, ty) envty -> In (x, ty) envty') ->
               incl (idty envck) envty ->
               NoDupMembers envty ->
               NoDupMembers envck ->
               Forall (wt_enum G) (map snd envty) ->
               wt_clock G.(enums) envty' bck ->
               NoDupLocals (map fst envty) blk ->
               wt_block G envty blk ->
               switch_block envck bck sub blk st = (blk', st') ->
               wt_block G envty' blk') blks ->
        (forall x, Env.In x sub -> InMembers x envck) ->
        (forall x y ty, Env.find x sub = Some y -> In (x, ty) envty -> In (y, ty) envty') ->
        (forall x ty, In (x, ty) envty -> In (x, ty) envty') ->
        incl (idty envck) envty ->
        NoDupMembers envty ->
        NoDupMembers envck ->
        Forall (wt_enum G) (map snd envty) ->
        wt_clock G.(enums) envty' bck ->
        Forall (NoDupLocals (map fst envty)) blks ->
        Forall (wt_block G envty) blks ->
        mmap (switch_block envck bck sub) blks st = (blks', st') ->
        Forall (wt_block G envty') blks'.
    Proof.
      induction blks; intros * Hf Hsubin Hsub Hnsub Hincl Hnd1 Hnd2 Hwenv Hbck Hnd3 Hwt Hmmap;
        inv Hf; inv Hnd3; inv Hwt; repeat inv_bind; eauto.
    Qed.

    Lemma switch_block_wt : forall blk bck sub envck envty envty' blk' st st',
        (forall x, Env.In x sub -> InMembers x envck) ->
        (forall x y ty, Env.find x sub = Some y -> In (x, ty) envty -> In (y, ty) envty') ->
        (forall x ty, In (x, ty) envty -> In (x, ty) envty') ->
        incl (idty envck) envty ->
        NoDupMembers envty ->
        NoDupMembers envck ->
        Forall (wt_enum G) (map snd envty) ->
        wt_clock G.(enums) envty' bck ->
        NoDupLocals (map fst envty) blk ->
        wt_block G envty blk ->
        switch_block envck bck sub blk st = (blk', st') ->
        wt_block G envty' blk'.
    Proof.
      induction blk using block_ind2; intros * Hsubin Hsub Hnsub Hincl Hnd1 Hnd2 Hwenv Hbck Hnd3 Hwt Hsw;
        inv Hnd3; inv Hwt; repeat inv_bind; simpl in *.
      - (* equation *)
        constructor. eapply subclock_equation_wt; eauto.

      - (* reset *)
        econstructor; eauto using subclock_exp_wt.
        2:rewrite subclock_exp_typeof; eauto.
        eapply switch_blocks_wt' with (envty:=envty) in H0; eauto.

      - (* switch *)
        destruct (partition _ _) eqn:Hpart; repeat inv_bind.
        apply partition_Partition in Hpart.
        destruct x; repeat inv_bind.

        assert (length (clockof ec) = 1) as Hlck.
        { rewrite length_clockof_numstreams, <-length_typeof_numstreams, H4; auto. }
        remember (clockof ec) as ck; symmetry in Heqck. singleton_length. rename c into ck.
        assert (wt_clock G.(enums) envty' (subclock_clock bck sub ck)) as Hck'.
        { eapply subclock_clock_wt; eauto.
          eapply wt_exp_clockof in H3; eauto. rewrite Heqck in H3. apply Forall_singl in H3; auto. }

        rewrite subclock_exp_typeof, H4 in *; simpl in *.
        rewrite subclock_exp_clockof, Heqck in *; simpl in *.

        assert (In (i, Tenum tn) (envty' ++ idty (idty (map (fun '(xc, (ty, ck0)) => (xc, (ty, ck0, 1%positive))) l1)))) as Hini.
        { eapply cond_eq_In in H0; eauto using subclock_exp_wt.
          2:now rewrite subclock_exp_typeof.
          unfold idty. erewrite 2 map_map, map_ext; eauto. intros (?&?&?); auto. }

        assert (NoDupMembers (filter (fun '(_, (_, ck')) => ck' ==b ck) l0 ++ l)) as Hnd'.
        { rewrite Permutation_app_comm.
          eapply switch_block_NoDupMembers_env; eauto. }

        econstructor; eauto; unfold wt_clocks; repeat rewrite idty_app; repeat rewrite idck_app;
          repeat rewrite map_app; repeat rewrite Forall_app; repeat split.
        + rewrite Forall_map. apply Forall_forall; intros (?&?&?) Hin.
          eapply merge_defs_wt; eauto.
          * rewrite app_assoc. apply in_or_app, or_introl; auto.
          * apply in_or_app; left.
            eapply rename_var_wt; eauto.
            assert (Is_defined_in i0 (Bswitch ec branches)) as Hdef.
            { eapply vars_defined_Is_defined_in.
              eapply Partition_Forall1, Forall_forall in Hpart; eauto; simpl in *.
              apply PSF.mem_2; auto. }
            inv Hdef. rename H11 into Hex. do 2 (eapply Exists_exists in Hex as (?&?&Hex)).
            eapply Hincl.
            apply Partition_Permutation in Hpart. rewrite Hpart.
            rewrite idty_app, in_app_iff. left. solve_In.
          * eapply wt_clock_incl; eauto. solve_incl_app.
          * apply mmap_length in H1. destruct x, branches; simpl in *; try congruence; auto.
          * rewrite <-H6.
            replace (map fst (map _ x)) with (map fst branches). reflexivity.
            clear - H1. apply mmap_values in H1.
            induction H1 as [|(?&?) (((?&?)&?)&?)]; simpl; auto.
            destruct H as (?&?&?); repeat inv_bind.
            f_equal; auto.
          * eapply mmap_values, Forall2_ignore1 in H1.
            rewrite Forall_map. eapply Forall_impl_In; [|eauto]; intros (((?&?)&?)&?) Hin2 ((?&?)&Hin3&?&?&?); repeat inv_bind.
            rewrite 2 in_app_iff. do 2 right.
            eapply new_idents_In with (ids1:=filter _ _) in H11; eauto.
            2:{ rewrite idty_app, in_app_iff. right. solve_In. } simpl in *.
            solve_In.
        + eapply CS.mmap2_values in H7. eapply mmap_values, Forall3_ignore3' with (zs:=x3) in H1.
          2:{ eapply Forall3_length in H7 as (?&?); congruence. }
          2:{ eapply mmap_length in H1; eauto. }
          eapply Forall3_Forall3 in H1; eauto. clear H7.
          eapply Forall_concat, Forall_forall; intros ? Hinblks.
          eapply Forall3_ignore12, Forall_forall in H1 as ((?&?)&?&Hin2&Hin3&(?&?&?)&?&?&?); eauto.
          repeat inv_bind.

          assert (forall x, InMembers x (map (fun '(x, y, _) => (x, y)) (x10 ++ x12)) ->
                       InMembers x (filter (fun '(_, (_, ck')) => ck' ==b ck) l0 ++ l)) as Hinminv.
          { intros ? Hinm. rewrite fst_InMembers in Hinm. rewrite fst_InMembers.
            erewrite map_app, <-2 new_idents_old, <-map_app; eauto.
            erewrite map_map, map_ext in Hinm; eauto. intros ((?&?)&(?&?)); auto.
          }

          apply Forall_app; split.
          *{ repeat (take (Forall _ branches) and eapply Forall_forall in it; eauto).
             eapply switch_blocks_wt' with (envty:=envty) in H1; eauto.
             - intros ? Hin. erewrite Env.In_from_list in Hin.
               erewrite Permutation_app_comm, fst_InMembers, map_map, map_ext, <-fst_InMembers; auto.
               intros (?&?&?); auto.
             - intros ??? Hfind Hin.
               assert (In (x4, ty) (idty (filter (fun '(_, (_, ck')) => ck' ==b ck) l0 ++ l))) as Hin'.
               { eapply Env.find_In, Env.In_from_list, Hinminv in Hfind; eauto.
                 eapply InMembers_In in Hfind as ((ty'&?)&?).
                 solve_In.
                 assert (ty' = ty); subst; auto.
                 eapply NoDupMembers_det in Hin; eauto.
                 eapply Hincl.
                 apply Partition_Permutation in Hpart. rewrite Hpart.
                 solve_In.
                 2:eapply in_app_iff in H as [|]; eauto using in_filter with datatypes. auto.
               }
               eapply new_idents_In with (ids1:=filter _ _) in H10; eauto. clear Hin'.
               simpl_In.
               repeat rewrite in_app_iff. do 2 right. solve_In.
               unfold rename_var. destruct (Env.find _ _); try congruence. rewrite Hfind; auto.
             - intros ?? Hin. apply in_or_app; auto.
             - etransitivity; [|eauto].
               apply Partition_Permutation in Hpart. rewrite Hpart.
               unfold idty. erewrite map_map, map_ext. apply incl_map.
               apply incl_app; [solve_incl_app|apply incl_appr, incl_filter', incl_refl].
               intros (?&?&?); auto.
             - erewrite fst_NoDupMembers, map_map, <-map_ext, <-fst_NoDupMembers; eauto. 2:intros (?&?&?); auto.
               now rewrite Permutation_app_comm.
             - constructor; auto.
               + rewrite app_assoc. apply in_or_app; auto.
               + eapply In_InMembers, fst_InMembers in Hin2.
                 rewrite H6 in Hin2. apply in_seq in Hin2 as (?&?); auto.
               + eapply wt_clock_incl; eauto. solve_incl_app.
           }
          *{ rewrite Forall_map. apply Forall_forall; intros ((?&?)&?&?) Hin.
             eapply when_free_wt; eauto.
             - eapply in_or_app, or_introl, rename_var_wt; eauto.
               eapply new_idents_In_inv in Hin as (?&Hin); eauto.
               eapply filter_In in Hin as (Hin&Hfilter).
               rewrite equiv_decb_equiv in Hfilter. inv Hfilter.
               eapply Hincl.
               apply Partition_Permutation in Hpart. rewrite Hpart, idty_app.
               apply in_or_app, or_intror. solve_In.
             - rewrite 2 in_app_iff. do 2 right. solve_In; eauto with datatypes. reflexivity.
             - rewrite app_assoc. apply in_or_app; auto.
             - eapply In_InMembers, fst_InMembers in Hin2.
               rewrite H6 in Hin2. apply in_seq in Hin2 as (?&?); auto.
             - eapply wt_clock_incl; eauto. solve_incl_app.
           }
        + rewrite Forall_map.
          eapply cond_eq_wt in H0; eauto using subclock_exp_wt.
          2:rewrite subclock_exp_typeof; auto.
          eapply Forall_impl; [|eauto]; intros ? Hwt.
          constructor. eapply wt_equation_incl; eauto.
          apply incl_app; [solve_incl_app|]. apply incl_appr, incl_appl.
          unfold idty. erewrite 2 map_map, map_ext; eauto. reflexivity.
          intros (?&?&?); auto.
        + eapply cond_eq_wt_clock in H0; eauto.
          unfold idty, idck in *. repeat rewrite Forall_map in H0. repeat rewrite Forall_map.
          eapply Forall_impl; [|eauto]; intros (?&?&?) ?.
          eapply wt_clock_incl; eauto. solve_incl_app.
        + assert (Forall (fun k => k < snd tn) (map fst branches)) as Hlt.
          { rewrite H6. apply Forall_forall; intros ? Hin.
            apply in_seq in Hin as (?&?); auto. }
          clear - Hini H1 H5 Hlt Hck'.
          eapply Forall_impl with (P:=fun '(_, (_, ck, _)) => wt_clock G.(enums) (envty'++idty l1) ck). intros (?&(?&?)&?) ?.
          1:{ eapply wt_clock_incl; eauto.
              apply incl_app; [solve_incl_app|].
              apply incl_appr, incl_appl.
              unfold idck, idty. repeat rewrite map_map. erewrite map_ext. reflexivity.
              intros (?&?&?); eauto. }
          eapply mmap_values in H1.
          induction H1 as [|(?&?) (((?&?)&?)&?)]; simpl in *; inv Hlt; auto.
          rewrite map_app. apply Forall_app; split; auto.
          clear - Hini H5 H3 H Hck'. destruct H as (?&?&?); repeat inv_bind.
          eapply new_idents_wt_clock with (vars':=envty'++_) in H; eauto.
          eapply new_idents_wt_clock with (vars':=envty'++_) in H0; eauto.
          2,3:eapply wt_clock_incl; eauto; solve_incl_app.
          unfold idck, idty in *. repeat rewrite Forall_map in H, H0.
          apply Forall_app; split; rewrite Forall_map;
            (eapply Forall_impl; [|eauto]); intros ((?&?)&?&?) Hwt; simpl in *.
          1,2:repeat rewrite map_map in Hwt; erewrite map_ext in Hwt; eauto; intros (?&?&?); auto.
        + eapply cond_eq_wt_enum in H0; eauto.
          2:{ constructor; auto; destruct tn as (?&[]); simpl in *; try lia.
              apply Permutation_sym, Permutation_nil, map_eq_nil in H6. congruence. }
          clear - H0.
          unfold idty in *. repeat rewrite map_map in *. erewrite map_ext; eauto. intros (?&?&?); auto.
        + eapply Forall_incl in Hwenv; [|eapply incl_map; eauto].
          apply Partition_Permutation in Hpart. rewrite Hpart, idty_app, map_app, Forall_app in Hwenv.
          clear - Hwenv H1 H5 Hck'.
          eapply mmap_values in H1.
          induction H1 as [|(?&?) (((?&?)&?)&?)]; simpl in *; auto.
          rewrite 2 idty_app, map_app. apply Forall_app; split; auto.
          rewrite map_app, 2 idty_app, map_app.
          destruct H as (?&?&?); repeat inv_bind.
          apply Forall_app; split; eapply new_idents_wt_enum. 2,4:eauto.
          1,2:destruct Hwenv as (Hwenv1&Hwenv2); eauto.
          eapply Forall_incl; [eapply Hwenv2|]. apply incl_map, incl_map, incl_filter', incl_refl.
      - (* local *)
        econstructor; eauto.
        + eapply switch_blocks_wt' with (envty:=envty++idty (idty locs)) in H0; eauto.
          * intros ? Hin. apply InMembers_app; auto.
          * intros ??? Hfind Hin.
            repeat rewrite in_app_iff in *. destruct Hin as [Hin|Hin]; eauto.
            exfalso. eapply Env.find_In, Hsubin, fst_InMembers in Hfind; eauto.
            eapply In_InMembers in Hin. rewrite InMembers_idty, InMembers_idty in Hin.
            eapply H5; eauto.
            eapply incl_map; eauto. now rewrite map_fst_idty.
          * intros ?? Hin.
            repeat rewrite in_app_iff in *. destruct Hin as [Hin|Hin]; eauto.
            right. clear - Hin. solve_In.
          * rewrite idty_app, Permutation_app_comm.
            apply incl_app; [apply incl_appl; auto|solve_incl_app].
          * apply NoDupMembers_app; auto. now rewrite 2 NoDupMembers_idty.
            intros ? Hinm1 Hinm2. rewrite 2 InMembers_idty in Hinm2. rewrite fst_InMembers in Hinm1.
            eapply H5; eauto.
          * apply NoDupMembers_app; auto. now rewrite NoDupMembers_idty.
            intros ? Hinm1 Hinm2. rewrite InMembers_idty in Hinm1.
            eapply H5; eauto.
            eapply fst_InMembers, InMembers_incl; eauto. now rewrite InMembers_idty.
          * rewrite map_app, Forall_app. split; auto.
          * eapply wt_clock_incl; eauto; solve_incl_app.
          * rewrite map_app, map_fst_idty.
            eapply Forall_impl; [|eapply H2]; intros. now rewrite map_fst_idty.
        + unfold wt_clocks, idck, idty in *.
          repeat rewrite Forall_map. eapply Forall_impl; [|eauto]. intros (?&(?&?)&?) Hwt; simpl.
          eapply subclock_clock_wt with (vars:=envty++_); eauto.
          * intros ??? Hfind Hin. rewrite in_app_iff in *. repeat rewrite map_map in *; simpl in *.
            destruct Hin as [Hin|Hin]; eauto.
            exfalso. simpl_In.
            eapply Env.find_In, Hsubin, fst_InMembers in Hfind.
            eapply H5; eauto using In_InMembers.
            eapply incl_map; eauto. erewrite map_map, map_ext; eauto.
          * intros ?? Hfind Hin. rewrite in_app_iff in *. repeat rewrite map_map in *; simpl in *.
            destruct Hin as [Hin|Hin]; eauto.
            right. clear - Hin. solve_In.
          * eapply wt_clock_incl; eauto; solve_incl_app.
        + clear - H8. unfold idty in *.
          repeat rewrite map_map in *. erewrite map_ext; eauto. intros (?&((?&?)&?)); auto.
    Qed.

  End switch_block.

  Fact subclock_clock_idem : forall ck,
    subclock_clock Cbase (Env.empty ident) ck = ck.
  Proof.
    induction ck; simpl; auto.
    unfold rename_var. rewrite Env.gempty; simpl.
    f_equal; auto.
  Qed.

  Lemma switch_node_wt G1 G2 : forall n,
      global_iface_eq G1 G2 ->
      wt_node G1 n ->
      wt_node G2 (switch_node n).
  Proof.
    intros * Heq (Hwc1&Hwc2&Hwc3&Hwt4).
    repeat split; simpl; auto.
    1-2:destruct Heq as (Henums&_); congruence.
    1:eapply Forall_impl; [|eauto]; intros; eauto using iface_eq_wt_enum.
    eapply iface_eq_wt_block; eauto.
    eapply switch_block_wt in Hwt4; eauto. 8:eapply surjective_pairing.
    - intros ? Hin. apply Env.Props.P.F.empty_in_iff in Hin. inv Hin.
    - intros ??? Hfind. rewrite Env.gempty in Hfind. congruence.
    - reflexivity.
    - rewrite 2 NoDupMembers_idty. apply n_nodup.
    - rewrite NoDupMembers_idty. apply n_nodup.
    - constructor.
    - rewrite 2 map_fst_idty. apply n_nodup.
  Qed.

  Lemma switch_global_wt : forall G,
      wt_global G ->
      wt_global (switch_global G).
  Proof.
    intros (enums&nds) (Hbool&Hwt). unfold wt_global, CommonTyping.wt_program in *; simpl.
    constructor; auto.
    induction nds; simpl; inv Hwt; auto with datatypes.
    destruct H1.
    constructor; [constructor|].
    - eapply switch_node_wt; eauto.
      eapply switch_global_iface_eq.
    - rewrite Forall_map. eapply Forall_impl; [|eapply H0]; intros.
      simpl; eauto.
    - eapply IHnds; eauto.
  Qed.

End CSTYPING.

Module CSTypingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Syn : LSYNTAX Ids Op OpAux Cks)
       (Typ : LTYPING Ids Op OpAux Cks Syn)
       (CS  : CLOCKSWITCH Ids Op OpAux Cks Syn)
       <: CSTYPING Ids Op OpAux Cks Syn Typ CS.
  Include CSTYPING Ids Op OpAux Cks Syn Typ CS.
End CSTypingFun.
