From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Setoid Morphisms.

From Velus Require Import Common.
From Velus Require Import Operators FunctionalEnvironment.
From Velus Require Import Clocks.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Import CoindIndexed.
From Velus Require Import Fresh.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LClocking Lustre.LSemantics Lustre.LClockedSemantics.
From Velus Require Import Lustre.NormFby.NormFby.
From Velus Require Import Lustre.NormFby.NFClocking.
From Velus Require Import Lustre.SubClock.SCCorrectness.

Module Type NFCORRECTNESS
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import CStr : COINDSTREAMS Ids Op OpAux Cks)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Cl : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Import Ord : LORDERED Ids Op OpAux Cks Senv Syn)
       (Import Sem : LSEMANTICS Ids Op OpAux Cks Senv Syn Ord CStr)
       (Import LCS : LCLOCKEDSEMANTICS Ids Op OpAux Cks Senv Syn Cl Ord CStr Sem)
       (Import NF  : NORMFBY Ids Op OpAux Cks Senv Syn).

  Import Fresh Tactics NF.

  Module Import Clocking := NFClockingFun Ids Op OpAux Cks Senv Syn Cl NF.
  Module Import SCC := SCCorrectnessFun Ids Op OpAux Cks CStr Senv Syn Cl Ord Sem LCS SC. Import SC.

  Section normfby_node_sem.
    Variable G1 : @global normlast last_prefs.
    Variable G2 : @global normalized fby_prefs.

    Hypothesis Hiface : global_iface_incl G1 G2.
    Hypothesis HGref : global_sem_refines G1 G2.

    Hypothesis HwcG1 : wc_global G1.

    (** *** Manipulation of initialization streams *)

    (** We want to specify the semantics of the init equations created during the normalization
      with idents stored in the env *)

    Definition false_val := Venum 0.
    Definition true_val := Venum 1.

    Lemma sfby_const : forall bs v,
        sfby v (const_val bs v) ≡ (const_val bs v).
    Proof.
      cofix CoFix.
      intros [b bs] v.
      rewrite const_val_Cons.
      destruct b; rewrite sfby_Cons; constructor; simpl; auto.
    Qed.

    Lemma case_false : forall bs xs ys,
        aligned xs bs ->
        aligned ys bs ->
        case (const_val bs false_val) [(1, ys); (0, xs)] None xs.
    Proof.
      cofix CoFix.
      intros [b bs] xs ys Hsync1 Hsync2.
      rewrite const_val_Cons. unfold false_val.
      inv Hsync1; inv Hsync2; econstructor; simpl; eauto.
      + repeat constructor; simpl; congruence.
    Qed.

    Lemma sfby_fby1 : forall bs v y ys,
        aligned ys bs ->
        fby1 y (const_val bs v) ys (sfby y ys).
    Proof with eauto.
      cofix sfby_fby1.
      intros [b bs] v y ys Hsync.
      specialize (sfby_fby1 bs).
      inv Hsync;
        rewrite const_val_Cons; rewrite unfold_Stream; simpl.
      - constructor...
      - constructor...
    Qed.

    Lemma sfby_fby1' : forall y y0s ys zs,
        fby1 y y0s ys zs ->
        zs ≡ (sfby y ys).
    Proof.
      cofix CoFix.
      intros y y0s ys zs Hfby1.
      inv Hfby1; constructor; simpl; eauto.
    Qed.

    Lemma sfby_fby : forall b v y,
        aligned y b ->
        fby (const_val b v) y (sfby v y).
    Proof with eauto.
      cofix sfby_fby.
      intros [b bs] v y Hsync.
      rewrite const_val_Cons.
      rewrite unfold_Stream; simpl.
      destruct b; simpl; inv Hsync.
      - econstructor. eapply sfby_fby1...
      - econstructor; simpl...
    Qed.

    Definition init_stream bs :=
      sfby true_val (enum bs 0).

    Global Instance init_stream_Proper:
      Proper (@EqSt bool ==> @EqSt svalue) init_stream.
    Proof.
      intros bs bs' Heq1.
      unfold init_stream. rewrite Heq1. reflexivity.
    Qed.

    Lemma fby_case : forall bs v y0s ys zs,
        (aligned y0s bs \/ aligned ys bs \/ aligned zs bs) ->
        fby y0s ys zs ->
        case (sfby true_val (const_val bs false_val)) [(1, y0s);(0, sfby v ys)] None zs.
    Proof with eauto.
      cofix CoFix.
    intros [b bs] v y0s ys zs Hsync Hfby1.
    apply fby_aligned in Hsync as [Hsync1 [Hsync2 Hsync3]]; [|auto].
    destruct b; inv Hsync1; inv Hsync2; inv Hsync3.
    - repeat rewrite const_val_Cons.
      inv Hfby1.
      repeat rewrite sfby_Cons. econstructor; simpl.
      + rewrite sfby_const.
        assert (vs1 ≡ sfby v1 vs0) as Heq by (eapply sfby_fby1'; eauto).
        rewrite Heq.
        apply case_false... rewrite <-Heq; auto.
      + repeat constructor; simpl; auto; congruence.
      + constructor.
      + repeat constructor.
    - rewrite const_val_Cons. repeat rewrite sfby_Cons.
      inv Hfby1.
      constructor; auto.
      eapply CoFix; eauto. simpl; auto.
    Qed.

    Corollary fby_init_stream_case : forall bs v y0s ys zs,
        (aligned y0s bs \/ aligned ys bs \/ aligned zs bs) ->
        fby y0s ys zs ->
        case (init_stream bs) [(1, y0s); (0, sfby v ys)] None zs.
      intros * Hsync Hfby1.
      eapply fby_case in Hfby1; eauto.
      unfold init_stream.
      rewrite const_val_enum; eauto.
    Qed.

    Lemma arrow_case : forall bs y0s ys zs,
        (aligned y0s bs \/ aligned ys bs \/ aligned zs bs) ->
        arrow y0s ys zs ->
        case (sfby true_val (const_val bs false_val)) [(1,y0s);(0,ys)] None zs.
    Proof with eauto.
      cofix CoFix.
      intros [b bs] y0s ys zs Hsync Harrow.
      apply arrow_aligned in Hsync as [Hsync1 [Hsync2 Hsync3]]; [|auto].
      destruct b; inv Hsync1; inv Hsync2; inv Hsync3; inv Harrow.
      - rewrite const_val_Cons, sfby_Cons.
        econstructor; simpl; auto.
        + rewrite sfby_const.
          clear - H0 H1 H2 H3. revert bs vs vs0 vs1 H1 H2 H3 H0.
          cofix CoFix. intros * Hsync1 Hsync2 Hsync3 Harrow.
          destruct bs as [[|] bs]; inv Hsync1; inv Hsync2; inv Hsync3; inv Harrow.
          1,2:rewrite const_val_Cons; econstructor; simpl; eauto.
          repeat constructor; auto; simpl; congruence.
        + repeat constructor; auto; simpl; congruence.
      - rewrite const_val_Cons, sfby_Cons.
        constructor; simpl; eauto.
    Qed.

    Corollary arrow_init_stream_case : forall bs y0s ys zs,
        (aligned y0s bs \/ aligned ys bs \/ aligned zs bs) ->
        arrow y0s ys zs ->
        case (init_stream bs) [(1,y0s);(0,ys)] None zs.
    Proof.
      intros * Hsync Harrow.
      eapply arrow_case in Harrow; eauto.
      unfold init_stream.
      rewrite const_val_enum; auto.
    Qed.

    Lemma ac_sfby : forall v0 xs,
        abstract_clock (sfby v0 xs) ≡ abstract_clock xs.
    Proof.
      cofix CoFix. intros v0 [x xs].
      rewrite sfby_Cons.
      destruct x; constructor; simpl; auto.
    Qed.

    Lemma init_stream_ac : forall bs,
        abstract_clock (init_stream bs) ≡ bs.
    Proof.
      intros bs.
      unfold init_stream.
      rewrite ac_sfby. apply ac_enum.
    Qed.

    Section normfby_block_sem.

      Variable vars : static_env.

      Hypothesis Atoms : Forall (fun '(x, _) => AtomOrGensym last_prefs x) vars.

      Import NormFby.

      Definition hist_st {pref} vars b H (st: fresh_st pref _) :=
        dom H (vars++st_senv st) /\
          LCS.sc_vars (vars++st_senv st) H b.

      Lemma fresh_ident_refines : forall hint H a id (v: Stream svalue) (st st' : fresh_st Ids.fby_id _),
          dom H (vars++st_senv st) ->
          fresh_ident hint a st = (id, st') ->
          FEnv.refines (@EqSt _) H (FEnv.add (Var id) v H).
      Proof with eauto.
        intros * Hdom Hfresh.
        eapply FEnv.add_refines; auto using EqStrel_Reflexive.
        intro contra. apply Hdom, IsVar_app in contra as [contra|contra].
        + eapply Facts.fresh_ident_In in Hfresh.
          inv contra. simpl_In. simpl_Forall.
          assert (In id (st_ids st')).
          { unfold st_ids, idty. solve_In. }
          eapply Facts.st_valid_AtomOrGensym_nIn; eauto using fby_not_in_last_prefs.
        + inv contra. simpl_In.
          eapply Facts.fresh_ident_nIn in Hfresh; eauto. eapply Hfresh. solve_In.
      Qed.

      Fact fresh_ident_dom : forall pref hint vars H a id v (st st' : fresh_st pref _),
          dom H (vars++st_senv st) ->
          fresh_ident hint a st = (id, st') ->
          dom (FEnv.add (Var id) v H) (vars++st_senv st').
      Proof.
        intros * (D1&D2) Hfresh. unfold st_senv in *.
        destruct_conjs.
        apply Ker.fresh_ident_anns in Hfresh. rewrite Hfresh; simpl.
        split; intros ?; rewrite FEnv.add_In; [rewrite D1|rewrite D2];
          rewrite <-Permutation.Permutation_middle;
          (split; [intros [Eq|]; try inv Eq; eauto with senv datatypes
                  |intros Var; inv Var; simpl in *]).
        - take (_ \/ _) and destruct it; subst; eauto with senv.
        - take (_ \/ _) and destruct it; inv_equalities; simpl in *; try congruence.
          right. econstructor; eauto.
      Qed.

      Fact fresh_ident_hist_st : forall hint b ty ck id v H (st st': fresh_st Ids.fby_id _),
          sem_clock (var_history H) b ck (abstract_clock v) ->
          fresh_ident hint (ty, ck) st = (id, st') ->
          hist_st vars b H st ->
          hist_st vars b (FEnv.add (Var id) v H) st'.
      Proof with auto.
        intros * Hsem Hfresh [Hdom Hsc].
        assert (~In id (st_ids st)) as Hnin by (eapply Facts.fresh_ident_nIn in Hfresh; eauto).
        assert (Hfresh':=Hfresh). apply fresh_ident_anns in Hfresh'.
        assert (FEnv.refines (@EqSt _) H (FEnv.add (Var id) v H)) as Href.
        { eapply fresh_ident_refines in Hfresh; eauto. }
        destruct Hsc as (Hsc1&Hsc2). split; [|split]; auto.
        - eapply fresh_ident_dom; eauto.
        - intros * Hck Hv. unfold st_senv in *.
          rewrite Hfresh' in Hck. simpl_app. simpl in *. rewrite <-Permutation.Permutation_middle in Hck.
          inv Hck. inv H0.
          + inv H1. inv Hv. rewrite FEnv.gss in H1; inv H1.
            rewrite H2. eapply sem_clock_refines; eauto using var_history_refines.
          + eapply sem_clock_refines, Hsc1; eauto using var_history_refines with senv.
            inv Hv. econstructor; eauto. rewrite FEnv.gso in H2; auto.
            intro contra; inv contra.
            take (In _ (_ ++ _)) and apply in_app_iff in it as [Hin|Hin].
            * eapply Facts.fresh_ident_nIn' with (aft:=List.map fst vars); eauto using fby_not_in_last_prefs.
              clear Hin. simpl_Forall; auto.
              solve_In.
            * eapply Hnin. unfold st_ids. solve_In.
        - intros * Hck Hla Hv. unfold st_senv in *.
          rewrite Hfresh' in Hck, Hla. simpl_app. simpl in *. rewrite <-Permutation.Permutation_middle in Hck, Hla.
          inv Hck. inv Hla. inv H0; inv H1; inv_equalities.
          + exfalso. simpl in *. congruence.
          + exfalso.
            apply in_app_iff in H0 as [Hin|Hin]; [|eapply Hnin; solve_In].
            eapply Facts.fresh_ident_nIn' with (aft:=List.map fst vars); eauto using fby_not_in_last_prefs. 2:solve_In.
            clear Hin. simpl_Forall. auto.
          + eapply sem_clock_refines, Hsc2; eauto using var_history_refines with senv.
            inv Hv. econstructor; eauto.
            unfold FEnv.add in *. cases_eqn Eq; auto.
            rewrite equiv_decb_equiv in Eq. inv Eq.
          + eapply sem_clock_refines, Hsc2; eauto using var_history_refines with senv.
            inv Hv. econstructor; eauto.
            unfold FEnv.add in *. cases_eqn Eq; auto.
            rewrite equiv_decb_equiv in Eq. inv Eq.
      Qed.

      Fact init_var_for_clock_sem : forall bs H ck bs' x eqs' st st',
          sem_clock (var_history H) bs ck bs' ->
          hist_st vars bs H st ->
          init_var_for_clock ck st = (x, eqs', st') ->
          (exists H',
              FEnv.refines (@EqSt _) H H' /\
                hist_st vars bs H' st' /\
                sem_var H' (Var x) (init_stream bs') /\
                Forall (sem_equation_ck G2 H' bs) eqs').
      Proof with eauto.
        intros * Hsemc Histst Hinit.
        unfold init_var_for_clock in Hinit.
        destruct (fresh_ident _ _) eqn:Hident. repeat inv_bind.
        remember (FEnv.add (Var x) (init_stream bs' (* rs' *)) H) as H'.
        assert (H ⊑ H') as Href1.
        { subst. eapply fresh_ident_refines in Hident; eauto.
          now destruct Histst. }
        assert (hist_st vars bs H' st') as Histst1.
        { subst. eapply fresh_ident_hist_st in Hident...
          destruct Histst as (Hdom&Hsc).
          now rewrite init_stream_ac. }
        exists H'. repeat (split; eauto).
        + rewrite HeqH'. econstructor. 2:reflexivity.
          apply FEnv.gss.
        + repeat constructor.
          apply Seq with (ss:=[[(init_stream bs' (* rs' *))]]); simpl; repeat constructor.
          * econstructor; repeat constructor.
            1,2:apply add_whens_enum_sem; eauto using sem_clock_refines, var_history_refines.
            repeat constructor. unfold init_stream.
            repeat rewrite const_val_const; subst.
            do 2 rewrite const_val_enum. apply sfby_fby; simpl; eauto.
            rewrite <- const_val_enum. apply enum_aligned.
          * econstructor. 2:reflexivity.
            rewrite HeqH'. apply FEnv.gss.
      Qed.

      Hint Constructors Forall3 : datatypes.

      Fact fby_iteexp_sem : forall bs H e0 e ty nck y0 y z e' eqs' st st' ,
          normalized_lexp e0 ->
          clockof e0 = [nck] ->
          wc_exp G1 (vars++st_senv st) e0 ->
          wc_exp G1 (vars++st_senv st) e ->
          sem_exp_ck G1 H bs e0 [y0] ->
          sem_exp_ck G1 H bs e [y] ->
          fby y0 y z ->
          hist_st vars bs H st ->
          fby_iteexp e0 e (ty, nck) st = (e', eqs', st') ->
          (exists H',
              FEnv.refines (@EqSt _) H H' /\
                hist_st vars bs H' st' /\
                sem_exp_ck G2 H' bs e' [z] /\
                Forall (sem_equation_ck G2 H' bs) eqs').
      Proof with eauto.
        intros * Hnormed Hck Hwc0 Hwc Hsem0 Hsem Hfby Histst Hiteexp.
        assert (st_follows st st') as Hfollows by (eapply fby_iteexp_st_follows; eauto).
        unfold fby_iteexp in Hiteexp; repeat inv_bind.
        assert (Hsck:=Hsem0). eapply sc_exp with (Γ:=vars++st_senv st) in Hsck... simpl in Hsck.
        2:(destruct Histst; auto).
        rewrite Hck in Hsck. eapply Forall2_singl in Hsck.

        eapply init_var_for_clock_sem in H0 as [H' [Href1 [Histst1 [Hsem1 Hsem1']]]]...
        remember (abstract_clock y0) as bs'.
        remember (match ty with
                  | Tprimitive cty => Vscalar (Op.sem_cconst (Op.init_ctype cty))
                  | Tenum _ n => Venum 0 end) as v0.
        remember (sfby v0 y) as y'.
        remember (FEnv.add (Var x2) y' H') as H''.
        assert (FEnv.refines (@EqSt _) H' H'') by (subst; destruct Histst1; eauto using fresh_ident_refines).
        assert (hist_st vars bs H'' st') as Histst2.
        { subst. eapply fresh_ident_hist_st...
          rewrite ac_sfby.
          rewrite ac_fby2, <- ac_fby1; eauto using sem_clock_refines, var_history_refines. }
        exists H''. repeat (split; eauto with fresh norm); try constructor.
        - etransitivity; eauto.
        - eapply ScaseTotal with (s:=(init_stream bs')) (vs:=[[(1, y0);(0, y')]]).
          + econstructor. eapply sem_var_refines...
          + econstructor. 2:econstructor. 3:econstructor.
            1,2:constructor; eauto.
            4,5:simpl; rewrite app_nil_r; econstructor; eauto with datatypes.
            * eapply sem_exp_refines; [|eauto using sem_ref_sem_exp].
              etransitivity; eauto.
            * subst. do 2 econstructor; eauto. eapply FEnv.gss. reflexivity.
            * simpl. constructor; auto.
          + constructor; auto with datatypes. subst.
            eapply fby_init_stream_case; eauto using ac_aligned.
        - apply Seq with (ss:=[[y']]); repeat constructor.
          + eapply Sfby with (s0ss:=[[const_val bs' v0]]) (sss:=[[y]]); repeat constructor.
            * destruct ty as [|]; simpl; rewrite Heqv0; subst.
              -- eapply sem_exp_ck_morph; eauto. 1,2:reflexivity.
                 econstructor; eauto. eapply const_val_const.
                 eapply add_whens_const_sem; eauto using sem_clock_refines, var_history_refines.
              -- eapply sem_exp_ck_morph; eauto. 1,2:reflexivity.
                 econstructor; eauto. eapply const_val_enum.
                 eapply add_whens_enum_sem; eauto using sem_clock_refines, var_history_refines.
            * eapply sem_ref_sem_exp; eauto using sem_exp_refines.
            (* * eapply bools_ofs_empty. *)
            * rewrite Heqy'.
              eapply sfby_fby.
              eapply fby_aligned in Hfby as [_ [? _]]; eauto.
              left. rewrite Heqbs'. apply ac_aligned.
          + econstructor.
            rewrite HeqH''. apply FEnv.gss. reflexivity.
        - simpl_Forall; eauto using sem_equation_refines.
      Qed.

      Fact arrow_iteexp_sem : forall bs H e0 e ty nck y0 y z e' eqs' st st',
          normalized_lexp e0 ->
          clockof e0 = [nck] ->
          wc_exp G1 (vars++st_senv st) e0 ->
          wc_exp G1 (vars++st_senv st) e ->
          sem_exp_ck G1 H bs e0 [y0] ->
          sem_exp_ck G1 H bs e [y] ->
          arrow y0 y z ->
          hist_st vars bs H st ->
          arrow_iteexp e0 e (ty, nck) st = (e', eqs', st') ->
          (exists H',
              FEnv.refines (@EqSt _) H H' /\
                hist_st vars bs H' st' /\
                sem_exp_ck G2 H' bs e' [z] /\
                Forall (sem_equation_ck G2 H' bs) eqs').
      Proof with eauto.
        intros * Hnormed Hck Hwc0 Hwc1 Hsem0 Hsem Harrow Histst Hiteexp.
        assert (st_follows st st') as Hfollows by (eapply arrow_iteexp_st_follows; eauto).
        unfold arrow_iteexp in Hiteexp. repeat inv_bind.
        assert (Hsck:=Hsem0). eapply sc_exp with (Γ:=vars++st_senv st) in Hsck... simpl in Hsck.
        2:(destruct Histst; auto).
        rewrite Hck in Hsck. eapply Forall2_singl in Hsck.

        eapply init_var_for_clock_sem in H0 as [H' [Href1 [Histst1 [Hsem1 Hsem1']]]]...
        remember (abstract_clock y0) as bs'.
        exists H'. repeat (split; auto).
        eapply ScaseTotal with (s:=(init_stream bs')) (vs:=[[(1, y0);(0, y)]]).
        - econstructor; eauto.
        - econstructor. 2:econstructor. 3:econstructor.
          1,2:constructor; eauto; eapply sem_exp_refines; [|eauto using sem_ref_sem_exp]; eauto.
          2,3:simpl; constructor; eauto with datatypes. auto.
        - simpl. repeat econstructor.
          eapply arrow_init_stream_case; eauto.
          subst. left. eapply ac_aligned.
      Qed.

      Fact normfby_equation_sem lasts : forall bs H to_cut equ eqs' st st' ,
          unnested_equation lasts equ ->
          wc_equation G1 (vars++st_senv st) equ ->
          sem_equation_ck G1 H bs equ ->
          hist_st vars bs H st ->
          normfby_equation to_cut equ st = (eqs', st') ->
          (exists H',
              FEnv.refines (@EqSt _) H H' /\
                hist_st vars bs H' st' /\
                Forall (sem_equation_ck G2 H' bs) eqs').
      Proof with eauto.
        intros * Hun Hwc Hsem Histst Hfby.
        inv_normfby_equation Hfby to_cut equ; try destruct x2 as (ty&ck).
        - (* constant fby *)
          destruct PS.mem; repeat inv_bind.
          + inv Hsem. inv H6; inv H5.
            simpl in H7; rewrite app_nil_r in H7. inv H7; inv H6.
            assert (Hsem':=H3). inversion_clear H3 as [| | | | | | |???????? Hsem0 Hsem1 Hsem| | | | | |].
            inv Hsem0; inv H6. inv Hsem1; inv H7.
            simpl in Hsem; repeat rewrite app_nil_r in Hsem. inv Hsem; inv H9.
            inv Hwc. rename H6 into Hwc. apply Forall_singl in Hwc. assert (Hwc':=Hwc). inv Hwc'.
            simpl in *. simpl_Forall. rewrite app_nil_r in *.

            remember (FEnv.add (Var x2) y0 H) as H'.
            assert (FEnv.refines (@EqSt _) H H') as Href.
            { subst. destruct Histst as [Hdom _].
              eapply fresh_ident_refines in H0... }
            assert (hist_st vars bs H' st') as Histst1.
            { subst. eapply fresh_ident_hist_st in H0...
              inv Hun. 2:inv H2; inv H1.
              eapply sc_exp in H3... 2:destruct Histst; auto.
              simpl in H3; rewrite <-H7 in H3. simpl_Forall.
              apply ac_fby1 in H8. now rewrite <-H8.
            }
            exists H'. repeat (split; eauto with norm fresh).
            repeat constructor; auto.
            * eapply Seq with (ss:=[[y0]]); simpl; repeat constructor.
              2:eapply sem_var_refines; eauto.
              rewrite HeqH'. econstructor. eapply FEnv.gss. reflexivity.
            * eapply Seq with (ss:=[[y0]]); simpl; repeat constructor.
              -- eapply sem_ref_sem_exp... eapply sem_exp_refines...
              -- rewrite HeqH'. econstructor. eapply FEnv.gss. reflexivity.
          + exists H. repeat (split; eauto). reflexivity.
            constructor; auto.
            eapply sem_ref_sem_equation; eauto.
        - (* fby *)
          inv Hwc. rename H3 into Hwc. clear H4.
          apply Forall_singl in Hwc. inv Hwc. simpl_Forall. rewrite app_nil_r in *.
          inv Hsem. simpl_Forall. rewrite app_nil_r in *; subst.
          inversion_clear H11 as [| | | | | | |???????? Hsem0 Hsem1 Hsem| | | | | |].
          simpl_Forall. repeat rewrite app_nil_r in *. inv Hsem; inv H13.
          eapply fby_iteexp_sem in H0 as [H' [Href1 [Hhistst1 [Hsem' Hsem'']]]]...
          2:{ inv Hun; auto. inv H2; inv H1. }
          exists H'. repeat (split; eauto).
          constructor; auto.
          eapply Seq with (ss:=[[y]]); simpl; repeat constructor; auto.
          eapply sem_var_refines; eauto.
        - (* arrow *)
          inv Hwc. rename H3 into Hwc. clear H4. simpl_Forall. inv H3. simpl_Forall. rewrite app_nil_r in *.
          inv Hsem. simpl_Forall. rewrite app_nil_r in *; subst.
          inversion_clear H11 as [| | | | | | | |???????? Hsem0 Hsem1 Hsem| | | | |].
          simpl_Forall. repeat rewrite app_nil_r in *. inv Hsem; inv H13.
          eapply arrow_iteexp_sem in H0 as [H' [Href1 [Hhistst1 [Hsem' Hsem'']]]]...
          2:{ inv Hun; auto. inv H2; inv H1. }
          exists H'. repeat (split; eauto).
          constructor; auto.
          eapply Seq with (ss:=[[y]]); simpl; repeat constructor; auto.
          eapply sem_var_refines; eauto.
        - (* other *)
          exists H. repeat (split; eauto). reflexivity.
          constructor; auto.
          eapply sem_ref_sem_equation; eauto.
      Qed.

      Lemma hist_st_mask {pref} : forall vars bs H (st: fresh_st pref _) r k,
          hist_st vars bs H st ->
          hist_st vars (maskb k r bs) (mask_hist k r H) st.
      Proof.
        intros * (?&?).
        split.
        - eapply dom_map; eauto.
        - eapply LCS.sc_vars_mask; eauto.
      Qed.

      Lemma normfby_block_sem lasts : forall to_cut d blocks' bs H st st' ,
          normlast_block lasts d ->
          wc_block G1 (vars++st_senv st) d ->
          sem_block_ck G1 H bs d ->
          hist_st vars bs H st ->
          normfby_block to_cut d st = (blocks', st') ->
          (exists H',
              FEnv.refines (@EqSt _) H H' /\
                hist_st vars bs H' st' /\
                Forall (sem_block_ck G2 H' bs) blocks').
      Proof.
        induction d using block_ind2; intros * Hun Hwc Hsem Hist Hnorm;
          inv Hun; inv Hwc; inv Hsem; repeat inv_bind.
        - (* eq *)
          eapply normfby_equation_sem in H0 as (H'&?&?&?); eauto.
          exists H'. repeat (split; auto).
          simpl_Forall.
          constructor; auto.
        - (* last *)
          exists H. repeat (split; auto).
          + reflexivity.
          + repeat (econstructor; eauto using sem_ref_sem_exp).
        - (* reset *)
          simpl in Hnorm; cases; repeat inv_bind.
          apply Forall_singl in H. apply Forall_singl in H4.
          assert (forall k, exists H'k,
                     FEnv.refines (@EqSt _) (CStr.mask_hist k r H0) (CStr.mask_hist k r H'k) /\
                       hist_st vars (maskb k r bs) (mask_hist k r H'k) st' /\
                       Forall (sem_block_ck G2 (mask_hist k r H'k) (maskb k r bs)) x0) as Hblocks'.
          { intros k. specialize (H12 k).
            apply Forall_singl in H12. eapply H in H12 as (H'k&?&(?&Hsc)&?); eauto.
            2:eapply hist_st_mask; eauto.
            assert (slower_hist H'k (maskb k r bs)) as Hslow.
            { eapply sc_vars_slower_hist in Hsc; eauto using dom_dom_ub. }
            eapply slower_mask_hist in Hslow.
            exists H'k. split; [|split; [split|]]; intros.
            - rewrite <-Hslow; auto.
            - now apply dom_map.
            - unfold mask_hist. simpl. eapply sc_vars_morph. 1,3,4:eauto; reflexivity.
              apply Hslow.
            - simpl_Forall. eapply sem_block_ck_morph; eauto. reflexivity.
          }
          eapply consolidate_mask_hist
            with (P := fun k H'k => FEnv.refines (@EqSt _) (CStr.mask_hist k r H0) H'k /\
                                   hist_st vars (maskb k r bs) H'k st' /\
                                   Forall (sem_block_ck G2 H'k (maskb k r bs)) x0)
            in Hblocks' as (H'&HH').
          2:{ intros ????? Heq (?&(?&Hsc1)&?); subst. split; [|split; [split|]]; intros; auto.
              2:split; intros ?. 1-3:rewrite <-Heq; auto.
              1,2:eapply H9; eauto.
              - eapply sc_vars_morph; eauto. reflexivity.
              - simpl_Forall. eapply sem_block_ck_morph; eauto. reflexivity.
          }
          2:{ intros ?? (_&(Hdom1&_)&_); simpl. eapply dom_fenv_dom; eauto. }
          exists H'.
          assert (FEnv.refines (@EqSt _) H0 H') as Href.
          { eapply refines_unmask; intros.
            specialize (HH' k) as (?&_); eauto.
          }
          split; [|split; [split|]]; auto.
          + specialize (HH' 0) as (_&(Hdom&_)&_); auto.
            setoid_rewrite dom_map in Hdom; auto.
          + eapply sc_vars_unmask.
            intros k. specialize (HH' k) as (_&(_&?)&_); eauto.
          + simpl_Forall. econstructor; eauto.
            * eapply sem_ref_sem_exp; eauto. eapply sem_exp_refines; eauto.
            * intros ?. specialize (HH' k) as (_&_&?).
              constructor; auto. eapply Forall_forall in H5; eauto.
      Qed.

      Fact normfby_blocks_sem lasts : forall bs to_cut blocks blocks' H st st' ,
          Forall (normlast_block lasts) blocks ->
          Forall (wc_block G1 (vars++st_senv st)) blocks ->
          Forall (sem_block_ck G1 H bs) blocks ->
          hist_st vars bs H st ->
          normfby_blocks to_cut blocks st = (blocks', st') ->
          (exists H',
              FEnv.refines (@EqSt _) H H' /\
                hist_st vars bs H' st' /\
                Forall (sem_block_ck G2 H' bs) blocks').
      Proof with eauto.
        induction blocks; intros * Hunt Hwc Hsem Hhistst Hfby;
          unfold normfby_blocks in Hfby; simpl in *; repeat inv_bind.
        - exists H; simpl; repeat (split; auto). reflexivity.
        - assert (normfby_blocks to_cut blocks x1 = (concat x2, st')) as Hnorm.
          { unfold normfby_blocks; repeat inv_bind.
            repeat eexists; eauto. repeat inv_bind; auto. }
          inv Hunt. inv Hwc. inv Hsem.
          assert (st_follows st x1) as Hfollows by (eapply normfby_block_st_follows in H0; eauto).
          eapply normfby_block_sem in H0 as [H' [Href1 [Hhistst1 Hsem1]]]. 2-5:eauto.
          assert (Forall (sem_block_ck G1 H' bs) blocks) as Hsem'.
          { simpl_Forall. eapply sem_block_refines... } clear H9.
          eapply IHblocks in Hnorm as (H''&Href&Hdom&Hsem2). 2-5:eauto.
          2:simpl_Forall; repeat solve_incl.
          + exists H''. split;[|split]...
            * etransitivity...
            * simpl. apply Forall_app; split; eauto.
              simpl_Forall. eapply sem_block_refines...
      Qed.

    End normfby_block_sem.

    Fact init_st_hist_st : forall b H xs,
        dom H xs ->
        sc_vars xs H b ->
        hist_st xs b H (@init_st Ids.fby_id _).
    Proof.
      intros b H n Hdom (?&?).
      split; [|split].
      1-3:unfold st_senv; rewrite init_st_anns, app_nil_r; auto.
    Qed.

    Lemma normfby_node_sem : forall f n ins outs,
        wc_global (Global G1.(types) G1.(externs) (n::G1.(nodes))) ->
        wc_global G2 ->
        Ordered_nodes (Global G1.(types) G1.(externs) (n::G1.(nodes))) ->
        Ordered_nodes (Global G2.(types) G2.(externs) ((normfby_node n)::G2.(nodes))) ->
        sem_node_ck (Global G1.(types) G1.(externs) (n::G1.(nodes))) f ins outs ->
        sem_node_ck (Global G2.(types) G2.(externs) ((normfby_node n)::G2.(nodes))) f ins outs.
    Proof with eauto.
      intros * HwcG HwcG' Hord1 Hord2 Hsem.
      assert (Ordered_nodes (Global G2.(types) G2.(externs) (normfby_node n :: G2.(nodes)))) as Hord'.
      { inv Hord2. destruct H1. constructor; [split|]... }

      inv Hsem; assert (Hfind:=H0). destruct (ident_eq_dec (n_name n) f).
      - erewrite find_node_now in H0; eauto. inv H0.
        inversion_clear HwcG as [|?? (?&?)].
        (* The semantics of equations can be given according to G only *)
        assert (~Is_node_in_block (n_name n0) (n_block n0)) as Blk.
        { inv Hord1. destruct H9 as (Hisin&_). intro contra. eapply Hisin in contra as [? _]; auto. }
        eapply sem_block_ck_cons1 in Blk; eauto. clear H3.

        remember (normfby_node n0) as n'.
        unfold normfby_node in Heqn'; inv Heqn'.
        specialize (n_nodup n0) as (Hnd1&Hnd2).
        specialize (n_good n0) as (Hgood1&Hgood2&_).
        pose proof (n_syn n0) as Hsyn. inversion Hsyn as [??? _ Hsyn2 _].
        rewrite <-H7 in *. symmetry in H3; inv H3. inv Blk. inv_scope.
        simpl in *. repeat rewrite app_nil_r in *.
        inversion_clear H0 as [? _ _ Hwc]. rewrite <-H7 in Hwc. inv Hwc.
        repeat inv_scope'. subst Γ'.
        assert (Forall (sem_block_ck G1 (H + Hi') bs) blks) as Hsem by (destruct G1; auto).

        eapply normfby_blocks_sem
          with (vars:=senv_of_ins (n_in n0) ++ senv_of_decls (n_out n0) ++ senv_of_decls locs)
               (to_cut := (ps_from_list (List.map fst (n_out n0)))) (st:=init_st)
          in Hsem as (Hf&Href&(Hdom&Hsc)&Heqs'')... 5:eapply surjective_pairing.
        2:{ inv Hgood2. take (GoodLocalsScope _ _ _) and inv it.
            rewrite app_assoc. apply Forall_app; split; simpl_Forall; simpl_In; simpl_Forall; auto.
            eapply Forall_forall in Hgood1; eauto. rewrite <-map_fst_senv_of_ins, <-map_fst_senv_of_decls, <-map_app. solve_In. }
        2:{ destruct G1. unfold st_senv. now rewrite init_st_anns, app_nil_r, app_assoc. }
        2:{ take (clocked_node _ _ _) and destruct it as (Hdom&Hsc).
            constructor; simpl.
            * unfold st_senv. rewrite init_st_anns, app_nil_r, app_assoc.
              apply local_hist_dom; auto.
            * unfold st_senv. rewrite init_st_anns, app_nil_r, app_assoc.
              eapply local_hist_sc_vars with (H:=H); eauto using dom_dom_ub. reflexivity.
              inv Hnd2. take (NoDupScope _ _ _) and inv it.
              intros ?? contra; rewrite IsVar_fst, map_app, map_fst_senv_of_ins, map_fst_senv_of_decls in contra. eapply H15; eauto.
        }
        assert (Href':=Href). eapply FEnv.union_refines_inv in Href' as (Hi''&Heq&Href'&Hdom'); auto using EqStrel_Reflexive.
        2:{ intros * Hin Hin2. destruct x0; apply H4 in Hin; apply H9 in Hin2.
            - inv Hnd2. take (NoDupScope _ _ _) and inv it.
              take (forall x, InMembers x locs -> ~ _) and eapply it.
              + eapply IsVar_senv_of_decls; eauto.
              + now rewrite IsVar_fst, map_app, map_fst_senv_of_ins, map_fst_senv_of_decls in Hin.
            - inv Hnd2. take (NoDupScope _ _ _) and inv it.
              take (forall x, InMembers x locs -> ~ _) and eapply it.
              + eapply IsLast_senv_of_decls; eauto.
              + inv Hin. rewrite <- map_fst_senv_of_ins, <- map_fst_senv_of_decls, <-map_app. solve_In. }

        eapply Snode with (H:=H); simpl...
        + erewrite find_node_now...
        + assumption.
        + assumption.
        + apply sem_block_ck_cons2; simpl...
          2:{ eapply find_node_not_Is_node_in in Hord2.
              2:erewrite find_node_now; eauto. auto. }
          rewrite <-H7.
          do 2 econstructor.
          3:{ destruct G2; eauto.
              simpl_Forall. eapply sem_block_ck_morph. 4:eauto. 2,3:reflexivity.
              symmetry. eapply Heq. }
          *{ destruct Hdom as (D1&DL1). destruct H4 as ((D2&DL2)&_).
             split; intros *; simpl in *.
             - rewrite Hdom', D1, D2. setoid_rewrite senv_of_decls_app. rewrite <-st_senv_senv_of_decls.
               repeat rewrite IsVar_app.
               split; [intros ([[In|[In|In]]|In]&Hnin)|intros [In|In]]; try congruence; auto.
               + exfalso. eapply Hnin; eauto.
               + exfalso. eapply Hnin; eauto.
               + split; auto. intros contra.
                 inv Hnd2. take (NoDupScope _ _ _) and inv it.
                 eapply H15; eauto. eapply IsVar_senv_of_decls; eauto.
                 now rewrite 2 IsVar_fst, map_fst_senv_of_ins, map_fst_senv_of_decls, <-in_app_iff in contra.
               + split; auto.
                 intros contra. rewrite 2 IsVar_fst, map_fst_senv_of_ins, map_fst_senv_of_decls, <-in_app_iff in contra.
                 inv In. simpl_In. simpl_Forall.
                 eapply Facts.st_valid_AtomOrGensym_nIn; eauto using fby_not_in_last_prefs.
                 unfold st_ids. solve_In.
             - rewrite Hdom', DL1, DL2. setoid_rewrite senv_of_decls_app. rewrite <-st_senv_senv_of_decls.
               repeat rewrite IsLast_app.
               split; [intros ([[In|[In|In]]|In]&Hnin)|intros [In|In]]; try congruence; auto.
               + exfalso. eapply Hnin; eauto.
               + exfalso. eapply Hnin; eauto.
               + split; auto. intros contra.
                 inv Hnd2. take (NoDupScope _ _ _) and inv it.
                 eapply H15; eauto. eapply IsLast_senv_of_decls; eauto. rewrite <-IsLast_app in *.
                 inv contra. rewrite <- map_fst_senv_of_ins, <- map_fst_senv_of_decls, <-map_app. solve_In.
               + split; auto.
                 intros contra. rewrite <-IsLast_app in contra.
                 assert (List.In x0 (List.map fst (n_in n0) ++ List.map fst (n_out n0))) as InM.
                 { inv contra. rewrite <- map_fst_senv_of_ins, <- map_fst_senv_of_decls, <-map_app. solve_In. }
                 simpl_Forall.
                 eapply Facts.st_valid_AtomOrGensym_nIn; eauto using fby_not_in_last_prefs.
                 inv In. simpl_In. solve_In.
           }
          * eapply sc_vars_morph, sc_vars_incl; [reflexivity| |reflexivity| |eauto].
            now symmetry. setoid_rewrite senv_of_decls_app. rewrite <-st_senv_senv_of_decls.
            solve_incl_app.
        + simpl. now subst bs.
      - erewrite find_node_other in Hfind; eauto.
        eapply sem_node_ck_cons2...
        destruct G2; apply HGref.
        destruct G1; econstructor...
        eapply sem_block_ck_cons1; eauto.
        eapply find_node_later_not_Is_node_in in Hord1...
    Qed.

  End normfby_node_sem.

  Local Hint Resolve wc_global_Ordered_nodes : norm.

  Lemma normfby_global_refines : forall G,
      wc_global G ->
      global_sem_refines G (normfby_global G).
  Proof with eauto with norm.
    intros [].
    induction nodes0; intros * Hwc; simpl.
    - apply global_sem_ref_nil.
    - apply global_sem_ref_cons with (f:=n_name a)...
      + eapply normfby_global_wc, wc_global_Ordered_nodes in Hwc;
          unfold normfby_global in Hwc; simpl in Hwc...
      + inv Hwc. eapply IHnodes0...
      + intros ins outs Hsem; simpl.
        eapply normfby_node_sem with (G1:=(Global types0 externs0 nodes0)) (G2:=(Global _ _ _)) in Hsem...
        * apply iface_eq_iface_incl, normfby_global_eq.
        * inv Hwc. eapply IHnodes0...
        * inv Hwc; simpl in *...
        * eapply normfby_global_wc in Hwc... inv Hwc...
        * eapply wc_global_Ordered_nodes.
          eapply normfby_global_wc in Hwc...
  Qed.

  Corollary normfby_global_sem : forall G f ins outs,
      wc_global G ->
      sem_node_ck G f ins outs ->
      sem_node_ck (normfby_global G) f ins outs.
  Proof.
    intros.
    eapply normfby_global_refines in H; eauto.
    apply H; auto.
  Qed.

End NFCORRECTNESS.

Module NFCorrectnessFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (CStr : COINDSTREAMS Ids Op OpAux Cks)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Lord : LORDERED Ids Op OpAux Cks Senv Syn)
       (Sem : LSEMANTICS Ids Op OpAux Cks Senv Syn Lord CStr)
       (LClockSem : LCLOCKEDSEMANTICS Ids Op OpAux Cks Senv Syn Clo Lord CStr Sem)
       (NF  : NORMFBY Ids Op OpAux Cks Senv Syn)
       <: NFCORRECTNESS Ids Op OpAux Cks CStr Senv Syn Clo Lord Sem LClockSem NF.
  Include NFCORRECTNESS Ids Op OpAux Cks CStr Senv Syn Clo Lord Sem LClockSem NF.
End NFCorrectnessFun.
