From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import Transcription.Tr.

From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import Lustre.LClocking.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import NLustre.Memories.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.NLClocking.

From Coq Require Import String.
From Coq Require Import Permutation.

From Coq Require Import List.
Import List.ListNotations.

From compcert Require Import common.Errors.
Open Scope error_monad_scope.

(** * Clocking Preservation for Transcription *)


Module Type TRCLOCKING
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import OpAux: OPERATORS_AUX  Op)
       (L           : LSYNTAX    Ids Op)
       (LC          : LCLOCKING  Ids Op L)
       (Import CE   : CESYNTAX       Op)
       (NL          : NLSYNTAX   Ids Op CE)
       (Import Ord  : NLORDERED  Ids Op CE NL)
       (Import Mem  : MEMORIES   Ids Op CE NL)
       (Import IsD  : ISDEFINED  Ids Op CE NL Mem)
       (Import CEClo: CECLOCKING Ids Op CE)
       (NLC         : NLCLOCKING Ids Op CE NL Ord Mem IsD CEClo)
       (Import TR   : TR Ids Op OpAux L CE NL).

  Lemma envs_eq_in :
    forall env cenv x ck,
      envs_eq env cenv ->
      find_clock env x = OK ck ->
      In (x, ck) cenv.
  Proof.
    unfold find_clock, envs_eq. intros * Heq Hin.
    cases_eqn HH. inv Hin. apply Heq; eauto.
  Qed.

  Lemma find_clock_det :
    forall env x ck ck',
      find_clock env x = OK ck ->
      find_clock env x = OK ck' ->
      ck = ck'.
  Proof.
    unfold find_clock. intros. cases. congruence.
  Qed.

  Lemma wc_lexp :
    forall G vars e e',
      to_lexp e = OK e' ->
      LC.wc_exp G vars e ->
      (exists ck,
          L.clockof e = [ck]
          /\ wc_exp vars e' ck).
  Proof.
    intros * Hto Hwc. revert dependent e'.
    induction e using L.exp_ind2; intros; inv Hto; inv Hwc.
    - exists Cbase. split; constructor.
    - simpl. unfold L.clock_of_nclock, stripname. simpl. esplit; split; eauto.
      monadInv H0. now constructor.
    - simpl. unfold L.clock_of_nclock, stripname. simpl. esplit; split; eauto.
      monadInv H0. now constructor.
    - simpl. unfold L.clock_of_nclock, stripname. simpl. esplit; split; eauto.
      monadInv H0. constructor. apply IHe in EQ as (?&?&?); eauto.
      congruence.
    - simpl. unfold L.clock_of_nclock, stripname. simpl. esplit; split; eauto.
      monadInv H0. constructor.
      + apply IHe1 in EQ as (?&?&?); eauto. congruence.
      + apply IHe2 in EQ1 as (?&?&?); eauto. congruence.
    - cases.
      simpl. unfold L.clock_of_nclock, stripname. simpl. esplit; split; eauto.
      take (_ = OK e') and monadInv it. simpl_Foralls.
      constructor; auto.
      take (_ -> _) and apply it in EQ as (?& Heq &?); auto.
      unfold L.clocksof in *. simpl in *. rewrite app_nil_r in *.
      rewrite Heq in *. simpl_Foralls. congruence.
  Qed.

  Lemma wc_exp_cexp :
    forall vars e ck,
      wc_exp vars e ck ->
      wc_cexp vars (Eexp e) ck.
  Proof.
    now constructor.
  Qed.

  Lemma wc_cexp :
    forall G vars e e',
      to_cexp e = OK e' ->
      LC.wc_exp G vars e ->
      (exists ck,
          L.clockof e = [ck]
          /\ wc_cexp vars e' ck).
  Proof.
    intros * Hto Hwc. revert dependent e'.
    induction e using L.exp_ind2; intros;
      unfold to_cexp in Hto; try monadInv Hto;
        repeat (take (to_lexp _ = _) and eapply wc_lexp in it as (?&?&?);
                eauto); eauto using wc_exp_cexp.
    - cases. monadInv Hto.
      simpl_Foralls.
      simpl. unfold L.clock_of_nclock, stripname. simpl. esplit; split; eauto.
      inv Hwc. simpl_Foralls. constructor; simpl; auto.
      + take (_ -> _) and apply it in EQ as (?& Heq &?); auto.
        unfold L.clocksof in *. simpl in *. rewrite app_nil_r in *.
        rewrite Heq in *. simpl_Foralls. congruence.
      + take (LC.wc_exp _ _ e0 -> _) and apply it in EQ1 as (?& Heq &?); auto.
        unfold L.clocksof in *. simpl in *. rewrite app_nil_r in *.
        rewrite Heq in *. simpl_Foralls. congruence.
    - cases. monadInv Hto.
      simpl_Foralls.
      simpl. unfold L.clock_of_nclock, stripname. simpl. esplit; split; eauto.
      inv Hwc. simpl_Foralls. constructor; simpl; auto.
      + eapply wc_lexp in EQ as (?& Heq &?); eauto. congruence.
      + take (_ -> _) and apply it in EQ1 as (?& Heq &?); auto.
        unfold L.clocksof in *. simpl in *. rewrite app_nil_r in *.
        rewrite Heq in *. simpl_Foralls. congruence.
      + take (LC.wc_exp _ _ e1 -> _) and apply it in EQ0 as (?& Heq &?); auto.
        unfold L.clocksof in *. simpl in *. rewrite app_nil_r in *.
        rewrite Heq in *. simpl_Foralls. congruence.
  Qed.

  (* correctness of substition extension *)
  Lemma instck_sub_ext :
    forall bck sub ck ck' P,
      instck bck sub ck = Some ck' ->
      instck bck (fun x => match sub x with
                        | None => P x
                        | s => s
                        end) ck = Some ck'.
  Proof.
    intros * Hinst.
    revert dependent ck'. induction ck; intros; auto.
    inv Hinst.
    destruct (instck bck sub ck) eqn:?; try discriminate.
    destruct (sub i) eqn:Hs; try discriminate.
    specialize (IHck c eq_refl).
    simpl. now rewrite IHck, Hs.
  Qed.

  Lemma wc_equation :
    forall G Hprefs P env envo vars e e',
      to_global G Hprefs = OK P ->
      to_equation env envo e = OK e' ->
      envs_eq env vars ->
      LC.wc_global G ->
      LC.wc_equation G vars e ->
      NLC.wc_equation P vars e'.
  Proof.
    intros ?????? [xs [|? []]] e' Hg Htr Henvs Hwcg (Hwc & Hlift & Hf2);
      try (inv Htr; cases; discriminate).
    destruct e; simpl in *; simpl_Foralls; try monadInv Htr.
    - constructor; eauto using envs_eq_in.
      eapply envs_eq_find in Henvs; eauto.
      pose proof (find_clock_det _ _ _ _ EQ Henvs) as ->.
      repeat constructor.
    - constructor; eauto using envs_eq_in.
      monadInv EQ1. destruct a. inv EQ0.
      unfold L.clock_of_nclock, stripname in *; simpl in *.
      take (LC.wc_exp _ _ _) and inv it; simpl in *; subst.
      + eapply envs_eq_find with (x:=i) in Henvs; eauto.
        rewrite EQ in Henvs; inv Henvs.
        now repeat constructor.
      + eapply envs_eq_find with (x:=x) in Henvs; eauto.
        rewrite EQ in Henvs; inv Henvs.
        now repeat constructor.
    - constructor; eauto using envs_eq_in. destruct a.
      monadInv EQ1. monadInv EQ0.
      take (LC.wc_exp _ _ _) and inv it.
      eapply wc_lexp in EQ1 as (?&?&?); eauto.
      unfold L.clock_of_nclock, stripname in *. simpl in *.
      eapply envs_eq_find in Henvs; eauto.
      pose proof (find_clock_det _ _ _ _ EQ Henvs) as ->.
      repeat constructor.
      congruence.
    - constructor; eauto using envs_eq_in. destruct a.
      monadInv EQ1. monadInv EQ0.
      take (LC.wc_exp _ _ _) and inv it.
      eapply wc_lexp in EQ0 as (?&?&?); eauto.
      eapply wc_lexp in EQ1 as (?&?&?); eauto.
      unfold L.clock_of_nclock, stripname in *. simpl in *.
      eapply envs_eq_find in Henvs; eauto.
      pose proof (find_clock_det _ _ _ _ EQ Henvs) as ->.
      repeat constructor; congruence.
    - destruct (vars_of l1) eqn:Vars. eapply vars_of_spec in Vars.
      1,2:cases; try monadInv Htr.
      constructor; eauto using envs_eq_in.
      + take (LC.wc_exp _ _ _) and inv it. simpl_Foralls.
        eapply wc_lexp in EQ2 as (?& Heq &?); eauto.
        take (Forall2 eq _ _) and rewrite Forall2_eq in it.
        unfold L.clocksof in it. simpl in *. rewrite app_nil_r in *.
        rewrite Heq in it. rewrite it in *.
        eapply envs_eq_find in Henvs; eauto.
        pose proof (find_clock_det _ _ _ _ EQ0 Henvs) as ->.
        congruence.
      + eapply Forall2_ignore1 in Vars.
        eapply Forall_impl; [|eauto]. intros (?&?) (?&?&?&?&?); subst.
        inv H1. eapply Forall_forall in H7; eauto. inv H7; auto.
    - cases; try monadInv Htr; monadInv EQ1; monadInv EQ0.
    - cases; try monadInv Htr; monadInv EQ1; monadInv EQ0.
      constructor; eauto using envs_eq_in. constructor.
      take (LC.wc_exp _ _ _) and inv it. simpl_Foralls.
      eapply wc_lexp in EQ1 as (?& Heq &?); eauto.
      unfold L.clock_of_nclock, stripname in *. simpl in *.
      eapply envs_eq_find in Henvs; eauto.
      pose proof (find_clock_det _ _ _ _ EQ Henvs) as ->.
      constructor; auto.
      rewrite app_nil_r in *.
      take (Forall (eq _) _) and rewrite Heq in it. now inv it.
    - cases; try monadInv Htr; monadInv EQ1.
      constructor; eauto using envs_eq_in.
      take (LC.wc_exp _ _ _) and inv it. simpl_Foralls.
      unfold L.clock_of_nclock, stripname in *. simpl in *. rewrite app_nil_r in *.
      eapply envs_eq_find in Henvs; eauto.
      pose proof (find_clock_det _ _ _ _ EQ Henvs) as ->.
      constructor; auto.
      + eapply wc_cexp in EQ0 as (?& Heq &?); eauto.
        rewrite Heq in *. now simpl_Foralls.
      + eapply wc_cexp in EQ1 as (?& Heq &?); eauto.
        rewrite Heq in *. now simpl_Foralls.
    - cases; try monadInv Htr; monadInv EQ1.
      constructor; eauto using envs_eq_in.
      take (LC.wc_exp _ _ _) and inv it. simpl_Foralls.
      unfold L.clock_of_nclock, stripname in *. simpl in *. rewrite app_nil_r in *.
      eapply envs_eq_find in Henvs; eauto.
      pose proof (find_clock_det _ _ _ _ EQ Henvs) as ->.
      constructor; auto.
      + eapply wc_lexp in EQ0 as (?& Heq &?); eauto. congruence.
      + eapply wc_cexp in EQ1 as (?& Heq &?); eauto.
        rewrite Heq in *. now simpl_Foralls.
      + eapply wc_cexp in EQ2 as (?& Heq &?); eauto.
        rewrite Heq in *. now simpl_Foralls.
    - destruct (vars_of l0) eqn:Vars; monadInv EQ0. eapply vars_of_spec in Vars.
      take (LC.wc_exp _ _ _) and inversion_clear it
        as [| | | | | | | | | |????? bck sub Wce Wcer ? WIi WIo].
      eapply find_node_global in Hg as (n' & Hpref & Hfind & Hton); eauto;
        assert (find_base_clock (L.clocksof l) = bck) as ->
          by (take (L.find_node _ _ = Some n) and
                   pose proof (LC.wc_find_node _ _ n Hwcg it) as (?& (Wcin &?));
              apply find_base_clock_bck;
              [rewrite L.clocksof_nclocksof; eapply LC.WellInstantiated_bck; eauto;
               unfold idck; rewrite map_length; exact (L.n_ingt0 n)
              | apply LC.WellInstantiated_parent in WIi;
                rewrite L.clocksof_nclocksof, Forall_map;
                eapply Forall_impl; eauto; now simpl]).
      econstructor; eauto; try discriminate;
        rewrite app_nil_r in *.
      (* We can't use [sub] directly because some variables
           in the left side of the equation may have no image bu [sub].
           -> see LClocking.wc_equation *)
      + instantiate (1 := fun x => match sub x with
                                | None => assoc_ident x (combine (L.idents (L.n_out n)) xs)
                                | s => s
                                end).
        (* inputs *)
        erewrite <- (to_node_in n n'); eauto.
        apply mmap_inversion in EQ.
        pose proof (L.n_nodup n) as Hdup.
        remember (L.n_in n) as ins. clear Heqins.
        revert dependent ins.
        revert dependent x.
        induction l as [| e].
        { intros. inv EQ. simpl in WIi. inv WIi.
          take ([] = _) and apply symmetry, map_eq_nil in it.
          now subst. }
        intros le Htr ins WIi.
        inv Htr. simpl in WIi.
        take (Forall _ (e::_)) and inv it.
        take (to_lexp e = _) and pose proof it as Tolexp; eapply wc_lexp in it as (ck & Hck & Wce);
          eauto.
        rewrite L.clockof_nclockof in Hck.
        destruct (L.nclockof e) as [|nc []] eqn:Hcke; simpl in *; inv Hck.
        inversion WIi as [|???? Wi ? Hmap]. subst.
        unfold idck in Hmap.
        apply symmetry, map_cons'' in Hmap as ((?&(?&?))&?&?&?&?). subst.
        unfold LC.WellInstantiated in Wi. destruct Wi; simpl in *.
        constructor; eauto.
        2:{ eapply IHl; eauto. now apply nodupmembers_cons in Hdup. }
        split; simpl; eauto.
        2:{ exists (stripname nc). split. apply Wce. auto using instck_sub_ext. }
        simpl in *. take (sub _ = _) and rewrite it. destruct nc as (ck & []).
        2:{ simpl.
            rewrite assoc_ident_false. constructor.
            apply nodupmembers_cons in Hdup as [Hin].
            rewrite <- In_InMembers_combine. unfold L.idents. intro Hin'.
            apply in_map_iff in Hin' as ((?&?)&?&?). simpl in *. subst.
            eapply Hin, In_InMembers.
            repeat rewrite in_app_iff. right; right; left; eauto.
            apply Forall2_length in Hf2. apply Forall2_length in WIo.
            unfold L.idents, idck in *. repeat rewrite map_length in *.
            congruence.
        }
        simpl. destruct e; take (LC.wc_exp G vars _) and inv it;
                 inv Hcke; inv Tolexp.
        * constructor.
        * destruct tys; take (map _ _ = [_]) and inv it.
      + (* outputs *)
        unfold idck in *.
        erewrite <- (to_node_out n n'); eauto.
        clear - Hlift Hf2 WIo.
        apply Forall2_forall. split.
        2:{ apply Forall2_length in Hlift. apply Forall2_length in WIo.
            repeat rewrite map_length in *. congruence. }
        intros (?&(?&?)) ? Hin. split.
        * destruct (sub i) eqn:Hsub.
          apply Forall2_swap_args in Hlift.
          pose proof (Forall2_trans_ex _ _ _ _ _ WIo Hlift) as Ho.
          rewrite Forall2_map_1 in Ho.
          eapply Forall2_In in Hin; eauto.
          destruct Hin as (?&?&(Heq&?)&Hl). simpl in *.
          rewrite Hsub in Heq. rewrite <- Heq in Hl. simpl in Hl.
          now subst.
          unfold L.idents. apply assoc_ident_true.
          2:{ rewrite combine_map_fst, in_map_iff.
              esplit; split; eauto. now simpl. }
          apply NoDup_NoDupMembers_combine.
          pose proof (L.n_nodup n) as Hdup.
          rewrite fst_NoDupMembers in Hdup. repeat rewrite map_app in Hdup.
          eauto using NoDup_app_l, NoDup_app_r.
        * rewrite Forall2_map_2 in Hf2. rewrite Forall2_map_2 in WIo.
          apply Forall2_swap_args in Hf2.
          pose proof (Forall2_trans_ex _ _ _ _ _ WIo Hf2) as Ho.
          rewrite Forall2_map_1 in Ho.
          eapply Forall2_In in Hin; eauto.
          destruct Hin as (?&?&(Heq&?)&Hl). simpl in *.
          esplit; split; eauto.
          eauto using instck_sub_ext.
      + eapply Forall2_ignore1 in Vars.
        eapply Forall_impl; [|eauto]. intros (?&?) (?&?&?&?&?); subst.
        eapply Forall_forall in Wcer; eauto. inv Wcer; auto.
  Qed.

  Lemma wc_node :
    forall G P n n' Hpref Hprefs,
      to_node n Hpref = OK n' ->
      to_global G Hprefs = OK P ->
      LC.wc_global G ->
      LC.wc_node G n ->
      NLC.wc_node P n'.
  Proof.
    intros * Htn Hwcg Htg Hwc.
    unfold NLC.wc_node.
    erewrite <- (to_node_in n n'), <- (to_node_out n n'), <- (to_node_vars n n');
      eauto.
    inversion Hwc as (?&?&?& WCeq). repeat (split; try tauto).
    now setoid_rewrite  Permutation_app_comm at 2.
    unfold to_node in Htn. cases. inv Htn. simpl.
    revert dependent x. induction (L.n_eqs n) as [| e]; intros * Hmmap.
    now inv Hmmap. inv WCeq.
    apply mmap_cons in Hmmap as (e' & es & -> & Htoeq & Hmmap).
    constructor; eauto using wc_equation, envs_eq_node.
  Qed.

  Lemma wc_transcription :
    forall G P Hprefs,
      LC.wc_global G ->
      to_global G Hprefs = OK P ->
      NLC.wc_global P.
  Proof.
    induction G as [| n]. inversion 2. constructor.
    intros * Hwt Htr. monadInv Htr.
    inversion_clear Hwt as [|???? Hf ].
    constructor; eauto using wc_node.
  Qed.

End TRCLOCKING.

Module TrClockingFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX  Op)
       (L     : LSYNTAX    Ids Op)
       (LC    : LCLOCKING  Ids Op L)
       (CE    : CESYNTAX       Op)
       (NL    : NLSYNTAX   Ids Op CE)
       (Ord   : NLORDERED  Ids Op CE NL)
       (Mem   : MEMORIES   Ids Op CE NL)
       (IsD   : ISDEFINED  Ids Op CE NL Mem)
       (CEClo : CECLOCKING Ids Op CE)
       (NLC   : NLCLOCKING Ids Op CE NL Ord Mem IsD CEClo)
       (TR    : TR Ids Op OpAux L CE NL)
<: TRCLOCKING Ids Op OpAux L LC CE NL Ord Mem IsD CEClo NLC TR.
  Include TRCLOCKING Ids Op OpAux L LC CE NL Ord Mem IsD CEClo NLC TR.
End TrClockingFun.
