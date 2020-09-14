From Coq Require Import Streams.
From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Omega.

From Coq Require Import Sorting.Permutation.
From Coq Require Import Setoid.
From Coq Require Import Morphisms.

From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import CommonList.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Import CoindIndexed.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax Lustre.LTyping Lustre.LClocking Lustre.LCausality Lustre.LOrdered Lustre.LSemantics.

Local Set Warnings "-masking-absolute-name".
Module Type LCLOCKSEMANTICS
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Syn : LSYNTAX Ids Op)
       (Import Typ : LTYPING Ids Op Syn)
       (Import Clo : LCLOCKING Ids Op Syn)
       (LCA        : LCAUSALITY Ids Op Syn)
       (Import Lord : LORDERED Ids Op Syn)
       (Import CStr : COINDSTREAMS Op OpAux)
       (Import IStr : INDEXEDSTREAMS Op OpAux)
       (Import Sem : LSEMANTICS Ids Op OpAux Syn Lord CStr).

  Import CStr.
  Module Import CIStr := CoindIndexedFun Op OpAux CStr IStr.

  Fact history_nth_add : forall H n id vs,
      Env.Equal (history_nth n (Env.add id vs H)) (Env.add id (vs # n) (history_nth n H)).
  Proof.
    intros H n id vs id'.
    destruct Env.find eqn:Hfind; symmetry.
    - eapply history_nth_find_Some' in Hfind as [vs' [? Hfind]]; subst.
      destruct (ident_eqb id id') eqn:Heq.
      + rewrite ident_eqb_eq in Heq; subst.
        rewrite Env.gss in *.
        inv H0. auto.
      + rewrite ident_eqb_neq in Heq.
        rewrite Env.gso in *; auto.
        eapply history_nth_find_Some in H0; eauto.
    - eapply history_nth_find_None' in Hfind.
      destruct (ident_eqb id id') eqn:Heq.
      + rewrite ident_eqb_eq in Heq; subst.
        rewrite Env.gss in *. inv Hfind.
      + rewrite ident_eqb_neq in Heq.
        rewrite Env.gso in *; auto.
        eapply history_nth_find_None; auto.
  Qed.

  Lemma sem_clock_refines : forall H H' ck bs bs',
      Env.refines eq H H' ->
      sem_clock H bs ck bs' ->
      sem_clock H' bs ck bs'.
  Proof.
    cofix CoFix; destruct ck; intros * Href Hsem.
    - inv Hsem; constructor; auto.
    - inv Hsem.
      + econstructor; eauto.
        * eapply sem_var_refines; eauto.
        * eapply CoFix; [|eauto]. eapply history_tl_refines; eauto.
      + econstructor; eauto.
        * eapply sem_var_refines; eauto.
        * eapply CoFix; [|eauto]. eapply history_tl_refines; eauto.
      + eapply Son_abs2; eauto.
        * eapply sem_var_refines; eauto.
        * eapply CoFix; [|eauto]. eapply history_tl_refines; eauto.
  Qed.

  Lemma history_tl_same_find : forall H H' vars,
      Forall (fun x => orel (EqSt (A:=value)) (Env.find x H) (Env.find x H')) vars ->
      Forall (fun x => orel (EqSt (A:=value)) (Env.find x (history_tl H)) (Env.find x (history_tl H'))) vars.
  Proof.
    intros * Hsem.
    eapply Forall_impl; [|eauto]. intros; simpl in *.
    destruct (Env.find a H) eqn:Hfind; inv H0.
    - symmetry in H2.
      apply history_tl_find_Some in Hfind. apply history_tl_find_Some in H2.
      rewrite Hfind, H2. constructor. rewrite H3; reflexivity.
    - symmetry in H1.
      apply history_tl_find_None in Hfind. apply history_tl_find_None in H1.
      rewrite Hfind, H1. constructor.
  Qed.

  Lemma sem_var_same_find : forall H H' vars id vs,
      Forall (fun x => orel (EqSt (A:=value)) (Env.find x H') (Env.find x H)) vars ->
      In id vars ->
      sem_var H id vs ->
      sem_var H' id vs.
  Proof.
    intros * Hf Hin Hsem.
    eapply Forall_forall in Hf; eauto.
    inv Hsem.
    apply Env.find_1 in H1. rewrite H1 in Hf. inv Hf.
    econstructor. eapply Env.find_2; eauto.
    rewrite H2, H4; reflexivity.
  Qed.

  Lemma sem_clock_same_find : forall H H' vars ck bs bs',
      wc_clock vars ck ->
      Forall (fun x => orel (EqSt (A:=value)) (Env.find x H') (Env.find x H)) (map fst vars) ->
      sem_clock H bs ck bs' ->
      sem_clock H' bs ck bs'.
  Proof.
    cofix CoFix; destruct ck; intros * Hwc Hf Hsem.
    - inv Hsem; constructor; auto.
    - inv Hwc; inv Hsem.
      + econstructor; eauto.
        * eapply sem_var_same_find; eauto.
          apply in_map_iff. exists (i, ck); auto.
        * eapply CoFix; [| |eauto]. 1:constructor; eauto.
          apply history_tl_same_find; auto.
      + econstructor; eauto.
        * eapply sem_var_same_find; eauto.
          apply in_map_iff. exists (i, ck); auto.
        * eapply CoFix; [| |eauto]. 1:constructor; eauto.
          apply history_tl_same_find; auto.
      + eapply Son_abs2; eauto.
        * eapply sem_var_same_find; eauto.
          apply in_map_iff. exists (i, ck); auto.
        * eapply CoFix; [| |eauto]. 1:constructor; eauto.
          eapply history_tl_same_find; auto.
  Qed.

  (** ** Synchronization (alignement ?) *)

  (** fby keeps the synchronization *)

  Lemma ac_fby1 :
    forall xs ys rs,
      fby xs ys rs -> abstract_clock xs ≡ abstract_clock rs.
  Proof.
    cofix Cofix.
    intros * Hfby.
    unfold_Stv xs; inv Hfby; econstructor; simpl; eauto.
    clear - H3. revert H3. revert y xs ys0 rs0.
    cofix Cofix.
    intros * Hfby1.
    unfold_Stv xs; inv Hfby1; econstructor; simpl; eauto.
  Qed.

  Lemma ac_fby2 :
    forall xs ys rs,
      fby xs ys rs -> abstract_clock ys ≡ abstract_clock rs.
  Proof.
    cofix Cofix. intros * Hfby.
    unfold_Stv ys; inv Hfby; econstructor; simpl; eauto.
    clear - H3. revert H3. revert v ys xs0 rs0.
    cofix Cofix. intros * Hfby1.
    unfold_Stv ys; inv Hfby1; econstructor; simpl; eauto.
  Qed.

  Lemma fby_aligned : forall bs xs ys zs,
      fby xs ys zs ->
      (aligned xs bs \/ aligned ys bs \/ aligned zs bs) ->
      (aligned xs bs /\ aligned ys bs /\ aligned zs bs).
  Proof with eauto.
    intros bs xs ys zs Hfby.
    specialize (ac_fby1 _ _ _ Hfby) as Hac1. specialize (ac_fby2 _ _ _ Hfby) as Hac2.
    specialize (ac_aligned xs) as Hs1. specialize (ac_aligned ys) as Hs2. specialize (ac_aligned zs) as Hs3.
    intros [Hsync|[Hsync|Hsync]]; repeat split; auto.
    - eapply aligned_EqSt in Hs1; eauto. rewrite Hs1, Hac1, <- Hac2; auto.
    - eapply aligned_EqSt in Hs1; eauto. rewrite Hs1, Hac1; auto.
    - eapply aligned_EqSt in Hs2; eauto. rewrite Hs2, Hac2, <- Hac1; auto.
    - eapply aligned_EqSt in Hs2; eauto. rewrite Hs2, Hac2; auto.
    - eapply aligned_EqSt in Hs3; eauto. rewrite Hs3, <- Hac1; auto.
    - eapply aligned_EqSt in Hs3; eauto. rewrite Hs3, <- Hac2; auto.
  Qed.

  (** ** Alignment proof extracted from Transcription/Correctness.v *)

  Lemma length_typeof :
    forall G H b env e os,
      wt_exp G env e ->
      sem_exp G H b e os ->
      length (typeof e) = length os.
  Proof.
    intros * Hwt Hsem.
    eapply sem_exp_numstreams in Hsem; eauto.
    rewrite length_typeof_numstreams; auto.
  Qed.

  Lemma length_clockof :
    forall G H b env e os,
      wc_exp G env e ->
      sem_exp G H b e os ->
      length (clockof e) = length os.
  Proof.
    intros * Hwc Hsem.
    eapply sem_exp_numstreams in Hsem; eauto.
    rewrite length_clockof_numstreams; auto.
  Qed.

  Lemma free_left_env :
    forall G x env eq,
      wc_equation G env eq ->
      Exists (fun e : exp => LCA.Is_free_left x e) (snd eq) ->
      InMembers x env.
  Proof.
    intros ??? [xs es] (Hwc & _ & _) Hfr.
    induction es as [| e]. inv Hfr. simpl in *.
    inversion_clear Hwc as [|?? HWc].
    inversion_clear Hfr as [?? Hf | ]; auto.
    clear - Hf HWc.
    induction e using exp_ind2; inv Hf; inv HWc; eauto using In_InMembers.
    - tauto.
    - take (Exists _ _) and apply Exists_exists in it as (?& Hin &?).
      eapply Forall_forall in H; eauto. apply H; auto.
      eapply Forall_forall in Hin; eauto.
    - intuition; subst; eauto using In_InMembers.
      take (Exists _ _) and apply Exists_exists in it as (?& Hin &?).
      eapply Forall_forall in H; eauto. apply H; auto.
      eapply Forall_forall in Hin; eauto.
    - intuition; subst; eauto using In_InMembers.
      take (Exists _ _) and apply Exists_exists in it as (?& Hin &?).
      eapply Forall_forall in H; eauto. apply H; auto.
      eapply Forall_forall in Hin; eauto.
      take (Exists _ _) and apply Exists_exists in it as (?& Hin &?).
      eapply Forall_forall in H0; eauto. apply H0; auto.
      eapply Forall_forall in Hin; eauto.
    - intuition; subst; eauto using In_InMembers.
      take (Exists _ _) and apply Exists_exists in it as (?& Hin &?).
      eapply Forall_forall in H; eauto. apply H; auto.
      eapply Forall_forall in Hin; eauto.
      take (Exists _ _) and apply Exists_exists in it as (?& Hin &?).
      eapply Forall_forall in H0; eauto. apply H0; auto.
      eapply Forall_forall in Hin; eauto.
    - take (Exists _ _) and apply Exists_exists in it as (?& Hin &?).
      eapply Forall_forall in H0; eauto. apply H0; auto.
      eapply Forall_forall in Hin; eauto.
    - take (Exists _ _) and apply Exists_exists in it as (?& Hin &?).
      destruct Hin as [| Hin]. subst. auto.
      eapply Forall_forall in H0; eauto. apply H0; auto.
      eapply Forall_forall in Hin; eauto.
  Qed.

  Definition sc_var_inv (D : positive -> Prop) (env : list (ident * clock))
                     (H : history) (b : Stream bool) : Prop :=
    forall x, D x ->
         (forall ck xs,
             In (x, ck) env ->
             sem_var H x xs ->
             sem_clock H b ck (abstract_clock xs)).

  Lemma sc_var_inv_weaken:
    forall (D1 D2 : positive -> Prop) (env : list (ident * clock))
      (H : history) (b : Stream bool),
      sc_var_inv D1 env H b  ->
      (forall x, D2 x -> D1 x) ->
      sc_var_inv D2 env H b.
  Proof.
    intros D1 D2 env H b I1 H12 x D2x.
    now apply H12, I1 in D2x.
  Qed.

  Lemma sc_when :
    forall H x b k ck xs ys rs,
      sem_var H x xs ->
      sem_clock H b ck (abstract_clock ys) ->
      when k ys xs rs ->
      sem_clock H b (Con ck x k) (abstract_clock rs).
  Proof.
    cofix Cofix. intros * Hsemv Hsemc Hwhen.
    unfold_Stv rs; inv Hwhen; rewrite unfold_Stream; simpl;
      rewrite unfold_Stream in Hsemc; simpl in Hsemc.
    - econstructor; eauto.
      apply sem_var_step in Hsemv. apply sc_step in Hsemc.
      eapply Cofix; eauto; reflexivity.
    - assert (k = negb (negb k)) as Hk by apply Bool.negb_involutive_reverse.
      rewrite Hk. eapply Son_abs2 with (c:=c); eauto.
      rewrite <- Hk.
      apply sem_var_step in Hsemv. apply sc_step in Hsemc.
      eapply Cofix; eauto; reflexivity.
    - econstructor; eauto.
      apply sem_var_step in Hsemv. apply sc_step in Hsemc.
      eapply Cofix; eauto; reflexivity.
  Qed.

  Lemma sc_merge :
    forall H b ck x xs ts fs ss,
      sem_var H x xs ->
      sem_clock H b (Con ck x true) (abstract_clock ts) ->
      sem_clock H b (Con ck x false)(abstract_clock fs) ->
      merge xs ts fs ss ->
      sem_clock H b ck (abstract_clock ss).
  Proof.
    destruct ck; intros ???????? Hmerge.
    - econstructor. revert dependent H. revert Hmerge. revert b x xs ts fs ss.
      cofix Cofix; intros * Hmerge H Hsemv Hsct Hscf.
      unfold_Stv ss; inv Hmerge; rewrite unfold_Stream;
        rewrite unfold_Stream in Hsct, Hscf; simpl in *.
      + inv Hscf; try discriminate_var.
        inv H8. apply sem_var_step in Hsemv.
        apply sc_step in Hsct. eapply Cofix in Hsemv; eauto. inv H1.
        econstructor; simpl in *; auto.
      + inv Hsct; [| rewrite Bool.negb_true_iff in H3; subst; now simpl in H5].
        apply sem_var_step in Hsemv. apply sc_step in Hscf.
        eapply Cofix in Hsemv; eauto.
        inv H8. inv H1. econstructor; simpl in *; auto.
      + inv Hscf; [| now rewrite H3 in H5].
        inv H8. apply sem_var_step in Hsemv.
        apply sc_step in Hsct. eapply Cofix in Hsemv; eauto. inv H1.
        econstructor; simpl in *; auto.
    - revert dependent H. revert Hmerge. revert b ck i b0 x xs ts fs ss.
      cofix Cofix; intros * Hmerge H Hsemv Hsct Hscf.
      unfold_Stv ss; inv Hmerge; rewrite unfold_Stream;
        rewrite unfold_Stream in Hsct, Hscf; simpl in *.
      + inv Hscf; inv H8; try discriminate_var;
          apply sem_var_step in Hsemv;
          apply sc_step in Hsct; now econstructor; eauto.
      + inv Hsct; [| rewrite Bool.negb_true_iff in H3; subst; now simpl in H5].
        inv H8. econstructor; eauto.
        apply sem_var_step in Hsemv. apply sc_step in Hscf.
        eapply Cofix; eauto.
      + inv Hscf; [| now rewrite H3 in H5 ].
        inv H8. econstructor; eauto.
        apply sem_var_step in Hsemv. apply sc_step in Hsct.
        eapply Cofix; eauto.
  Qed.

  Lemma sc_switch_env:
    forall b H H' ck v,
      (forall x, Is_free_in_clock x ck ->
            orel (@EqSt value) (Env.find x H) (Env.find x H')) ->
      sem_clock H b ck v <-> sem_clock H' b ck v.
  Proof.
    intros * Hf. revert Hf. revert b H H' v.
    induction ck.
    - (* Cbase *)
      split; inversion_clear 1; eauto using sem_clock.
    - (* Con *)
      split; revert Hf; revert b v H H' b0; cofix Cofix; intros * Hf Hsem;
        inversion_clear Hsem.
      + econstructor; eauto. apply (IHck b0 H H'); eauto.
        intros. apply Hf. now econstructor.
        rewrite <- sem_var_switch_env; eauto. apply Hf. econstructor.
        eauto. eapply Cofix; [| eassumption]. intros. apply env_find_tl.
        eapply Hf. inv H0; now econstructor.
      + econstructor; eauto. apply (IHck b0 H H'); eauto.
        intros. apply Hf. now econstructor.
        rewrite <- sem_var_switch_env; eauto. apply Hf. econstructor.
        eauto. eapply Cofix; [| eassumption]. intros. apply env_find_tl.
        eapply Hf. inv H0; now econstructor.
      +  eapply Son_abs2; eauto. apply (IHck b0 H H'); eauto.
        intros. apply Hf. now econstructor.
        rewrite <- sem_var_switch_env; eauto. apply Hf. econstructor.
        eauto. eapply Cofix; [| eassumption]. intros. apply env_find_tl.
        eapply Hf. inv H0; now econstructor.
      + econstructor; eauto. apply (IHck b0 H H') in H1; eauto.
        intros. apply Hf. now econstructor.
        eapply sem_var_switch_env; try apply Hf. econstructor.
        eauto. eapply Cofix; [| eassumption]. intros. apply env_find_tl.
        eauto.
      + econstructor; eauto. apply (IHck b0 H H') in H1; eauto.
        intros. apply Hf. now econstructor.
        eapply sem_var_switch_env; try apply Hf. econstructor.
        eauto. eapply Cofix; [| eassumption]. intros. apply env_find_tl.
        eauto.
      + eapply Son_abs2; eauto. apply (IHck b0 H H') in H1; eauto.
        intros. apply Hf. now econstructor.
        eapply sem_var_switch_env; try apply Hf. econstructor.
        eauto. eapply Cofix; [| eassumption]. intros. apply env_find_tl.
        eapply Hf. inv H0; now econstructor.
  Qed.

  Hint Resolve Env.find_1 Env.find_2.

  Lemma sc_inst:
    forall H H' b b' ck ck' bck sub cks,
      instck bck sub ck = Some ck' ->
      sem_clock H b ck cks ->
      sem_clock H' b' bck b ->
      (forall x x',
          Is_free_in_clock x ck ->
          sub x = Some x' ->
          orel (@EqSt value) (Env.find x H) (Env.find x' H')) ->
      sem_clock H' b' ck' cks.
  Proof.
    intros * Hinst Hck Hbck Henv.
    rewrite sem_clock_equiv in *.
    intros n. specialize (Hck n). specialize (Hbck n).
    assert (forall x x' n, Is_free_in_clock x ck -> sub x = Some x' -> orel (eq (A:=value)) (Env.find x (CIStr.tr_history H n)) (Env.find x' (CIStr.tr_history H' n))) as Henv'.
    { intros * Hfree Hsub. specialize (Henv x x' Hfree Hsub).
    eapply tr_history_find_orel in Henv; eauto. } clear Henv.
    unfold tr_Stream in *.
    revert H H' b b' ck' bck cks sub Hinst Hck Hbck Henv'.
    induction ck; intros.
    - inv Hinst. inv Hck; auto.
    - inversion Hinst as [Hcase]. cases_eqn Hcase. inv Hcase.
      inv Hck.
      1,2:econstructor;eauto. 5:eapply IStr.Son_abs2; eauto.
      2,4,6:(unfold sem_var_instant in *;
             specialize (Henv' i i0 n (FreeCon1 _ _ _) Hcase1); rewrite H5 in Henv';
             inv Henv'; auto).
      * rewrite H3 in *; eapply IHck in Hcase0; eauto.
        intros. eapply Henv'; auto. right; auto.
      * rewrite H4 in *; eapply IHck in Hcase0; eauto.
        intros. eapply Henv'; auto. right; auto.
      * eapply IHck with (cks:=Streams.const true) in Hcase0; eauto.
        rewrite const_nth in Hcase0; auto. rewrite const_nth; eauto.
        intros; eapply Henv'; auto; right; auto.
  Qed.

  Lemma sc_inst':
      forall H' H b b' ck ck' bck sub cks,
      instck bck sub ck = Some ck' ->
      sem_clock H' b' ck' cks ->
      sem_clock H' b' bck b ->
      (forall x x',
          Is_free_in_clock x ck ->
          sub x = Some x' ->
          orel (@EqSt value) (Env.find x H) (Env.find x' H')) ->
      sem_clock H b ck cks.
  Proof.
    intros * Hinst Hck Hbck Henv.
    revert dependent H. revert Hinst Hck Hbck. revert H' b b' ck' bck cks sub.
    induction ck; intros.
    - inv Hinst. constructor. eauto using sem_clock_det.
    - revert dependent H'. revert dependent cks.
      revert Hinst. revert b' i b0 ck' b H. cofix Cofix; intros.
      inversion Hinst as [Hcase]. cases_eqn Hcase. inv Hcase.
      unfold_Stv cks; assert (Hck' := Hck); inv Hck.
      + econstructor; eauto. eapply IHck in Hcase0; eauto.
        intros. eapply Henv; eauto. now constructor.
        specialize (Henv i i0 (FreeCon1 i ck b) Hcase1).
        inversion_clear H8 as [???? Hf]. rewrite Hf in Henv. inv Henv.
        rewrite <- H3 in H1. econstructor; eauto. destruct b0.
        eapply Cofix; eauto using sc_step. intros * Hfree ?.
        apply Henv with (x':= x') in Hfree; auto. now apply env_find_tl.
      + econstructor; eauto. eapply IHck in Hcase0; eauto.
        intros. eapply Henv; eauto. now constructor.
        specialize (Henv i i0 (FreeCon1 i ck b) Hcase1).
        inversion_clear H8 as [???? Hf]. rewrite Hf in Henv. inv Henv.
        rewrite <- H3 in H1. econstructor; eauto. destruct b0.
        eapply Cofix; eauto using sc_step. intros * Hfree ?.
        apply Henv with (x':= x') in Hfree; auto. now apply env_find_tl.
      + eapply Son_abs2; eauto. eapply IHck in Hcase0; eauto.
        intros. eapply Henv; eauto. now constructor.
        specialize (Henv i i0 (FreeCon1 i ck (negb k)) Hcase1).
        inversion_clear H8 as [???? Hf]. rewrite Hf in Henv. inv Henv.
        rewrite <- H3 in H1. econstructor; eauto. destruct b0.
        eapply Cofix; eauto using sc_step. intros * Hfree ?.
        apply Henv with (x':= x') in Hfree; auto. now apply env_find_tl.
  Qed.

  Lemma sc_parent :
    forall H b ck lck ss,
      Forall2 (sem_clock H b) lck (map abstract_clock ss) ->
      In ck lck ->
      Forall (fun ck' => ck' = ck \/ clock_parent ck ck') lck ->
      sem_clock H b ck (clocks_of ss).
  Proof.
    intros * Hsc Hin Hparent.
    pose proof (Forall2_in_left _ _ _ _ Hsc Hin) as [s (Hins & Hsc0)].
    rewrite Forall2_map_2 in Hsc. apply in_map_iff in Hins as [?(?&?)]. subst.
    assert (
        Forall (fun s' => sub_clock (abstract_clock x) (abstract_clock s')) ss
      ) as Hf. {
      apply Forall_forall; intros * Hx0.
      pose proof (Forall2_in_right _ _ _ _ Hsc Hx0) as [? (Hx1&Hsc1)].
      eapply Forall_forall in Hx1; eauto. destruct Hx1.
      subst.
      apply sem_clock_det with (2 := Hsc1) in Hsc0. now rewrite Hsc0.
      eapply sub_clock_parent; eauto.
    }
    apply sub_clock_sclocksof in Hf; auto. now rewrite Hf.
  Qed.


  Lemma wc_env_free_in_clock :
    forall x i ck vars,
      wc_env vars ->
      In (x, ck) vars ->
      Is_free_in_clock i ck ->
      exists ick, In (i, ick) vars.
  Proof.
    intros * WC Ix Hfree.
    revert x Ix. induction ck; inv Hfree;
    intros; eapply Forall_forall in WC; eauto; inv WC; eauto.
  Qed.

  Lemma idck_idents :
    forall l, idents l = map fst (idck l).
  Proof.
    unfold idents, idck. induction l; simpl; auto.
    f_equal. auto.
  Qed.

  Ltac inv_NoDup_fresh_ins H :=
    unfold anon_ins, fresh_ins in H; simpl in H;
    repeat rewrite idck_app.

  Lemma In_clockof :
    forall ck e es,
      In ck (clockof e) ->
      In e es ->
      In ck (clocksof es).
  Proof.
    intros. unfold clocksof.
    rewrite in_flat_map. eauto.
  Qed.

  Lemma In_nclockof :
    forall ck e es,
      In ck (nclockof e) ->
      In e es ->
      In ck (nclocksof es).
  Proof.
    intros. unfold nclocksof.
    rewrite in_flat_map. eauto.
  Qed.

  Fact InMembers_fresh_in : forall x e es,
      In e es ->
      InMembers x (fresh_in e) ->
      InMembers x (fresh_ins es).
  Proof.
    intros * Hin Hinm.
    eapply fresh_in_incl, incl_map with (f:=fst) in Hin.
    rewrite fst_InMembers in *. eauto.
  Qed.

  Fact InMembers_anon_in : forall x e es,
      In e es ->
      InMembers x (anon_in e) ->
      InMembers x (anon_ins es).
  Proof.
    intros * Hin Hinm.
    eapply anon_in_incl, incl_map with (f:=fst) in Hin.
    rewrite fst_InMembers in *. eauto.
  Qed.

  Fact InMembers_anon_in_eq : forall x e es,
      In e es ->
      InMembers x (anon_in_eq e) ->
      InMembers x (anon_in_eqs es).
  Proof.
    intros * Hin Hinm.
    eapply anon_in_eq_incl, incl_map with (f:=fst) in Hin.
    rewrite fst_InMembers in *. eauto.
  Qed.

  Fact Ino_In_anon_streams : forall x anns,
      Ino x (map (fun x => snd (snd x)) anns) ->
      InMembers x (Syn.anon_streams anns).
  Proof.
    intros x anns H.
    rewrite Ino_In, in_map_iff in H; destruct H as [[? [? ?]] [? ?]]; simpl in *; subst.
    rewrite fst_InMembers, in_map_iff.
    exists (x, (t, c)); split; auto.
    eapply map_filter_In; eauto.
  Qed.

  Lemma var_clock_defined:
    forall G vars e x,
      wc_exp G vars e ->
      wc_global G ->
      wc_env vars ->
      (Ino x (map snd (nclockof e))
       \/ Exists (Is_free_in_clock x) (clockof e)) ->
      InMembers x vars \/ InMembers x (fresh_in e).
  Proof.
    induction e using exp_ind2; intros * Hwc Hwcg Henv Hfree; simpl in Hfree.
    - inv Hwc. inversion_clear Hfree as [| Hfree']; try tauto.
      inversion_clear Hfree' as [?? Hf|?? Hf]; inv Hf.
    - inv Hwc.
      + inversion_clear Hfree as [[]| Hf]; intuition; simpl in *. subst.
        eauto using In_InMembers.
        unfold clock_of_nclock, stripname in Hf. simpl in Hf.
        eapply wc_env_free_in_clock in Henv as []; eauto using In_InMembers.
        now inv Hf.
      + inversion_clear Hfree as [[]| Hf]; intuition; simpl in *. subst.
        eauto using In_InMembers.
        unfold clock_of_nclock, stripname in Hf. simpl in Hf.
        eapply wc_env_free_in_clock in Henv as []; eauto using In_InMembers.
        now inv Hf.
    - (* Eunop *)
      inv Hwc. simpl in *. inversion_clear Hfree as [[|]|Hfree']; intuition.
      inversion_clear Hfree' as [?? Hf|?? Hf]; try now inv Hf.
      unfold clock_of_nclock, stripname in Hf. simpl in Hf.
      eapply IHe in Henv; eauto.
      right. rewrite H3. constructor; auto.
    - (* Ebinop *)
      inv Hwc. simpl in *. inversion_clear Hfree as [[|]|Hfree']; intuition.
      inversion_clear Hfree' as [?? Hf|?? Hf]; try now inv Hf.
      unfold clock_of_nclock, stripname in Hf. simpl in Hf.
      eapply IHe1 in Henv; eauto.
      2:{ take (clockof e1 = _) and rewrite it; eauto. }
      destruct Henv; auto. right. rewrite InMembers_app; auto.
    - (* Efby *)
      inv Hwc. take (Forall2 eq _ _) and apply Forall2_eq in it as Heq.
      rewrite Heq, Exists_exists in Hfree. destruct Hfree as [Hino|(?&Hin &?)].
      apply Ino_In in Hino. apply in_map_iff in Hino as ((?&?)&?&Hino).
      apply in_map_iff in Hino as ((?&?)&?&Hino).
      eapply Forall_forall in Hino; eauto. simpl in *. subst. inv Hino.
      unfold clocksof in Hin. apply in_flat_map in Hin as (?&?&?).
      eapply Forall_forall in H0; eauto.
      eapply H0 in Henv; auto; [|eapply Forall_forall|right; eapply Exists_exists];
        eauto.
      destruct Henv; auto. right.
      simpl. rewrite InMembers_app; right.
      eapply InMembers_fresh_in; eauto.
    - (* Ewhen *)
      inv Hwc. simpl in Hfree. destruct Hfree as [Hf|Hf].
      { clear - Hf. exfalso. induction tys; simpl in *; intuition. }
      rewrite CommonList.Exists_map in Hf. unfold clock_of_nclock, stripname in Hf.
      simpl in Hf. apply Exists_exists in Hf as (?&?&Hf).
      inv Hf; eauto using In_InMembers.
      destruct (clocksof es) eqn:Heql; simpl in *.
      take (length tys = 0) and apply length_zero_iff_nil in it. subst. contradiction.
      apply flat_map_ExistsIn in Heql as (?&?&?&Hckof).
      eapply Forall_forall in H; eauto. take (Forall (eq _) _) and inv it.
      eapply H in Henv; eauto. 2:{ eapply Forall_forall; eauto. }
      2:{ right. rewrite Hckof. eauto. } destruct Henv; auto. right.
      eapply InMembers_fresh_in; eauto.
    - (* Emerge *)
      inv Hwc. simpl in Hfree. destruct Hfree as [Hf|Hf].
      { clear - Hf. exfalso. induction tys; simpl in *; intuition. }
      rewrite CommonList.Exists_map in Hf. unfold clock_of_nclock, stripname in Hf.
      simpl in Hf. apply Exists_exists in Hf as (?&?&Hf).
      destruct (clocksof ets) eqn:Heql; simpl in *.
      take (length tys = 0) and apply length_zero_iff_nil in it. subst. contradiction.
      apply flat_map_ExistsIn in Heql as (?&?&?&Hckof).
      eapply Forall_forall in H; eauto. take (Forall (eq _) (_::_)) and inv it.
      eapply H with (x := x0) in Henv; eauto.
      2:{ eapply Forall_forall; [|eauto]. auto. }
      2:{ right. rewrite Hckof. left. now constructor. }
      destruct Henv; auto. right. rewrite InMembers_app; left.
      eapply InMembers_fresh_in; eauto.
    - (* Eite *)
      inv Hwc. simpl in Hfree. destruct Hfree as [Hf|Hf].
      { clear - Hf. exfalso. induction tys; simpl in *; intuition. }
      rewrite CommonList.Exists_map in Hf. unfold clock_of_nclock, stripname in Hf.
      simpl in Hf. apply Exists_exists in Hf as (?&?&Hf).
      eapply IHe in Henv; eauto.
      2:{ right. take (clockof e = _) and rewrite it. eauto. }
      destruct Henv; auto. right.
      simpl; rewrite InMembers_app; left; auto.
    - (* Eapp and Ereset *)
      inv Hwc; simpl.
      + destruct Hfree as [Hino| Hfree'].
        * right. rewrite InMembers_app; right.
          rewrite map_map in Hino.
          eapply Ino_In_anon_streams; eauto.
        * apply Exists_exists in Hfree' as (?&Hin&?).
          assert (Hwio := H8). assert (Hwcg' := Hwcg).
          apply in_map_iff in Hin as ((?&?)&?&?). rewrite Forall2_map_2 in Hwio.
          eapply Forall2_in_right in Hwio as ((?&ck)&?&(?&Hinst)); eauto.
          eapply wc_find_node in Hwcg as (?&(?& WCio&?)); eauto.
          unfold clock_of_nclock, stripname in *. simpl in *. subst.
          eapply instck_inv in Hinst as [Hbck|(?&Heq&?)]; eauto.
          -- (* la variable est dans bck, donc dans une entrée *)
            destruct (nclocksof es) as [|(?&?)] eqn:Heql.
            { inversion H7 as [Hlen|].
              apply (f_equal (@length (ident * clock))) in Hlen; simpl in Hlen.
              unfold idck in Hlen. rewrite map_length in Hlen.
              pose proof (n_ingt0 n). omega. }
            inversion_clear H7 as [|???? (?&?)].
            eapply instck_free_bck in Hbck; eauto.
            apply flat_map_ExistsIn in Heql as (?&?&?&Hnc).
            eapply Forall_forall in H0; eauto. eapply H0 in Hwcg'; eauto.
            2:{ eapply Forall_forall in H5; eauto. }
            2:{ rewrite clockof_nclockof. rewrite Hnc. simpl in *. eauto. }
            destruct Hwcg'; auto. right.
            rewrite InMembers_app; left.
            eapply InMembers_fresh_in; eauto.
          -- eapply wc_env_free_in_clock with (ck := ck) in WCio as (?&Hin); eauto.
             2:{ rewrite idck_app, in_app. eauto. }
             rewrite idck_app, in_app in Hin. destruct Hin as [Hini | Hino].
             (* Hini, Hypothèse d'induction *)
             eapply Forall2_in_left in H7 as (?&Hin&(Heq'&?)); eauto. simpl in *.
             eapply In_nclocksof in Hin as (?&?&?). eapply Forall_forall in H0; eauto.
             eapply H0 in Hwcg' as HH; eauto.
             2:{ eapply Forall_forall; eauto. }
             2:{ left. instantiate (1 := x).
                 rewrite Ino_In, <- Heq, Heq', in_map_iff; eauto. }
             ++ destruct HH; auto. right.
                rewrite InMembers_app; left.
                eapply InMembers_fresh_in; eauto.
             ++ (* Hino *)
               right. rewrite InMembers_app; right.
               eapply Forall2_in_left in H8 as (nc &?&(Heq'&?)); eauto.
               simpl in *. eapply Ino_In_anon_streams.
               rewrite Heq in Heq'.
               rewrite in_map_iff in H8; destruct H8 as [[? ?] [? ?]]; simpl in *; subst.
               rewrite Ino_In, in_map_iff. unfold stream_name.
               exists (t0, nc). split; auto.
      + destruct Hfree as [Hino| Hfree'].
        * right. repeat (rewrite InMembers_app; right).
          rewrite map_map in Hino.
          eapply Ino_In_anon_streams; eauto.
        * apply Exists_exists in Hfree' as (?&Hin&?).
          assert (Hwio := H8). assert (Hwcg' := Hwcg).
          apply in_map_iff in Hin as ((?&?)&?&?). rewrite Forall2_map_2 in Hwio.
          eapply Forall2_in_right in Hwio as ((?&ck)&?&(?&Hinst)); eauto.
          eapply wc_find_node in Hwcg as (?&(?& WCio&?)); eauto.
          unfold clock_of_nclock, stripname in *. simpl in *. subst.
          eapply instck_inv in Hinst as [Hbck|(?&Heq&?)]; eauto.
          -- (* la variable est dans bck, donc dans une entrée *)
            destruct (nclocksof es) as [|(?&?)] eqn:Heql.
            { inversion H7 as [Hlen|].
              apply (f_equal (@length (ident * clock))) in Hlen; simpl in Hlen.
              unfold idck in Hlen. rewrite map_length in Hlen.
              pose proof (n_ingt0 n). omega. }
            inversion_clear H7 as [|???? (?&?)].
            eapply instck_free_bck in Hbck; eauto.
            apply flat_map_ExistsIn in Heql as (?&?&?&Hnc).
            eapply Forall_forall in H0; eauto. eapply H0 in Hwcg'; eauto.
            2:{ eapply Forall_forall in H5; eauto. }
            2:{ rewrite clockof_nclockof. rewrite Hnc. simpl in *. eauto. }
            destruct Hwcg'; auto. right.
            rewrite InMembers_app; left.
            eapply InMembers_fresh_in; eauto.
          -- eapply wc_env_free_in_clock with (ck := ck) in WCio as (?&Hin); eauto.
             2:{ rewrite idck_app, in_app. eauto. }
             rewrite idck_app, in_app in Hin. destruct Hin as [Hini | Hino].
             (* Hini, Hypothèse d'induction *)
             eapply Forall2_in_left in H7 as (?&Hin&(Heq'&?)); eauto. simpl in *.
             eapply In_nclocksof in Hin as (?&?&?). eapply Forall_forall in H0; eauto.
             eapply H0 in Hwcg' as HH; eauto.
             2:{ eapply Forall_forall; eauto. }
             2:{ left. instantiate (1 := x).
                 rewrite Ino_In, <- Heq, Heq', in_map_iff; eauto. }
             ++ destruct HH; auto. right.
                rewrite InMembers_app; left.
                eapply InMembers_fresh_in; eauto.
             ++ (* Hino *)
               right. repeat (rewrite InMembers_app; right).
               eapply Forall2_in_left in H8 as (nc &?&(Heq'&?)); eauto.
               simpl in *. eapply Ino_In_anon_streams.
               rewrite Heq in Heq'.
               rewrite in_map_iff in H8; destruct H8 as [[? ?] [? ?]]; simpl in *; subst.
               rewrite Ino_In, in_map_iff. unfold stream_name.
               exists (t0, nc). split; auto.
  Qed.

  Corollary free_clock_defined :
    forall G vars e x,
      wc_exp G vars e ->
      wc_global G ->
      wc_env vars ->
      Exists (Is_free_in_clock x) (clockof e) ->
      InMembers x vars \/ InMembers x (fresh_in e).
  Proof.
    eauto using var_clock_defined.
  Qed.

  Corollary snd_nclocks_defined :
    forall G vars e x,
      wc_exp G vars e ->
      wc_global G ->
      wc_env vars ->
      Ino x (map snd (nclockof e)) ->
      InMembers x vars \/ InMembers x (fresh_in e).
  Proof.
    eauto using var_clock_defined.
  Qed.

  Corollary snd_nclocks_fresh :
    forall G vars e x,
      wc_exp G vars e ->
      wc_global G ->
      wc_env vars ->
      Ino x (map snd (nclockof e)) ->
      ~ InMembers x vars ->
      InMembers x (fresh_in e).
  Proof.
    intros * ??? Hino ?. eapply snd_nclocks_defined in Hino as []; eauto.
    contradiction.
  Qed.

  Lemma wc_app_reset:
    forall G vars f es r anns,
      wc_exp G vars (Eapp f es r anns) ->
      exists n bck sub,
        (Forall (wc_exp G vars) es
        /\ find_node f G = Some n
        /\ Forall2 (WellInstantiated bck sub) (idck (n_in n)) (nclocksof es)
        /\ Forall2 (WellInstantiated bck sub) (idck (n_out n)) (map snd anns)).
  Proof.
    intros * Hwc.
    inv Hwc; eauto 7.
  Qed.

  Ltac simpl_Foralls :=
    repeat
      match goal with
      | H: Forall _ [] |- _ => inv H
      | H: Forall _ [_] |- _ => inv H
      | H: Forall _ (_ :: _) |- _ => inv H
      | H: Forall2 _ [_] _ |- _ => inv H
      | H: Forall2 _ [] _ |- _ => inv H
      | H: Forall2 _ _ [_] |- _ => inv H
      | H: Forall2 _ _ [] |- _ => inv H
      end.

  Fact NoDupMembers_fresh_in : forall e es,
      In e es ->
      NoDupMembers (fresh_ins es) ->
      NoDupMembers (fresh_in e).
  Proof.
    intros * Hin Hndup.
    unfold fresh_ins in *.
    induction es; inv Hin; simpl in Hndup.
    - apply NoDupMembers_app_l in Hndup; auto.
    - apply NoDupMembers_app_r in Hndup; auto.
  Qed.

  Corollary NoDupMembers_fresh_in' : forall vars e es,
      In e es ->
      NoDupMembers (vars ++ fresh_ins es) ->
      NoDupMembers (vars ++ fresh_in e).
  Proof.
    intros * Hin Hndup.
    apply NoDupMembers_app.
    - apply NoDupMembers_app_l in Hndup; auto.
    - apply NoDupMembers_app_r in Hndup; auto.
      eapply NoDupMembers_fresh_in; eauto.
    - intros x HIn contra.
      eapply NoDupMembers_app_InMembers in Hndup; eauto.
      eapply InMembers_fresh_in in contra; eauto.
  Qed.

  Fact NoDupMembers_anon_in : forall e es,
      In e es ->
      NoDupMembers (anon_ins es) ->
      NoDupMembers (anon_in e).
  Proof.
    intros * Hin Hndup.
    unfold anon_ins in *.
    induction es; inv Hin; simpl in Hndup.
    - apply NoDupMembers_app_l in Hndup; auto.
    - apply NoDupMembers_app_r in Hndup; auto.
  Qed.

  Corollary NoDupMembers_anon_in' : forall vars e es,
      In e es ->
      NoDupMembers (vars ++ anon_ins es) ->
      NoDupMembers (vars ++ anon_in e).
  Proof.
    intros * Hin Hndup.
    apply NoDupMembers_app.
    - apply NoDupMembers_app_l in Hndup; auto.
    - apply NoDupMembers_app_r in Hndup; auto.
      eapply NoDupMembers_anon_in; eauto.
    - intros x HIn contra.
      eapply NoDupMembers_app_InMembers in Hndup; eauto.
      eapply InMembers_anon_in in contra; eauto.
  Qed.

  Fact NoDupMembers_anon_in_eq : forall eq eqs,
      In eq eqs ->
      NoDupMembers (anon_in_eqs eqs) ->
      NoDupMembers (anon_in_eq eq).
  Proof.
    intros * Hin Hndup.
    unfold fresh_ins in *.
    induction eqs; inv Hin; simpl in Hndup.
    - apply NoDupMembers_app_l in Hndup; auto.
    - apply NoDupMembers_app_r in Hndup; auto.
  Qed.

  Corollary NoDupMembers_anon_in_eq' : forall vars eq eqs,
      In eq eqs ->
      NoDupMembers (vars ++ anon_in_eqs eqs) ->
      NoDupMembers (vars ++ anon_in_eq eq).
  Proof.
    intros * Hin Hndup.
    apply NoDupMembers_app.
    - apply NoDupMembers_app_l in Hndup; auto.
    - apply NoDupMembers_app_r in Hndup; auto.
      eapply NoDupMembers_anon_in_eq; eauto.
    - intros x HIn contra.
      eapply NoDupMembers_app_InMembers in Hndup; eauto.
      eapply InMembers_anon_in_eq in contra; eauto.
  Qed.

  Fact NoDupMembers_idck : forall (xs : list (ident * (type * clock))),
      NoDupMembers (idck xs) <-> NoDupMembers xs.
  Proof.
    intros. repeat rewrite fst_NoDupMembers.
    rewrite <- idck_idents. reflexivity.
  Qed.

  Lemma sc_switch_adds :
    forall H b ck cks xs ss,
      sem_clock (Env.adds_opt' xs ss H) b ck cks ->
      (forall x, Is_free_in_clock x ck -> ~Ino x xs) ->
      sem_clock H b ck cks.
  Proof.
    intros * Hsc Hino. eapply sc_switch_env; eauto.
    intros * Hfree. apply Hino in Hfree.
    rewrite Env.find_In_gsso_opt'; auto.
  Qed.

  Lemma sc_switch_adds' :
    forall H b ck cks xs ss,
      sem_clock H b ck cks ->
      (forall x, Is_free_in_clock x ck -> ~Ino x xs) ->
      sem_clock (Env.adds_opt' xs ss H) b ck cks.
  Proof.
    intros * Hsc Hino. eapply sc_switch_env; eauto.
    intros * Hfree. apply Hino in Hfree.
    rewrite Env.find_In_gsso_opt'; auto.
  Qed.

  (* permute quantifiers to ease instantiation *)
  Lemma Forall2_in_right':
    forall {A B} P (xs: list A) (ys: list B),
      Forall2 P xs ys ->
      forall y,
        In y ys ->
        exists x, In x xs /\ P x y.
  Proof.
    eauto using Forall2_in_right.
  Qed.

  (* induction hypothesis over the program *)
  Definition sc_nodes (G : global) : Prop :=
    forall H f n xs (* vs *) os,
      sem_node G f xs os ->
      find_node f G = Some n ->
      Forall2 (sem_var H) (idents (n_in n)) xs ->
      (* Forall2 (sem_var H) (idents (n_vars n)) vs -> *)
      Forall2 (sem_var H) (idents (n_out n)) os ->
      Forall2 (fun xc => sem_clock H (clocks_of xs) (snd xc))
              (idck (n_in n)) (map abstract_clock xs) ->
      (* Forall2 (fun xc => sem_clock H (clocks_of xs) (snd xc)) *)
      (*         (idck (n_vars n)) (map abstract_clock vs) /\ *)
      Forall2 (fun xc => sem_clock H (clocks_of xs) (snd xc))
              (idck (n_out n)) (map abstract_clock os).
  Hint Unfold sc_nodes.

  Definition filter_anons (env : list (ident * clock)) (ncs : list nclock) :
    list (option ident) :=
    map (fun nc => match snd nc with
                | None => None
                | Some x => if mem_assoc_ident x env
                           then None
                           else Some x
                end) ncs.

  Lemma filter_anons_spec :
    forall env ncs x,
      Ino x (filter_anons env ncs) ->
      Ino x (map snd ncs) /\ ~ InMembers x env.
  Proof.
    unfold filter_anons.
    intros * Hino. rewrite Ino_In, in_map_iff in Hino.
    destruct Hino as [(c & o) (H & ?)]. simpl in H.
    destruct o; cases_eqn H; inv H. split.
    rewrite Ino_In, in_map_iff. esplit; split; eauto; simpl; eauto.
    apply NotIn_NotInMembers; intros. now apply mem_assoc_ident_false.
  Qed.

  Lemma filter_anons_ino :
    forall env ncs x,
    Ino x (filter_anons env ncs) ->
    ~ InMembers x env.
  Proof.
    intros. eapply filter_anons_spec; eauto.
  Qed.

  Lemma filter_anons_app :
    forall env l l',
      filter_anons env (l ++ l') = filter_anons env l ++ filter_anons env l'.
  Proof.
    unfold filter_anons. now setoid_rewrite map_app.
  Qed.

  Lemma filter_anons_filter :
    forall env x xs,
      Ino x (filter_anons env xs) ->
      Ino x (map snd xs).
  Proof.
    intros * Hin. induction xs; inv Hin; [| right; auto].
    destruct a as [? []]; simpl in *; cases; tauto.
  Qed.

  Lemma filter_anons_filter' :
    forall env x xs,
      Ino x (map snd xs) ->
      ~ Ino x (filter_anons env xs) ->
      InMembers x env.
  Proof.
    intros * Hin Hnin. induction xs. inv Hin.
    rewrite Ino_In in Hin, Hnin, IHxs, IHxs. simpl in *.
    apply not_or' in Hnin as [Ha Hnin]. destruct Hin as [Heq | Hin].
    + destruct (snd a); inv Heq. destruct (mem_assoc_ident x env0) eqn:Hm.
      apply mem_assoc_ident_true in Hm as []. eauto using In_InMembers.
      congruence.
    + apply IHxs in Hin; auto.
  Qed.

  Lemma filter_anons_ino' : forall env ncs x,
      Ino x (map snd ncs) ->
      ~ InMembers x env ->
      Ino x (filter_anons env ncs).
  Proof.
    intros * Hino Hnin. induction ncs; inv Hino.
    - simpl. destruct a as [ck [id|]]; simpl; inv H.
      destruct mem_assoc_ident eqn:Hm.
      + apply mem_assoc_ident_true in Hm. destruct Hm as [? Hin].
        apply In_InMembers in Hin. congruence.
      + left; constructor.
    - right; auto.
  Qed.

  Lemma filter_anons_incl : forall env1 env2 ncs x,
      incl env1 env2 ->
      Ino x (filter_anons env2 ncs) ->
      Ino x (filter_anons env1 ncs).
  Proof.
    intros * Hincl Hin.
    assert (Hin':=Hin). apply filter_anons_filter in Hin. apply filter_anons_ino in Hin'.
    apply filter_anons_ino'; auto.
    intro contra. apply Hin'; clear Hin'.
    apply InMembers_In in contra as [? ?]. apply Hincl in H.
    eauto using In_InMembers.
  Qed.

  Fact filter_anons_anon_streams_In : forall x vars anns,
      Ino x (filter_anons vars (map snd anns)) ->
      InMembers x (Syn.anon_streams anns).
  Proof.
    intros * Hino.
    induction anns; simpl in *; auto.
    destruct a as [? [? [?|]]]; simpl in *.
    - destruct Hino; auto.
      left. destruct mem_assoc_ident; simpl in H; inv H; auto.
    - destruct Hino; [inv H|]; auto.
  Qed.

  Fact filter_anons_anon_streams_NoDupMembers : forall vars anns,
      NoDupMembers (Syn.anon_streams anns) ->
      NoDupo (filter_anons vars (map snd anns)).
  Proof.
    intros * H.
    induction anns; simpl in *; [constructor|].
    destruct a as [? [? [?|]]].
    - inv H; simpl.
      destruct mem_assoc_ident; constructor; auto.
      intro contra; apply H2.
      eapply filter_anons_anon_streams_In; eauto.
    - constructor; auto.
  Qed.

  Lemma nodupo_filter_anons :
    forall G env e,
      wc_exp G env e ->
      NoDupMembers (fresh_in e) ->
      NoDupo (filter_anons env (nclockof e)).
  Proof.
    destruct e; intros Hwc Hdf; inv Hwc; simpl.
    1,3,4,5:repeat constructor.
    - destruct mem_assoc_ident; repeat constructor; auto.
    - clear - H6. induction l1; simpl in *. constructor.
      inv H6. unfold unnamed_stream in *. destruct a as (?&?&?).
      simpl in *. subst. constructor. auto.
    - clear - tys. induction tys; simpl; constructor. auto.
    - clear - tys. induction tys; simpl; constructor. auto.
    - clear - tys. induction tys; simpl; constructor. auto.
    - simpl in Hdf.
      apply NoDupMembers_app_r in Hdf.
      eapply filter_anons_anon_streams_NoDupMembers in Hdf; eauto.
    - simpl in Hdf.
      repeat apply NoDupMembers_app_r in Hdf.
      eapply filter_anons_anon_streams_NoDupMembers in Hdf; eauto.
  Qed.

  (* TODO: move *)
  Lemma LiftO_impl:
    forall {A} d (P P' : A -> Prop) (x : option A),
      (forall a, P a -> P' a) ->
      LiftO d P x ->
      LiftO d P' x.
  Proof.
    intros. destruct x; simpl in *; auto.
  Qed.

  Lemma sc_permute_adds :
    forall H b ck cks xs vs xs' vs',
      sem_clock (Env.adds_opt' xs vs (Env.adds_opt' xs' vs' H)) b ck cks ->
      (forall x, Ino x xs -> ~ Ino x xs') ->
      sem_clock (Env.adds_opt' xs' vs' (Env.adds_opt' xs vs H)) b ck cks.
  Proof.
    intros * Hsc Hino. eapply sc_switch_env; eauto.
    intros * Hfree.
    rewrite <- Env.find_permute_adds_opt'; auto.
  Qed.

  Lemma sc_permute_adds_nest :
    forall H b ck cks xs vs xs' vs' xs'' vs'',
      sem_clock (Env.adds_opt' xs vs (Env.adds_opt' xs' vs' (Env.adds_opt' xs'' vs'' H))) b ck cks ->
      (forall x, Ino x xs -> ~ Ino x xs') ->
      (forall x, Ino x xs -> ~ Ino x xs'') ->
      length xs' = length vs' ->
      sem_clock (Env.adds_opt' xs' vs' (Env.adds_opt' xs'' vs'' (Env.adds_opt' xs vs H))) b ck cks.
  Proof.
    intros * Hsc Hino Hino' Hlen. eapply sc_switch_env; eauto.
    intros * Hfree.
    rewrite <- Env.adds_opt'_app; auto. setoid_rewrite <- Env.adds_opt'_app at 3; auto.
    rewrite Env.find_permute_adds_opt'; auto.
    intros ? HH ?. apply ino_app_iff in HH as [Hin|Hin]; eauto.
    apply Hino in Hin; auto. apply Hino' in Hin; auto.
  Qed.

  Lemma filter_nclock_eq :
    forall G env e,
      wc_exp G env e ->
      filter_anons env (nclockof (e)) =
      match e with
      | Eapp _ _ _ anns => filter_anons env (map snd anns)
      | _ => map (fun _ => None) (nclockof (e))
      end.
  Proof.
    destruct e; intros Hwc; inv Hwc; simpl; auto.
    - take (In _ _) and cases_eqn it. eapply mem_assoc_ident_false in it; tauto.
    - eapply map_ext_in; eauto. intros (?&?) Hin.
      apply in_map_iff in Hin as ((?&?)&?&?).
      take (_ unnamed_stream _) and eapply Forall_forall in it as un; eauto.
      unfold  unnamed_stream in un. now repeat (simpl in *; subst).
    - eapply map_ext_in; eauto. intros (?&?) Hin.
      apply in_map_iff in Hin as (?&HH&?). inv HH. now simpl.
    - eapply map_ext_in; eauto. intros (?&?) Hin.
      apply in_map_iff in Hin as (?&HH&?). inv HH. now simpl.
    - eapply map_ext_in; eauto. intros (?&?) Hin.
      apply in_map_iff in Hin as (?&HH&?). inv HH. now simpl.
  Qed.

  Lemma clockof_defined:
    forall G env e,
      wt_exp G (idty env) e ->
      wc_exp G (idck env) e ->
      forall ck x,
      In ck (clockof e) ->
      Is_free_in_clock x ck ->
      match e with
      | Eapp _ _ _ anns => True
      | _ => InMembers x env
      end.
  Proof.
    destruct e; intros * Hwt Hwc * Hin Hfr; simpl in *; auto.
    - inv Hin; inv Hfr; tauto.
    - inv Hin; intuition; inv Hwt; inv Hwc;
        eapply wt_nclock_Is_free_in in H2; eauto;
          eapply InMembers_idty; eauto.
    - inv Hin; intuition; inv Hwt; inv Hwc.
      eapply wt_nclock_Is_free_in in H5; eauto.
      eapply InMembers_idty; eauto.
    - inv Hin; intuition; inv Hwt; inv Hwc.
      eapply wt_nclock_Is_free_in in H8; eauto.
      eapply InMembers_idty; eauto.
    - inv Hwt; inv Hwc.
      eapply wt_clock_Is_free_in with (env:=idty env0) in Hfr; eauto. eapply InMembers_idty; eauto.
      rewrite Forall_map, Forall_forall in H6. unfold clock_of_nclock, stripname in *.
      apply in_map_iff in Hin as [[? ?] [? Hin]].
      apply H6 in Hin; simpl in *; subst; inv Hin; auto.
    - inv Hwt; inv Hwc.
      eapply wt_clock_Is_free_in with (env:=idty env0) in Hfr; eauto. eapply InMembers_idty; eauto.
      unfold clock_of_nclock, stripname in *.
      simpl in Hin. apply in_map_iff in Hin as [? [? _]]; subst. inv H6; auto.
    - inv Hwt; inv Hwc.
      eapply wt_clock_Is_free_in with (env:=idty env0) in Hfr; eauto. eapply InMembers_idty; eauto.
      unfold clock_of_nclock, stripname in *.
      simpl in Hin. apply in_map_iff in Hin as [? [? _]]; subst. inv H8; auto.
    - inv Hwt; inv Hwc.
      eapply wt_clock_Is_free_in with (env:=idty env0) in Hfr; eauto. eapply InMembers_idty; eauto.
      unfold clock_of_nclock, stripname in *.
      simpl in Hin. apply in_map_iff in Hin as [? [? _]]; subst. inv H9; auto.
  Qed.

  (* Given a [sem_clock] hypothesis over local expressions [es],
     build a global environment (disjoint union of the respective
     environments) which could be used for the whole [clocksof es]
   *)
  Lemma sc_union_envs :
    forall G es env H b ss0,
      Forall (wt_exp G (idty env)) es ->
      Forall (wc_exp G (idck env)) es ->
      Forall2 (sem_exp G H b) es ss0 ->
      wc_global G ->
      wc_env (idck env) ->
      NoDupMembers (env++fresh_ins es) ->
      Forall2
        (fun (e : exp) (ss : list (Stream value)) =>
           match e with
           | Eapp _ _ _ anns =>
             exists ncs nss,
             Datatypes.length ncs = Datatypes.length nss /\
             Forall (LiftO True (fun x : ident => InMembers x (fresh_in e))) ncs /\
             (let H := Env.adds_opt' ncs nss H in
              let H0 := Env.adds_opt' (filter_anons (idck env)(map snd anns)) ss H in
              Forall2 (sem_clock H0 b) (clockof e) (map abstract_clock ss))
           | _ => Forall2 (sem_clock H b) (clockof e) (map abstract_clock ss)
           end) es ss0
      ->
      exists ncs nss,
        Datatypes.length ncs = Datatypes.length nss /\
        Forall (LiftO True (fun x : ident => Exists (fun e => InMembers x (fresh_in e)) es)) ncs /\
        (let H0 := Env.adds_opt' ncs nss H in
         let H1 := Env.adds_opt' (filter_anons (idck env)(nclocksof es)) (concat ss0) H0 in
         Forall2 (sem_clock H1 b) (clocksof es)
                 (map abstract_clock (concat ss0))).
  Proof.
    intros * Hwt Hwc Hse Hwcg Henv Hndup Hes.
    revert dependent ss0.
    induction es; intros; inv Hes. exists [], []. now simpl.
    assert (Hwc' := Hwc). inv Hse. inv Hwt. inv Hwc'.
    inv_NoDup_fresh_ins Hndup.
    take (Forall (wc_exp _ _) _) and eapply IHes in it
      as (ncs & nss & Hlen & Hfresh & Hscl); eauto.
    Local Ltac solve_length :=
      rewrite map_length, nclockof_length; eapply length_clockof; eauto.
    Local Ltac solve_NoDupMembers H :=
      eapply NoDupMembers_app_InMembers in H; eauto;
      eapply H, InMembers_app, or_intror, InMembers_fresh_in; eauto.
    simpl in *. destruct a.
    1-8: exists ncs,nss; split; auto; split;
                 [ apply Forall_impl with (2 := Hfresh); auto; intros;
                   eapply LiftO_impl; eauto; intros; now right |].
    (* all cases except Eapp are identical... *)
    (* { *)
    (*   (* clear - Henv Hwc H2 H10 H5 Hfresh H13 Hscl. *) *)
    (*   inv Hwc. rewrite map_app. apply Forall2_app. *)
    (*   - take (_ _ (clockof _) (map abstract_clock _)) and *)
    (*          eapply Forall2_impl_In in it; eauto. intros ck ? Hinck ??. *)
    (*     erewrite filter_anons_app, filter_nclock_eq, *)
    (*     adds_opt'_app, adds_opt'_None; eauto. 2: solve_length. *)
    (*     apply sc_switch_adds'; simpl; eauto. *)
    (*     2:{ intros x Hfr Hfil. eapply clockof_defined in Hfr; eauto. simpl in Hfr. *)
    (*         apply filter_anons_ino in Hfil. eapply InMembers_idck in Hfr; eauto. } *)
    (*     apply sc_switch_adds'; simpl; eauto. *)
    (*     intros x Hfree Hncs. eapply clockof_defined in Hfree; eauto. simpl in Hfree. *)
    (*     eapply Ino_Forall in Hncs; eauto. simpl in Hncs. *)
    (*     apply Exists_exists in Hncs as (?&?& Hfr). *)
    (*     solve_NoDupMembers Hndup. *)
    (*   - eapply Forall2_impl_In; eauto; intros. *)
    (*     erewrite filter_anons_app, filter_nclock_eq, *)
    (*     adds_opt'_app, adds_opt'_None; eauto. solve_length. *)
    (* } *)

    1-8:(inv Hwc; rewrite map_app; apply Forall2_app;
         [ (take (_ _ (clockof _) (map abstract_clock _)) and eapply Forall2_impl_In in it); eauto;
           intros ck ? Hinck ??; auto;
           erewrite filter_anons_app, filter_nclock_eq, Env.adds_opt'_app, Env.adds_opt'_None; eauto; [| solve_length];
           apply sc_switch_adds'; simpl; eauto;
           [ apply sc_switch_adds'; simpl; eauto;
             intros x Hfree Hncs; eapply clockof_defined in Hfree; eauto; simpl in Hfree;
             eapply Ino_Forall in Hncs; eauto; simpl in Hncs;
             apply Exists_exists in Hncs as (?&?& Hfr); solve_NoDupMembers Hndup
           | intros x Hfr Hfil; eapply clockof_defined in Hfr; eauto; simpl in Hfr;
             apply filter_anons_ino in Hfil; apply InMembers_idck in Hfr; eauto ]
         | eapply Forall2_impl_In; eauto; intros;
           erewrite filter_anons_app, filter_nclock_eq, Env.adds_opt'_app, Env.adds_opt'_None; eauto; solve_length ]).

    (* Eapp *)
    Local Ltac solve_NoDupMembers2 H :=
      eapply NoDupMembers_app_r, NoDupMembers_app_InMembers in H; eauto;
      eapply H, InMembers_fresh_in; eauto.

    take (exists _,_) and destruct it as (ncs'& nss'& Hlen' & Hncs' & Hsc).
    exists (ncs ++ ncs'),(nss ++ nss'). split. rewrite 2 app_length. omega. split.
    apply Forall_app. split.
    apply Forall_impl with (2 := Hfresh); auto; intros;
      eapply LiftO_impl; eauto; intros; now right.
    apply Forall_impl with (2 := Hncs'); auto; intros;
      eapply LiftO_impl; eauto; intros; now left.
    rewrite map_app. apply Forall2_app.

    3:{ rewrite Permutation_swap in Hndup. apply NoDupMembers_app_r in Hndup; auto. }

    - take (_ _ (clockof _) (map abstract_clock _)) and
           eapply Forall2_impl_In in it; eauto.
      intros c ? Hin ? Hsc. simpl in *.
      rewrite Env.adds_opt'_app; auto.
      unfold filter_anons. rewrite map_app, Env.adds_opt'_app.
      2:{ apply Forall2_length in it. now rewrite 2 map_length in *. }
      apply sc_permute_adds.
      2:{
        intros x Hinnc Hinl0.
        apply filter_anons_spec in Hinnc as (Hino &?).
        apply filter_anons_spec in Hinl0 as (Hino' &?).
        rewrite Ino_In in Hino.
        eapply In_snd_nclocksof in Hino as (?&?& Hsnd).
        inv Hwc. rewrite <- Ino_In in Hsnd.
        eapply snd_nclocks_defined with (vars := idck env0) in Hsnd as []; eauto.
        2:{ eapply Forall_forall; eauto. }
        eapply snd_nclocks_fresh in H12; eauto; simpl in H12.
        solve_NoDupMembers2 Hndup.
      }
      eapply sc_switch_adds'.
      2:{
        intros x Hinnc Hinl0.
        apply filter_anons_spec in Hinl0 as (Hino &?).
        take (wc_exp _ _ _) and eapply free_clock_defined in it as []; eauto.
        2:{ simpl. unfold clock_of_nclock, stripname. apply Exists_exists.
            esplit. split; eauto. }
        eapply Ino_In, In_snd_nclocksof in Hino as (?&?& Hsnd).
        inv Hwc. rewrite <- Ino_In in Hsnd.
        eapply snd_nclocks_defined with (vars := idck env0) in Hsnd as []; eauto.
        2:{ eapply Forall_forall; eauto. }
        solve_NoDupMembers2 Hndup.
      }
      apply sc_permute_adds.
      2:{
        intros x Hinc Hinl0.
        eapply Ino_In, Forall_forall in Hinc; eauto. simpl in Hinc.
        apply filter_anons_spec in Hinl0 as (Hino &?).
        eapply snd_nclocks_fresh in H8; eauto; simpl in H8.
        rewrite Exists_exists in Hinc; destruct Hinc as [? [? ?]].
        solve_NoDupMembers2 Hndup.
      }
      apply sc_switch_adds'.
      2:{
        intros x Hfr Hinc.
        eapply Ino_In, Forall_forall in Hinc; eauto; simpl in Hinc.
        take (wc_exp _ _ _) and eapply free_clock_defined in it as []; eauto.
        3:{ simpl. unfold clock_of_nclock, stripname. apply Exists_exists.
            esplit. split; eauto. }
        1,2:eapply Exists_exists in Hinc as (e&?&Hfr'); inv Hwc.
        2: solve_NoDupMembers2 Hndup.
        eapply InMembers_idck in H1. solve_NoDupMembers Hndup.
      }
      assumption.
    - eapply Forall2_impl_In in Hscl; eauto; intros c ? Hin ? Hsc'. simpl in *.
      unfold filter_anons. rewrite map_app.
      rewrite 2 Env.adds_opt'_app; auto.
      2:{ apply Forall2_length in Hsc. now rewrite 2 map_length in *. }
      apply sc_switch_adds'.
      2:{
        intros x Hinnc Hinl0.
        apply filter_anons_spec in Hinl0 as (Hino &?).
        take (wc_exp _ _ _) and eapply snd_nclocks_fresh in it; simpl in it; eauto.
        apply In_clocksof in Hin as (e&?&?). inv Hwc.
        eapply free_clock_defined with (e := e) (x := x) in Henv as []; eauto.
        + solve_NoDupMembers2 Hndup.
        + inv H11; eapply Forall_forall in H2; eauto.
        + apply Exists_exists; eauto.
      }
      apply sc_permute_adds_nest.
      2:{
        intros x Hinnc Hinl0. apply Ino_In in Hinnc.
        apply filter_anons_spec in Hinl0 as (Hino & Hmem).
        eapply Forall_forall in Hinnc; eauto.
        rewrite Ino_In in Hino.
        apply In_snd_nclocksof in Hino as (e&?&?). inv Hwc.
        eapply snd_nclocks_fresh with (e := e) in Hmem; eauto.
        + solve_NoDupMembers2 Hndup.
        + inv H11; eapply Forall_forall in H1; eauto.
        + now apply Ino_In.
      }
      2:{
        intros x Hinnc' Hinnc. rewrite Ino_In in Hinnc, Hinnc'.
        eapply Forall_forall in Hinnc; eauto.
        eapply Forall_forall in Hinnc'; eauto. simpl in *.
        apply Exists_exists in Hinnc as [? [? ?]].
        solve_NoDupMembers2 Hndup.
      }
      2:{ apply Forall2_length in Hscl.
          now rewrite clocksof_nclocksof, 2 map_length in *. }
      apply sc_switch_adds'; auto.
      1:{
        intros x Hfree Hinnc. rewrite Ino_In in Hinnc.
        eapply Forall_forall in Hinnc; eauto. simpl in *.
        apply In_clocksof in Hin as (e&?&?). inv Hwc.
        eapply free_clock_defined with (e := e) (x := x) in Henv as []; eauto.
        + eapply NoDupMembers_app_InMembers in Hndup; eauto.
          eapply Hndup, InMembers_app; eauto. eapply InMembers_idck in H9; eauto.
        + solve_NoDupMembers2 Hndup.
        + eapply Forall_forall; eauto.
        + apply Exists_exists; eauto.
      }
  Qed.

  Lemma inst_in_eqst:
    forall G env H Hi b n es ss0 i ck bck sub,
      In (i, ck) (idck (n_in n)) ->
      wc_global G ->
      wc_env (idck env) ->
      wc_env (idck (n_in n)) ->
      Forall (wt_exp G (idty env)) es ->
      Forall (wc_exp G (idck env)) es ->
      NoDupMembers (env++fresh_ins es) ->
      Forall2 (WellInstantiated bck sub) (idck (n_in n)) (nclocksof es) ->
      Forall2 (sem_exp G H b) es ss0 ->
      Forall2 (sem_var Hi) (idents (n_in n)) (concat ss0) ->
      forall i' ncs nss,
        sub i = Some i' ->
        Forall (LiftO True (fun x : ident => Exists (fun e => InMembers x (fresh_in e)) es)) ncs ->
        orel (@EqSt value) (Env.find i Hi)
             (Env.find i' (Env.adds_opt' (filter_anons (idck env) (nclocksof es))
                                         (concat ss0) (Env.adds_opt' ncs nss H))).
  Proof.
    intros * Hin Hwcg Henv WCin Hwt Hwc Hndup WIi Hse Hsv i' ncs nss Sub Hncs.
    (* i is a node variable, i' its image *)
    destruct (ino_dec i' ((filter_anons (idck env0) (nclocksof es)))
                      (ident_eq_dec)) as [Hino|Hnino].
    + (* i' is an anonymous variable manually added to H *)
      rewrite idck_idents, Forall2_map_1 in Hsv.
      pose proof (Forall2_in_left_combine  _ _ _ _ Hsv Hin) as (?&Hcomb&Hvar).
      inv Hvar. take (Env.MapsTo _ _ _) and apply Env.find_1 in it as Heq.
      simpl in *. erewrite Env.In_find_adds_opt'. rewrite Heq; eauto.
      now take (_ ≡ _) and rewrite <- it.
      { (* nodupo *)
        clear - Hwcg Henv Hwc Hwt Hndup. induction es; simpl. constructor.
        unfold filter_anons. rewrite map_app.
        inv Hwt. inv Hwc.
        inv_NoDup_fresh_ins Hndup. rewrite Permutation_swap in Hndup.
        assert (Hndup':=Hndup). apply NoDupMembers_app' in Hndup' as [Hndup1 ?].
        apply NoDupo_app'; auto. eapply nodupo_filter_anons; eauto.
        intros ? Hino Hino'. assert (Henv' := Henv).
        apply filter_anons_spec in Hino as (Hnd&?).
        eapply var_clock_defined in Henv as []; eauto.
        apply filter_anons_spec in Hino' as (Hnd'&?).
        apply Ino_In, In_snd_nclocksof in Hnd' as (e&?&Hnd').
        apply Ino_In in Hnd'.
        eapply var_clock_defined with (e := e) in Henv' as []; eauto.
        2: eapply Forall_forall; eauto.
        eapply NoDupMembers_app_InMembers in Hndup; eauto.
        eapply Hndup, InMembers_app, or_intror, InMembers_fresh_in; eauto.
      }
      apply Forall2_swap_args in WIi.
      pose proof (Forall2_trans_ex _ _ _ _ _ WIi Hsv) as Hesss0.
      apply Forall2_swap_args in WIi.
      pose proof (Forall2_chain_In' _ _ _ _ _ _ _ WIi Hesss0 Hcomb)
        as ((?&?)&(Sub'&?)&?&?& Hok).
      simpl in *. rewrite Sub in Sub'.
      eapply in_combine_nodup in Hcomb; eauto. subst.
      2:{ apply NoDupMembers_NoDup. apply NoDupMembers_idck.
          exact (NoDupMembers_app_l _ _ (n_nodup n)). }
      unfold filter_anons. rewrite combine_map_fst, in_map_iff.
      esplit. split; eauto. simpl.
      eapply filter_anons_spec in Hino as (?&Hinm).
      destruct (mem_assoc_ident i' _) eqn:Hb; auto.
      apply mem_assoc_ident_true in Hb as (?&IM).
      apply In_InMembers in IM; congruence.
    + (* i' was not added, it necessarily comes from the environment *)
      rewrite Env.find_In_gsso_opt'; auto.
      apply filter_anons_filter' in Hnino; auto.
      2:{ eapply Forall2_in_left in WIi as (?&?&Heq&?); eauto. simpl in *.
          rewrite Ino_In, in_map_iff. rewrite Heq in Sub. eauto. }
      rewrite Env.find_In_gsso_opt'.
      2:{ intro Hino. rewrite Ino_In in Hino. eapply Forall_forall in Hncs; eauto.
          simpl in Hncs. eapply Exists_exists in Hncs as (?&?&Hfr).
          eapply NoDupMembers_app_InMembers in Hndup; eauto.
          eapply Hndup, InMembers_fresh_in; eauto. eapply InMembers_idck in Hnino; eauto. }
      clear - Hwc Hse Hsv Hin Sub WIi Hnino Hndup.
      rewrite idck_idents in *.
      remember (idck (n_in n)) as ids. clear Heqids.
      revert dependent ids. revert dependent ss0.
      induction es as [|e]; intros. inv WIi. inv Hin.
      simpl in *. apply Forall2_app_inv_r in WIi as (l&?&Hf&Hc&?).
      subst. inv_NoDup_fresh_ins Hndup. inv Hse.
      inversion_clear Hwc as [| ?? Hwce].
      simpl in Hsv. rewrite map_app in Hsv.
      eapply Forall2_app_split in Hsv as (?&?); eauto.
      2:{ eapply length_clockof in Hwce; eauto. apply Forall2_length in Hf.
          rewrite clockof_nclockof, map_length in *. etransitivity; eauto. }
      apply in_app_or in Hin as [Hin|Hin]; eauto.
      clear Hc IHes. eapply Forall2_in_left in Hf as ((?&?)& Hck & Sub'&?); eauto.
      simpl in *. rewrite Sub in Sub'.
      { destruct e; inv Hwce; simpl in Hck.
        - inv Hck; try tauto. congruence.
        - (* variable *)
          destruct Hck as [Hck|]; try tauto. inv Hck.
          take (sem_exp _ _ _ _ _) and inv it.
          take (Forall2 _ _ [_]) and inv it.
          take (Forall2 _ _ []) and inv it.
          destruct l. inv Hin. simpl in *.
          destruct l; take ([_] = _) and inv it. inv Hin; intuition.
          simpl in *. do 2 take (sem_var _ _ _) and inv it.
          do 2 (erewrite Env.find_1; eauto). constructor.
          etransitivity; eauto. now symmetry.
        - inv Hck; try tauto. congruence.
        - inv Hck; try tauto. congruence.
        - inv Hck; try tauto. congruence.
        - eapply in_map_iff in Hck as ((?&?&?)&?&HH). simpl in *.
          eapply Forall_forall in HH; eauto. inv H6. inv HH.
        - clear - Hck. induction tys; simpl; inv Hck; auto. congruence.
        - clear - Hck. induction tys; simpl; inv Hck; auto. congruence.
        - clear - Hck. induction tys; simpl; inv Hck; auto. congruence.
        - eapply in_map with (f := snd) in Hck.
          simpl in *. rewrite map_map in Hck.
          exfalso. apply InMembers_idck in Hnino. eapply NoDupMembers_app_InMembers in Hndup; eauto.
          eapply Hndup, InMembers_app, or_introl, InMembers_app, or_intror, Ino_In_anon_streams.
          rewrite Ino_In; auto.
        - eapply in_map with (f := snd) in Hck.
          simpl in *. rewrite map_map in Hck.
          exfalso. apply InMembers_idck in Hnino. eapply NoDupMembers_app_InMembers in Hndup; eauto.
          eapply Hndup, InMembers_app, or_introl.
          repeat eapply InMembers_app, or_intror. eapply Ino_In_anon_streams.
          rewrite Ino_In; auto.
      }
      eapply IHes; eauto.
      rewrite Permutation_swap in Hndup.
      apply NoDupMembers_app_r in Hndup; auto.
  Qed.


  (* When function call parameters are well instantiated and have
     the [sem_clock] property, we obtain the same property inside
     the node (Hi = "H inside").
   *)
  Lemma sc_inside :
    forall G H Hi b env es ss0 bck sub n,
      Forall (wt_exp G (idty env)) es ->
      Forall (wc_exp G (idck env)) es ->
      Forall2 (sem_exp G H b) es ss0 ->
      wc_global G ->
      wc_env (idck env) ->
      wc_env (idck (n_in n)) ->
      NoDupMembers (env ++ fresh_ins es) ->
      Forall2
        (fun e ss =>
           match e with
           | Eapp f _ _ anns =>
             exists ncs nss,
             length ncs = length nss /\
             Forall (LiftO True (fun x => InMembers x (fresh_in e))) ncs /\
             let H := Env.adds_opt' ncs nss H in
             let H := Env.adds_opt' (filter_anons (idck env)(map snd anns)) ss H in
             Forall2 (sem_clock H b) (clockof e) (map abstract_clock ss)
           | _ =>
             Forall2 (sem_clock H b) (clockof e) (map abstract_clock ss)
           end) es ss0 ->
      Forall2 (WellInstantiated bck sub) (idck (n_in n)) (nclocksof es) ->
      Forall2 (sem_var Hi) (idents (n_in n)) (concat ss0) ->
      Forall2 (fun xc => sem_clock Hi (clocks_of (concat ss0)) (snd xc))
              (idck (n_in n)) (map abstract_clock (concat ss0)).
  Proof.
    intros * Hwt Hwc Hse Hwcg Henv WCin Hndup Hes WIi Hsv. assert (Hse' := Hse).
    eapply sc_union_envs in Hse' as (ncs & nss & Hlen & Hncs & Hscin); eauto.

    rewrite clocksof_nclocksof, Forall2_map_1 in Hscin.
    apply Forall2_trans_ex with (1 := WIi) in Hscin as H1.
    eapply Forall2_impl_In; eauto.
    intros (x & ck) xs  Hxin ? ((yck & ny) & Hyin & (Hsub & Hinst) & Hsc).
    simpl in *. unfold WellInstantiated in WIi.
    eapply sc_inst'; eauto.
    - pose proof (wc_env_has_Cbase _ WCin) as [i Hin];
        [ unfold idck; rewrite map_length; exact (n_ingt0 n) |].
      apply WellInstantiated_parent in WIi as Hp.
      change (Forall (fun ck => (fun x => x = bck \/ clock_parent bck x) (fst ck))
                     (nclocksof es)) in Hp.
      rewrite <- Forall_map in Hp.
      eapply sc_parent; eauto.
      now rewrite Forall2_map_1.
      pose proof (Forall2_in_left _ _ _ _ WIi Hin) as [?(?&?& H14)].
      simpl in H14. inv H14. now apply in_map.
    - intros i i' Free Sub.
      pose proof (wc_env_free_in_clock _ _ _ _ WCin Hxin Free) as [].
      eapply inst_in_eqst; eauto.
  Qed.

  Lemma sc_inst_mask:
    forall H' b b' ck ck' bck sub cks rs,
      instck bck sub ck = Some ck' ->
      sem_clock H' b' bck b ->
      (forall k, exists H, sem_clock H (maskb k rs b) ck (maskb k rs cks) /\
                 (forall x x',
                     Is_free_in_clock x ck ->
                     sub x = Some x' ->
                     orel (fun v1 v2 => EqSt v1 (mask k rs v2)) (Env.find x H) (Env.find x' H'))) ->
      sem_clock H' b' ck' cks.
  Proof.
    intros * Hinst Hbck Hk.
    rewrite sem_clock_equiv in *. unfold tr_Stream in *.
    intros n. specialize (Hbck n); simpl in Hbck.
    specialize (Hk ((count rs) # n)) as [H [Hck Henv]].
    rewrite sem_clock_equiv in Hck. unfold tr_Stream in Hck.
    specialize (Hck n); simpl in Hck.
    repeat rewrite maskb_nth in Hck.
    repeat rewrite Nat.eqb_refl in Hck.
    assert (forall x x', Is_free_in_clock x ck -> sub x = Some x' -> orel (@eq value) (Env.find x (CIStr.tr_history H n)) (Env.find x' (CIStr.tr_history H' n))) as Henv'.
    { intros * Hfree Hsub. specialize (Henv x x' Hfree Hsub).
      eapply tr_history_find_orel_mask' with (n:=n) in Henv.
      assert (relation_equivalence eq (fun v1 v2 : value => v1 = (if (count rs) # n =? (count rs) # n then v2 else absent))) as Heq.
      { intros x1 x2.
        rewrite Nat.eqb_refl.
        constructor; auto. }
      rewrite Heq; auto.
    } clear Henv.
    revert H H' b b' ck' bck cks sub Hinst Hck Hbck Henv'.
    induction ck; intros.
    - inv Hinst. inv Hck; auto.
    - inversion Hinst as [Hcase]. cases_eqn Hcase. inv Hcase.
      inv Hck.
      1,2:econstructor;eauto. 5:eapply IStr.Son_abs2; eauto.
      2,4,6:(unfold sem_var_instant in *;
             specialize (Henv' i i0 (FreeCon1 _ _ _) Hcase1); rewrite H5 in Henv';
             inv Henv'; auto).
      * rewrite H3 in *; eapply IHck in Hcase0; eauto.
        intros. eapply Henv'; auto; right; auto.
      * rewrite H4 in *; eapply IHck in Hcase0; eauto.
        intros. eapply Henv'; auto; right; auto.
      * eapply IHck with (cks:=Streams.const true) in Hcase0; eauto.
        rewrite const_nth in Hcase0; auto. rewrite const_nth; eauto.
        intros; eapply Henv'; auto; right; auto.
  Qed.

  Lemma sc_inst_mask':
    forall H H' b b' ck ck' bck sub cks k rs,
      instck bck sub ck = Some ck' ->
      sem_clock H' b' ck' cks ->
      sem_clock H' b' bck b ->
      (forall x x',
          Is_free_in_clock x ck ->
          sub x = Some x' ->
          orel (fun v1 v2 => EqSt v1 (mask k rs v2)) (Env.find x H) (Env.find x' H')) ->
      sem_clock H (maskb k rs b) ck (maskb k rs cks).
  Proof.
    intros * Hinst Hck Hbck Henv.
    rewrite sem_clock_equiv in *.
    intros n. specialize (Hck n). specialize (Hbck n).
    assert (forall x x' n, Is_free_in_clock x ck -> sub x = Some x' -> orel (fun v1 v2 => v1 = (if (CStr.count rs) # n =? k then v2 else absent)) (Env.find x (CIStr.tr_history H n)) (Env.find x' (CIStr.tr_history H' n))) as Henv'.
    { intros * Hfree Hsub. specialize (Henv x x' Hfree Hsub).
      eapply tr_history_find_orel_mask' in Henv; eauto. } clear Henv.
    unfold tr_Stream in *.
    revert H H' b b' ck' bck cks sub Hinst Hck Hbck Henv'.
    induction ck; intros.
    - inv Hinst.
      repeat rewrite maskb_nth in *. destruct (_ =? k); auto.
      eapply sem_clock_instant_det in Hck; eauto.
      rewrite Hck; auto.
    - inversion Hinst as [Hcase]. cases_eqn Hcase. inv Hcase.
      repeat rewrite maskb_nth in *; destruct (_ =? k) eqn:Hcount.
      + inv Hck.
        1,2:econstructor;eauto. 5:eapply IStr.Son_abs2; eauto.
        2,4,6:(unfold sem_var_instant in *;
               specialize (Henv' i i0 n (FreeCon1 _ _ _) Hcase1); rewrite H5 in Henv';
               inv Henv'; auto; rewrite Hcount; auto).
        * rewrite H3 in *; eapply IHck with (b':=b') in Hcase0; eauto.
          repeat rewrite maskb_nth, Hcount, <- H3 in Hcase0. rewrite <- H3; eauto.
          repeat rewrite maskb_nth, Hcount, <- H3; auto.
          intros. eapply Henv'; auto. right; auto.
        * rewrite H4 in *; eapply IHck with (b':=b') in Hcase0; eauto.
          repeat rewrite maskb_nth, Hcount in Hcase0; eauto.
          repeat rewrite maskb_nth, Hcount; auto.
          intros. eapply Henv'; auto. right; auto.
        * assert (Htrue:=H4). apply sem_clock_instant_true_inv in H4; eauto.
          eapply IHck with (b:=b0) (b':=b') (cks:=Streams.const true) in Hcase0; eauto.
          repeat rewrite maskb_nth, Hcount in Hcase0. rewrite const_nth in Hcase0; eauto.
          rewrite const_nth; eauto.
          repeat rewrite maskb_nth, Hcount; auto.
          intros; eapply Henv'; auto; right; auto.
      + inv Hck.
        1,2,3:econstructor; eauto.
        2,4,6:(unfold sem_var_instant in *;
               specialize (Henv' i i0 n (FreeCon1 _ _ _) Hcase1); rewrite H5 in Henv';
               inv Henv'; auto; rewrite Hcount; auto).
        2:eapply IHck with (b':=b') (b:=b0) (cks:=Streams.const false) in Hcase0; eauto.
        1,5:eapply IHck with (b':=b') (b:=b0) (cks:=Streams.const true) in Hcase0; eauto.
        3,6,9:(intros; eapply Henv'; auto; right; auto).
        1-9:repeat rewrite maskb_nth, Hcount in *; repeat rewrite const_nth in *; auto.
  Qed.

  Lemma inst_in_eqst_mask:
    forall G env H Hi b n es ss0 i ck bck sub k rs,
      In (i, ck) (idck (n_in n)) ->
      wc_global G ->
      wc_env (idck env) ->
      wc_env (idck (n_in n)) ->
      Forall (wt_exp G (idty env)) es ->
      Forall (wc_exp G (idck env)) es ->
      NoDupMembers (env++fresh_ins es) ->
      Forall2 (WellInstantiated bck sub) (idck (n_in n)) (nclocksof es) ->
      Forall2 (sem_exp G H b) es ss0 ->
      Forall2 (sem_var Hi) (idents (n_in n)) (map (mask k rs) (concat ss0)) ->
      forall i' ncs nss,
        sub i = Some i' ->
        Forall (LiftO True (fun x : ident => Exists (fun e => InMembers x (fresh_in e)) es)) ncs ->
        orel (fun v1 v2 => v1 ≡ mask k rs v2) (Env.find i Hi)
             (Env.find i' (Env.adds_opt' (filter_anons (idck env) (nclocksof es))
                                         (concat ss0) (Env.adds_opt' ncs nss H))).
  Proof.
    intros * Hin Hwcg Henv WCin Hwt Hwc Hndup WIi Hse Hsv i' ncs nss Sub Hncs.
    (* i is a node variable, i' its image *)
    destruct (ino_dec i' ((filter_anons (idck env0) (nclocksof es)))
                      (ident_eq_dec)) as [Hino|Hnino].
    + (* i' is an anonymous variable manually added to H *)
      rewrite idck_idents, Forall2_map_1 in Hsv.
      pose proof (Forall2_in_left_combine  _ _ _ _ Hsv Hin) as (?&Hcomb&Hvar).
      apply Forall2_swap_args in WIi.
      pose proof (Forall2_trans_ex _ _ _ _ _ WIi Hsv) as Hesss0.
      apply Forall2_swap_args in WIi.
      pose proof (Forall2_chain_In' _ _ _ _ _ _ _ WIi Hesss0 Hcomb)
        as ((?&?)&(Sub'&?)&?&?& Hok).
      assert (Hok':=Hok). rewrite combine_map_snd in Hok'.
      apply in_map_iff in Hok' as [[[? ?] ?] [Heq Hok']]; inv Heq.
      inv Hvar. take (Env.MapsTo _ _ _) and apply Env.find_1 in it as Heq.
      simpl in *. erewrite Env.In_find_adds_opt'. rewrite Heq; eauto.
      { constructor; symmetry; eauto. }
      { (* nodupo *)
        clear - Hwcg Henv Hwc Hwt Hndup. induction es; simpl. constructor.
        unfold filter_anons. rewrite map_app.
        inv Hwt. inv Hwc.
        inv_NoDup_fresh_ins Hndup. rewrite Permutation_swap in Hndup.
        assert (Hndup':=Hndup). apply NoDupMembers_app' in Hndup' as [Hndup1 ?].
        apply NoDupo_app'; auto. eapply nodupo_filter_anons; eauto.
        intros ? Hino Hino'. assert (Henv' := Henv).
        apply filter_anons_spec in Hino as (Hnd&?).
        eapply var_clock_defined in Henv as []; eauto.
        apply filter_anons_spec in Hino' as (Hnd'&?).
        apply Ino_In, In_snd_nclocksof in Hnd' as (e&?&Hnd').
        apply Ino_In in Hnd'.
        eapply var_clock_defined with (e := e) in Henv' as []; eauto.
        2: eapply Forall_forall; eauto.
        eapply NoDupMembers_app_InMembers in Hndup; eauto.
        eapply Hndup, InMembers_app, or_intror, InMembers_fresh_in; eauto.
      }
      simpl in *. rewrite Sub in Sub'.
      eapply in_combine_nodup in Hcomb; eauto. subst.
      2:{ apply NoDupMembers_NoDup. apply NoDupMembers_idck.
          exact (NoDupMembers_app_l _ _ (n_nodup n)). }
      unfold filter_anons. rewrite combine_map_fst, in_map_iff.
      exists ((c, Some i'), s). split; eauto. simpl.
      eapply filter_anons_spec in Hino as (?&Hinm).
      destruct (mem_assoc_ident i' _) eqn:Hb; auto.
      apply mem_assoc_ident_true in Hb as (?&IM).
      apply In_InMembers in IM; congruence.
    + (* i' was not added, it necessarily comes from the environment *)
      rewrite Env.find_In_gsso_opt'; auto.
      apply filter_anons_filter' in Hnino; auto.
      2:{ eapply Forall2_in_left in WIi as (?&?&Heq&?); eauto. simpl in *.
          rewrite Ino_In, in_map_iff. rewrite Heq in Sub. eauto. }
      rewrite Env.find_In_gsso_opt'.
      2:{ intro Hino. rewrite Ino_In in Hino. eapply Forall_forall in Hncs; eauto.
          simpl in Hncs. eapply Exists_exists in Hncs as (?&?&Hfr).
          eapply NoDupMembers_app_InMembers in Hndup; eauto.
          eapply Hndup, InMembers_fresh_in; eauto. eapply InMembers_idck in Hnino; eauto. }
      clear - Hwc Hse Hsv Hin Sub WIi Hnino Hndup.
      rewrite idck_idents in *.
      remember (idck (n_in n)) as ids. clear Heqids.
      revert dependent ids. revert dependent ss0.
      induction es as [|e]; intros. inv WIi. inv Hin.
      simpl in *. apply Forall2_app_inv_r in WIi as (l&?&Hf&Hc&?).
      subst. inv_NoDup_fresh_ins Hndup. inv Hse.
      inversion_clear Hwc as [| ?? Hwce].
      simpl in Hsv. rewrite map_app in Hsv.
      rewrite map_app in Hsv. eapply Forall2_app_split in Hsv as (?&?); eauto.
      2:{ eapply length_clockof in Hwce; eauto. apply Forall2_length in Hf.
          rewrite clockof_nclockof, map_length, map_length in *. etransitivity; eauto. }
      apply in_app_or in Hin as [Hin|Hin]; eauto.
      2:{ eapply IHes; eauto.
          rewrite Permutation_swap in Hndup. apply NoDupMembers_app_r in Hndup; auto. }
      clear Hc IHes. eapply Forall2_in_left in Hf as ((?&?)& Hck & Sub'&?); eauto.
      simpl in *. rewrite Sub in Sub'.
      { destruct e; inv Hwce; simpl in Hck.
        - inv Hck; try tauto. congruence.
        - (* variable *)
          destruct Hck as [Hck|]; try tauto. inv Hck.
          take (sem_exp _ _ _ _ _) and inv it.
          take (Forall2 _ _ [_]) and inv it.
          take (Forall2 _ _ []) and inv it.
          destruct l. inv Hin. simpl in *.
          destruct l; take ([_] = _) and inv it. inv Hin; intuition.
          simpl in *. do 2 take (sem_var _ _ _) and inv it.
          do 2 (erewrite Env.find_1; eauto). constructor.
          etransitivity; eauto. now symmetry.
          rewrite <- H6, H9. reflexivity.
        - inv Hck; try tauto. congruence.
        - inv Hck; try tauto. congruence.
        - inv Hck; try tauto. congruence.
        - eapply in_map_iff in Hck as ((?&?&?)&?&HH). simpl in *.
          eapply Forall_forall in HH; eauto. inv H6. inv HH.
        - clear - Hck. induction tys; simpl; inv Hck; auto. congruence.
        - clear - Hck. induction tys; simpl; inv Hck; auto. congruence.
        - clear - Hck. induction tys; simpl; inv Hck; auto. congruence.
        - eapply in_map with (f := snd) in Hck.
          simpl in *. rewrite map_map in Hck.
          exfalso. apply InMembers_idck in Hnino. eapply NoDupMembers_app_InMembers in Hndup; eauto.
          eapply Hndup, InMembers_app, or_introl, InMembers_app, or_intror, Ino_In_anon_streams.
          rewrite Ino_In; auto.
        - eapply in_map with (f := snd) in Hck.
          simpl in *. rewrite map_map in Hck.
          exfalso. apply InMembers_idck in Hnino. eapply NoDupMembers_app_InMembers in Hndup; eauto.
          eapply Hndup, InMembers_app, or_introl.
          repeat eapply InMembers_app, or_intror. eapply Ino_In_anon_streams.
          rewrite Ino_In; auto.
      }
  Qed.

  Corollary sc_inside_mask :
    forall G H Hi b env es ss0 bck sub n k rs,
      Forall (wt_exp G (idty env)) es ->
      Forall (wc_exp G (idck env)) es ->
      Forall2 (sem_exp G H b) es ss0 ->
      wc_global G ->
      wc_env (idck env) ->
      wc_env (idck (n_in n)) ->
      NoDupMembers (env ++ fresh_ins es) ->
      Forall2
        (fun e ss =>
           match e with
           | Eapp f _ _ anns =>
             exists ncs nss,
             length ncs = length nss /\
             Forall (LiftO True (fun x => InMembers x (fresh_in e))) ncs /\
             let H := Env.adds_opt' ncs nss H in
             let H := Env.adds_opt' (filter_anons (idck env)(map snd anns)) ss H in
             Forall2 (sem_clock H b) (clockof e) (map abstract_clock ss)
           | _ =>
             Forall2 (sem_clock H b) (clockof e) (map abstract_clock ss)
           end) es ss0 ->
      Forall2 (WellInstantiated bck sub) (idck (n_in n)) (nclocksof es) ->
      Forall2 (sem_var Hi) (idents (n_in n)) (map (mask k rs) (concat ss0)) ->
      Forall2 (fun xc => sem_clock Hi (clocks_of (map (mask k rs) (concat ss0))) (snd xc))
              (idck (n_in n)) (map abstract_clock (map (mask k rs) (concat ss0))).
  Proof.
    intros * Hwt Hwc Hse Hwcg Henv WCin Hndup Hes WIi Hsv. assert (Hse' := Hse).
    eapply sc_union_envs in Hse' as (ncs & nss & Hlen & Hncs & Hscin); eauto.

    rewrite clocksof_nclocksof, Forall2_map_1 in Hscin.
    apply Forall2_trans_ex with (1 := WIi) in Hscin as H1.
    assert (Forall2 (fun xc : ident * clock => sem_clock Hi (clocks_of (map (mask k rs) (concat ss0))) (snd xc)) (idck (n_in n)) (map (maskb k rs) (map abstract_clock (concat ss0)))) as H0.
    2:{ clear - H0.
        rewrite map_map, Forall2_map_2 in *.
        eapply Forall2_impl_In; eauto.
        intros [? ?] ? _ _ ?. rewrite ac_mask; auto. }
    rewrite Forall2_map_2. eapply Forall2_impl_In; eauto.
    intros (x & ck) xs  Hxin ? ((yck & ny) & Hyin & (Hsub & Hinst) & Hsc).
    simpl in *. unfold WellInstantiated in WIi.
    eapply sc_inst_mask' in Hinst; eauto.
    - rewrite clocks_of_mask; eauto.
    - pose proof (wc_env_has_Cbase _ WCin) as [i Hin];
        [ unfold idck; rewrite map_length; exact (n_ingt0 n) |].
      apply WellInstantiated_parent in WIi as Hp.
      change (Forall (fun ck => (fun x => x = bck \/ clock_parent bck x) (fst ck))
                     (nclocksof es)) in Hp.
      rewrite <- Forall_map in Hp.
      eapply sc_parent; eauto.
      now rewrite Forall2_map_1.
      pose proof (Forall2_in_left _ _ _ _ WIi Hin) as [?(?&?& H14)].
      simpl in H14. inv H14. now apply in_map.
    - intros i i' Free Sub.
      pose proof (wc_env_free_in_clock _ _ _ _ WCin Hxin Free) as [].
      eapply inst_in_eqst_mask; eauto.
  Qed.

  (* In the Eapp case, we must extend the [sem_clock] environment
     with a map for anonymous variables introduced by the application.
     The resulting environment contains the fresh (anonymous) outputs of
     the current call plus the fresh variables from sub-expressions (ncs).
   *)
  Lemma sc_exp :
    forall G H b env e ss,
      sem_exp G H b e ss ->
      wt_exp G (idty env) e ->
      wc_exp G (idck env) e ->
      wc_env (idck env) ->
      NoDupMembers (env ++ fresh_in e) ->
      wc_global G ->
      sc_nodes G ->
      sc_var_inv (fun x => LCA.Is_free_left x e) (idck env) H b ->
      match e with
      | Eapp f es _ anns =>
        exists ncs nss,
        length ncs = length nss /\
        Forall (LiftO True (fun x => InMembers x (fresh_in e))) ncs /\
        let H := Env.adds_opt' ncs nss H in
        (* no need for disjointedness with ncs here *)
        let H := Env.adds_opt' (filter_anons (idck env) (map snd anns)) ss H in
        Forall2 (sem_clock H b) (clockof e) (map abstract_clock ss)
      | _ =>
        Forall2 (sem_clock H b) (clockof e) (map abstract_clock ss)
      end.
  Proof.
    induction e using exp_ind2;
      intros * Hsem Hwt Hwc Henv Hndup Hwcg Hnode Hvar;
      specialize (clockof_defined G env0 _ Hwt Hwc) as Hmem; simpl in *.
     - inv Hsem. constructor; eauto. constructor. symmetry in H4.
       destruct cs. eapply ac_const; eauto.
     - inv Hsem.
       inv Hwc; constructor; auto; unfold clock_of_nclock, stripname;
         simpl; eapply Hvar; eauto; constructor.
     - inv Hsem. constructor; eauto. inv Hwt. inv Hwc.
       unfold clock_of_nclock, stripname. simpl.
       take (clockof e = _) and rewrite it in IHe.
       take (sem_exp _ _ _ e _) and apply IHe in it as He; auto. simpl in He.
       2:{ eapply sc_var_inv_weaken; eauto. simpl. intros. now constructor. }
       destruct e; inv He;
         take (lift1 _ _ _ _) and apply ac_lift1 in it; rewrite <- it; auto.
       take (exists _, _) and destruct it as (?&?&?&HH).
       inversion_clear HH as [|???? Hsc].
       eapply sc_switch_adds in Hsc; eauto.
       2:{ intros ? Hfree Hino. apply filter_anons_spec in Hino as []. rewrite InMembers_idck in H10.
           eapply Hmem in Hfree; tauto. }
       eapply sc_switch_adds in Hsc; eauto.
       intros ? Hfree Hino. eapply Ino_Forall in Hino; eauto. simpl in Hino.
       eapply wt_nclock_Is_free_in in Hfree; eauto.
       eapply NoDupMembers_app_InMembers in Hndup; eauto.
       apply InMembers_idty; auto.
     - inv Hsem. constructor; eauto. inv Hwt. inv Hwc.
       unfold clock_of_nclock, stripname. simpl.
       take (clockof e1 = _) and rewrite it in IHe1. simpl in IHe1.
       take (sem_exp _ _ _ e1 _) and apply IHe1 in it as He; auto.
       simpl in He.
       2:{ rewrite app_assoc in Hndup. apply NoDupMembers_app_l in Hndup; auto. }
       2:{ eapply sc_var_inv_weaken; eauto. simpl. intros. constructor. auto. }
       destruct e1; inv He; take (lift2 _ _ _ _ _ _) and apply ac_lift2 in it;
         rewrite <- it; auto.
       take (exists _, _) and destruct it as (?&?&?&HH).
       inversion_clear HH as [|???? Hsc].
       eapply sc_switch_adds in Hsc; eauto.
       2:{ intros ? Hfree Hino. apply filter_anons_spec in Hino as [].
           rewrite InMembers_idck in H5. eapply Hmem in Hfree; tauto. }
       eapply sc_switch_adds in Hsc; eauto.
       intros ? Hfree Hino. eapply Ino_Forall in Hino; eauto. simpl in Hino.
       eapply wt_nclock_Is_free_in in Hfree; eauto.
       { rewrite app_assoc in Hndup. eapply NoDupMembers_app_l, NoDupMembers_app_InMembers in Hndup; eauto.
         apply InMembers_idty; auto. }
     - (* Efby *)
       inv Hwc. inv Hsem.
       assert (EqSts (map abstract_clock ss)
                     (map abstract_clock (concat s0ss))) as Hmap.
       clear - H16.
       revert dependent s0ss. revert sss.
       induction ss; intros. inv H16. simpl. constructor.
       inv H16. rewrite 2 map_cons.
       constructor. symmetry. eapply ac_fby1; eauto.
       assert (l0 = concat [l0]) as Hl0 by (simpl; rewrite app_nil_r; auto).
       assert (l1 = concat [l1]) as Hl1 by (simpl; rewrite app_nil_r; auto).
       rewrite Hl0. rewrite Hl1 in H4.
       eapply IHss; eauto. simpl. rewrite app_nil_r. eauto.
       setoid_rewrite Hmap.

       pose proof (Forall2_in_right' _ _ _ H7) as Heq.
       rewrite Forall2_eq in H7. rewrite H7.
       take (Forall2 (sem_exp _ _ _) e0s _) and rename it into Hsem.
       take (Forall (wc_exp _ _) e0s) and rename it into Hwc.
       inv Hwt. rename H5 into Hwt.
       clear - Hndup H0 Hsem Henv Hwcg Hnode Hvar Hwt Hwc Heq Hmem.
       revert dependent s0ss.
       induction e0s as [|e]; intros. inv Hsem. now simpl.
       inv Hsem. inv Hwc; inv Hwt.
       simpl. rewrite map_app. apply Forall2_app.
       + simpl in Hndup; repeat rewrite <- app_assoc, idck_app in Hndup;
           rewrite app_assoc in Hndup; apply NoDupMembers_app_l in Hndup; auto.
         inversion_clear H0 as [|?? He Hg]. clear Hg IHe0s.
         take (sem_exp _ _ _ e _) and apply He in it as ?; auto.
         2:{ rewrite app_assoc in Hndup. apply NoDupMembers_app_l in Hndup; auto. }
         2:{ eapply sc_var_inv_weaken; eauto. simpl. intros. constructor. auto. }
         destruct e; auto. simpl in *.
         take (exists _, _) and destruct it as (?&?&?&?&HF2).
         eapply Forall2_impl_In in HF2; eauto. intros * Hin ? Hsc.
         eapply in_app_weak in Hin. apply Heq in Hin as (?&Hin&?). subst.
         unfold clock_of_nclock, stripname in Hin.
         apply in_map_iff in Hin as ((?&?&?)&?&?). simpl in *. subst.
         eapply sc_switch_adds in Hsc; eauto.
         2:{ intros ? Hfree Hino. apply filter_anons_spec in Hino as []. rewrite InMembers_idck in H10.
             eapply Hmem in Hfree; eauto. apply in_map_iff.
             esplit; split; eauto; simpl; eauto. }
         eapply sc_switch_adds in Hsc; eauto.
         intros ? Hfree Hino. eapply Ino_Forall in Hino; eauto. simpl in Hino.
         apply Hmem in Hfree. 2:apply in_map_iff; esplit; split; eauto; simpl; eauto.
         eapply NoDupMembers_app_InMembers in Hndup; eauto.
         apply Hndup, InMembers_app; eauto.
       + inv H0.
         eapply IHe0s; eauto; try constructor; eauto.
         { simpl in Hndup; repeat rewrite <- app_assoc in Hndup.
           rewrite Permutation_swap in Hndup; apply NoDupMembers_app_r in Hndup; auto. }
         { eapply sc_var_inv_weaken; eauto. simpl. intros * Hf. constructor.
           inv Hf. now right. }
         { intros. apply Heq. simpl. apply in_or_app. now right. }
     - (* Ewhen *)
       clear Hwt. inv Hwc. unfold clock_of_nclock, stripname. simpl. clear Hmem.
       revert dependent tys. revert dependent ss.
       induction es; intros; inv Hsem; inv H13.
       inv H15. apply length_zero_iff_nil in H8. subst. simpl. constructor.
       rename a into e0. simpl in H15. inv H0.
       apply Forall2_app_inv_l in H15. destruct H15 as (?&?&?&?&?). subst.
       unfold clocksof, flat_map in H8. simpl in H8.
       apply length_app in H8. destruct H8 as (?&?&?&?&?). subst.
       rewrite map_app. rewrite map_app. apply Forall2_app.
       + clear H10 IHes. apply Forall2_forall; split; intros.
         2:{ rewrite map_length. rewrite map_length.
             apply Forall2_length in H0. rewrite <- H0. rewrite H8.
             inv H5. eapply length_clockof; eauto. }
         assert (Hin := H2).
         apply in_combine_l in H2. apply in_combine_r in Hin.
         clear - H0 Hin H2 Hvar H6 H14. induction x2. inv H2.
         inv H2; [| apply IHx2; auto].
         2:{ eapply sc_var_inv_weaken; eauto. simpl. intros.
             inv H2. now constructor. }
         rewrite in_map_iff in Hin. destruct Hin as (?&?&?). subst.
         eapply Forall2_in_right in H2; eauto. destruct H2 as (?&?&?).
         eapply sc_when; eauto. apply ac_when in H2. rewrite H2.
         eapply Hvar; eauto. constructor. now left.
       + unfold clocksof, flat_map in H7. simpl in H7.
         apply Forall_app in H7. destruct H7.
         inv H5.
         eapply IHes in H10; eauto; try econstructor; eauto.
         { simpl in Hndup. rewrite Permutation_swap in Hndup.
           apply NoDupMembers_app_r in Hndup; auto. }
         eapply sc_var_inv_weaken; eauto. simpl. intros * Hf.
         inv Hf. constructor. intuition.
     - (* EMerge *)
       assert (Hlen := Hwc). eapply length_clockof in Hlen; eauto.
       inv Hwt. inv Hwc. inv Hsem. unfold clock_of_nclock, stripname. simpl.
       simpl in Hlen. rewrite map_length in Hlen.
       apply Forall2_const_map; [| now rewrite map_length].
       apply Forall_forall; intros * Hin.
       rewrite in_map_iff in Hin. destruct Hin as (s0 & Hac & Hin).
       apply Forall3_in_right with (z := s0) in H25; auto.
       destruct H25 as (st & sf & Hints & Hinfs & Hmerge).
       rewrite <- Hac.
       apply in_concat in Hints. destruct Hints as (lts & Hints & Hinlst).
       eapply Forall2_in_right in H23; eauto. destruct H23 as (e1 & Hine1 & Hseme1).
       eapply Forall_forall in H6; eauto. eapply Forall_forall in H12; eauto.
       eapply Forall_forall in H0; eauto.
       apply H0 in Hseme1; eauto.
       2:{ rewrite app_assoc in Hndup; apply NoDupMembers_app_l in Hndup.
           eapply NoDupMembers_fresh_in'; eauto. }
       2:{ eapply sc_var_inv_weaken; eauto. simpl. intros. constructor.
           right. left. apply Exists_exists. now exists e1. }

       apply in_concat in Hinfs. destruct Hinfs as (lfs & Hinfs & Hinlsf).
       eapply Forall2_in_right in H24; eauto. destruct H24 as (e2 & Hine2 & Hseme2).
       eapply Forall_forall in H7; eauto. eapply Forall_forall in H13; eauto.
       eapply Forall_forall in H1; eauto.
       apply H1 in Hseme2; auto.
       2:{ rewrite Permutation_swap in Hndup; apply NoDupMembers_app_r in Hndup.
           eapply NoDupMembers_fresh_in'; eauto. }
       2:{ eapply sc_var_inv_weaken; eauto. simpl. intros. constructor.
           right. right. apply Exists_exists. now exists e2. }
       eapply sc_merge; eauto.
       + apply in_map with (f := abstract_clock) in Hints.
         destruct e1; try (destruct Hseme1 as (?&?&?&?&Hseme1));
           eapply Forall2_in_right in Hseme1; eauto;
           destruct Hseme1 as (ck1 & Hinck1 & Hsc1);
           assert (In ck1 (clocksof ets)) by (apply in_flat_map; eauto);
           eapply Forall_forall in H15; eauto; subst; auto.
         (* Eapp case *)
         eapply sc_switch_adds in Hsc1; eauto.
         2:{ intros ? Hfree Hino. apply filter_anons_spec in Hino as []. rewrite InMembers_idck in H9.
             inv Hfree; eauto. eapply In_InMembers, InMembers_idck in H14; eauto.
             eapply wt_nclock_Is_free_in in H11; eauto. rewrite InMembers_idty in H11; eauto. }
         eapply sc_switch_adds in Hsc1; eauto.
         intros ? Hfree Hino. eapply Ino_Forall in Hino; eauto. simpl in Hino.
         rewrite app_assoc in Hndup; eapply NoDupMembers_app_l, NoDupMembers_app_InMembers in Hndup; eauto.
         eapply Hndup, InMembers_fresh_in; eauto.
         eapply wt_clock_Is_free_in with (env:= idty env0), InMembers_idty in Hfree; eauto.
         inv H11; constructor; auto.
       + apply in_map with (f := abstract_clock) in Hinfs.
         destruct e2; try (destruct Hseme2 as (?&?&?&?&Hseme2));
           eapply Forall2_in_right in Hseme2; eauto;
         destruct Hseme2 as (ck2 & Hinck2 & Hsc2);
         assert (In ck2 (clocksof efs)) by (apply in_flat_map; eauto);
         eapply Forall_forall in H16; eauto; subst; auto.
         (* Eapp case *)
         eapply sc_switch_adds in Hsc2; eauto.
         2:{ intros ? Hfree Hino. apply filter_anons_spec in Hino as []. rewrite InMembers_idck in H9.
             inv Hfree; eauto. eapply In_InMembers, InMembers_idck in H14; eauto.
             eapply wt_nclock_Is_free_in in H11; eauto. rewrite InMembers_idty in H11; eauto. }
         eapply sc_switch_adds in Hsc2; eauto.
         intros ? Hfree Hino. eapply Ino_Forall in Hino; eauto. simpl in Hino.
         rewrite Permutation_swap in Hndup; eapply NoDupMembers_app_r, NoDupMembers_app_InMembers in Hndup; eauto.
         eapply Hndup, InMembers_fresh_in; eauto.
         eapply wt_clock_Is_free_in with (env:= idty env0), InMembers_idty in Hfree; eauto.
         inv H11; constructor; auto.
     - (* Eite *)
       inv Hwc. inv Hsem. simpl. take (Forall3 _ _ _ _) and rename it into Hite.
       assert (EqSts (map abstract_clock ss)
                     (map abstract_clock (concat ts))) as Hmap.
       1:{
         clear - Hite.
         revert dependent ts. revert fs.
         induction ss; intros. inv Hite. simpl. constructor.
         inv Hite. rewrite 2 map_cons.
         constructor. symmetry. eapply ac_ite; eauto.
         assert (l0 = concat [l0]) as Hl0 by (simpl; rewrite app_nil_r; auto).
         assert (l1 = concat [l1]) as Hl1 by (simpl; rewrite app_nil_r; auto).
         rewrite Hl0. rewrite Hl1 in *.
         eapply IHss; eauto. simpl. rewrite app_nil_r. eauto. }
       setoid_rewrite Hmap. unfold clock_of_nclock, stripname. simpl.
       assert (Forall (wt_exp G (idty env0)) ets) as Hwt1 by (inv Hwt; eauto).
       clear Hmap Hwt Hite H13 H14. revert dependent ts. revert dependent tys.
       induction ets; intros.
       take (Forall2 _ [] _) and inv it. take (length _ = _) and inv it.
       take (length tys = 0) and apply length_zero_iff_nil in it. subst. simpl. auto.
       take (Forall2 _ (_::_) _) and inv it. simpl in *.
       take (Forall _ (_++_)) and apply  Forall_app in it as (?&?).
       take (length _ = _) and apply length_app in it as (?&?&?&?&?). subst.
       rewrite map_app. rewrite map_app.
       apply Forall2_app;
         take (Forall (wc_exp _ _) (_::_)) and inversion_clear it as [|?? Hwc];
         inversion_clear H0 as [|?? Ha].
       + assert (map (fun _ : type => ck) x = clockof a) as Hmap.
         { clear - H2 H10. revert dependent x.
           induction (clockof a); intros lty Hlen.
           inversion Hlen as [Hnil]. apply length_zero_iff_nil in Hnil. now subst.
           destruct lty; inv Hlen. simpl. inv H2. f_equal. now apply IHl. }
         rewrite Hmap.
         assert (NoDupMembers (env0 ++ fresh_in a)) as Hndup'.
         { clear - Hndup. rewrite Permutation_swap in Hndup. apply NoDupMembers_app_r in Hndup.
           repeat rewrite app_assoc in Hndup. repeat (apply NoDupMembers_app_l in Hndup; auto). }
         inv Hwt1.
         destruct a; eapply Ha in Hwc as Hsc; eauto;
           try (eapply sc_var_inv_weaken; eauto; simpl; constructor; intuition).
         (* Eapp case *)
         destruct Hsc as (?&?&?&?&HF2).
         eapply Forall2_impl_In in HF2; eauto. intros * Hin ? Hsc.
         eapply sc_switch_adds in Hsc; eauto.
         2:{ intros ? Hfree Hino.
             apply filter_anons_spec in Hino as []. rewrite InMembers_idck in H20.
             eapply Hmem in Hfree; eauto.
             rewrite <- Hmap, in_map_iff in Hin. destruct Hin as (?&?&?). subst.
             apply in_map_iff. esplit; split; eauto. eauto using in_or_app.
         }
         eapply sc_switch_adds in Hsc; eauto.
         intros ? Hfree Hino. eapply Ino_Forall in Hino; eauto. simpl in Hino.
         eapply NoDupMembers_app_InMembers in Hndup'; eauto.
         eapply Hmem in Hfree; eauto.
         rewrite <- Hmap, in_map_iff in Hin. destruct Hin as (?&?&?). subst.
         apply in_map_iff. esplit; split; eauto. eauto using in_or_app.
       + inv Hwt1. apply IHets; try constructor; auto.
         { clear - Hndup. repeat rewrite idck_app.
           rewrite <- app_assoc in Hndup. rewrite app_assoc, Permutation_swap, <- app_assoc in Hndup.
           apply NoDupMembers_app_r in Hndup; auto. }
         intros. eapply Hmem; eauto. rewrite map_app, in_app_iff; eauto.
         eapply sc_var_inv_weaken; eauto. simpl. intros * Hf.
         constructor. inv Hf. intuition.
     - destruct ro. all: swap 1 2.
       + (* Eapp *)
         assert (Hndup':=Hndup).
         eapply NoDupMembers_app_r in Hndup'.
         pose proof (nodupo_filter_anons _ _ _ Hwc Hndup') as Hnodupo.
         inversion_clear Hwc as
             [| | | | | | | | |???? bck sub Hwce Hfind WIi WIo|].
         inversion_clear Hsem as [| | | | | | | |??????? Hse Hsemn |].

         rewrite app_assoc in Hndup.
         assert (Hndup'':=Hndup). apply NoDupMembers_app_l in Hndup''; auto.
         assert (Hse' := Hse).
         eapply sc_union_envs in Hse'; eauto. 2:inv Hwt; eauto.
         2:{
           inv Hwt.
           eapply Forall2_impl_In; eauto. intros e? Hin ??.
           pose proof Hin as He; eapply Forall_forall with (1:=H1) in He; eauto.
           apply He; auto; try (now eapply Forall_forall; eauto).
           { eapply NoDupMembers_fresh_in'; eauto. }
           eapply sc_var_inv_weaken; eauto. simpl. intros. constructor.
           eapply Exists_exists. eauto.
         }

         inversion Hsemn as [ ???? Hi ?? Hvin Hvout ? Hsck]. subst.
         match goal with
         | H1: find_node f G = Some _, H2: find_node f G = Some _ |- _
           => rewrite H2 in H1; inv H1
         end.
         unfold sc_nodes in Hnode. eapply Hnode in Hsemn; eauto.
         { (* output *)

           (* forall k, sem_node (mask _ k) (mask ss k) ->
              exists ss', sem_node _ ss', (map abstract_clock ss') = (map abstract_clock ss)
              Forall2 _ (map abstract_clock ss) ->
              Forall2 _ (mask (abstract_clock ss)) *)

           destruct Hse' as (ncs & nss & Hlen & Hncs & Hscin); eauto.
           exists ((filter_anons (idck env0) (nclocksof es)) ++ ncs), ((concat ss0) ++ nss).
           split.
           { unfold filter_anons. apply Forall2_length in Hscin.
             now rewrite clocksof_nclocksof, 2 app_length, 2 map_length,
             Hlen, <- Hscin in *. }
           split.
           { apply Forall_app. split.
             apply Forall_forall. intros [x|] Hin; simpl; auto. apply Ino_In in Hin.
             apply filter_anons_spec in Hin as [Hin].
             apply Ino_In, In_snd_nclocksof in Hin as (?&?&Hin).
             eapply Ino_In, snd_nclocks_fresh in Hin; eauto.
             - apply InMembers_app, or_introl. eapply InMembers_fresh_in; eauto.
             - rewrite Forall_forall in Hwce; eauto.
             - eapply Forall_impl_In in Hncs; eauto. intros [] ??; auto; simpl in *.
               apply Exists_exists in H5 as [? [Hin Hinm]].
               apply InMembers_app, or_introl. eapply InMembers_fresh_in; eauto.
           }
           unfold WellInstantiated in WIo. unfold clock_of_nclock, stripname.
           rewrite Forall2_map_1. rewrite Forall2_map_2 in WIo.
           apply Forall2_swap_args in WIo.
           apply Forall2_trans_ex with (1 := WIo) in Hsemn.
           eapply Forall2_impl_In; eauto.
           intros [aty (ack & anm)] so ??((x&ck)& Hxin & (Hsub & Hinst) & Hsc).
           simpl in *.
           pose proof (wc_find_node G f n Hwcg) as [?(WCin&(WCio&?))]; eauto.
           unfold WellInstantiated in WIi.
           eapply sc_inst; eauto.
           - pose proof (wc_env_has_Cbase _ WCin) as [i Hin];
               [ unfold idck; rewrite map_length; exact (n_ingt0 n) |].
             apply WellInstantiated_parent in WIi as Hp.
             change (Forall (fun ck => (fun x => x = bck \/ clock_parent bck x) (fst ck))
                            (nclocksof es)) in Hp.
             rewrite <- Forall_map in Hp.
             eapply sc_parent; eauto.
             2:{ pose proof (Forall2_in_left _ _ _ _ WIi Hin) as [?(?&?& H14)].
                 simpl in H14. inv H14. now apply in_map. }
             rewrite clocksof_nclocksof in Hscin.
             eapply Forall2_impl_In in Hscin; eauto. simpl. intros ?? Hinnc ??.
             rewrite Env.adds_opt'_app.
             2:{ unfold filter_anons. apply Forall2_length in Hscin.
                 now rewrite 2 map_length in *. }
             eapply sc_switch_adds'; eauto.
             intros ? Hfr Hino. apply filter_anons_spec in Hino as [Hino].
             rewrite map_map in Hino.
             rewrite <- clocksof_nclocksof in Hinnc. apply In_clocksof in Hinnc as (e&?&?).
             eapply free_clock_defined with (x := x1) (e := e) (vars := idck env0)
               in Henv as []; auto; try (now eapply Forall_forall; eauto); auto.
             2:apply Exists_exists; eauto.
             eapply NoDupMembers_app_InMembers in Hndup'. 2:eapply InMembers_fresh_in; eauto.
             apply Hndup', Ino_In_anon_streams; auto.
           - intros i i' Hfree Hisub.
             eapply wc_env_free_in_clock in WCio as [ick Hin]; eauto.
             2:{ unfold idck. rewrite map_app. apply in_or_app. right. eauto. }
             rewrite idck_app in Hin. apply in_app_or in Hin as [Hin | Hin].
             + (* i ∈ idck(n_in n) *)
               rewrite Env.adds_opt'_app.
               2: unfold filter_anons; apply Forall2_length in Hscin;
                 now rewrite clocksof_nclocksof, 2 map_length in *.
               rewrite Env.find_In_gsso_opt'.
               2:{
                 intro Hino. apply filter_anons_spec in Hino as [Hino].
                 unfold stream_name in Hino; rewrite map_map in Hino.
                 apply Forall2_in_left with (2 := Hin) in WIi as (?& Hnc & Sub &?).
                 simpl in Sub. rewrite Hisub in Sub.
                 apply in_map with (f := snd), In_snd_nclocksof in Hnc as (?&?& Hsnd).
                 rewrite <- Sub, <- Ino_In in Hsnd.
                 eapply snd_nclocks_fresh with (vars := idck env0) in Hsnd; eauto.
                 2: eapply Forall_forall; eauto.
                 eapply NoDupMembers_app_InMembers in Hndup'. 2:eapply InMembers_fresh_in; eauto.
                 apply Hndup', Ino_In_anon_streams; auto. }
               eapply inst_in_eqst; eauto. inv Hwt; auto.
             + (* i ∈ idck(n_out n) *)
               rewrite idck_idents, Forall2_map_1 in Hvout.
               pose proof (Forall2_in_left_combine  _ _ _ _ Hvout Hin) as (?&Hcomb&Hv).
               inv Hv. take (Env.MapsTo _ _ _) and apply Env.find_1 in it as Heq.
               simpl in *. erewrite Env.In_find_adds_opt'; auto. rewrite Heq; eauto.
               now take (_ ≡ _) and rewrite <- it.
               rewrite Forall2_swap_args in WIo. rewrite Forall2_map_2 in Hsemn.
               pose proof (Forall2_chain_In' _ _ _ _ _ _ _ WIo Hsemn Hcomb)
                 as ((?&?)&(Sub'&?)&?&?& Hok). simpl in *.
               unfold filter_anons. rewrite 2 combine_map_fst, in_map_iff.
               esplit; split.
               2:{ rewrite in_map_iff. esplit; split; eauto. }
               simpl. f_equal. rewrite <- Sub', Hisub. cases_eqn Hm. exfalso.
               apply mem_assoc_ident_true in Hm as (?&Hm); apply In_InMembers in Hm.
               eapply in_combine_l,in_map with (f := snd),in_map with (f := snd) in Hok.
               rewrite map_map in Hok. simpl in *.
               rewrite <- app_assoc, Permutation_swap in Hndup. rewrite InMembers_idck in Hm.
               eapply NoDupMembers_app_r, NoDupMembers_app_InMembers in Hndup; eauto.
               eapply Hndup, Ino_In_anon_streams; auto.
               rewrite <- Sub', Hisub, <- Ino_In in Hok; auto.
         }
         { (* input *)
           take (find_node _ _ = _) and eapply wc_find_node in it
             as (?&(?&?)); eauto.
           inv Hwt. eapply sc_inside; eauto.
           eapply Forall2_impl_In; eauto. intros ? Hin ???.
           eapply Forall_forall in H1; eauto.
           apply H1; auto. 3:{ eapply NoDupMembers_fresh_in'; eauto. }
           1,2:eapply Forall_forall; eauto.
           eapply sc_var_inv_weaken; eauto. simpl. intros. constructor.
           eapply Exists_exists. eauto.
         }
       + (* EAppReset *)
         assert (Hndup':=Hndup).
         eapply NoDupMembers_app_r in Hndup'.
         pose proof (nodupo_filter_anons _ _ _ Hwc Hndup') as Hnodupo.
         inversion_clear Hwc as
             [| | | | | | | | | |?????? bck sub Hwce Hfind WIi WIo Hwcr Hckr].
         inversion_clear Hsem as [| | | | | | | | |?????????? Hse Hsr Hboolsof Hsemn].

         rewrite app_assoc in Hndup.
         assert (Hndup'':=Hndup). apply NoDupMembers_app_l in Hndup''; auto.
         assert (Hse' := Hse).
         eapply sc_union_envs in Hse' as (ncs & nss & Hlen & Hncs & Hscin); eauto. 2:inv Hwt; eauto.
         2:{
           inv Hwt.
           eapply Forall2_impl_In; eauto. intros ?? Hin ??.
           pose proof Hin as He; eapply Forall_forall with (1:=H1) in He; eauto.
           apply He; auto; try (now eapply Forall_forall; eauto).
           { eapply NoDupMembers_fresh_in'; eauto. }
           eapply sc_var_inv_weaken; eauto. simpl. intros. constructor.
           right. eapply Exists_exists. eauto.
         }
         exists ((filter_anons (idck env0) (nclocksof es)) ++ ncs), ((concat ss0) ++ nss).

         split.
         { unfold filter_anons. apply Forall2_length in Hscin.
           now rewrite clocksof_nclocksof, 2 app_length, 2 map_length,
           Hlen, <- Hscin in *. }

         split.
         { apply Forall_app. split.
           apply Forall_forall. intros [x|] Hin; simpl; auto. apply Ino_In in Hin.
           apply filter_anons_spec in Hin as [Hin].
           apply Ino_In, In_snd_nclocksof in Hin as (?&?&Hin).
           eapply Ino_In, snd_nclocks_fresh in Hin; eauto.
           - apply InMembers_app, or_introl. eapply InMembers_fresh_in; eauto.
           - rewrite Forall_forall in Hwce; eauto.
           - eapply Forall_impl_In in Hncs; eauto. intros [] ??; auto; simpl in *.
             apply Exists_exists in H3 as [? [Hin Hinm]].
             apply InMembers_app, or_introl. eapply InMembers_fresh_in; eauto.
         }

         (* Taking a trip inside the node *)
         assert (forall k, exists Hi,
                      Forall2 (sem_var Hi) (idents (n_in n)) (map (mask k bs) (concat ss0)) /\
                      Forall2 (sem_var Hi) (idents (n_out n)) (map (mask k bs) ss) /\
                      Forall2 (fun xc : ident * clock =>
                                 sem_clock Hi (clocks_of (map (mask k bs) (concat ss0))) (snd xc))
                              (idck (n_out n))
                              (map abstract_clock (map (mask k bs) ss))) as Hk.
         { intros k. specialize (Hsemn k).
           inversion Hsemn as [ ???? Hi ?? Hvin Hvout ? Hsck]; subst.

           assert (Hnodes:=Hnode). specialize (Hnode _ _ _ _ _ Hsemn H2 Hvin Hvout).
           match goal with
           | H1: find_node f G = Some _, H2: find_node f G = Some _ |- _
             => rewrite H2 in H1; inv H1
           end.

           exists Hi; repeat split; auto.

           assert (Forall2 (fun xc : ident * clock => sem_clock Hi (clocks_of (map (mask k bs) (concat ss0))) (snd xc))
                           (idck (n_in n)) (map abstract_clock (map (mask k bs) (concat ss0)))) as Hf.
           { take (find_node _ _ = _) and eapply wc_find_node in it
               as (?&(?&?)); eauto.
             inv Hwt. eapply sc_inside_mask; eauto.
             eapply Forall2_impl_In; eauto. intros ? Hin ???.
             eapply Forall_forall in H1; eauto.
             apply H1; auto. 3:{ eapply NoDupMembers_fresh_in'; eauto. }
             1,2:eapply Forall_forall; eauto.
             eapply sc_var_inv_weaken; eauto. simpl. intros. constructor.
             eapply Exists_exists. exists a0; split; eauto. right; auto. }
           eapply Hnode; eauto.
         } clear Hsemn.

         (* We can push the quantifier inside Forall *)
         assert (Forall2 (fun xc s => forall k, exists Hi,
                                Forall2 (sem_var Hi) (idents (n_in n)) (map (mask k bs) (concat ss0)) /\
                                Forall2 (sem_var Hi) (idents (n_out n)) (map (mask k bs) ss) /\
                                sem_clock Hi (clocks_of (map (mask k bs) (concat ss0))) (snd xc) (abstract_clock (mask k bs s))) (idck (n_out n)) ss) as Hk'.
         { rewrite Forall2_forall2; split.
           - specialize (Hk 0) as [? [Hvin [Hvout Hf]]]. apply Forall2_length in Hf.
             apply Forall2_length in WIo.
             repeat rewrite map_length in *. congruence.
           - intros * Hn1 Hn2 Hn3 k.
             specialize (Hk k) as [Hi [Hvin [Hvout Hk]]]. exists Hi; split; auto.
             apply Forall2_forall2 in Hk as [Hlen' Hk]. repeat rewrite map_length in Hlen'.
             specialize (Hk a0 (abstract_clock b0) _ _ _ Hn1 Hn2 eq_refl).
             erewrite map_nth' with (d':=b0) in Hk. 2:rewrite map_length; congruence.
             erewrite map_nth' in Hk. 2:congruence.
             erewrite Hn3 in Hk; eauto.
         } clear Hk.

         { (* output *)
           unfold WellInstantiated in WIo. unfold clock_of_nclock, stripname.
           rewrite Forall2_map_1, Forall2_map_2. rewrite Forall2_map_2 in WIo.
           apply Forall2_swap_args in WIo.
           eapply Forall2_trans_ex with (1:=WIo) in Hk'.
           eapply Forall2_impl_In; eauto.
           intros [aty (ack & anm)] so ??((x&ck)& Hxin & (Hsub & Hinst) & Hsc).
           simpl in *.
           pose proof (wc_find_node G f n Hwcg) as [?(WCin&(WCio&?))]; eauto.
           unfold WellInstantiated in WIi.
           eapply sc_inst_mask with (b:=(clocks_of (concat ss0))) (rs:=bs) in Hinst; eauto.
           - pose proof (wc_env_has_Cbase _ WCin) as [i Hin];
               [ unfold idck; rewrite map_length; exact (n_ingt0 n) |].
             apply WellInstantiated_parent in WIi as Hp.
             change (Forall (fun ck => (fun x => x = bck \/ clock_parent bck x) (fst ck))
                            (nclocksof es)) in Hp.
             rewrite <- Forall_map in Hp.
             eapply sc_parent; eauto.
             2:{ pose proof (Forall2_in_left _ _ _ _ WIi Hin) as [?(?&?& H14)].
                 simpl in H14. inv H14. now apply in_map. }
             rewrite clocksof_nclocksof in Hscin.
             rewrite Forall2_map_2. rewrite Forall2_map_2 in Hscin.
             eapply Forall2_impl_In in Hscin; eauto. simpl. intros ?? Hinnc ??.
             rewrite Env.adds_opt'_app.
             2:{ unfold filter_anons. apply Forall2_length in Hscin.
                 now rewrite map_length in *. }
             eapply sc_switch_adds'; eauto.
             intros ? Hfr Hino. apply filter_anons_spec in Hino as [Hino].
             rewrite map_map in Hino.
             rewrite <- clocksof_nclocksof in Hinnc. apply In_clocksof in Hinnc as (e'&?&?).
             eapply free_clock_defined with (x := x1) (e := e') (vars := idck env0)
               in Henv as []; auto; try (now eapply Forall_forall; eauto); auto.
             2:apply Exists_exists; eauto.
             eapply NoDupMembers_app_InMembers in Hndup'. 2:eapply InMembers_fresh_in; eauto.
             apply Hndup'. rewrite InMembers_app. right. apply Ino_In_anon_streams; auto.
           - intros k. specialize (Hsc k) as [Hi [Hvin [Hvout Hsem]]].
             exists Hi. split.
             + now rewrite clocks_of_mask, ac_mask in Hsem.
             + intros i i' Hfree Hisub.
               eapply wc_env_free_in_clock in WCio as [ick Hin]; eauto.
               2:{ unfold idck. rewrite map_app. apply in_or_app. right. eauto. }
               rewrite idck_app in Hin. apply in_app_or in Hin as [Hin | Hin].
               * (* i ∈ idck(n_in n) *)
                 rewrite Env.adds_opt'_app.
                 2: unfold filter_anons; apply Forall2_length in Hscin;
                   now rewrite clocksof_nclocksof, 2 map_length in *.
                 rewrite Env.find_In_gsso_opt'.
                 2:{
                   intro Hino. apply filter_anons_spec in Hino as [Hino].
                   unfold stream_name in Hino; rewrite map_map in Hino.
                   apply Forall2_in_left with (2 := Hin) in WIi as (?& Hnc & Sub &?).
                   simpl in Sub. rewrite Hisub in Sub.
                   apply in_map with (f := snd), In_snd_nclocksof in Hnc as (?&?& Hsnd).
                   rewrite <- Sub, <- Ino_In in Hsnd.
                   eapply snd_nclocks_fresh with (vars := idck env0) in Hsnd; eauto.
                   2: eapply Forall_forall; eauto.
                   rewrite app_assoc in Hndup'.
                   eapply NoDupMembers_app_InMembers in Hndup'. 2:eapply InMembers_app, or_introl, InMembers_fresh_in; eauto.
                   apply Hndup', Ino_In_anon_streams; auto. }
                 eapply inst_in_eqst_mask; eauto. inv Hwt; auto.
               * (* i ∈ idck(n_out n) *)
                 rewrite idck_idents, Forall2_map_1 in Hvout.
                 pose proof (Forall2_in_left_combine  _ _ _ _ Hvout Hin) as (?&Hcomb&Hv).
                 inv Hv. take (Env.MapsTo _ _ _) and apply Env.find_1 in it as Heq.
                 rewrite combine_map_snd in Hcomb. apply in_map_iff in Hcomb as [[? ?] [Heq' Hcomb]]; inv Heq'.
                 simpl in *. erewrite Env.In_find_adds_opt'; auto. rewrite Heq; eauto.
                 { constructor. symmetry. eassumption. }
                 rewrite Forall2_swap_args in WIo.
                 pose proof (Forall2_chain_In' _ _ _ _ _ _ _ WIo Hk' Hcomb)
                   as ((?&?)&(Sub'&?)&?&?& Hok). simpl in *.
                 unfold filter_anons. rewrite 2 combine_map_fst, in_map_iff.
                 esplit; split.
                 2:{ rewrite in_map_iff. esplit; split; eauto. }
                 simpl. f_equal. rewrite <- Sub', Hisub.
                 destruct (mem_assoc_ident _ _) eqn:Hm; auto. exfalso.
                 apply mem_assoc_ident_true in Hm as (?&Hm); apply In_InMembers in Hm.
                 eapply in_combine_l,in_map with (f := snd),in_map with (f := snd) in Hok.
                 rewrite map_map in Hok. simpl in *.
                 rewrite <- app_assoc, Permutation_swap in Hndup. rewrite InMembers_idck in Hm.
                 eapply NoDupMembers_app_r, NoDupMembers_app_InMembers in Hndup; eauto.
                 eapply Hndup. rewrite InMembers_app. right. apply Ino_In_anon_streams; auto.
                 rewrite <- Sub', Hisub, <- Ino_In in Hok; auto.
         }
  Qed.

  Lemma extract_sc:
    forall H b cenv x xs ys ss e ck,
      Forall2 (sem_var H) xs ys ->
      Forall2 (sem_clock H b) (clockof e) (map abstract_clock ys) ->
      Forall2 (fun x ck => In (x, ck) cenv) xs (clockof e) ->
      NoDupMembers cenv ->
      In x xs ->
      In (x, ck) cenv ->
      sem_var H x ss ->
      sem_clock H b ck (abstract_clock ss).
  Proof.
    intros * Hl1 Hse HFin1 Hndup Hin Hfind Hsemv.
    revert dependent ys. revert HFin1.
    generalize (clockof e).
    induction xs; intros; inv Hin.
    + inv Hl1. simpl in *. inv Hse. inv HFin1.
      assert (Hin := H9).
      eapply sem_var_det in Hsemv; eauto.
      eapply NoDupMembers_det in Hfind; eauto.
      rewrite <- Hfind, <- Hsemv; auto.
    + inv Hl1. simpl in *. inv Hse. inv HFin1. eapply IHxs; eauto.
  Qed.

  Lemma sc_equation :
    forall G H b x cenv ck eq ss,
      wt_equation G (idty cenv) eq ->
      wc_equation G (idck cenv) eq ->
      sem_equation G H b eq ->
      wc_global G ->
      wc_env (idck cenv) ->
      In x (fst eq) ->
      NoDupMembers (cenv ++ anon_in_eq eq) ->
      sc_var_inv (fun x => Exists (fun e => LCA.Is_free_left x e) (snd eq)) (idck cenv) H b ->
      sem_var H x ss ->
      In (x, ck) (idck cenv) ->
      sc_nodes G ->
      sem_clock H b ck (abstract_clock ss).
  Proof.
    intros * Hwt Hwc Hsemeq Hwcg Henvs Hin Hndup Hinv Hsemv Hfind Hnode.
    destruct eq as [xs es]. simpl in Hin.
    destruct Hwc as (Hwceq & Hlifto & HFin).
    destruct Hwt as (Hwt & _).

    inv Hsemeq. revert dependent ss0. revert dependent xs.
    induction es as [| e]; intros. inv H5. inv H6. now inv Hin.
    inversion H5 as [| ? ys ba yss Hse Hf2]. subst. simpl in *.
    apply Forall2_app_inv_r in H6. destruct H6 as (l1 & l2 & Hl1 & Hl2 & Hxs).
    subst.
    inversion_clear Hwceq as [| ?? Hwc].
    apply Forall2_app_split in HFin.
    2:{ apply Forall2_length in Hl1. rewrite Hl1.
        symmetry. eapply length_clockof; eauto. }
    apply Forall2_app_split in Hlifto.
    2:{ apply Forall2_length in Hl1. rewrite Hl1.
        symmetry. rewrite nclockof_length. eapply length_clockof; eauto. }
    destruct HFin as [HFin1 HFin2]. destruct Hlifto as [Hlifto1 Hlifto2].
    apply in_app_iff in Hin. destruct Hin as [Hin|].
    - unfold anon_in_eq, anon_ins in Hndup; simpl in Hndup.
      rewrite app_assoc in Hndup; apply NoDupMembers_app_l in Hndup.
      clear dependent l2. clear IHes. rename l1 into xs. inv Hwt.
      assert (NoDupMembers (idck cenv)) as Hndup'.
      { apply NoDupMembers_app_l in Hndup. apply NoDupMembers_idck; auto. }
      destruct e.
      1-8:(eapply sc_exp in Hse; eauto using extract_sc;
           eapply sc_var_inv_weaken; eauto; intros; simpl; left; eauto).
      (* Eapp case, we can't use sc_exp directly because
         we don't have DisjointFresh at top-level *)
      eapply extract_sc; eauto.
      inv Hse.
      + take (sem_node _ _ _ _) and inversion it; subst.
        inversion_clear Hwc as [| | | | | | | | |???? bck sub Wce ? WIi WIo|].
        match goal with
        | H1: find_node _ G = Some _, H2: find_node _ G = Some _ |- _
          => rewrite H2 in H1; inv H1
        end. simpl in *.
        unfold sc_nodes in Hnode.
        take (sem_node _ _ _ _) and eapply Hnode in it as Hsco; eauto.
        { (* output *)
          rename es into es'. rename l into es. clear Hin. rename i into f.
          assert (Hndup'' := Hndup). inv H3.
          eapply sc_union_envs in Hndup'' as (ncs & nss & Hlen & Hncs & Hscin); eauto.
          2:{ eapply Forall2_impl_In; eauto. intros ???? Hse.
              eapply sc_exp in Hse; eauto;
                try (now eapply Forall_forall; eauto).
              { eapply NoDupMembers_fresh_in'; eauto. }
              eapply sc_var_inv_weaken; eauto. intros. simpl. constructor.
              constructor. apply Exists_exists; eauto. }

          (* forall k, exists xss, sem_clock _ xss /\ (maskb _ _ xss) == abstract_clock (mask _ _ ys) ->
             sem_clock _ ys *)

          unfold WellInstantiated in WIo. unfold clock_of_nclock, stripname.
          rewrite Forall2_map_1. rewrite Forall2_map_2 in WIo.
          apply Forall2_swap_args in WIo.
          apply Forall2_trans_ex with (1 := WIo) in Hsco.
          eapply Forall2_impl_In; eauto.
          intros [aty (ack & anm)] so Hl0 ?((x'&ck')& Hxin & (Hsub & Hinst) & Hsc).
          simpl in *.
          pose proof (wc_find_node G f n Hwcg) as [?(WCin&(WCio&?))]; eauto.
          eapply sc_inst; eauto.
          - pose proof (wc_env_has_Cbase _ WCin) as [i Hin];
              [ unfold idck; rewrite map_length; exact (n_ingt0 n) |].
            apply WellInstantiated_parent in WIi as Hp.
            change (Forall (fun ck => (fun x => x = bck \/ clock_parent bck x) (fst ck))
                           (nclocksof es)) in Hp.
            rewrite <- Forall_map in Hp. eapply sc_parent in Hp.
            2: rewrite <- clocksof_nclocksof; eauto.
            2:{ pose proof (Forall2_in_left _ _ _ _ WIi Hin) as [?(?&?& H42)].
                simpl in H42. inv H42. now apply in_map. }
            assert (forall x, Is_free_in_clock x bck -> InMembers x cenv). {
              intros ? Hfree. eapply instck_free_bck in Hfree; eauto.
              rewrite Forall2_map_2 in HFin1.
              eapply Forall2_in_right with (2 := Hl0) in HFin1 as (?&?&HH).
              unfold clock_of_nclock, stripname in HH. simpl in HH.
              eapply wc_env_free_in_clock in HH as []; eauto. eapply In_InMembers, InMembers_idck in H11; eauto.
            }
            apply sc_switch_adds in Hp.
            2: { intros ?? Hino; apply filter_anons_spec in Hino as []; eauto.
                 rewrite InMembers_idck in H19; eauto. }
            apply sc_switch_adds in Hp.
            2:{ intros ?? Hino.
                eapply Ino_Forall in Hino; eauto. simpl in Hino.
                apply Exists_exists in Hino as (?&?&Hf).
                eapply H10 in H11.
                eapply NoDupMembers_app_InMembers in Hndup; eauto.
                eapply InMembers_fresh_in in Hf; eauto.
            }
            assumption.
          - intros i i' Hfree Hisub.
            assert (InMembers i' cenv) as Hinm. {
              pose proof (Forall2_in_right _ _ _ _ WIo Hxin)
                as ((?&?)& Hin&?& Inst). simpl in *.
              pose proof (instck_free_sub _ _ _ _ _ _ Inst Hfree Hisub).
              rewrite Forall2_map_2 in HFin1.
              eapply Forall2_in_right with (2 := Hin) in HFin1 as (?&?&HH).
              unfold clock_of_nclock, stripname in HH. simpl in HH.
              eapply wc_env_free_in_clock in HH as []; eauto. eapply In_InMembers, InMembers_idck in H19; eauto.
            }
            eapply wc_env_free_in_clock in WCio as [ick Hin]; eauto.
            2:{ unfold idck. rewrite map_app. apply in_or_app. right. eauto. }
            rewrite idck_app in Hin. apply in_app_or in Hin as [Hin | Hin].
            + (* i ∈ idck(n_in n) *)
              eapply inst_in_eqst with (env := cenv) (nss := nss) in Hin; eauto.
              rewrite Env.find_In_gsso_opt' in Hin.
              2: { intro HH; apply filter_anons_spec in HH as []; eauto.
                   rewrite InMembers_idck in H11; eauto. }
              rewrite Env.find_In_gsso_opt' in Hin.
              2:{ intro Hino.
                  eapply Ino_Forall in Hino; eauto. simpl in Hino.
                  apply Exists_exists in Hino as (?&?&Hf).
                  eapply NoDupMembers_app_InMembers in Hndup; eauto.
                  eapply InMembers_fresh_in in Hf; eauto. }
              assumption.
            + (* i ∈ idck(n_out n) *)
              rename H7 into Hvout.
              rewrite idck_idents, Forall2_map_1 in Hvout.
              apply Forall2_swap_args in Hl1.
              eapply Forall2_trans_ex with (1 := Hvout) in Hl1.
              eapply Forall2_trans_ex with (1 := Hl1) in Hlifto1.
              rewrite Forall2_map_2 in Hlifto1.
              apply Forall2_swap_args in WIo.
              pose proof (Forall2_in_left_combine  _ _ _ _ WIo Hin)
                as (?& Comb & Sub &?).
              eapply Forall2_In with (1 := Comb) in Hlifto1
                as (?&?&(s &?&?&?)& Heq).
              simpl in *. rewrite <- Sub, Hisub in Heq. simpl in Heq. subst.
              do 2 take (sem_var _ _ _) and inv it.
                 do 2 take (Env.MapsTo _ _ _) and apply Env.find_1 in it as ->.
                    constructor. transitivity s; auto. now symmetry.
        }
        { (* input *)
          take (find_node _ _ = _) and pose proof
               (wc_find_node _ _ _ Hwcg it) as (?&(?&?)); eauto.
          inv H3. eapply sc_inside with (es := l) (env := cenv); eauto.
          eapply Forall2_impl_In; eauto. intros ???? Hsem.
          eapply sc_exp in Hsem; eauto;
            try now (eapply Forall_forall; eauto).
          { eapply NoDupMembers_fresh_in'; eauto. }
          eapply sc_var_inv_weaken; eauto. simpl. intros. constructor.
          constructor. apply Exists_exists; eauto.
        }
      + rename i into f.
        rename H3 into Hwt.
        rename H15 into Hsemn.
        inversion_clear Hwc as
            [| | | | | | | | | |?????? bck sub Hwce ? WIi WIo Hwcr Hckr].

        assert (Hndup'':=Hndup); simpl in Hndup''. rewrite app_assoc in Hndup''. apply NoDupMembers_app_l in Hndup''.
        assert (Hse':=H11).
        eapply sc_union_envs in H11 as (ncs & nss & Hlen & Hncs & Hscin); eauto. 2,3:inv Hwt; eauto.
        2:{ eapply Forall2_impl_In; eauto. intros ???? Hse.
            eapply sc_exp in Hse; eauto;
              try (now eapply Forall_forall; eauto).
            { eapply NoDupMembers_fresh_in'; eauto. }
            eapply sc_var_inv_weaken; eauto. intros. simpl. constructor.
            constructor. right. apply Exists_exists; eauto. }

         (* Taking a trip inside the node *)
         assert (forall k, exists Hi,
                      Forall2 (sem_var Hi) (idents (n_in n)) (map (mask k bs) (concat ss0)) /\
                      Forall2 (sem_var Hi) (idents (n_out n)) (map (mask k bs) ys) /\
                      Forall2 (fun xc : ident * clock => sem_clock Hi (clocks_of (map (mask k bs) (concat ss0))) (snd xc)) (idck (n_out n)) (map abstract_clock (map (mask k bs) ys))) as Hk.
         { intros k. specialize (Hsemn k).
           inversion Hsemn as [ ???? Hi ?? Hvin Hvout ? Hsck]; subst.

           assert (Hnodes:=Hnode). specialize (Hnode _ _ _ _ _ Hsemn H2 Hvin Hvout).
           match goal with
           | H1: find_node f G = Some _, H2: find_node f G = Some _ |- _
             => rewrite H2 in H1; inv H1
           end.

           exists Hi; split; auto.

           assert (Forall2 (fun xc : ident * clock => sem_clock Hi (clocks_of (map (mask k bs) (concat ss0))) (snd xc))
                           (idck (n_in n)) (map abstract_clock (map (mask k bs) (concat ss0)))) as Hf.
           { take (find_node _ _ = _) and eapply wc_find_node in it
               as (?&(?&?)); eauto.
             inv Hwt. eapply sc_inside_mask; eauto.
             eapply Forall2_impl_In; eauto. intros ???? Hsem.
             eapply sc_exp in Hsem; eauto;
            try now (eapply Forall_forall; eauto).
             { eapply NoDupMembers_fresh_in'; eauto. }
             eapply sc_var_inv_weaken; eauto. simpl. intros. constructor.
             constructor. right. apply Exists_exists; eauto.
           }
           eapply Hnode in Hf; eauto.
         }

         (* We can push the quantifier inside Forall *)
         assert (Forall2 (fun xc s => forall k, exists Hi,
                                Forall2 (sem_var Hi) (idents (n_in n)) (map (mask k bs) (concat ss0)) /\
                                Forall2 (sem_var Hi) (idents (n_out n)) (map (mask k bs) ys) /\
                                sem_clock Hi (clocks_of (map (mask k bs) (concat ss0))) (snd xc) (abstract_clock (mask k bs s))) (idck (n_out n)) ys) as Hk'.
         { rewrite Forall2_forall2; split.
           - specialize (Hk 0) as [? [Hvin [Hvout Hf]]]. apply Forall2_length in Hf.
             apply Forall2_length in WIo.
             repeat rewrite map_length in *. congruence.
           - intros * Hn1 Hn2 Hn3 k.
             specialize (Hk k) as [Hi [Hvin [Hvout Hk]]]. exists Hi; split; auto.
             apply Forall2_forall2 in Hk as [Hlen' Hk]. repeat rewrite map_length in Hlen'.
             specialize (Hk a (abstract_clock b0) _ _ _ Hn1 Hn2 eq_refl).
             erewrite map_nth' with (d':=b0) in Hk. 2:rewrite map_length; congruence.
             erewrite map_nth' in Hk. 2:congruence.
             erewrite Hn3 in Hk; eauto.
         } clear Hk.

         { (* output *)
           unfold WellInstantiated in WIo. unfold clock_of_nclock, stripname.
           simpl. rewrite Forall2_map_1, Forall2_map_2. rewrite Forall2_map_2 in WIo.
           apply Forall2_swap_args in WIo.
           eapply Forall2_trans_ex with (1:=WIo) in Hk'.
           eapply Forall2_impl_In; eauto.
           intros [aty (ack & anm)] so ??((?&?)& Hxin & (Hsub & Hinst) & Hsc).
           simpl in *.
           pose proof (wc_find_node G f n Hwcg) as [?(WCin&(WCio&?))]; eauto.
           unfold WellInstantiated in WIi.
           eapply sc_inst_mask in Hinst; eauto.
           2:{ intros k. specialize (Hsc k) as [Hi [Hvin [Hvout Hsem]]].
               exists Hi. split.
               - rewrite clocks_of_mask, ac_mask in Hsem. eassumption.
               - intros i'' i' Hfree Hisub.
                 assert (InMembers i' cenv) as Hinm. {
                   pose proof (Forall2_in_right _ _ _ _ WIo Hxin)
                     as ((?&?)& Hin'&?& Inst). simpl in *.
                   pose proof (instck_free_sub _ _ _ _ _ _ Inst Hfree Hisub).
                   rewrite Forall2_map_2 in HFin1.
                   eapply Forall2_in_right with (2 := Hin') in HFin1 as (?&?&HH).
                   unfold clock_of_nclock, stripname in HH. simpl in HH.
                   eapply wc_env_free_in_clock in HH as []; eauto. eapply In_InMembers, InMembers_idck in H10; eauto.
                 }
                 eapply wc_env_free_in_clock in WCio as [ick Hin']; eauto.
                 2:{ unfold idck. rewrite map_app. apply in_or_app. right. eauto. }
                 rewrite idck_app in Hin'. apply in_app_or in Hin' as [Hin' | Hin'].
                 + (* i'' ∈ idck(n_in n) *)
                   eapply inst_in_eqst_mask with (es:=l) (env:=cenv) (nss:=nss) in Hin'; eauto. 2:inv Hwt; auto.
                   rewrite Env.find_In_gsso_opt' in Hin'.
                   2: { intro HH; apply filter_anons_spec in HH as []; eauto.
                        rewrite InMembers_idck in H8; eauto. }
                   rewrite Env.find_In_gsso_opt' in Hin'; auto.
                   intro Hino.
                   eapply Ino_Forall in Hino; eauto. simpl in Hino.
                   apply Exists_exists in Hino as (?&?&Hf).
                   eapply NoDupMembers_app_InMembers in Hndup; eauto.
                   eapply InMembers_fresh_in in Hf; eauto.
                   eapply Hndup. rewrite InMembers_app; auto.

                 + (* i ∈ idck(n_out n) *)
                   rewrite idck_idents, Forall2_map_1 in Hvout.
                   apply Forall2_swap_args in Hl1.
                   rewrite Forall2_map_2 in Hvout. eapply Forall2_trans_ex with (1 := Hvout) in Hl1.
                   eapply Forall2_trans_ex with (1 := Hl1) in Hlifto1.
                   rewrite Forall2_map_2 in Hlifto1.
                   apply Forall2_swap_args in WIo.
                   pose proof (Forall2_in_left_combine  _ _ _ _ WIo Hin')
                     as (?& Comb & Sub &?).
                   eapply Forall2_In with (1 := Comb) in Hlifto1
                     as (?&?&(s &?&?&?)& Heq).
                   simpl in *. rewrite <- Sub, Hisub in Heq. simpl in Heq. subst.
                   do 2 take (sem_var _ _ _) and inv it.
                      rewrite H12, H11. constructor.
                      rewrite H15 in H16. symmetry; auto.
           }
           - pose proof (wc_env_has_Cbase _ WCin) as [i' Hin'];
              [ unfold idck; rewrite map_length; exact (n_ingt0 n) |].
            apply WellInstantiated_parent in WIi as Hp.
            change (Forall (fun ck => (fun x => x = bck \/ clock_parent bck x) (fst ck))
                           (nclocksof l)) in Hp.
            rewrite <- Forall_map in Hp. eapply sc_parent in Hp.
            2: rewrite <- clocksof_nclocksof; eauto.
            2:{ pose proof (Forall2_in_left _ _ _ _ WIi Hin') as [?(?&?& H42)].
                simpl in H42. inv H42. now apply in_map. }
            assert (forall x, Is_free_in_clock x bck -> InMembers x cenv). {
              intros ? Hfree. eapply instck_free_bck in Hfree; eauto.
              rewrite Forall2_map_2 in HFin1.
              eapply Forall2_in_right with (2 := H2) in HFin1 as (?&?&HH).
              unfold clock_of_nclock, stripname in HH. simpl in HH.
              eapply wc_env_free_in_clock in HH as []; eauto. eapply In_InMembers, InMembers_idck in H8; eauto.
            }
            apply sc_switch_adds in Hp.
            2: { intros ?? Hino; apply filter_anons_spec in Hino as []; eauto.
                 rewrite InMembers_idck in H10; eauto. }
            apply sc_switch_adds in Hp.
            2:{ intros ?? Hino.
                eapply Ino_Forall in Hino; eauto. simpl in Hino.
                apply Exists_exists in Hino as (?&?&Hf).
                eapply H7 in H8.
                eapply NoDupMembers_app_InMembers in Hndup; eauto.
                eapply InMembers_fresh_in in Hf; eauto.
                apply Hndup. rewrite InMembers_app; auto.
            }
            assumption.
         }
    - inv Hwt. eapply IHes; eauto.
      { unfold anon_in_eq, anon_ins in *; simpl in *.
        rewrite Permutation_swap in Hndup. apply NoDupMembers_app_r in Hndup; auto. }
      eapply sc_var_inv_weaken; eauto. intros. simpl. right. auto.
  Qed.

  Lemma wc_free_clock :
    forall x ck vars,
      wc_clock vars ck ->
      Is_free_in_clock x ck ->
      In x (map fst vars).
  Proof.
    intros * Hwc Hfree. induction ck; inv Hfree; inv Hwc; auto.
    now apply in_map with (f := fst) in H3.
  Qed.

  (* Extract the [sc_var_inv] invariant for defined variables (out + vars)
     from the causality of the node and the sem_clock of inputs. *)
  Lemma causal_variables :
    forall G n H xs H0,
      sc_nodes G ->
      Lord.Ordered_nodes G ->
      wt_global G ->
      wc_global G ->
      Forall2 (fun xc : ident * clock => sem_clock H (clocks_of xs) (snd xc))
              (idck (n_in n)) (map abstract_clock xs) ->
      Forall2 (sem_var H) (idents (n_in n)) xs ->
      Forall2 (sem_var H0) (idents (n_in n)) xs ->
      wc_env (idck (n_in n)) ->
      wc_env (idck (n_in n ++ n_out n ++ n_vars n)) ->
      LCA.node_causal n ->
      Forall (sem_equation G H0 (clocks_of xs)) (n_eqs n) ->
      Forall (wt_equation G (idty (n_in n ++ n_vars n ++ n_out n))) (n_eqs n) ->
      Forall (wc_equation G (idck (n_in n ++ n_vars n ++ n_out n))) (n_eqs n) ->
      Forall
        (fun x : ident => forall (ss : Stream value) (ck : clock),
             sem_var H0 x ss ->
             In (x, ck) (idck (n_in n ++ n_vars n ++ n_out n)) ->
             sem_clock H0 (clocks_of xs) ck (abstract_clock ss))
        (vars_defined (n_eqs n)).
  Proof.
    intros * Hscn Hord Hwcg Hwtg Hscin Hinv Hins Hwcin Hwcenv Hcaus Heqs Hwteq Hwceq.
    destruct Hcaus as [eqs (Hperm & Hcausal)].
    rewrite Hperm in Heqs, Hwteq, Hwceq.
    assert (Forall (fun e => NoDupMembers (n_in n ++ n_vars n ++ n_out n ++ anon_in_eq e)) eqs) as Hndup'.
    { rewrite Forall_forall. intros e Hin.
      assert (Hndup':=(n_nodup n)).
      unfold anon_in_eqs in Hndup'; rewrite Hperm in Hndup'.
      repeat rewrite app_assoc. eapply NoDupMembers_anon_in_eq'; eauto.
      repeat rewrite <- app_assoc; eauto. }
    unfold vars_defined. setoid_rewrite Hperm. clear Hperm.

    induction eqs as [| e]; inv Hwteq; inv Hwceq; inv Heqs;
      inversion_clear Hcausal as [| ?? Hcaus Hor]; simpl; auto.
    apply Forall_app; split; auto. eapply Forall_forall.
    intros z Hin zs ck Hsemz Hfind. eapply sc_equation; eauto.
    eapply wc_env_Proper; try eassumption. unfold idck. rewrite 4 map_app.
    now apply Permutation_app_head, Permutation_app_comm.
    { inv Hndup'. repeat rewrite <- app_assoc; auto. }
    2: { inv Hndup'; eauto. }
    intros y Hfree cky ys Iny Semy.
    pose proof (Hor y Hfree) as [Hydef | Hyin].
    - eapply IHeqs in Hcaus; eauto. eapply Forall_forall in Hcaus; eauto.
      inv Hndup'; auto.
    - unfold idents, idck in Hscin, Hins, Hinv.
      rewrite Forall2_map_1 in Hins, Hinv.
      rewrite Forall2_map_1, Forall2_map_2 in Hscin.
      apply in_map_iff in Hyin
        as ((y' & (yt & yc)) & (Hyy' & Hyin)). simpl in Hyy'. inv Hyy'.
      eapply Forall2_Forall2 with (2 := Hins) in Hscin as Hscsv.
      eapply Forall2_in_left in Hscsv as (ys'&?&?&?); eauto. simpl in *.
      eapply sem_var_det in Semy; eauto.
      rewrite <- Semy. assert (Hyck := Hyin).
      apply in_app_weak with (l' := n_vars n) in Hyin.
      apply in_app_weak with (l' := n_out n) in Hyin.
      rewrite <- app_assoc in Hyin. unfold idck in Iny.
      apply in_map_iff in Iny as ((?&?)& HP & Hcky).
      destruct p. simpl in *. inv HP.
      eapply NoDupMembers_det in Hcky; eauto using (n_nodup n). inv Hcky.
      eapply sc_switch_env; eauto. intros x0 Hf.
      apply in_map with (f := fun xtc => (fst xtc, snd (snd xtc))) in Hyck.
      simpl in *. apply wc_env_var in Hyck; auto.
      eapply wc_free_clock in Hyck; eauto.
      apply Forall2_Forall2 with (1 := Hinv) in Hins.
      rewrite map_map in Hyck. apply in_map_iff in Hyck as ((?&?)&Heq&?).
      simpl in *. inv Heq.
      eapply Forall2_in_left in Hins as (?&?& V1 & V2); eauto.
      inversion_clear V1 as [???? a w]. inversion_clear V2 as [???? a' w'].
      now rewrite a, a', <- w, <- w'.
      specialize (n_nodup n) as Hndup.
      repeat rewrite app_assoc in *. apply NoDupMembers_app_l in Hndup; auto.
  Qed.

  Theorem l_sem_node_clock :
    forall G,
      Forall LCA.node_causal G ->
      Lord.Ordered_nodes G ->
      wt_global G ->
      wc_global G ->
      sc_nodes G.
  Proof.
    unfold sc_nodes.
    induction G as [|node]. now inversion 5.
    intros Hcaus Hord Hwt Hwc ????? Hsem Hfind Hinv Houtv Hscin. assert (Hsem' := Hsem).
    pose proof (Lord.find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    inversion_clear Hsem' as [? ? ? ? ? ? Hfind' Hins Houts Heqs Hbk].
    simpl in Hfind. destruct (ident_eqb (n_name node) f) eqn:Hnf.
    - inv Hfind. simpl in Hfind'. rewrite Hnf in Hfind'. inv Hfind'.
      eapply Forall_sem_equation_global_tl in Heqs; eauto.
      inversion_clear Hord as [|? ? Hord'' Hnneqs Hnn].
      inversion_clear Hwc as [|?? Hwcg Hwcn]. destruct Hwcn as (Hwcin & Hwcio &?& Hwceq).
      inversion_clear Hwt as [|?? Hwtg Hwtn]. destruct Hwtn as (Hwtin & Hwtio &?& Hwteq).

      assert (Houts' := Houts). unfold idents in Houts. unfold idck.
      rewrite Forall2_map_1 in Houts. rewrite Forall2_map_1, Forall2_map_2.
      eapply Forall2_impl_In; eauto. intros (y & ?) ys Hiny ? Hsvy.
      simpl in *.

      inv Hcaus.
      assert (Hsc:=H8).
      eapply causal_variables in Hsc; eauto.

      unfold vars_defined in Hsc.
      eapply (Forall_forall) in Hsc; eauto.
      2:{ rewrite (n_defd n0). rewrite map_app, in_app. right.
          rewrite in_map_iff. exists (y,p). eauto. }

      destruct p as [ty ck]. simpl.
      assert (In (y, ck) (idck (n_in n0 ++ n_vars n0 ++ n_out n0))) as HIn.
      { unfold idck. rewrite in_map_iff. exists (y, (ty, ck)).
        split; auto. repeat (apply in_or_app; right; auto). }
      specialize (Hsc ys ck Hsvy HIn).
      eapply sc_switch_env; eauto. intros x0 Hf.
      eapply in_app_weak in Hiny as Hx0. apply in_app_comm in Hx0.
      apply in_map with (f := fun xtc => (fst xtc, snd (snd xtc))) in Hx0.
      simpl in *. apply wc_env_var in Hx0; eauto.
      eapply wc_free_clock in Hx0; eauto.
      apply Forall2_Forall2 with (1 := Hinv) in Hins.
      apply Forall2_Forall2 with (1 := Houtv) in Houts'.
      unfold idents in Hins, Houts'. rewrite Forall2_map_1 in Hins, Houts'.
      rewrite map_map in Hx0. apply in_map_iff in Hx0 as ((?&?)&Heq& Hx0).
      simpl in *. inv Heq.
      apply in_app_iff in Hx0 as [Hin|Hin];
        [ eapply Forall2_in_left in Hins as (?&?& V1 & V2)
        | eapply Forall2_in_left in Houts' as (?&?& V1 & V2)]; eauto;
          inversion_clear V1 as [???? t u]; inversion_clear V2 as [???? v w];
            inversion t as [Eq1]; inversion v as [Eq2];
            now rewrite Eq1, Eq2, <- u, <- w.
    - apply ident_eqb_neq in Hnf.
      eapply sem_node_cons in Hsem; auto.
      rewrite cons_is_app in Hord.
      apply Lord.Ordered_nodes_append in Hord.
      inv Hwt. inv Hwc. inv Hcaus. eapply IHG; eauto.
  Qed.

  (* We can also get the semantics for the clocks of internal variables.
     But we have to open sem_node for that *)
  Definition sc_node' (G : global) (n : node) : Prop :=
    forall H xs vs os,
      Forall2 (sem_var H) (idents (n_in n)) xs ->
      Forall2 (sem_var H) (idents (n_vars n)) vs ->
      Forall2 (sem_var H) (idents (n_out n)) os ->
      Forall (sem_equation G H (clocks_of xs)) (n_eqs n) ->
      Forall2 (fun xc => sem_clock H (clocks_of xs) (snd xc))
              (idck (n_in n)) (map abstract_clock xs) ->
      Forall2 (fun xc => sem_clock H (clocks_of xs) (snd xc))
              (idck (n_vars n)) (map abstract_clock vs) /\
      Forall2 (fun xc => sem_clock H (clocks_of xs) (snd xc))
              (idck (n_out n)) (map abstract_clock os).

  Lemma sc_node'_global_tl : forall G n,
      Ordered_nodes (n::G) ->
      sc_node' (n::G) n ->
      sc_node' G n.
  Proof.
    intros * Hord Hsc.
    unfold sc_node' in *.
    intros. eapply Hsc; eauto.
    apply Forall_sem_equation_global_tl'; auto.
    eapply find_node_not_Is_node_in with (f:=n_name n); eauto.
    simpl. rewrite ident_eqb_refl; auto.
  Qed.

  Theorem l_sem_node_clock' : forall G n,
      Forall LCA.node_causal G ->
      Lord.Ordered_nodes G ->
      wt_global G ->
      wc_global G ->
      In n G ->
      sc_node' G n.
  Proof.
    intros * Hcaus Hord Hwt Hwc Hin.
    specialize (wt_global_Forall _ Hwt) as Hwt'.
    specialize (wc_global_Forall _ Hwc) as Hwc'.
    assert (NoDupMembers (n_in n ++ n_vars n ++ n_out n)) as Hndup.
    { specialize (n_nodup n) as Hndup.
      repeat rewrite app_assoc in *. apply NoDupMembers_app_l in Hndup; auto. }
    assert (sc_nodes G) as Hsc by (eapply l_sem_node_clock; eauto).
    unfold sc_node'. intros * Hinv Hvarsv Houtv Heqs Hins.
    eapply causal_variables in Hord; eauto.
    4: (eapply Forall_forall in Hin; eauto).
    4: (eapply Forall_forall in Hwt' as (?&?&?&?); eauto).
    2,3,4: (eapply Forall_forall in Hwc' as (?&?&?&?); eauto).
    rewrite n_defd, map_app, Forall_app in Hord. destruct Hord as [Hsemc1 Hsemc2].
    rewrite Forall_map in Hsemc1, Hsemc2.
    unfold idents in Hvarsv, Houtv. rewrite Forall2_map_1 in Hvarsv, Houtv.
    split; unfold idck; rewrite Forall2_map_1, Forall2_map_2;
      eapply Forall2_impl_In; eauto; intros [? [? ?]] ? ? ? ?; simpl in *.
    - eapply Forall_forall in Hsemc1; eauto; simpl in *.
      eapply Hsemc1; eauto.
      unfold idck; rewrite in_map_iff. exists (i, (t, c)); split; auto.
      apply in_or_app, or_intror, in_or_app, or_introl, H0.
    - eapply Forall_forall in Hsemc2; eauto; simpl in *.
      eapply Hsemc2; eauto.
      unfold idck; rewrite in_map_iff. exists (i, (t, c)); split; auto.
      apply in_or_app, or_intror, in_or_app, or_intror, H0.
  Qed.

  Definition sc_var_inv' env H b :=
    Forall (fun '(x, ck) => exists ss, (sem_var H x ss /\ sem_clock H b ck (abstract_clock ss))) env.

  Fact sc_var_inv'_refines : forall env H H' b,
      Env.refines eq H H' ->
      sc_var_inv' env H b ->
      sc_var_inv' env H' b.
  Proof.
    intros * Href Hsc.
    unfold sc_var_inv' in *.
    eapply Forall_impl; eauto.
    intros [id ck] [ss [Hsemv Hsemc]].
    exists ss. split; [eapply sem_var_refines|eapply sem_clock_refines]; eauto.
  Qed.

  Lemma sc_node_sc_var_inv : forall G n H xs,
      sc_node' G n ->
      Forall2 (sem_var H) (idents (n_in n)) xs ->
      Forall2 (fun xc => sem_clock H (clocks_of xs) (snd xc)) (idck (n_in n)) (map abstract_clock xs) ->
      Forall (sem_equation G H (clocks_of xs)) (n_eqs n) ->
      sc_var_inv' (idck (n_in n ++ n_vars n ++ n_out n)) H (clocks_of xs).
  Proof.
    intros * Hnode Hin Hinc Heqs. unfold sc_node' in Hnode.
    assert (Heqs':=Heqs).
    eapply sem_node_sem_vars_outs in Heqs' as [[vs Hvars] [os Hout]]. 2:eapply n_defd.
    unfold sc_var_inv'.
    specialize (Hnode _ _ _ _ Hin Hvars Hout Heqs Hinc) as [Hvarsc Houtc]. clear Heqs.
    unfold idck, idents in *. rewrite Forall2_map_1, Forall2_map_2 in Hinc, Hvarsc, Houtc.
    rewrite Forall2_map_1 in Hin, Hvars, Hout. rewrite Forall_map.
    eapply Forall2_Forall2 in Hin; eauto. clear Hinc.
    eapply Forall2_Forall2 in Hvars; eauto. clear Hvarsc.
    eapply Forall2_Forall2 in Hout; eauto. clear Houtc.
    eapply Forall2_app in Hout; [|eapply Hvars]. eapply Forall2_app in Hout; [|eapply Hin].
    clear Hin Hvars.
    eapply Forall2_ignore2 in Hout.
    eapply Forall_impl; eauto; intros; simpl in *.
    destruct H0 as [y [_ [? ?]]]. exists y; auto.
  Qed.

  (** Now, we can use this conclusion to write a simpler version of sc_exp *)

  Lemma sc_var_inv'_sc_var_inv : forall D H b env,
      sc_var_inv' env H b ->
      sc_var_inv D env H b.
  Proof.
    intros * Hinv.
    unfold sc_var_inv', sc_var_inv in *.
    intros ? _ ck xs Hin Hsem.
    eapply Forall_forall in Hin; eauto; simpl in *.
    destruct Hin as [? [Hsem' ?]]; eauto.
    eapply sem_var_det in Hsem; eauto.
    rewrite Hsem in H0; auto.
  Qed.

  Lemma sc_exp' :
    forall G H b env e ss,
      wc_global G ->
      sc_nodes G ->
      NoDupMembers (env ++ fresh_in e) ->
      wc_env (idck env) ->
      wt_exp G (idty env) e ->
      wc_exp G (idck env) e ->
      sem_exp G H b e ss ->
      sc_var_inv' (idck env) H b ->
      match e with
      | Eapp f es _ anns =>
        exists ncs nss,
        length ncs = length nss /\
        Forall (LiftO True (fun x => InMembers x (fresh_in e))) ncs /\
        let H := Env.adds_opt' ncs nss H in
        let H := Env.adds_opt' (filter_anons (idck env) (map snd anns)) ss H in
        Forall2 (sem_clock H b) (clockof e) (map abstract_clock ss)
      | _ =>
        Forall2 (sem_clock H b) (clockof e) (map abstract_clock ss)
      end.
  Proof with eauto.
    intros. eapply sc_exp; eauto.
    eapply sc_var_inv'_sc_var_inv; eauto.
  Qed.

  Corollary sc_exps' : forall G H b env es ss,
      wc_global G ->
      sc_nodes G ->
      NoDupMembers (env ++ fresh_ins es) ->
      wc_env (idck env) ->
      Forall (wt_exp G (idty env)) es ->
      Forall (wc_exp G (idck env)) es ->
      Forall2 (sem_exp G H b) es ss ->
      sc_var_inv' (idck env) H b ->
      Forall2 (fun e ss =>
                 match e with
                 | Eapp f es _ anns =>
                   exists ncs nss,
                   length ncs = length nss /\
                   Forall (LiftO True (fun x => InMembers x (fresh_in e))) ncs /\
                   let H := Env.adds_opt' ncs nss H in
                   let H := Env.adds_opt' (filter_anons (idck env) (map snd anns)) ss H in
                   Forall2 (sem_clock H b) (clockof e) (map abstract_clock ss)
                 | _ =>
                   Forall2 (sem_clock H b) (clockof e) (map abstract_clock ss)
                 end) es ss.
  Proof.
    intros * HwcG Hsc Hndup Hwenv Hwt Hwc Hsem Hinv.
    assert (length es = length ss) as Hlength by (eapply Forall2_length in Hsem; eauto).
    eapply Forall2_ignore2' in Hwt; eauto.
    eapply Forall2_ignore2' in Hwc; eauto.
    eapply Forall2_Forall2 in Hsem; eauto. clear Hwc.
    eapply Forall2_Forall2 in Hsem; [|eapply Hwt]. clear Hwt.
    eapply Forall2_impl_In; eauto. clear Hsem.
    intros ? ? ? ? (Hwt&Hwc&Hsem).
    eapply sc_exp'; eauto using NoDupMembers_fresh_in'.
  Qed.

  Corollary sc_inside' : forall G H Hi b env es ss bck sub n,
      wc_global G ->
      sc_nodes G ->
      NoDupMembers (env ++ fresh_ins es) ->
      wc_env (idck env) ->
      Forall (wt_exp G (idty env)) es ->
      Forall (wc_exp G (idck env)) es ->
      Forall2 (sem_exp G H b) es ss ->
      sc_var_inv' (idck env) H b ->
      wc_env (idck (n_in n)) ->
      Forall2 (WellInstantiated bck sub) (idck (n_in n)) (nclocksof es) ->
      Forall2 (sem_var Hi) (idents (n_in n)) (concat ss) ->
      Forall2 (fun xc : ident * clock => sem_clock Hi (clocks_of (concat ss)) (snd xc)) (idck (n_in n)) (map abstract_clock (concat ss)).
  Proof.
    intros.
    eapply sc_inside; eauto.
    eapply sc_exps'; eauto.
  Qed.

  Corollary sc_inside_mask' : forall G H Hi b env es ss bck sub n k rs,
      wc_global G ->
      sc_nodes G ->
      NoDupMembers (env ++ fresh_ins es) ->
      wc_env (idck env) ->
      Forall (wt_exp G (idty env)) es ->
      Forall (wc_exp G (idck env)) es ->
      Forall2 (sem_exp G H b) es ss ->
      sc_var_inv' (idck env) H b ->
      wc_env (idck (n_in n)) ->
      Forall2 (WellInstantiated bck sub) (idck (n_in n)) (nclocksof es) ->
      Forall2 (sem_var Hi) (idents (n_in n)) (map (mask k rs) (concat ss)) ->
      Forall2 (fun xc : ident * clock => sem_clock Hi (clocks_of (map (mask k rs) (concat ss))) (snd xc)) (idck (n_in n)) (map abstract_clock (map (mask k rs) (concat ss))).
  Proof.
    intros.
    eapply sc_inside_mask; eauto.
    eapply sc_exps'; eauto.
  Qed.

  Definition sem_clock_inputs (G : global) (f : ident) (xs : list (Stream value)): Prop :=
    exists H n,
      find_node f G = Some n /\
      Forall2 (sem_var H) (idents (n_in n)) xs /\
      Forall2 (fun xc => sem_clock H (clocks_of xs) (snd xc))
              (idck (n_in n)) (map abstract_clock xs).

  Lemma sem_clock_inputs_cons :
    forall G f n ins,
      n_name n <> f ->
      sem_clock_inputs G f ins <-> sem_clock_inputs (n :: G) f ins.
  Proof.
    intros * Hname.
    split; intros (H & n' & Hfind &?&?);
      exists H, n'; repeat split; auto.
    - rewrite find_node_other; eauto.
    - rewrite <- find_node_other; eauto.
  Qed.

  Lemma inputs_clocked_vars :
    forall n G H f ins,
      sem_clock_inputs (n :: G) f ins ->
      n_name n = f ->
      wc_env (idck (n_in n)) ->
      Forall2 (sem_var H) (idents (n_in n)) ins ->
      Forall2 (fun xc => sem_clock H (clocks_of ins) (snd xc)) (idck (n_in n)) (map abstract_clock ins).
  Proof.
    intros * (H'&n'& Hfind & Hv & Hscin) Hnf Wcin Hins.
    simpl in Hfind. rewrite <- Hnf, ident_eqb_refl in Hfind. inv Hfind.
    pose proof (sem_var_env_eq _ _ _ _ Hins Hv) as Horel.
    rewrite idck_idents in *. rewrite Forall2_map_1 in Hv, Hins.
    eapply Forall2_impl_In; [|eauto]. intros; simpl in *.
    eapply sem_clock_same_find; eauto.
    unfold wc_env in Wcin. eapply Forall_forall in H0; [|eauto]. auto.
  Qed.

  Fact NoDupMembers_fresh_in_anon_in : forall vars e,
      NoDupMembers (vars ++ fresh_in e) ->
      NoDupMembers (vars ++ anon_in e).
  Proof.
    intros * Hndup.
    destruct e; auto.
    destruct o; simpl in *.
    - repeat rewrite app_assoc in *.
      apply NoDupMembers_app_l in Hndup; auto.
    - repeat rewrite app_assoc in *.
      apply NoDupMembers_app_l in Hndup; auto.
  Qed.

  (** ** Another version of semantics equivalence, including sem_clock_inputs *)
  Section sc_ref.

    (** Functional equivalence for nodes *)
    Definition node_sc_refines G G' f : Prop :=
      (forall ins outs, (sem_clock_inputs G f ins /\ sem_node G f ins outs) ->
                   (sem_clock_inputs G' f ins /\ sem_node G' f ins outs)).

    Definition global_sc_refines G G' : Prop :=
      forall f, node_sc_refines G G' f.

    Ltac ndup_l H :=
      rewrite app_assoc in H;
      apply NoDupMembers_app_l in H; auto.
    Ltac ndup_r H :=
      rewrite Permutation_swap in H;
      apply NoDupMembers_app_r in H; auto.

    Hint Resolve NoDupMembers_fresh_in_anon_in NoDupMembers_fresh_in' NoDupMembers_anon_in' nth_In.
    Hint Constructors sem_exp.
    Fact sc_ref_sem_exp : forall G G' H b vars e vs,
        global_sc_refines G G' ->
        wc_global G ->
        sc_nodes G ->
        NoDupMembers (vars ++ anon_in e) ->
        wc_env (idck vars) ->
        wt_exp G (idty vars) e ->
        wc_exp G (idck vars) e ->
        sc_var_inv' (idck vars) H b ->
        sem_exp G H b e vs ->
        sem_exp G' H b e vs.
    Proof with eauto.
      induction e using exp_ind2; intros * Heq HwcG Hsc Hndup Hwenv Hwt Hwc Hinv Hsem;
        simpl in Hndup; inv Hwt; inv Hwc; inv Hsem...
      - (* binop *)
        econstructor... ndup_l Hndup... ndup_r Hndup...
      - (* fby *)
        econstructor...
        + ndup_l Hndup. repeat rewrite_Forall_forall... eapply H0...
        + ndup_r Hndup. repeat rewrite_Forall_forall... eapply H1...
      - (* when *)
        econstructor...
        repeat rewrite_Forall_forall... eapply H0...
      - (* merge *)
        econstructor...
        + ndup_l Hndup. repeat rewrite_Forall_forall... eapply H0...
        + ndup_r Hndup. repeat rewrite_Forall_forall... eapply H1...
      - (* ite *)
        econstructor...
        + ndup_l Hndup.
        + ndup_r Hndup. ndup_l Hndup. repeat rewrite_Forall_forall... eapply H0...
        + do 2 ndup_r Hndup. repeat rewrite_Forall_forall... eapply H1...
      - (* app *)
        econstructor...
        + repeat rewrite_Forall_forall... eapply H1...
        + specialize (Heq f (concat ss) vs).
          eapply Heq. split; auto.
          inv H19. rewrite H3 in H7; inv H7. rewrite H3 in H11; inv H11.
          exists H2; exists n0.
          repeat split; auto.
          eapply sc_inside'...
          eapply wc_find_node in HwcG as [G'' [? _]]...
      - (* app (reset) *)
        econstructor...
        + ndup_l Hndup. repeat rewrite_Forall_forall... eapply H1...
        + ndup_r Hndup.
        + intros k. specialize (H26 k).
          specialize (Heq f (map (mask k bs) (concat ss)) (map (mask k bs) vs)).
          eapply Heq. split; auto.
          inv H26. rewrite H3 in H7; inv H7. rewrite H3 in H14; inv H14.
          exists H2. exists n0.
          repeat split; auto.
          eapply sc_inside_mask'...
          ndup_l Hndup.
          eapply wc_find_node in H3 as [? [? _]]; eauto.
    Qed.

    Fact sc_ref_sem_equation : forall G G' H b vars eq,
        global_sc_refines G G' ->
        wc_global G ->
        sc_nodes G ->
        NoDupMembers (vars ++ anon_in_eq eq) ->
        wc_env (idck vars) ->
        wt_equation G (idty vars) eq ->
        wc_equation G (idck vars) eq ->
        sc_var_inv' (idck vars) H b ->
        sem_equation G H b eq ->
        sem_equation G' H b eq.
    Proof.
      intros G G' H b vars [xs es] Heq HwcG Hsc Hndup Hwenv [Hwt _] [Hwc _] Hinv Hsem.
      inv Hsem.
      econstructor; eauto.
      repeat rewrite_Forall_forall; eauto.
      eapply sc_ref_sem_exp; eauto.
    Qed.

    Fact global_sc_ref_nil :
      global_sc_refines [] [].
    Proof.
      intros f ins outs Hsem. assumption.
    Qed.

    Fact global_sc_ref_cons : forall G G' n n' f,
        Ordered_nodes (n::G) ->
        Ordered_nodes (n'::G') ->
        n_name n = f ->
        n_name n' = f ->
        global_sc_refines G G' ->
        node_sc_refines (n::G) (n'::G') f ->
        global_sc_refines (n::G) (n'::G').
    Proof with eauto.
      intros G G' n n' f Hord1 Hord2 Hname1 Hname2 Hglob Hnode f0 ins outs Hsem.
      inv Hsem.
      simpl in H0.
      destruct (ident_eqb (n_name n) f0) eqn:Heq.
      + specialize (Hnode ins outs).
        rewrite ident_eqb_eq in Heq; subst.
        eapply Hnode.
        econstructor; eauto.
      + rewrite ident_eqb_neq in Heq.
        rewrite <- sem_clock_inputs_cons... rewrite <- sem_node_cons_iff...
        specialize (Hglob f0 ins outs). apply Hglob.
        rewrite sem_clock_inputs_cons... rewrite sem_node_cons_iff...
    Qed.

  End sc_ref.
End LCLOCKSEMANTICS.

Module LClockSemanticsFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Syn : LSYNTAX Ids Op)
       (Typ : LTYPING Ids Op Syn)
       (Clo : LCLOCKING Ids Op Syn)
       (LCA        : LCAUSALITY Ids Op Syn)
       (Lord : LORDERED Ids Op Syn)
       (CStr : COINDSTREAMS Op OpAux)
       (IStr : INDEXEDSTREAMS Op OpAux)
       (Sem : LSEMANTICS Ids Op OpAux Syn Lord CStr)
<: LCLOCKSEMANTICS Ids Op OpAux Syn Typ Clo LCA Lord CStr IStr Sem.
  Include LCLOCKSEMANTICS Ids Op OpAux Syn Typ Clo LCA Lord CStr IStr Sem.
End LClockSemanticsFun.
