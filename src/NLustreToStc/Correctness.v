From Coq Require Import FSets.FMapPositive.
From Coq Require Import PArith.
From Coq Require Import Logic.FunctionalExtensionality.

From Velus Require Import NLustre.
From Velus Require Import Stc.

From Velus Require Import NLustreToStc.Translation.

From Velus Require Import Common.
From Velus Require Import CommonTyping.
From Velus Require Import Environment.
From Velus Require Import VelusMemory.
From Velus Require Import CoindToIndexed.

From Coq Require Import List.
Import List.ListNotations.

Open Scope list.
Open Scope nat.

Module Type CORRECTNESS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Ids Op)
       (Import ComTyp: COMMONTYPING    Ids Op OpAux)
       (Import Cks   : CLOCKS          Ids Op OpAux)
       (Import CStr  : COINDSTREAMS    Ids Op OpAux Cks)
       (Import IStr  : INDEXEDSTREAMS  Ids Op OpAux Cks)
       (Import CIStr : COINDTOINDEXED  Ids Op OpAux        Cks CStr IStr)
       (Import CE    : COREEXPR        Ids Op OpAux ComTyp Cks      IStr)
       (Import NL    : NLUSTRE         Ids Op OpAux ComTyp Cks CStr IStr CIStr CE)
       (Import Stc   : STC             Ids Op OpAux ComTyp Cks      IStr CE)
       (Import Trans : TRANSLATION     Ids Op OpAux Cks              CE.Syn NL.Syn Stc.Syn NL.Mem).

  Lemma In_snd_gather_eqs_Is_node_in:
    forall eqs i f,
      In (i, f) (snd (gather_eqs eqs)) ->
      Is_node_in f eqs.
  Proof.
    unfold gather_eqs.
    intro.
    generalize (@nil (ident * (Op.const * type * clock))).
    induction eqs as [|[]]; simpl; try contradiction; intros * Hin; auto.
    - right; eapply IHeqs; eauto.
    - destruct l.
      + right; eapply IHeqs; eauto.
      + apply In_snd_fold_left_gather_eq in Hin as [Hin|Hin].
        * destruct Hin as [E|]; try contradiction; inv E.
          left; constructor.
        * right; eapply IHeqs; eauto.
    - right; eapply IHeqs; eauto.
  Qed.

  Lemma Ordered_nodes_systems:
    forall G,
      Ordered_nodes G ->
      Ordered_systems (translate G).
  Proof.
    intros; eapply transform_units_Ordered_program; eauto.
    intros * Hin; apply in_map_iff in Hin as ((?&?)&?&?); simpl in *; subst.
    eapply In_snd_gather_eqs_Is_node_in; eauto.
  Qed.

  Lemma msem_eqs_reset_nexts:
    forall G bk H M n,
      memory_closed_n M (n_eqs n) ->
      Forall (msem_equation G bk H M) (n_eqs n) ->
      reset_nexts (translate_node n) (M 0).
  Proof.
    intros * Closed Heqs ???? Hin.
    destruct n; simpl in *.
    unfold gather_eqs in *.
    clear - Heqs Hin.
    revert Hin; generalize (@nil (ident * ident)).
    induction n_eqs0 as [|[] ? IH]; simpl in *; intros; try contradiction;
      inversion_clear Heqs as [|?? Heq]; inv Heq; eauto.
    - destruct l; try discriminate; eauto.
    - apply In_fst_fold_left_gather_eq in Hin as [Hin|]; eauto.
      destruct Hin as [E|]; try contradiction; inv E.
      match goal with H: mfbyreset _ _ _ _ _ _ |- _ => destruct H as (?&?) end; auto.
  Qed.

  Lemma msem_eqs_In_snd_gather_eqs_spec:
    forall eqs G bk H M x f,
      Forall (msem_equation G bk H M) eqs ->
      In (x, f) (snd (gather_eqs eqs)) ->
      exists xss Mx yss,
        (msem_node G f xss Mx yss
         \/ exists r, forall k, exists Mk, msem_node G f (mask k r xss) Mk (mask k r yss)
                           /\ memory_masked k r Mx Mk)
        /\ sub_inst_n x M Mx.
  Proof.
    unfold gather_eqs.
    intro; generalize (@nil (ident * (Op.const * type * clock))).
    induction eqs as [|[]]; simpl; intros ??????? Heqs Hin;
      inversion_clear Heqs as [|?? Heq];
      try inversion_clear Heq as [|?????????????? Hd ?????? Rst|];
      try contradiction; eauto.
    - destruct l; simpl in *; try congruence.
      apply In_snd_fold_left_gather_eq in Hin as [Hin|]; eauto.
      destruct Hin as [E|]; try contradiction; inv E; inv Hd.
      exists ls, Mx, xss.
      split; auto.
      right; eexists; intro k; destruct (Rst k) as (?&?&?); eauto.
  Qed.

  Lemma msem_node_initial_state:
    forall G f xss M yss,
      Ordered_nodes G ->
      msem_node G f xss M yss ->
      initial_state (translate G) f (M 0).
  Proof.
    intros (?& G).
    induction G as [|node ? IH].
    inversion 2;
      match goal with Hf: find_node _ (Global _ []) = _ |- _ => inversion Hf end.
    intros * Hord Hsem.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [??????? Clock Hfind Ins ?? Heqs Closed].
    pose proof (find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    pose proof Hord; inversion_clear Hord as [|???? NodeIn].
    apply option_map_inv in Hfind as ((?&?)&Hfind&?); simpl in *; subst.
    pose proof Hfind as Hfind'.
    eapply find_unit_cons in Hfind as [[E Hfind]|[E Hfind]]; simpl in *; eauto.
    - inversion Hfind; subst.
      apply find_unit_transform_units_forward in Hfind'.
      eapply msem_equations_cons in Heqs; eauto.
      econstructor; eauto.
      + eapply msem_eqs_reset_nexts; eauto.
      + intros * Hin.
        edestruct msem_eqs_In_snd_gather_eqs_spec
          as (?& Mx &?& [Node|(rs & Reset)] & Sub); eauto.
        destruct (Reset (if rs 0 then pred (count rs 0) else count rs 0))
          as (M0 & Node & Mmask).
        apply IH in Node; auto.
        specialize (Mmask 0); specialize (Sub 0).
        rewrite Mmask in Sub.
        * eexists; split; eauto.
        * simpl; cases.
    - eapply msem_node_cons in Hsem; eauto.
      unfold translate; simpl.
      rewrite <-initial_state_other; eauto.
  Qed.

  Definition sem_trconstrs_n
             (P: program) (bk: stream bool) (H: history)
             (E: stream state) (T: stream state) (E': stream state)
             (tcs: list trconstr) :=
    forall n, Forall (sem_trconstr P (bk n) (H n) (E n) (T n) (E' n)) tcs.

  Definition sem_system_n
             (P: program) (f: ident)
             (E: stream state) (xss yss: stream (list svalue)) (E': stream state) :=
    forall n, sem_system P f (E n) (xss n) (yss n) (E' n).

  Lemma sem_trconstrs_n_add_val_n:
    forall P tcs bk H S S' Is x xs,
      sem_trconstrs_n P bk H S Is S' tcs ->
      ~(exists ck, Is_reset_in x ck tcs) ->
      ~Is_next_in x tcs ->
      sem_trconstrs_n P bk H S (add_val_n x xs Is) S' tcs.
  Proof.
    induction tcs as [|tc tcs]; intros * Sem Notin1 Notin2 n; constructor.
    - specialize (Sem n); inversion_clear Sem as [|?? Sem'].
      inv Sem'; eauto using sem_trconstr.
      + econstructor; eauto.
        unfold add_val_n; rewrite find_val_gso; auto.
        intro E; eapply Notin1; rewrite E. exists ckr. do 2 constructor.
      + econstructor; eauto.
        1,2:unfold add_val_n; rewrite find_val_gso; auto.
        1,2:intro E; eapply Notin2; rewrite E; do 2 constructor.
    - apply IHtcs.
      + intro n'; specialize (Sem n'); inv Sem; auto.
      + contradict Notin1. destruct Notin1 as (ck&Notin1).
        exists ck. right; auto.
      + apply not_Is_next_in_cons in Notin2 as []; auto.
  Qed.

  Lemma sem_trconstrs_n_add_inst_n:
    forall P tcs bk H S S' Is x Sx,
      sem_trconstrs_n P bk H S Is S' tcs ->
      ~(exists ck, Is_ireset_in x ck tcs) ->
      ~Is_step_in x tcs ->
      sem_trconstrs_n P bk H S (add_inst_n x Sx Is) S' tcs.
  Proof.
    induction tcs as [|tc tcs]; intros * Sem Notin1 Notin2 n; constructor.
    - specialize (Sem n); inversion_clear Sem as [|?? Sem'].
      inv Sem'; eauto using sem_trconstr.
      + econstructor; eauto.
        unfold add_inst_n; rewrite find_inst_gso; auto.
        intro E; subst; eapply Notin1. exists ck; do 2 constructor.
      + econstructor; eauto.
        unfold add_inst_n; rewrite find_inst_gso; auto.
        intro E; subst; eapply Notin2; do 2 constructor.
    - apply IHtcs.
      + intro n'; specialize (Sem n'); inv Sem; auto.
      + contradict Notin1. destruct Notin1 as (ck&?).
        exists ck. right; auto.
      + intro contra. apply Notin2; right; auto.
  Qed.

  Inductive translate_eqn_nodup_subs: NL.Syn.equation -> list trconstr -> Prop :=
    | TrNodupEqDef:
        forall x ck e eqs,
          translate_eqn_nodup_subs (NL.Syn.EqDef x ck e) eqs
    | TrNodupEqApp:
        forall xs ck f es r eqs x,
          hd_error xs = Some x ->
          (~(exists ck, Is_ireset_in x ck eqs) /\ ~Is_step_in x eqs) ->
          translate_eqn_nodup_subs (EqApp xs ck f es r) eqs
    | TrNodupEqFby:
        forall x ck c e ro eqs,
          translate_eqn_nodup_subs (EqFby x ck c e ro) eqs.

  Definition translate_eqn_nodup_nexts eq tcs :=
    forall x, In x (map fst (gather_mem_eq eq)) ->
         ~(exists ck, Is_reset_in x ck tcs) /\ ~Is_next_in x tcs.

  Inductive memory_closed_rec: global -> ident -> memory value -> Prop :=
    memory_closed_rec_intro:
      forall G f M n,
        find_node f G = Some n ->
        (forall x, find_val x M <> None -> In x (map fst (gather_mems n.(n_eqs)))) ->
        (forall i Mi, find_inst i M = Some Mi ->
              exists f',
                In (i, f') (gather_insts n.(n_eqs))
                /\ memory_closed_rec G f' Mi) ->
        memory_closed_rec G f M.

  Definition memory_closed_rec_n (G: global) (f: ident) (M: memories) : Prop :=
    forall n, memory_closed_rec G f (M n).

  Lemma memory_closed_rec_other:
    forall M G f node enums,
      Ordered_nodes (Global enums (node :: G)) ->
      node.(n_name) <> f ->
      (memory_closed_rec (Global enums (node :: G)) f M
       <-> memory_closed_rec (Global enums G) f M).
  Proof.
    induction M as [? IH] using memory_ind'.
    split; inversion_clear 1 as [???? Find ? Insts].
    - rewrite find_node_other in Find; auto.
      econstructor; eauto.
      intros * Find'; pose proof Find';
        apply Insts in Find' as (?& Hin & Closed).
      erewrite IH in Closed; eauto.
      rewrite <-gather_eqs_snd_spec in Hin.
      apply In_snd_gather_eqs_Is_node_in in Hin.
      intro; subst; contradict Hin.
      eapply find_node_other_not_Is_node_in; eauto.
    - pose proof Find; erewrite <-find_node_other in Find; eauto.
      econstructor; eauto.
      intros * Find'; pose proof Find';
        apply Insts in Find' as (?& Hin & Closed).
      erewrite <-IH in Closed; eauto.
      rewrite <-gather_eqs_snd_spec in Hin.
      apply In_snd_gather_eqs_Is_node_in in Hin.
      intro; subst; contradict Hin.
      eapply find_node_other_not_Is_node_in; eauto.
  Qed.

  Lemma memory_closed_rec_n_other:
    forall M G f node enums,
      Ordered_nodes (Global enums (node :: G)) ->
      node.(n_name) <> f ->
      (memory_closed_rec_n (Global enums (node :: G)) f M
       <-> memory_closed_rec_n (Global enums G) f M).
  Proof.
    split; intros Closed n; specialize (Closed n).
    - apply memory_closed_rec_other in Closed; auto.
    - apply memory_closed_rec_other; auto.
  Qed.

  Lemma msem_equations_memory_closed_rec:
    forall eqs G bk H M n x f Mx,
      (forall f xss M yss,
          msem_node G f xss M yss ->
          memory_closed_rec_n G f M) ->
      Forall (msem_equation G bk H M) eqs ->
      find_inst x (M n) = Some Mx ->
      In (x, f) (gather_insts eqs) ->
      memory_closed_rec G f Mx.
  Proof.
    unfold gather_insts.
    induction eqs as [|eq]; simpl; intros * IH Heqs Find Hin;
      inversion_clear Heqs as [|?? Heq]; try contradiction.
    apply in_app in Hin as [Hin|]; eauto.
    destruct eq; simpl in Hin; try contradiction.
    destruct l; try contradiction.
    inversion_clear Hin as [E|]; try contradiction; inv E.
    inversion_clear Heq as [|?????????????? Hd Sub ????? Rst|];
      inv Hd; rewrite Sub in Find; inv Find.
    - specialize (Rst (if rs n then pred (count rs n) else count rs n));
        destruct Rst as (?& Node & Mask).
      apply IH in Node.
      rewrite Mask; auto.
      cases_eqn Hr; apply count_true_ge_1 in Hr.
      erewrite <-Lt.S_pred; eauto.
  Qed.

  Lemma msem_node_memory_closed_rec_n:
    forall G f xss M yss,
      Ordered_nodes G ->
      msem_node G f xss M yss ->
      memory_closed_rec_n G f M.
  Proof.
    intros (?& G).
    induction G as [|node]; intros ???? Ord;
      inversion_clear 1 as [???????? Find ??? Heqs Closed];
      try now inv Find.
    pose proof Find.
    apply option_map_inv in Find as ((?&?)&Find&?); simpl in *; subst.
    eapply find_unit_cons in Find as [[E Find]|[E Find]]; simpl in *; eauto.
    - inv Find.
      econstructor; eauto.
      + apply Closed.
      + intros * Find_i.
        assert (exists f', In (i, f') (gather_insts (n_eqs node))) as (f' & Hin)
            by (eapply InMembers_In, Closed, not_None_is_Some; eauto).
        eexists; split; eauto.
        assert (f' <> node.(n_name)).
        { rewrite <-gather_eqs_snd_spec in Hin.
          apply In_snd_gather_eqs_Is_node_in in Hin.
          intro; subst; contradict Hin; eapply find_node_not_Is_node_in; eauto.
        }
        apply memory_closed_rec_other; auto.
        assert (~ Is_node_in (n_name node) (n_eqs node))
          by (eapply find_node_not_Is_node_in; eauto).
        apply msem_equations_cons in Heqs; auto.
        inv Ord.
        eapply msem_equations_memory_closed_rec; eauto.
    - assert (find_node f {| NL.Syn.enums := enums0; nodes := G |} = Some n0)
        by (unfold find_node; rewrite Find; auto).
      assert (~ Is_node_in (n_name node) (n_eqs n0))
        by (eapply find_node_other_not_Is_node_in; eauto).
      apply msem_equations_cons in Heqs; auto.
      apply memory_closed_rec_n_other; auto; inv Ord; eauto.
  Qed.

  Lemma memory_closed_rec_state_closed:
    forall M G f,
      Ordered_nodes G ->
      memory_closed_rec G f M ->
      state_closed (translate G) f M.
  Proof.
    induction M as [? IH] using memory_ind'.
    intros * Ord Closed; inversion_clear Closed as [???? Find Mems Insts].
    apply option_map_inv in Find as ((?&?)& Find &?); simpl in *; subst.
    apply find_unit_transform_units_forward in Find.
    econstructor; eauto; simpl.
    - intros * ? Find'. apply Mems in Find'. rewrite <-gather_eqs_fst_spec in Find'; auto.
      apply in_map_iff in Find' as ((?&?)&?& Hin);
        apply in_map_iff in Hin as ((?&((?&?)&?))& E & Hin); simpl in *; inv E.
      apply in_map_iff; eexists; split; eauto; auto.
    - intros * FindInst; pose proof FindInst as FindInst'.
      apply Insts in FindInst as (?& Hin & Closed).
      rewrite <-gather_eqs_snd_spec in Hin.
      eexists; split; eauto.
      eapply IH in Closed; eauto.
      apply Ordered_nodes_systems in Ord.
      eapply state_closed_find_system_other; eauto.
  Qed.

  Corollary msem_node_state_closed:
     forall G f xss M yss,
      Ordered_nodes G ->
      msem_node G f xss M yss ->
      forall n, state_closed (translate G) f (M n).
  Proof.
    intros; apply memory_closed_rec_state_closed; auto.
    eapply msem_node_memory_closed_rec_n; eauto.
  Qed.

  Lemma state_closed_insts_add:
    forall P insts I x f M,
      state_closed_insts P insts I ->
      state_closed P f M ->
      state_closed_insts P ([(x, f)] ++ insts) (add_inst x M I).
  Proof.
    intros * Trans Closed.
    intros i ? Find.
    destruct (ident_eq_dec i x).
    - subst. rewrite find_inst_gss in Find; inv Find.
      exists f; split; auto.
      apply in_app; left; constructor; auto.
    - rewrite find_inst_gso in Find; auto.
      apply Trans in Find as (g&?&?).
      exists g; split; auto.
      apply in_app; auto.
  Qed.

  Definition next (M: memories) : memories := fun n => M (S n).

  Lemma sem_clock_vars_instant_Con:
    forall H b xs ys n,
      Forall2 (sem_var H) (map fst xs) ys ->
      Forall (fun y => exists r, svalue_to_bool (y n) = Some r) ys ->
      sem_clocked_vars_instant b (H n) xs ->
      Forall (fun ckr => exists r, sem_clock_instant b (H n) ckr r) (map (fun '(xr, ckr) => Con ckr xr (bool_velus_type, true_tag)) xs).
  Proof.
    intros * Vars Bools Clocked.
    rewrite Forall2_map_1 in Vars.
    induction Vars as [|(?&?)]; inversion_clear Bools as [|?? (?&Bool)]; inv Clocked; constructor; eauto.
    clear IHVars. specialize (H0 n).
    destruct (y n); simpl in *.
    - exists false. eapply Son_abs1; eauto.
      apply H4; eauto.
    - exists x0. destruct v; inv Bool.
      destruct (e ==b true_tag) eqn:Heq.
      + rewrite enumtag_eqb_eq in Heq; subst.
        econstructor; eauto.
        apply H4; eauto.
      + rewrite enumtag_eqb_neq in Heq; subst.
        eapply Son_abs2; eauto.
        apply H4; eauto.
  Qed.

  Lemma sem_clock_vars_instant_Con_true:
    forall H b xs ys n,
      Forall2 (sem_var H) (map fst xs) ys ->
      sem_clocked_vars_instant b (H n) xs ->
      Exists (fun y => svalue_to_bool (y n) = Some true) ys <->
      Exists (fun ckr => sem_clock_instant b (H n) ckr true) (map (fun '(xr, ckr) => Con ckr xr (bool_velus_type, true_tag)) xs).
  Proof.
    intros * Vars Clocked.
    rewrite Forall2_map_1 in Vars.
    induction Vars as [|(?&?)]; inv Clocked; split; intros Bools; inv Bools; eauto.
    - left. specialize (H0 n).
      destruct (y n); simpl in *. 2:destruct v; simpl in *. 1-3:inv H2.
      rewrite H5.
      rewrite enumtag_eqb_eq in H5; subst.
      econstructor; eauto.
      apply H3; eauto.
    - right. apply IHVars; auto.
    - left. specialize (H0 n).
      inv H2. 1,2:eapply sem_var_instant_det in H0; [|eauto]; try congruence.
      rewrite <- H0; auto.
    - right. apply IHVars; auto.
  Qed.

  Lemma sem_clock_vars_instant_Con_false:
    forall H b xs ys n,
      Forall2 (sem_var H) (map fst xs) ys ->
      sem_clocked_vars_instant b (H n) xs ->
      Forall (fun y => svalue_to_bool (y n) = Some false) ys <->
      Forall (fun ckr => sem_clock_instant b (H n) ckr false) (map (fun '(xr, ckr) => Con ckr xr (bool_velus_type, true_tag)) xs).
  Proof.
    intros * Vars Clocked.
    rewrite Forall2_map_1 in Vars.
    induction Vars as [|(?&?)]; inv Clocked; split; intros Bools; inv Bools; constructor; eauto.
    - specialize (H0 n).
      destruct (y n); simpl in *. 2:destruct v; simpl in *. 1-3:inv H5.
      + econstructor; eauto.
        eapply H3; eauto.
      + rewrite H2.
        rewrite enumtag_eqb_neq in H2; subst.
        eapply Son_abs2; eauto.
        apply H3; eauto.
    - apply IHVars; auto.
    - specialize (H0 n).
      destruct y; simpl in *; auto.
      inv H5; eapply sem_var_instant_det in H0; eauto; inv H0.
      assert (b' <> true_tag) as Hneq by auto.
      rewrite <-enumtag_eqb_neq in Hneq. rewrite <-Hneq; auto.
    - apply IHVars; auto.
  Qed.

  Lemma equation_correctness:
    forall G eq tcs bk H M Is vars insts nexts,
      (forall f xss M yss,
          msem_node G f xss M yss ->
          sem_system_n (translate G) f M xss yss (next M)) ->
      Ordered_nodes G ->
      NL.Clo.wc_equation G vars eq ->
      CE.Sem.sem_clocked_vars bk H vars ->
      translate_eqn_nodup_subs eq tcs ->
      translate_eqn_nodup_nexts eq tcs ->
      (forall n, state_closed_insts (translate G) insts (Is n)) ->
      (forall n, state_closed_nexts nexts (Is n)) ->
      msem_equation G bk H M eq ->
      sem_trconstrs_n (translate G) bk H M Is (next M) tcs ->
      exists Is',
        sem_trconstrs_n (translate G) bk H M Is' (next M) (translate_eqn eq ++ tcs)
        /\ (forall n, state_closed_insts (translate G) (gather_inst_eq eq ++ insts) (Is' n))
        /\ (forall n, state_closed_nexts (map fst (gather_mem_eq eq) ++ nexts) (Is' n)).
  Proof.
    intros * IHnode Hord WC ClkM TrNodup1 TrNodup2 Closed1 Closed2 Heq Htcs.
    destruct Heq as [|??????????????????? Var Bools Reset|
                     ???????????? Arg Var VarR ClockedVar Bools Mfby];
      inversion_clear TrNodup1 as [|???????? (Notin1&Notin2)|]; simpl.

    - eexists; split; [|split]; eauto.
      do 2 (econstructor; eauto).

    - destruct xs; try discriminate.
      match goal with
      | H: hd_error ?l = Some x,
           H': hd_error ?l = _ |- _ =>
        rewrite H' in H; inv H; simpl in H'; inv H'
      end.
      assert (forall Mx, sem_trconstrs_n (translate G) bk H M (add_inst_n x Mx Is) (next M) tcs) as Htcs'
          by now intro; apply sem_trconstrs_n_add_inst_n.
      assert (CE.Sem.sem_clocked_vars bk H xrs) as Cky.
      { intro n; specialize (ClkM n).
        eapply Forall_forall. intros (?&?) Hin.
        eapply Forall_forall in ClkM; eauto. inv WC; eauto; auto.
        eapply Forall_forall in H13; eauto.
      }
      exists (fun n => add_inst x (if rs n then Mx 0 else Mx n) (Is n)); split; [|split]; auto;
        try intro;
        destruct (Reset (count rs n)) as (Mn & Node_n & Mmask_n),
                                         (Reset 0) as (M0 & Node_0 & Mmask_0);
        specialize (Cky n); simpl in Cky;
          pose proof Node_n as Node_n'; apply IHnode in Node_n; specialize (Node_n n);
            rewrite 2 mask_transparent in Node_n; auto.
      + assert (Forall (fun ckr => exists r, sem_clock_instant (bk n) (H n) ckr r) (map (fun '(xr, ckr) => Con ckr xr (bool_velus_type, true_tag)) xrs)) as ClockR.
        { eapply sem_clock_vars_instant_Con in Cky; eauto.
          eapply bools_ofs_svalue_to_bool; eauto. }
        destruct (rs n) eqn: Hrst.
        *{ assert (find_inst x (add_inst x (Mx 0) (Is n)) = Some (Mx 0))
             by apply find_inst_gss.
           specialize (Htcs' (fun n => Mx 0) n).
           constructor; [|apply Forall_app;split;
                          [repeat rewrite Forall_map; eapply Forall_forall; intros;
                           rewrite Forall_map in ClockR; eapply Forall_forall in ClockR as (?&ClockR)|]];
             try econstructor; eauto using sem_trconstr.
           - intro contra. exfalso.
             assert (Exists (fun y : nat -> _ => svalue_to_bool (y n) = Some true) ys) as CkTrue.
             { eapply bools_ofs_svalue_to_bool_true; eauto. }
             eapply sem_clock_vars_instant_Con_true in CkTrue; eauto.
             eapply Forall_Exists in contra; eauto.
             eapply Exists_exists in contra as (?&In&(Clock1&Clock2)).
             eapply sem_clock_instant_det in Clock1; [|eauto]. congruence.
           - assert (Mn n ≋ Mn 0) as Eq.
             { eapply msem_node_absent_until; eauto.
               intros * Spec.
               rewrite mask_opaque.
               - apply all_absent_spec.
               - eapply count_positive in Spec; eauto; lia.
             }
             eapply same_initial_memory with (2 := Node_n') in Node_0; eauto.
             unfold next in Node_n; simpl in Node_n.
             specialize (Mmask_n (S n)).
             rewrite Mmask_n, Mmask_0, <-Node_0, <-Eq; auto.
           - destruct x1; auto.
             rewrite Mmask_0; auto.
             eapply msem_node_initial_state; eauto.
         }
        *{ rewrite <-Mmask_n in Node_n; try rewrite Hrst; auto.
           assert (find_inst x (add_inst x (Mx n) (Is n)) = Some (Mx n))
             by apply find_inst_gss.
           specialize (Htcs' Mx n).
           constructor; [|apply Forall_app;split;
                          [repeat rewrite Forall_map; eapply Forall_forall; intros;
                           rewrite Forall_map in ClockR; eapply Forall_forall in ClockR as (?&ClockR)|]];
             try econstructor; eauto using sem_trconstr.
           - intros _. rewrite H1. reflexivity.
           - unfold next; simpl.
             rewrite <-Mmask_n; auto.
           - assert (Forall (fun y : nat -> _ => svalue_to_bool (y n) = Some false) ys) as CkFalse.
             { eapply bools_ofs_svalue_to_bool_false; eauto. }
             eapply sem_clock_vars_instant_Con_false in CkFalse; eauto.
             rewrite Forall_map in CkFalse. eapply Forall_forall in CkFalse; eauto. destruct x0.
             eapply sem_clock_instant_det in ClockR; [|eauto]; subst; auto.
         }
      + apply state_closed_insts_add; auto.
        destruct (rs n) eqn: Hrst.
        * rewrite Mmask_0.
          -- eapply msem_node_state_closed; eauto.
          -- simpl; cases.
        * rewrite Mmask_n; try rewrite Hrst; auto.
          eapply msem_node_state_closed; eauto.

    - pose proof mfbyreset_holdreset as Hhold. specialize (Hhold _ _ _ _ _ _ Mfby).
      exists (add_val_n x (fun n => if (rs n) then sem_const c0 else holdreset (sem_const c0) ls rs n) Is).

      assert (forall n, Forall (fun ckr => exists r, sem_clock_instant (bk n) (H n) ckr r) (map (fun '(xr, ckr) => Con ckr xr (bool_velus_type, true_tag)) xrs)) as ClockR.
      { intros n. eapply sem_clock_vars_instant_Con in ClockedVar; eauto.
        eapply bools_ofs_svalue_to_bool; eauto. }

      repeat split; auto.
      constructor; specialize (ClockR n);
        [|apply Forall_app;split;
          [repeat rewrite Forall_map; eapply Forall_forall; intros;
           rewrite Forall_map in ClockR; eapply Forall_forall in ClockR as (?&ClockR)|]];
        try econstructor.
      2:unfold add_val_n; rewrite find_val_gss; eauto.
      1-10:eauto.
      + intros CkFalse.
        eapply sem_clock_vars_instant_Con_false in CkFalse; eauto.
        eapply bools_ofs_svalue_to_bool_false in CkFalse; eauto.
        rewrite CkFalse; auto.
      + destruct Mfby as (_&Spec).
        specialize (Spec n); rewrite Hhold in Spec.
        specialize (Var n); specialize (Arg n).
        pose proof Arg as Arg'. simpl in *.
        destruct (rs n) eqn:Hrs, (ls n) eqn:Hls;
          (destruct Spec as (?& Hxs); inv Arg'; try congruence).
      + unfold next. rewrite Hhold; simpl.
        destruct (rs n) eqn:Hrs, (ls n) eqn:Hls; auto.
      + unfold add_val_n. rewrite find_val_gss.
        destruct x1; auto.
        assert (Exists (fun ckr => sem_clock_instant (bk n) (H n) ckr true) (map (fun '(xr, ckr) => Con ckr xr (bool_velus_type, true_tag)) xrs)) as CkTrue.
        { rewrite CommonList.Exists_map. eapply Exists_exists; eauto. }
        eapply sem_clock_vars_instant_Con_true in CkTrue; eauto.
        eapply bools_ofs_svalue_to_bool_true in CkTrue; eauto.
        rewrite CkTrue; auto.
      + eapply sem_trconstrs_n_add_val_n; eauto.
        1,2:apply TrNodup2; simpl; auto.
      + intros n. apply state_closed_nexts_add; auto.
  Qed.

  Lemma not_Is_defined_not_Is_sub_in_eqs:
    forall x eqs,
      ~ NL.IsD.Is_defined_in x eqs ->
      ~ (exists ck : clock, Is_ireset_in x ck (translate_eqns eqs)) /\ ~Is_step_in x (translate_eqns eqs).
  Proof.
    unfold translate_eqns.
    induction eqs as [|eq]; simpl; intros Notin; (split; [intros (?&Hin)|intros Hin]).
    - inv Hin.
    - inv Hin.
    - eapply IsD.not_Is_defined_in_cons in Notin as (Notin1&Notin2).
      apply Exists_app' in Hin as [Hin|].
      + destruct eq; simpl in Hin.
        * inversion_clear Hin as [?? Hin'|?? Hin']; inv Hin'.
        *{ destruct l; inversion_clear Hin as [?? Hin'|?? Hin']. inv Hin'.
           clear - Notin1 Hin'. induction l1; simpl in Hin'; inv Hin'; auto.
           - inv H0. apply Notin1; auto using Is_defined_in_eq, in_eq.
           - apply IHl1; auto.
             contradict Notin1. inv Notin1; auto using Is_defined_in_eq.
         }
        * inversion_clear Hin as [?? Hin'|?? Hin']. inv Hin'.
          clear - Hin'. rewrite map_map, CommonList.Exists_map in Hin'.
          induction Hin'; auto. inv H.
      + eapply IHeqs in Notin2 as (Notin2&_); eauto.
    - eapply IsD.not_Is_defined_in_cons in Notin as (Notin1&Notin2).
      apply Exists_app' in Hin as [Hin|].
      + destruct eq; simpl in Hin.
        * inversion_clear Hin as [?? Hin'|?? Hin']; inv Hin'.
        *{ destruct l; try destruct o as [(?&?)|]; inversion_clear Hin as [?? Hin'|?? Hin'].
           - inv Hin'; apply Notin1; do 3 constructor; auto.
           - clear - Hin'. rewrite map_map, CommonList.Exists_map in Hin'.
             induction Hin'; auto. inv H.
         }
        * inversion_clear Hin as [?? Hin'|?? Hin']. inv Hin'.
          clear - Hin'. rewrite map_map, CommonList.Exists_map in Hin'.
          induction Hin'; auto. inv H.
      + eapply IHeqs in Notin2 as (_&Notin2); eauto.
  Qed.

  Lemma Nodup_defs_translate_eqns_subs:
    forall eq eqs G bk H M,
      msem_equation G bk H M eq ->
      NoDup_defs (eq :: eqs) ->
      translate_eqn_nodup_subs eq (translate_eqns eqs).
  Proof.
    destruct eq; inversion_clear 1; inversion_clear 1; econstructor; eauto.
    apply not_Is_defined_not_Is_sub_in_eqs.
    assert (In x l) by (now apply hd_error_Some_In); auto.
  Qed.

  Lemma not_Is_defined_not_Is_reset_in_eqs:
    forall x eqs,
      ~NL.IsD.Is_defined_in x eqs ->
      ~exists ck, Is_reset_in x ck (translate_eqns eqs).
  Proof.
    unfold translate_eqns.
    induction eqs as [|eq]; simpl; intros Notin (?&Hin).
    - inv Hin.
    - apply Exists_app' in Hin as [Hin|].
      + destruct eq; simpl in Hin.
        * inversion_clear Hin as [?? Hin'|?? Hin']; inv Hin'.
        *{ destruct l; try destruct o as [(((?&?)&?)&?)|]; inversion_clear Hin as [?? Hin'|?? Hin'].
           - inv Hin'; apply Notin; do 3 constructor; auto.
           - clear - Hin'. rewrite map_map, CommonList.Exists_map in Hin'.
             induction Hin'; auto. inv H.
         }
        * inversion_clear Hin as [?? Hin'|?? Hin']. inv Hin'.
          clear - Notin Hin'. induction l; simpl in Hin'; inv Hin'; auto.
          -- inv H0. apply Notin; left; auto using Is_defined_in_eq.
          -- apply IHl; auto.
             contradict Notin. inv Notin; [left|right]; auto.
             inv H1. constructor.
      + eapply IHeqs; eauto.
        eapply NL.IsD.not_Is_defined_in_cons in Notin as []; auto.
  Qed.

  Lemma not_Is_defined_not_Is_next_in_eqs:
    forall x eqs,
      ~ NL.IsD.Is_defined_in x eqs ->
      ~Is_next_in x (translate_eqns eqs).
  Proof.
    unfold translate_eqns.
    induction eqs as [|eq]; simpl; intros Notin Hin.
    - inv Hin.
    - apply Exists_app' in Hin as [Hin|].
      + destruct eq; simpl in Hin.
        * inversion_clear Hin as [?? Hin'|?? Hin']; inv Hin'.
        *{ destruct l; try destruct o as [(?&?)|]; inversion_clear Hin as [?? Hin'|?? Hin'].
           - inv Hin'; apply Notin; do 3 constructor; auto.
           - clear - Hin'. rewrite map_map, CommonList.Exists_map in Hin'.
             induction Hin'; auto. inv H.
         }
        *{ inversion_clear Hin as [?? Hin'|?? Hin'].
           - inv Hin'. apply Notin.
             left; constructor.
           - clear - Hin'. induction l; simpl in Hin'; inv Hin'; auto.
             inv H0.
         }
      + eapply IHeqs; eauto.
        eapply NL.IsD.not_Is_defined_in_cons in Notin as []; auto.
  Qed.

  Lemma Nodup_defs_translate_eqns_nexts:
    forall eq eqs G bk H M,
      msem_equation G bk H M eq ->
      NoDup_defs (eq :: eqs) ->
      translate_eqn_nodup_nexts eq (translate_eqns eqs).
  Proof.
    destruct eq; inversion_clear 1; inversion_clear 1; econstructor; eauto.
    1-2:simpl in H0; destruct H0; subst; try contradiction.
    - apply not_Is_defined_not_Is_reset_in_eqs; auto.
    - apply not_Is_defined_not_Is_next_in_eqs; auto.
  Qed.

  Lemma state_closed_insts_empty:
    forall P insts,
      state_closed_insts P insts (empty_memory _).
  Proof.
    intros ???? Find.
    rewrite find_inst_gempty in Find; discriminate.
  Qed.

  Corollary equations_correctness:
    forall G bk H M eqs vars,
      (forall f xss M yss,
          msem_node G f xss M yss ->
          sem_system_n (translate G) f M xss yss (next M)) ->
      Ordered_nodes G ->
      Forall (NL.Clo.wc_equation G vars) eqs ->
      CE.Sem.sem_clocked_vars bk H vars ->
      NoDup_defs eqs ->
      Forall (msem_equation G bk H M) eqs ->
      exists Is, sem_trconstrs_n (translate G) bk H M Is (next M) (translate_eqns eqs)
            /\ (forall n, state_closed_insts (translate G) (gather_insts eqs) (Is n))
            /\ (forall n, state_closed_nexts (map fst (gather_mems eqs)) (Is n)).
  Proof.
    intros ???????? WC ?? Heqs.
    unfold translate_eqns.
    induction eqs as [|eq eqs IHeqs]; simpl; inv WC.
    - exists (fun n => empty_memory _); split; try constructor.
      + intro; apply state_closed_insts_empty.
      + intros ?? Hfind. exfalso. apply Hfind, find_val_gempty.
    - apply Forall_cons2 in Heqs as [Heq Heqs].
      apply IHeqs in Heqs as (?&?&?&?); auto.
      + unfold gather_insts; simpl.
        rewrite map_app.
        eapply equation_correctness; eauto.
        eapply Nodup_defs_translate_eqns_subs; eauto.
        eapply Nodup_defs_translate_eqns_nexts; eauto.
      + eapply NoDup_defs_cons; eauto.
  Qed.

  Lemma not_Is_node_in_not_Is_system_in:
    forall eqs f,
      ~ Is_node_in f eqs ->
      ~ Is_system_in f (translate_eqns eqs).
  Proof.
    unfold translate_eqns.
    induction eqs as [|eq]; simpl; intros * Hnin Hin.
    - inv Hin.
    - apply not_Is_node_in_cons in Hnin as (Hnineq & Hnin).
      apply IHeqs in Hnin.
      destruct eq; simpl in *.
      + inversion_clear Hin as [?? E|?? Hins]; try inv E; auto.
      + destruct l; auto.
        apply Exists_app' in Hin as [Hin|?]; try contradiction.
        inv Hin.
        * inv H0. apply Hnineq; auto using Is_node_in_eq.
        * clear - H0 Hnineq. induction l1; inv H0; auto.
          -- inv H1. apply Hnineq; auto using Is_node_in_eq.
          -- apply IHl1; auto.
             contradict Hnineq. inv Hnineq; auto using Is_node_in_eq.
      + inv Hin.
        * inv H0.
        * apply Exists_app' in H0 as [Hin|?]; try contradiction.
          clear - Hin. induction l; inv Hin; auto. inv H0.
  Qed.

  Theorem correctness:
    forall G f xss M yss,
      Ordered_nodes G ->
      wc_global G ->
      msem_node G f xss M yss ->
      sem_system_n (translate G) f M xss yss (next M).
  Proof.
    intros (enums & G).
    induction G as [|node ? IH].
    inversion 3;
      match goal with Hf: find_node _ (Global _ []) = _ |- _ => inversion Hf end.
    intros * Hord WC Hsem n.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [??????? Clock Hfind Ins Outs Ck Heqs Closed].
    pose proof (find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    pose proof Hord as Hord'; inversion_clear Hord' as [|???? NodeIn].
    apply option_map_inv in Hfind as ((?&?)&Hfind&?).
    pose proof Hfind as Hfind'.
    assert (Ordered_systems (Program enums (translate_node node :: map translate_node G)))
      by (apply Ordered_nodes_systems in Hord; auto).
    inversion WC as [|?? (?&?&?& WCeqs)]; subst; simpl in WCeqs.
    eapply find_unit_cons in Hfind as [[E Hfind]|[E Hfind]]; simpl in *; eauto.
    - inv Hfind.
      apply find_unit_transform_units_forward in Hfind'.
      eapply msem_equations_cons in Heqs; eauto.
      pose proof (NoDup_defs_node node).
      eapply equations_correctness in Heqs as (I & Heqs &?&?); eauto.
      + econstructor; eauto.
        * apply sem_trconstrs_cons; eauto.
          apply not_Is_node_in_not_Is_system_in; auto.
        * eapply msem_node_state_closed; eauto.
        * econstructor; eauto; try congruence.
          rewrite s_nexts_in_tcs_fst; simpl. rewrite <-gather_mems_nexts_of; auto.
          eapply state_closed_insts_find_system_other, state_closed_insts_cons; eauto.
          simpl; rewrite gather_eqs_snd_spec; auto.
        * unfold next; eapply msem_node_state_closed; eauto.
      + rewrite idck_app.
        intro k; specialize (Ck k); setoid_rewrite Forall_app; split; auto.
        apply Forall_forall; intros (x, ck) ?.
        rewrite idck_app in WCeqs.
        eapply sem_clocked_var_eqs with (5 := WCeqs); eauto.
        * rewrite <-idck_app, NoDupMembers_idck.
          apply n_nodup.
        * eapply msem_sem_equations; eauto.
        * rewrite map_fst_idck.
          apply n_defd.
    - eapply msem_node_cons, IH in Hsem; eauto.
      apply sem_system_cons2; eauto.
  Qed.

  Corollary correctness_loop:
    forall G f xss M yss,
      Ordered_nodes G ->
      wc_global G ->
      msem_node G f xss M yss ->
      initial_state (translate G) f (M 0)
      /\ loop (translate G) f xss yss (M 0) 0.
  Proof.
    intros; split.
    - eapply msem_node_initial_state; eauto.
    - apply loop_coind with (R := fun P b xss yss S n =>
                                    P = translate G
                                    /\ S ≋ M n
                                    /\ msem_node G b xss M yss);
        try now intuition.
      intros * (?& E & Sem); subst.
      pose proof Sem; apply correctness in Sem; auto.
      exists (next M n); intuition eauto.
      + rewrite E; auto.
      + unfold next; simpl; reflexivity.
  Qed.

End CORRECTNESS.

Module CorrectnessFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Ids Op)
       (ComTyp: COMMONTYPING    Ids Op OpAux)
       (Cks   : CLOCKS          Ids Op OpAux)
       (CStr  : COINDSTREAMS    Ids Op OpAux Cks)
       (IStr  : INDEXEDSTREAMS  Ids Op OpAux Cks)
       (CIStr : COINDTOINDEXED  Ids Op OpAux        Cks CStr IStr)
       (CE    : COREEXPR        Ids Op OpAux ComTyp Cks      IStr)
       (NL    : NLUSTRE         Ids Op OpAux ComTyp Cks CStr IStr CIStr CE)
       (Stc   : STC             Ids Op OpAux ComTyp Cks      IStr       CE)
       (Trans : TRANSLATION     Ids Op OpAux Cks           CE.Syn NL.Syn Stc.Syn NL.Mem)
<: CORRECTNESS Ids Op OpAux ComTyp Cks CStr IStr CIStr CE NL Stc Trans.
  Include CORRECTNESS Ids Op OpAux ComTyp Cks CStr IStr CIStr CE NL Stc Trans.
End CorrectnessFun.
