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
       (       CStr  : COINDSTREAMS    Ids Op OpAux Cks)
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
    intros * G.
    rewrite gather_eqs_inst_flat_map in G. simpl_In.
    unfold gather_eq in *. cases. destruct Hinf as [Eq|Eq]; inv Eq.
    unfold Is_node_in. solve_Exists. constructor.
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

  Lemma msem_eqs_reset_states:
    forall G bk H M n,
      memory_closed_n M (n_eqs n) ->
      Forall (msem_equation G bk H M) (n_eqs n) ->
      reset_states (translate_node n) (M 0).
  Proof.
    intros * Closed Heqs ???? Hin.
    destruct n; simpl in *.
    clear - Heqs Hin.
    rewrite gather_eqs_last_flat_map, gather_eqs_next_flat_map in Hin.
    apply in_app_iff in Hin as [Hin|Hin]; simpl_In.
    - unfold gather_eq in *. cases. destruct Hinf as [Eq|Eq]; inv Eq.
      simpl_Forall. inv Heqs.
      match goal with H: mfbyreset _ _ _ _ _ _ |- _ => destruct H as (?&?) end; auto.
    - unfold gather_eq in *. cases. destruct Hinf as [Eq|Eq]; inv Eq.
      simpl_Forall. inv Heqs.
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
    intros * Sem In.
    rewrite gather_eqs_inst_flat_map in In. simpl_In.
    unfold gather_eq in *. cases. destruct Hinf as [Eq|Eq]; inv Eq.
    simpl_Forall. inversion_clear Sem as [|?????????????? Hd ?????? Rst| |]. inv Hd.
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
    intros [].
    induction nodes0 as [|node ? IH].
    inversion 2;
      match goal with Hf: find_node _ (Global _ _ []) = _ |- _ => inversion Hf end.
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
      + eapply msem_eqs_reset_states; eauto.
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

  Definition sem_trconstrs_n {prefs}
             (P: @program prefs) (bk: stream bool) (H: IStr.history)
             (E: stream state) (T: stream state) (E': stream state)
             (tcs: list trconstr) :=
    forall n, Forall (sem_trconstr P (bk n) (H n) (E n) (T n) (E' n)) tcs.

  Definition sem_system_n {prefs}
             (P: @program prefs) (f: ident)
             (E: stream state) (xss yss: stream (list svalue)) (E': stream state) :=
    forall n, sem_system P f (E n) (xss n) (yss n) (E' n).

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
    forall M G f node enums externs,
      Ordered_nodes (Global enums externs (node :: G)) ->
      node.(n_name) <> f ->
      (memory_closed_rec (Global enums externs (node :: G)) f M
       <-> memory_closed_rec (Global enums externs G) f M).
  Proof.
    induction M as [? IH] using memory_ind'.
    split; inversion_clear 1 as [???? Find ? Insts].
    - rewrite find_node_other in Find; auto.
      econstructor; eauto.
      intros * Find'; pose proof Find';
        apply Insts in Find' as (?& Hin & Closed).
      erewrite IH in Closed; eauto.
      rewrite <-gather_eqs_inst in Hin.
      apply In_snd_gather_eqs_Is_node_in in Hin.
      intro; subst; contradict Hin.
      eapply find_node_other_not_Is_node_in; eauto.
    - pose proof Find; erewrite <-find_node_other in Find; eauto.
      econstructor; eauto.
      intros * Find'; pose proof Find';
        apply Insts in Find' as (?& Hin & Closed).
      erewrite <-IH in Closed; eauto.
      rewrite <-gather_eqs_inst in Hin.
      apply In_snd_gather_eqs_Is_node_in in Hin.
      intro; subst; contradict Hin.
      eapply find_node_other_not_Is_node_in; eauto.
  Qed.

  Lemma memory_closed_rec_n_other:
    forall M G f node enums externs,
      Ordered_nodes (Global enums externs (node :: G)) ->
      node.(n_name) <> f ->
      (memory_closed_rec_n (Global enums externs (node :: G)) f M
       <-> memory_closed_rec_n (Global enums externs G) f M).
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
    inversion_clear Heq as [|?????????????? Hd Sub ????? Rst| |];
      inv Hd; rewrite Sub in Find; inv Find.
    - specialize (Rst (if rs n then pred (count rs n) else count rs n));
        destruct Rst as (?& Node & Mask).
      apply IH in Node.
      rewrite Mask; auto.
      cases_eqn Hr; apply count_true_ge_1 in Hr. lia.
  Qed.

  Lemma msem_node_memory_closed_rec_n:
    forall G f xss M yss,
      Ordered_nodes G ->
      msem_node G f xss M yss ->
      memory_closed_rec_n G f M.
  Proof.
    intros [].
    induction nodes0 as [|node]; intros ???? Ord;
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
        { rewrite <-gather_eqs_inst in Hin.
          apply In_snd_gather_eqs_Is_node_in in Hin.
          intro; subst; contradict Hin; eapply find_node_not_Is_node_in; eauto.
        }
        apply memory_closed_rec_other; auto.
        assert (~ Is_node_in (n_name node) (n_eqs node))
          by (eapply find_node_not_Is_node_in; eauto).
        apply msem_equations_cons in Heqs; auto.
        inv Ord.
        eapply msem_equations_memory_closed_rec; eauto.
    - assert (find_node f {| NL.Syn.types := types0; nodes := nodes0 |} = Some n0)
        by (unfold find_node; rewrite Find; auto).
      assert (~ Is_node_in (n_name node) (n_eqs n0))
        by (eapply find_node_other_not_Is_node_in; eauto).
      apply msem_equations_cons in Heqs; auto.
      apply memory_closed_rec_n_other; auto; inv Ord; eauto with nlsem.
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
    - intros * ? Find'. apply Mems in Find'.
      rewrite map_app, map_fst_idfst, gather_eqs_last_defined, gather_eqs_next_defined, in_app_iff.
      unfold gather_mems, gather_mem_eq in *. simpl_In.
      cases; [left|right]. 1,2:apply In_singleton in Hinf; inv Hinf.
      + unfold lasts_defined. solve_In. simpl. auto.
      + unfold vars_defined. solve_In. simpl. auto.
    - intros * FindInst; pose proof FindInst as FindInst'.
      apply Insts in FindInst as (?& Hin & Closed).
      rewrite <-gather_eqs_inst in Hin.
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

  Lemma state_closed_insts_add {prefs} :
    forall (P: @program prefs) insts I x f M,
      state_closed_insts P insts I ->
      state_closed P f M ->
      state_closed_insts P ((x, f) :: insts) (add_inst x M I).
  Proof.
    intros * Trans Closed.
    intros i ? Find.
    destruct (ident_eq_dec i x).
    - subst. rewrite find_inst_gss in Find; inv Find.
      exists f; split; auto.
      left; constructor; auto.
    - rewrite find_inst_gso in Find; auto.
      apply Trans in Find as (g&?&?).
      exists g; split; auto.
      right; auto.
  Qed.

  Definition next (M: memories) : memories := fun n => M (S n).

  Lemma sem_clock_vars_instant_Con:
    forall H b xs ys n,
      Forall2 (fun '(x, _) => IStr.sem_var H (FunctionalEnvironment.Var x)) xs ys ->
      Forall (fun y => exists r, svalue_to_bool (y n) = Some r) ys ->
      sem_clocked_vars_instant b (H n) xs ->
      Forall (fun '(xr, (ckr, _)) => exists r, sem_clock_instant b (var_env (H n)) (Con ckr xr (bool_velus_type, true_tag)) r) xs.
  Proof.
    intros * Vars Bools Clocked.
    unfold sem_clocked_vars_instant in *.
    eapply Forall2_ignore2 in Vars. simpl_Forall.
    take (sem_clocked_var_instant _ _ _ _) and destruct it as (Pres&Abs).
    take (IStr.sem_var _ _ _) and specialize (it n).
    destruct (x n); simpl in *; [inv H5|].
    - exists false. eapply Son_abs1; eauto.
      apply Abs; eauto.
    - exists x0. destruct v; inv H5.
      destruct (e ==b true_tag) eqn:Heq.
      + rewrite enumtag_eqb_eq in Heq; subst.
        econstructor; eauto.
        apply Pres; eauto.
      + rewrite enumtag_eqb_neq in Heq; subst.
        eapply Son_abs2; eauto.
        apply Pres; eauto.
  Qed.

  Lemma sem_clock_vars_instant_Con_true:
    forall H b xs ys n,
      Forall2 (fun '(x, _) => IStr.sem_var H (FunctionalEnvironment.Var x)) xs ys ->
      sem_clocked_vars_instant b (H n) xs ->
      Exists (fun y => svalue_to_bool (y n) = Some true) ys <->
      Exists (fun '(xr, (ckr, _)) => sem_clock_instant b (var_env (H n)) (Con ckr xr (bool_velus_type, true_tag)) true) xs.
  Proof.
    intros * Vars Clocked.
    unfold sem_clocked_vars_instant in *.
    split; intros Ex.
    - apply Forall2_ignore1 in Vars. simpl_Exists. simpl_Forall. solve_Exists.
      take (sem_clocked_var_instant _ _ _ _) and destruct it as (Pres&_).
      take (IStr.sem_var _ _ _) and specialize (it n).
      destruct (x n) as [|[]]; simpl in *; inv Ex.
      rewrite H2.
      rewrite enumtag_eqb_eq in H2; subst.
      econstructor; eauto. eapply Pres; eauto.
    - apply Forall2_ignore2 in Vars. simpl_Exists. simpl_Forall. solve_Exists.
      take (sem_clocked_var_instant _ _ _ _) and destruct it as (Pres&_).
      take (IStr.sem_var _ _ _) and specialize (it n).
      inv Ex. apply Pres in H4 as (?&V). eapply sem_var_instant_det in it; eauto.
      rewrite <-it. simpl. now rewrite equiv_decb_refl.
  Qed.

  Lemma sem_clock_vars_instant_Con_false:
    forall H b xs ys n,
      Forall2 (fun '(x, _) => IStr.sem_var H (FunctionalEnvironment.Var x)) xs ys ->
      sem_clocked_vars_instant b (H n) xs ->
      Forall (fun y => svalue_to_bool (y n) = Some false) ys <->
      Forall (fun '(xr, (ckr, _)) => sem_clock_instant b (var_env (H n)) (Con ckr xr (bool_velus_type, true_tag)) false) xs.
  Proof.
    intros * Vars Clocked.
    unfold sem_clocked_vars_instant in *.
    split; intros Ex.
    - apply Forall2_ignore2 in Vars. simpl_Forall.
      take (sem_clocked_var_instant _ _ _ _) and destruct it as (Pres&Abs).
      take (IStr.sem_var _ _ _) and specialize (it n).
      destruct (x n) as [|[]]; simpl in *; inv Ex.
      + eapply Son_abs1; eauto. apply Abs; auto.
      + rewrite H4. rewrite enumtag_eqb_neq in H4.
        eapply Son_abs2; eauto.
        eapply Pres; eauto.
    - apply Forall2_ignore1 in Vars. simpl_Forall.
      take (sem_clocked_var_instant _ _ _ _) and destruct it as (Pres&_).
      take (IStr.sem_var _ _ _) and specialize (it n). inv Ex.
      + eapply sem_var_instant_det in it; eauto. rewrite <-it; auto.
      + eapply sem_var_instant_det in it; eauto. rewrite <-it. simpl.
        assert (b' <> true_tag) as Hneq by auto.
        rewrite <-enumtag_eqb_neq in Hneq. rewrite <-Hneq; auto.
  Qed.

  Fact Forall2_sem_var_det H : forall (ckrs : list (ident * clock)) xs1 xs2,
    Forall2 (fun '(x, _) => IStr.sem_var H (FunctionalEnvironment.Var x)) ckrs xs1 ->
    Forall2 (fun '(x, _) => IStr.sem_var H (FunctionalEnvironment.Var x)) ckrs xs2 ->
    xs1 = xs2.
  Proof.
    induction ckrs as [|(?&?)]; intros * F1 F2; inv F1; inv F2; auto.
    f_equal; eauto using sem_var_det.
  Qed.

  Lemma state_closed_insts_empty {prefs} :
    forall (P: @program prefs) insts,
      state_closed_insts P insts (empty_memory _).
  Proof.
    intros ???? Find.
    rewrite find_inst_gempty in Find; discriminate.
  Qed.

  Lemma build_intermediate_state G bk H M : forall eqs,
      Ordered_nodes G ->
      NoDup (lasts_defined eqs ++ vars_defined (filter is_fby eqs)) ->
      NoDup (vars_defined (filter is_app eqs)) ->
      Forall (msem_equation G bk H M) eqs ->
      exists Is,
        (forall x ty ck c0 ckrs,
            In (EqLast x ty ck c0 ckrs) eqs ->
            exists xs ls ys rs,
              IStr.sem_var H (FunctionalEnvironment.Var x) xs
              /\ IStr.sem_var H (FunctionalEnvironment.Last x) ls
              /\ Forall2 (fun '(x, _) => IStr.sem_var H (FunctionalEnvironment.Var x)) ckrs ys
              /\ bools_ofs ys rs
              /\ mfbyreset x (sem_const c0) xs rs M ls
              /\ forall n, find_val x (Is n) = Some (if rs n then sem_const c0 else holdreset (sem_const c0) xs rs n))
        /\ (forall x ck c0 e ckrs xs ls ys rs,
              In (EqFby x ck c0 e ckrs) eqs ->
              Sem.sem_aexp bk H ck e ls ->
              IStr.sem_var H (FunctionalEnvironment.Var x) xs ->
              Forall2 (fun '(x, _) => IStr.sem_var H (FunctionalEnvironment.Var x)) ckrs ys ->
              bools_ofs ys rs ->
              mfbyreset x (sem_const c0) ls rs M xs ->
              forall n, find_val x (Is n) = Some (if rs n then sem_const c0 else holdreset (sem_const c0) ls rs n))
        /\ (forall x xs ck f es ckrs ys rs Mx,
              In (EqApp (x::xs) ck f es ckrs) eqs ->
              Forall2 (fun '(x0, _) => IStr.sem_var H (FunctionalEnvironment.Var x0)) ckrs ys ->
              bools_ofs ys rs ->
              sub_inst_n x M Mx ->
              forall n, find_inst x (Is n) = Some (if rs n then Mx 0 else Mx n))
        /\ (forall n, state_closed_insts (translate G) (gather_insts eqs) (Is n))
        /\ (forall n, state_closed_states (map fst (gather_mems eqs)) (Is n)).
  Proof.
    intros * Ord ND1 ND2 Sem.
    induction eqs; inv Sem.
    - exists (fun n => empty_memory _); split; [|split; [|split; [|split]]].
      + intros * In. inv In.
      + intros * In. inv In.
      + intros * In. inv In.
      + intro; apply state_closed_insts_empty.
      + intros ?? Hfind. exfalso. apply Hfind, find_val_gempty.
    - edestruct IHeqs as (Is&Lasts&Fbys&Insts&ClInsts&ClStates); eauto.
      1:{ simpl in *. clear - ND1. simpl_app.
          apply NoDup_app_r in ND1. cases. simpl in *.
          solve_NoDup_app. }
      1:{ simpl in *. clear - ND2. cases; eauto using NoDup_app_r. }
      take (msem_equation _ _ _ _ _) and
        inversion it as [|??????????????? Sub ??? Var Bools Reset
                           |???????????? Arg Var VarR Bools Mfby
                           |???????????? Var _ Last VarR Bools Mfby]; subst.
      + (* EqDef *)
        exists Is. split; [|split; [|split; [|split]]]; simpl; auto.
        all:intros * In; inv In; eauto; congruence.
      + (* EqApp *)
        destruct xs; simpl in *; inv H1.
        exists (fun n => add_inst x (if rs n then Mx 0 else Mx n) (Is n)); split; [|split; [|split; [|split]]]; auto.
        * intros * In. setoid_rewrite find_val_add_inst. inv In; eauto. congruence.
        * intros * In. setoid_rewrite find_val_add_inst. inv In; eauto. congruence.
        *{ intros * In. inv In; [inv H0|].
           - intros Var' Bools' Sub' ?.
             eapply Forall2_sem_var_det in Var; eauto; subst.
             eapply bools_ofs_det in Bools; eauto; subst.
             unfold sub_inst_n in *.
             rewrite find_inst_gss. f_equal. cases.
             + specialize (Sub 0). specialize (Sub' 0). rewrite Sub in Sub'. now inv Sub'.
             + specialize (Sub n). specialize (Sub' n). rewrite Sub in Sub'. now inv Sub'.
           - intros. destruct (ident_eq_dec x x0); [|rewrite find_inst_gso; eauto].
             exfalso. simpl in *. inv ND2.
             eapply H10, in_or_app. right. unfold vars_defined. solve_In. simpl; auto.
          }
        *{ simpl. intros ?. apply state_closed_insts_add; auto.
           destruct (Reset (count rs n)) as (Mn & Node_n & Mmask_n),
               (Reset 0) as (M0 & Node_0 & Mmask_0).
           destruct (rs n) eqn: Hrst.
           - rewrite Mmask_0.
              + eapply msem_node_state_closed; eauto.
              + simpl; cases.
           - rewrite Mmask_n; try rewrite Hrst; auto.
              eapply msem_node_state_closed; eauto.
         }
      + (* EqFby *)
        exists (add_val_n x (fun n => if (rs n) then sem_const c0 else holdreset (sem_const c0) ls rs n) Is).
        split; [|split; [|split; [|split]]]; auto.
        *{ intros * In. unfold add_val_n. inv In; [inv H0|].
           edestruct Lasts as (?&?&?&?&?&?&?&?&?&?); eauto.
           do 4 esplit. repeat (split; eauto). intros.
           destruct (ident_eq_dec x x0); [|rewrite find_val_gso; eauto].
           exfalso. simpl in *. rewrite <-Permutation.Permutation_middle in ND1. inv ND1.
           eapply H10, in_or_app. left. unfold lasts_defined. solve_In. simpl; auto.
         }
        *{ intros * In. unfold add_val_n. inv In; [inv H0|].
           - intros Arg' Var' VarR' Bools' Mfby' ?.
             eapply sem_var_det in Var; eauto; subst.
             eapply Forall2_sem_var_det in VarR; eauto; subst.
             eapply bools_ofs_det in Bools; eauto; subst.
             eapply sem_aexp_det in Arg; eauto; subst.
             rewrite find_val_gss. auto.
           - intros.
             destruct (ident_eq_dec x x0); [|rewrite find_val_gso; eauto].
             exfalso. simpl in *. rewrite <-Permutation.Permutation_middle in ND1. inv ND1.
             eapply H9, in_or_app. right. unfold vars_defined. solve_In. simpl; auto.
          }
        * intros * In. setoid_rewrite find_inst_add_val. inv In; eauto. congruence.
        * intros. apply state_closed_states_add; auto.
      + (* EqLast *)
        exists (add_val_n x (fun n => if (rs n) then sem_const c0 else holdreset (sem_const c0) xs rs n) Is).
        split; [|split; [|split; [|split]]]; auto.
        *{ intros * In. unfold add_val_n. inv In; [inv H0|].
           - do 4 esplit. repeat (split; eauto).
             intros ?. rewrite find_val_gss. auto.
           - edestruct Lasts as (?&?&?&?&?&?&?&?&?&?); eauto.
             do 4 esplit. repeat (split; eauto). intros.
             destruct (ident_eq_dec x x0); [|rewrite find_val_gso; eauto].
             exfalso. simpl in *. inv ND1.
             eapply H10, in_or_app. left. unfold lasts_defined. solve_In. simpl; auto.
         }
        *{ intros * In. unfold add_val_n. inv In; [inv H0|]. intros.
           destruct (ident_eq_dec x x0); [|rewrite find_val_gso; eauto].
           exfalso. simpl in *. inv ND1.
           eapply H9, in_or_app. right. unfold vars_defined. solve_In. simpl; auto.
         }
        * intros * In. setoid_rewrite find_inst_add_val. inv In; eauto. congruence.
        * intros. apply state_closed_states_add; auto.
  Qed.

  Lemma equations_correctness:
    forall G bk H M env eqs Γ,
      (forall f xss M yss,
          msem_node G f xss M yss ->
          sem_system_n (translate G) f M xss yss (next M)) ->
      Ordered_nodes G ->
      NoDup (lasts_defined eqs ++ vars_defined (filter is_fby eqs)) ->
      NoDup (vars_defined (filter is_app eqs)) ->
      (forall x ckrs, Env.find x env = Some ckrs -> exists ty ck c0, In (EqLast x ty ck c0 ckrs) eqs) ->
      Forall (NL.Clo.wc_equation G Γ) eqs ->
      CE.Sem.sem_clocked_vars bk H Γ ->
      Forall (msem_equation G bk H M) eqs ->
      exists Is, sem_trconstrs_n (translate G) bk H M Is (next M) (translate_eqns env eqs)
            /\ (forall n, state_closed_insts (translate G) (gather_insts eqs) (Is n))
            /\ (forall n, state_closed_states (map fst (gather_mems eqs)) (Is n)).
  Proof.
    intros * Node Ord ND1 ND2 Env WC ClkM (* ND *) Heqs.

    assert (forall x ckrs, Env.find x env0 = Some ckrs -> incl ckrs (idfst Γ)) as Incl.
    { intros * Find. edestruct Env as (?&?&?&In); eauto.
      simpl_Forall. inv WC.
      intros ? Hin. simpl_Forall. solve_In. }

    edestruct build_intermediate_state as (Is&Lasts&Fbys&Insts&ClInsts&ClStates); eauto.
    exists Is. split; [|split]; auto.
    intros n. unfold translate_eqns.
    simpl_Forall. simpl_In. simpl_Forall.

    destruct Heqs as [|??????????????? Sub ??? Var Bools Reset
                        |???????????? Arg Var Xrs Bools Mfby
                        |???????????? Var Arg Last Xrs Bools Mfby]; simpl in *.

    - cases_eqn Eq. all:apply In_singleton in Hinf; subst.
      1,3:do 2 (econstructor; eauto).

      edestruct Env as (?&?&c0&LastIn); eauto.
      edestruct Lasts as (?&ls&ys&rs&Var&Last&Xrs&Bools&Mfby&HIs); eauto.
      pose proof mfbyreset_holdreset as Hhold. specialize (Hhold _ _ _ _ _ _ Mfby).
      eapply sem_var_det in H0; eauto; subst.

      assert (CE.Sem.sem_clocked_vars bk H (map (fun '(x, ck) => (x, (ck, false))) l)) as Cky.
      { intro n1; specialize (ClkM n1). inv WC. take (In _ Γ) and clear it.
        unfold sem_clocked_vars_instant in *. simpl_Forall.
        eapply Incl in H0; eauto. simpl_In. simpl_Forall. auto. }

      assert (Forall (fun '(xr, (ckr, _)) => exists r, sem_clock_instant (bk n) (var_env (H n)) (Con ckr xr (bool_velus_type, true_tag)) r) (map (fun '(x, ck) => (x, (ck, false))) l)) as ClockR.
      { eapply sem_clock_vars_instant_Con with (ys:=ys) in Cky; eauto.
        - simpl_Forall; eauto.
        - eapply bools_ofs_svalue_to_bool in Bools; eauto. }

      eapply STcUpdateLast with (c:=if (rs n) then sem_const c0 else holdreset (sem_const c0) xs rs n); eauto.
      + intros CkFalse.
        eapply sem_clock_vars_instant_Con_false with (ys:=ys) in Cky as (_&Cky); eauto. 2:simpl_Forall; eauto.
        eapply bools_ofs_svalue_to_bool_false in Cky; eauto. 2:simpl_Forall; eauto.
        rewrite Cky. eauto.
      + specialize (H1 n). inv H1; take (sem_rhs_instant _ _ _ _) and inv it; econstructor; eauto.
      + apply mfbyreset_fbyreset in Mfby. rewrite Mfby in Last. clear - Last.
        specialize (Last n). unfold fbyreset in *. cases; auto.
      + unfold next. rewrite Hhold; simpl. cases.

    - destruct xs; take (hd_error _ = _) and inv it.
      assert (CE.Sem.sem_clocked_vars bk H (map (fun '(x, ck) => (x, (ck, false))) xrs)) as Cky.
      { intro n1; specialize (ClkM n1). inv WC.
        unfold sem_clocked_vars_instant in *. simpl_Forall.
        auto. }
      destruct (Reset (count rs n)) as (Mn & Node_n & Mmask_n), (Reset 0) as (M0 & Node_0 & Mmask_0).

      specialize (Cky n); simpl in Cky;
        pose proof Node_n as Node_n'; apply Node in Node_n; specialize (Node_n n);
        rewrite 2 mask_transparent in Node_n; auto.
      assert (Forall (fun '(xr, (ckr, _)) => exists r, sem_clock_instant (bk n) (var_env (H n)) (Con ckr xr (bool_velus_type, true_tag)) r) (map (fun '(x, ck) => (x, (ck, false))) xrs)) as ClockR.
      { eapply sem_clock_vars_instant_Con with (ys:=ys) in Cky; eauto.
        - simpl_Forall; eauto.
        - eapply bools_ofs_svalue_to_bool in Bools; eauto. }

      destruct (rs n) eqn: Hrst.
      *{ assert (find_inst x0 (Is n) = Some (Mx 0)).
         { eapply Insts in Sub; eauto. rewrite Hrst in Sub. auto. }
         destruct Hinf as [In|]; [inv In|simpl_In].
         - econstructor; eauto.
           + intro contra. exfalso.
             assert (Exists (fun y : nat -> _ => svalue_to_bool (y n) = Some true) ys) as CkTrue.
             { eapply bools_ofs_svalue_to_bool_true; eauto. }
             eapply sem_clock_vars_instant_Con_true in CkTrue; eauto. 2:simpl_Forall; eauto.
             simpl_Exists. simpl_Forall. clear H4.
             eapply sem_clock_instant_det in CkTrue; [|eauto]. congruence.
           + assert (Mn n ≋ Mn 0) as Eq.
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
         - simpl_Forall. econstructor; eauto.
           destruct x; auto.
           rewrite Mmask_0; auto.
           eapply msem_node_initial_state; eauto.
       }
      *{ rewrite <-Mmask_n in Node_n; try rewrite Hrst; auto.
         assert (find_inst x0 (Is n) = Some (Mx n)).
         { eapply Insts in Sub; eauto. rewrite Hrst in Sub. auto. }
         destruct Hinf as [In|]; [inv In|simpl_In].
         - econstructor; eauto.
           + simpl_Forall. intros _. rewrite Sub. reflexivity.
           + unfold next; simpl.
             rewrite <-Mmask_n; auto.
         - assert (Forall (fun y : nat -> _ => svalue_to_bool (y n) = Some false) ys) as CkFalse.
           { eapply bools_ofs_svalue_to_bool_false; eauto. }
           econstructor; eauto.
           eapply sem_clock_vars_instant_Con_false in CkFalse; eauto. 2:simpl_Forall; eauto.
           simpl_Forall. eauto. simpl. auto.
       }

    - pose proof mfbyreset_holdreset as Hhold. specialize (Hhold _ _ _ _ _ _ Mfby).

      assert (CE.Sem.sem_clocked_vars bk H (map (fun '(x, ck) => (x, (ck, false))) xrs)) as Cky.
      { intro n1; specialize (ClkM n1). inv WC. take (In _ _) and clear it.
        unfold sem_clocked_vars_instant in *. simpl_Forall.
        auto. }

      assert (forall n, Forall (fun '(xr, (ckr, _)) => exists r, sem_clock_instant (bk n) (var_env (H n)) (Con ckr xr (bool_velus_type, true_tag)) r) (map (fun '(x, ck) => (x, (ck, false))) xrs)) as ClockR.
      { intros n1. eapply sem_clock_vars_instant_Con with (ys:=ys) in Cky; eauto.
        - simpl_Forall; eauto.
        - eapply bools_ofs_svalue_to_bool in Bools; eauto. }

      specialize (ClockR n). destruct Hinf as [In|In]; [inv In|simpl_In; simpl_Forall]; econstructor.
      2:eapply Fbys; eauto. all:eauto.
      + intros CkFalse.
        eapply sem_clock_vars_instant_Con_false with (ys:=ys) in Cky as (_&Cky); eauto. 2:simpl_Forall; eauto.
        eapply bools_ofs_svalue_to_bool_false in Cky; eauto. 2:simpl_Forall; eauto.
        rewrite Cky; auto.
      + destruct Mfby as (_&Spec).
        specialize (Spec n); rewrite Hhold in Spec.
        specialize (Var n); specialize (Arg n).
        pose proof Arg as Arg'. simpl in *.
        destruct (rs n) eqn:Hrs, (ls n) eqn:Hls;
          (destruct Spec as (?& Hxs); inv Arg'; try congruence).
      + unfold next. rewrite Hhold; simpl.
        destruct (rs n) eqn:Hrs, (ls n) eqn:Hls; auto.
      + unfold add_val_n. destruct x; auto.
        eapply sem_clock_vars_instant_Con_true with (ys:=ys) in Cky as (_&Cky); eauto. 2:simpl_Forall; eauto.
        eapply bools_ofs_svalue_to_bool_true in Cky; eauto. 2:solve_Exists.
        erewrite Fbys, Cky; eauto.

    - edestruct Lasts as (?&ls1&ys1&rs1&Var'&Last'&Xrs'&Bools'&Mfby'&HIs'); eauto.
      eapply sem_var_det in Var; eauto; subst.
      eapply sem_var_det in Last; eauto; subst.
      eapply Forall2_sem_var_det in Xrs; eauto; subst.
      eapply bools_ofs_det in Bools; eauto; subst.
      pose proof mfbyreset_holdreset as Hhold. specialize (Hhold _ _ _ _ _ _ Mfby).

      assert (CE.Sem.sem_clocked_vars bk H (map (fun '(x, ck) => (x, (ck, false))) xrs)) as Cky.
      { intro n1; specialize (ClkM n1). inv WC. take (In _ _) and clear it.
        unfold sem_clocked_vars_instant in *. simpl_Forall.
        auto. }

      assert (forall n, Forall (fun '(xr, (ckr, _)) => exists r, sem_clock_instant (bk n) (var_env (H n)) (Con ckr xr (bool_velus_type, true_tag)) r) (map (fun '(x, ck) => (x, (ck, false))) xrs)) as ClockR.
      { intros n1. eapply sem_clock_vars_instant_Con with (ys:=ys) in Cky; eauto.
        - simpl_Forall; eauto.
        - eapply bools_ofs_svalue_to_bool in Bools'; eauto. }

      specialize (ClockR n). simpl_In. simpl_Forall.
      econstructor; eauto.
      destruct x; auto.
      eapply sem_clock_vars_instant_Con_true with (ys:=ys) in Cky as (_&Cky); eauto. 2:simpl_Forall; eauto.
      eapply bools_ofs_svalue_to_bool_true in Cky; eauto. 2:solve_Exists.
      rewrite HIs', Cky; auto.
  Qed.

  Lemma not_Is_node_in_not_Is_system_in:
    forall env eqs f,
      ~ Is_node_in f eqs ->
      ~ Is_system_in f (translate_eqns env eqs).
  Proof.
    unfold translate_eqns.
    induction eqs as [|eq]; simpl; intros * Hnin Hin.
    - inv Hin.
    - apply not_Is_node_in_cons in Hnin as (Hnineq & Hnin).
      apply IHeqs in Hnin.
      destruct eq; simpl in *.
      + cases; inv Hin; eauto. all:take (Is_system_in_tc _ _) and inv it.
      + apply Exists_app in Hin as [|]; eauto.
        simpl_Exists. take (Is_system_in_tc _ _) and inv it.
      + cases. unfold Is_system_in in *. rewrite Exists_app, Exists_cons in Hin.
        destruct Hin as [[Hin|Hin]|Hin]; eauto; [inv Hin|simpl_Exists; inv Hin].
        1,2:eapply Hnineq; constructor.
      + unfold Is_system_in in *. rewrite Exists_cons, Exists_app in Hin.
        destruct Hin as [Hin|[Hin|Hin]]; eauto; [|simpl_Exists]; inv Hin.
  Qed.

  Theorem correctness:
    forall G f xss M yss,
      Ordered_nodes G ->
      wc_global G ->
      msem_node G f xss M yss ->
      sem_system_n (translate G) f M xss yss (next M).
  Proof.
    intros [].
    induction nodes0 as [|node ? IH].
    inversion 3;
      match goal with Hf: find_node _ (Global _ _ []) = _ |- _ => inversion Hf end.
    intros * Hord WC Hsem n.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [??????? Clock Hfind Ins Outs Ck Heqs Closed].
    pose proof (find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    pose proof Hord as Hord'; inversion_clear Hord' as [|???? NodeIn].
    apply option_map_inv in Hfind as ((?&?)&Hfind&?).
    pose proof Hfind as Hfind'.
    assert (Ordered_systems (Program types0 externs0 (translate_node node :: map translate_node nodes0)))
      by (apply Ordered_nodes_systems in Hord; auto).
    inversion WC as [|?? (?&?&?& WCeqs)]; subst; simpl in WCeqs.
    eapply find_unit_cons in Hfind as [[E Hfind]|[E Hfind]]; simpl in *; eauto.
    - inv Hfind.
      apply find_unit_transform_units_forward in Hfind'.
      eapply msem_equations_cons in Heqs; eauto.
      eapply equations_correctness in Heqs as (I & Heqs & Insts & States); eauto.
      + econstructor; eauto.
        * apply sem_trconstrs_cons, Heqs; eauto; simpl in *.
          apply not_Is_node_in_not_Is_system_in; auto.
        * eapply msem_node_state_closed; eauto.
        * econstructor; eauto; try congruence.
          -- rewrite map_app, s_lasts_in_tcs, s_nexts_in_tcs; simpl.
             intros ? Find. eapply States in Find. rewrite translate_eqns_last, in_app_iff.
             unfold gather_mems, gather_mem_eq, translate_eqns in *. simpl_In.
             cases; apply In_singleton in Hinf; inv Hinf.
             ++ left.
                assert (In i (lasts_defined (n_eqs node))) as Last.
                { unfold lasts_defined. solve_In. simpl; auto. }
                assert (In i (vars_defined (filter is_def_cexp (n_eqs node)))) as Def.
                { rewrite n_lastd1 in Last. simpl_In. eapply n_lastd2; eauto. }
                unfold vars_defined in Def. simpl_In.
                destruct x; simpl in *; try congruence.
                destruct r; simpl in *; try congruence.
                destruct Hinf as [|[]]; subst.
                solve_In; cycle 1. rewrite Env.mem_1; eauto. 2:auto.
                apply Env.In_from_list. clear - Hin0. rewrite gather_eqs_last_flat_map. solve_In.
             ++ right. apply nexts_of_In. unfold Is_update_next_in.
                solve_Exists. solve_In. simpl; left; eauto.
                constructor.
          -- intros * Inst. eapply Insts in Inst as (?&?&?); eauto.
             simpl in *.
             do 2 esplit; eauto. now rewrite gather_eqs_inst.
        * unfold next; eapply msem_node_state_closed; eauto.
      + eapply NoDup_app'; eauto using NoDup_last_defined_n_eqs, NoDup_var_defined_fby.
        simpl_Forall; eauto using n_lastfby.
      + eauto using NoDup_var_defined_app.
      + intros * Find. clear - Find.
        eapply Env.from_list_find_In in Find. simpl_In.
        rewrite gather_eqs_last_flat_map in Hin. simpl_In.
        unfold gather_eq in *. cases. apply In_singleton in Hinf. inv Hinf. eauto.
      + rewrite map_app, <-app_assoc in *.
        intro k; specialize (Ck k); setoid_rewrite Forall_app; split; auto.
        apply Forall_forall; intros (x, (ck, islast)) In.
        eapply sem_clocked_var_eqs with (islast:=islast) in WCeqs as (CkVar&CkLast); eauto.
        * split; [|cases]; eauto.
        * rewrite fst_NoDupMembers, ? map_app, ? map_map, <- ? app_assoc, Permutation.Permutation_app_comm with (l:=map _ (n_out _)).
          erewrite map_ext with (l:=n_in _), map_ext with (l:=n_out _), map_ext with (l:=n_vars _).
          apply n_nodup.
          all:intros; destruct_conjs; auto.
        * eapply msem_sem_equations; eauto.
        * erewrite map_app, ? map_map, Permutation.Permutation_app_comm, map_ext with (l:=n_out _), map_ext with (l:=n_vars _).
          apply n_defd. 1,2:intros; destruct_conjs; auto.
        * rewrite filter_app, map_app, filter_nil; simpl. 2:simpl_Forall; auto.
          rewrite n_lastd1.
          clear - node. induction (n_vars node); simpl; auto.
          destruct_conjs; cases; simpl. constructor; auto.
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
