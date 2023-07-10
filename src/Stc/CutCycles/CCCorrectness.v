From Coq Require Import List Permutation.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CommonProgram.
From Velus Require Import IndexedStreams.
From Velus Require Import VelusMemory.
From Velus Require Import FunctionalEnvironment.
From Velus Require Import Fresh.

From Velus Require Import CoreExpr.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Stc.StcOrdered.
From Velus Require Import Stc.StcTyping.
From Velus Require Import Stc.StcClocking.
From Velus Require Import Stc.StcSemantics.
From Velus Require Import Stc.CutCycles.CC.

Module Type CCCORRECTNESS
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import OpAux : OPERATORS_AUX   Ids Op)
  (Import ComTyp: COMMONTYPING    Ids Op OpAux)
  (Import Cks   : CLOCKS          Ids Op OpAux)
  (Import Str   : INDEXEDSTREAMS  Ids Op OpAux Cks)
  (CE           : COREEXPR        Ids Op OpAux ComTyp Cks Str)
  (Import Syn   : STCSYNTAX       Ids Op OpAux Cks CE.Syn)
  (Import Ord   : STCORDERED      Ids Op OpAux Cks CE.Syn Syn)
  (Import Ty    : STCTYPING       Ids Op OpAux Cks CE.Syn Syn CE.Typ)
  (Import Clo   : STCCLOCKING     Ids Op OpAux Cks CE.Syn Syn Ord CE.Clo)
  (Import Sem   : STCSEMANTICS    Ids Op OpAux Cks CE.Syn Syn Ord Str CE.Sem)
  (Import ECC   : EXT_CC          Ids Op OpAux Cks CE.Syn Syn)
  (Import CC    : CC              Ids Op OpAux Cks CE.Syn Syn ECC).

  Import CE.Syn CE.Typ CE.Sem.

  Lemma cut_cycles_ordered : forall P,
      Ordered_systems P ->
      Ordered_systems (cut_cycles P).
  Proof.
    unfold Ordered_systems, Ordered_program; simpl.
    induction 1 as [|? us [Spec Names]]; simpl; constructor; simpl; auto.
    split; auto.
    - intros * Hin; apply Spec in Hin as (?&?&?& Find).
      intuition; apply cut_cycles_find_system in Find; eauto.
    - clear - Names; induction us; simpl; inv Names; constructor; auto.
  Qed.

  Lemma cut_cycles_initial_state : forall S P f,
      initial_state P f S ->
      initial_state (cut_cycles P) f S.
  Proof.
    induction S as [? IH] using memory_ind'.
    inversion_clear 1 as [????? Find ? Insts].
    apply cut_cycles_find_system in Find.
    econstructor; eauto.
    simpl; intros * Hin.
    apply Insts in Hin as (?&?&?).
    eexists; intuition; eauto.
  Qed.
  Global Hint Resolve cut_cycles_initial_state : stcsem.

  Lemma cut_cycles_state_closed : forall S P f,
      state_closed P f S ->
      state_closed (cut_cycles P) f S.
  Proof.
    induction S as [? IH] using memory_ind'.
    inversion_clear 1 as [????? Find ? Insts].
    apply cut_cycles_find_system in Find.
    econstructor; eauto.
    simpl; intros * Hin; pose proof Hin.
    apply Insts in Hin as (?&?&?).
    eexists; intuition; eauto.
  Qed.
  Global Hint Resolve cut_cycles_state_closed : stcsem.

  Section incl.
    Variable R R' : @FEnv.t var_last svalue.
    Variable Γ : list (ident * (type * bool)).

    Hypothesis InclV : forall x ty islast v,
        In (x, (ty, islast)) Γ -> R (Var x) = Some v -> R' (Var x) = Some v.
    Hypothesis InclL : forall x ty v,
        In (x, (ty, true)) Γ -> R (Last x) = Some v -> R' (Last x) = Some v.

    Lemma sem_exp_incl tys b : forall e v,
        wt_exp tys Γ e ->
        sem_exp_instant b R e v ->
        sem_exp_instant b R' e v.
    Proof.
      induction e; intros * Wc Sem; inv Wc; inv Sem; simpl in *.
      - (* const *) constructor; auto.
      - (* enum *) constructor; auto.
      - (* var *)
        constructor.
        unfold rename_var, sem_var_instant in *; eauto.
      - (* lasts *)
        constructor.
        unfold sem_var_instant in *; eauto.
      - (* when *)
        constructor; unfold sem_var_instant; eauto.
      - eapply Swhen_abs1; unfold sem_var_instant in *; eauto.
      - eapply Swhen_abs; unfold sem_var_instant in *; eauto.
      - (* unop *)
        econstructor; eauto.
      - econstructor; eauto.
      - (* binop *)
        econstructor; eauto.
      - econstructor; eauto.
    Qed.

    Lemma sem_cexp_incl tys b : forall e v,
        wt_cexp tys Γ e ->
        sem_cexp_instant b R e v ->
        sem_cexp_instant b R' e v.
    Proof.
      induction e using cexp_ind2; intros * Wc Sem; inv Wc; inv Sem.
      - (* merge *)
        rewrite Forall_app in *. repeat take (_ /\ _) and destruct it; simpl_Forall.
        econstructor; eauto.
        + unfold sem_var_instant in *; eauto.
        + apply Forall_app. split; simpl_Forall; eauto.
      - econstructor.
        + unfold sem_var_instant in *; eauto.
        + simpl_Forall; eauto.
      - (* case *)
        econstructor; eauto using sem_exp_incl.
        simpl_Forall.
        destruct a; eauto.
      - econstructor; eauto using sem_exp_incl.
        simpl_Forall.
        destruct x; eauto.
      - (* exp *)
        constructor; eauto using sem_exp_incl.
    Qed.

    Lemma sem_rhs_incl exts tys b : forall e v,
        wt_rhs exts tys Γ e ->
        sem_rhs_instant b R e v ->
        sem_rhs_instant b R' e v.
    Proof.
      intros * Wc Sem; inv Wc; inv Sem.
      - (* rhs *)
        econstructor; eauto.
        1:simpl_Forall; eauto using sem_exp_incl.
      - eapply Sextcall_abs with (tyins:=tyins); eauto.
        1:simpl_Forall; eauto using sem_exp_incl.
      - (* cexp *)
        constructor; eauto using sem_cexp_incl.
    Qed.

    Lemma sem_clock_incl tys b : forall ck b',
        wt_clock tys Γ ck ->
        sem_clock_instant b (var_env R) ck b' ->
        sem_clock_instant b (var_env R') ck b'.
    Proof.
      induction ck; intros * Wt Sem; inv Wt; inv Sem.
      - constructor.
      - constructor; unfold sem_var_instant in *; eauto.
      - constructor; unfold sem_var_instant in *; eauto.
      - eapply Son_abs2; unfold sem_var_instant in *; eauto.
    Qed.

    Definition rcks_spec tys Γ b R ckrs :=
      Forall (wt_clock tys Γ) ckrs
      /\ Forall (fun ckr => exists r, sem_clock_instant b (var_env R) ckr r) ckrs.

    Lemma sem_trconstr_incl {prefs1 prefs2} (P1: @program prefs1) (P2: @program prefs2) :
      forall b S I S' tc,
        wt_trconstr P1 Γ tc ->
        sem_trconstr P2 b R S I S' tc ->
        (forall s ckrs, Last_with_reset_in_tc s ckrs tc -> rcks_spec P1.(types) Γ b R ckrs) ->
        (forall s ckrs, Next_with_reset_in_tc s ckrs tc -> rcks_spec P1.(types) Γ b R ckrs) ->
        (forall s ckrs, Inst_with_reset_in_tc s ckrs tc -> rcks_spec P1.(types) Γ b R ckrs) ->
        sem_trconstr P2 b R' S I S' tc.
    Proof.
      intros * Wc Sem LastCks NextCks InstCks.
      inv Wc; inv Sem; simpl.
      - (* Def *)
        econstructor; eauto; unfold sem_var_instant in *; eauto.
        take (sem_arhs_instant _ _ _ _ _) and inv it; econstructor; eauto using sem_rhs_incl, sem_clock_incl.
      - (* Reset State *)
        econstructor; eauto using sem_clock_incl.
      - (* Update Last *)
        assert (Forall (fun ckr : clock => sem_clock_instant b (var_env R') ckr false) ckrs -> find_val x S = Some c) as SemS.
        { intros. take (Forall _ _ -> _) and apply it.
          edestruct LastCks as (WtCks&SemCks); [constructor|].
          simpl_Forall.
          take (sem_clock_instant _ (var_env R) _ _) and eapply sem_clock_incl in it as Ck'; eauto.
          eapply sem_clock_instant_det in H2; [|eauto]. subst; auto. }
        econstructor; eauto; unfold sem_var_instant in *; eauto.
        take (sem_caexp_instant _ _ _ _ _) and inv it; econstructor; eauto using sem_cexp_incl, sem_clock_incl.
      - (* Update Next *)
        assert (Forall (fun ckr : clock => sem_clock_instant b (var_env R') ckr false) ckrs -> find_val x S = Some c) as SemS.
        { intros. take (Forall _ _ -> _) and apply it.
          edestruct NextCks as (WtCks&SemCks); [constructor|].
          simpl_Forall.
          take (sem_clock_instant _ (var_env R) _ _) and eapply sem_clock_incl in it as Ck'; eauto.
          eapply sem_clock_instant_det in H2; [|eauto]. subst; auto. }
        econstructor; eauto; unfold sem_var_instant in *; eauto.
        take (sem_aexp_instant _ _ _ _ _) and inv it; econstructor; eauto using sem_exp_incl, sem_clock_incl.
      - (* Reset Inst *)
        econstructor; eauto using sem_clock_incl.
      - (* Update Inst *)
        assert (Forall (fun ckr : clock => sem_clock_instant b (var_env R') ckr false) rst -> find_inst i S ⌈≋⌉ Some Ii) as SemS.
        { intros. take (Forall _ _ -> _) and apply it.
          edestruct InstCks as (WtCks&SemCks); [constructor|].
          simpl_Forall.
          take (sem_clock_instant _ (var_env R) _ _) and eapply sem_clock_incl in it as Ck'; eauto.
          eapply sem_clock_instant_det in H4; [|eauto]. subst; auto.
        }
        assert (sem_vars_instant R' xs os) as Svs.
        { unfold sem_vars_instant, sem_var_instant, var_env in *.
          take (Forall2 _ xs (s_out _)) and apply Forall2_ignore2 in it.
          simpl_Forall; eauto. }
        cases; econstructor; eauto using sem_clock_incl.
        unfold sem_exps_instant in *; simpl_Forall; eauto using sem_exp_incl.
    Qed.

  End incl.

  Section rename.
    Variable R : @FEnv.t var_last svalue.
    Variable (x : var_last) (y : ident).

    Hypothesis SubL : forall x' v,
        x = Last x' -> R (Last x') = Some v -> R (Var y) = Some v.
    Hypothesis SubN : forall x' v,
        x = Var x' -> R (Var x') = Some v -> R (Var y) = Some v.

    (** Rename *)

    Lemma rename_exp_sem b : forall e v,
        sem_exp_instant b R e v ->
        sem_exp_instant b R (rename_exp x y e) v.
    Proof.
      induction e; intros * Sem; inv Sem; simpl in *.
      - (* const *) constructor; auto.
      - (* enum *) constructor; auto.
      - (* var *)
        constructor.
        unfold rename_var, sem_var_instant in *.
        cases_eqn Eq; eauto.
        rewrite equiv_decb_equiv in Eq0. inv Eq0; eauto.
      - (* lasts *)
        cases_eqn Eq; constructor.
        1-3:unfold sem_var_instant in *; eauto.
        rewrite equiv_decb_equiv in Eq0. inv Eq0; eauto.
      - (* when *)
        constructor; unfold sem_var_instant; eauto.
      - eapply Swhen_abs1; unfold sem_var_instant in *; eauto.
      - eapply Swhen_abs; unfold sem_var_instant in *; eauto.
      - (* unop *)
        econstructor; eauto. now rewrite rename_exp_typeof.
      - econstructor; eauto.
      - (* binop *)
        econstructor; eauto. now rewrite 2 rename_exp_typeof.
      - econstructor; eauto.
    Qed.

    Lemma rename_cexp_sem b : forall e v,
        sem_cexp_instant b R e v ->
        sem_cexp_instant b R (rename_cexp x y e) v.
    Proof.
      induction e using cexp_ind2; intros * Sem; inv Sem.
      - (* merge *)
        rewrite Forall_app in *. repeat take (_ /\ _) and destruct it; simpl_Forall.
        econstructor.
        2:rewrite map_app; simpl; eauto. all:eauto.
        + rewrite map_length. unfold sem_var_instant in *; eauto.
        + apply Forall_app. split; simpl_Forall; eauto.
      - econstructor.
        + unfold sem_var_instant in *; eauto.
        + simpl_Forall; eauto.
      - (* case *)
        econstructor; eauto using rename_exp_sem.
        simpl_Forall.
        destruct a; eauto.
      - econstructor; eauto using rename_exp_sem.
        simpl_Forall.
        destruct x0; eauto.
      - (* exp *)
        constructor; eauto using rename_exp_sem.
    Qed.

    Lemma rename_rhs_sem b : forall e v,
        sem_rhs_instant b R e v ->
        sem_rhs_instant b R (rename_rhs x y e) v.
    Proof.
      intros * Sem; inv Sem.
      - (* rhs *)
        econstructor; eauto.
        1,2:simpl_Forall; eauto using rename_exp_sem.
        now rewrite rename_exp_typeof.
      - eapply Sextcall_abs with (tyins:=tyins); eauto.
        1,2:simpl_Forall; eauto using rename_exp_sem.
        now rewrite rename_exp_typeof.
      - (* cexp *)
        constructor; eauto using rename_cexp_sem.
    Qed.

  End rename.

  Lemma rename_trconstr_sem {prefs1 prefs2} (P1: @program prefs1) (P2: @program prefs2) :
    forall b R S I S' x y tc,
      (forall x' v, x = Last x' -> R (Last x') = Some v -> R (Var y) = Some v) ->
      (forall x' v, x = Var x' -> R (Var x') = Some v -> R (Var y) = Some v) ->
      sem_trconstr P2 b R S I S' tc ->
      sem_trconstr P2 b R S I S' (rename_trconstr x y tc).
  Proof.
    intros * SubL SubN Sem.
    inv Sem; simpl.
    - (* Def *)
      cases; econstructor; eauto; unfold sem_var_instant in *; eauto.
      take (sem_arhs_instant _ _ _ _ _) and inv it; econstructor; eauto using rename_rhs_sem.
    - (* Reset State *)
      econstructor; eauto.
    - (* Reset Inst *)
      econstructor; eauto.
    - (* Update Last *)
      destruct (_ ==b _); econstructor; eauto; unfold sem_var_instant in *; eauto.
      take (sem_caexp_instant _ _ _ _ _) and inv it; econstructor; eauto using rename_cexp_sem.
    - (* Update Next *)
      destruct (_ ==b _); econstructor; eauto; unfold sem_var_instant in *; eauto.
      take (sem_aexp_instant _ _ _ _ _) and inv it; econstructor; eauto using rename_exp_sem.
    - (* Update Inst *)
      cases; econstructor; eauto.
      unfold sem_exps_instant in *; simpl_Forall; eauto.
      eapply rename_exp_sem; eauto.
  Qed.

  Fact fresh_idents_NoDup : forall xs xs' st st',
      @Fresh.fresh_idents stc (type * clock) xs st = (xs', st') ->
      NoDup (map snd (map fst xs')).
  Proof.
    unfold Fresh.fresh_idents.
    induction xs; intros * Hfresh;
      destruct_conjs; repeat Fresh.Tactics.inv_bind; constructor; eauto.
    - intros Hinm. simpl_In.
      eapply Fresh.fresh_idents_nIn_ids in H0.
      simpl_Forall.
      eapply H0, Fresh.Facts.fresh_ident_Inids; eauto.
  Qed.

  Lemma cut_cycles_tcs_sem {prefs1 prefs2} :
    forall (P1: @program prefs1) (P2: @program prefs2) Γ b R S I S' lasts nexts tcs tcs' st',
      Forall (AtomOrGensym (PSP.of_list lustre_prefs)) (map fst Γ) ->
      Forall (AtomOrGensym (PSP.of_list lustre_prefs)) (map fst nexts) ->
      last_consistency tcs ->
      next_consistency tcs ->
      inst_consistency tcs ->
      (forall x ty ck c, In (x, (c, ty, ck)) lasts -> exists ckrs e, In (TcUpdate ck ckrs (UpdLast x e)) tcs) ->
      (forall x ty ck c, In (x, (c, ty, ck)) nexts -> exists ckrs e, In (TcUpdate ck ckrs (UpdNext x e)) tcs) ->
      Forall (wt_trconstr P1 Γ) tcs ->
      Forall (sem_trconstr P2 b R S I S') tcs ->
      cut_cycles_tcs lasts nexts tcs Fresh.init_st = (tcs', st') ->
      exists R',
        (forall x ty islast v, In (x, (ty, islast)) Γ -> R (Var x) = Some v -> R' (Var x) = Some v) /\
        Forall (sem_trconstr P2 b R' S I S') tcs'.
  Proof.
    intros * (* NDl NDn *) At AtN LastCons NextCons InstCons LastIn NextIn Wt Sem Cut.
    unfold cut_cycles_tcs in *. repeat Fresh.Tactics.inv_bind.
    rename x into lasts'. rename x1 into nexts'.
    assert (Wt':=Wt); rewrite Forall_forall in Wt'.
    assert (Sem':=Sem); rewrite Forall_forall in Sem'.

    assert (NoDupMembers (map (fun x2 => (snd x2, fst x2)) (map fst lasts'))) as NDl'.
    { rewrite fst_NoDupMembers, ? map_map. simpl.
      apply fresh_idents_NoDup in H. now rewrite map_map in H. }

    assert (NoDupMembers (map (fun x2 => (snd x2, fst x2)) (map fst nexts'))) as NDn'.
    { rewrite fst_NoDupMembers, ? map_map. simpl.
      apply fresh_idents_NoDup in H0. now rewrite map_map in H0. }

    (* New environment *)
    remember (fun x => match x with
                    | Var x =>
                        match Env.find x (Env.from_list (map (fun x => (snd x, fst x)) (map fst lasts'))) with
                        | Some y => R (Last y)
                        | None => match Env.find x (Env.from_list (map (fun x => (snd x, fst x)) (map fst nexts'))) with
                                 | Some y => R (Var y)
                                 | None => R (Var x)
                                 end
                        end
                    | Last x => R (Last x)
                    end) as R'.

    assert (forall x ty islast v,
               In (x, (ty, islast)) Γ -> R (Var x) = Some v -> R' (Var x) = Some v) as Incl.
    { intros * In Sv. subst.
      cases_eqn Find; auto; exfalso.
      - apply Env.from_list_find_In in Find. simpl_In.
        eapply Fresh.fresh_idents_prefixed in H. simpl_Forall; subst.
        eapply Fresh.Facts.contradict_AtomOrGensym; eauto using stc_not_in_lustre_prefs.
      - apply Env.from_list_find_In in Find0. simpl_In.
        eapply Fresh.fresh_idents_prefixed in H0. simpl_Forall; subst.
        eapply Fresh.Facts.contradict_AtomOrGensym; eauto using stc_not_in_lustre_prefs.
    }

    exists R'. split; auto.
    rewrite ? Forall_app. repeat split; simpl_Forall.
    - eapply Fresh.fresh_idents_In' in H1 as In'; eauto. simpl_In.
      apply LastIn in Hin as (?&?&Hin').
      specialize (Wt' _ Hin'). inv Wt'. specialize (Sem' _ Hin'). inv Sem'.
      econstructor.
      2:{ unfold sem_var_instant in *.
          erewrite Env.find_In_from_list; eauto. solve_In. }
      take (sem_caexp_instant _ _ _ _ _) and inv it; econstructor; eauto using sem_clock_incl.
      1,2:repeat constructor; auto.
    - eapply Fresh.fresh_idents_In' in H1 as In'; eauto. simpl_In.
      apply NextIn in Hin as (?&?&Hin').
      specialize (Wt' _ Hin'). inv Wt'. specialize (Sem' _ Hin'). inv Sem'.
      econstructor.
      2:{ unfold sem_var_instant in *.
          destruct (Env.find _ _) eqn:Find.
          - exfalso.
            apply Env.from_list_find_In in Find. simpl_In.
            apply Fresh.fresh_idents_In_ids in H. apply Fresh.fresh_idents_nIn_ids in H0.
            simpl_Forall. contradiction.
          - erewrite Env.find_In_from_list; eauto. solve_In.
      }
      take (sem_aexp_instant _ _ _ _ _) and inv it; econstructor; eauto using sem_clock_incl.
      1,2:repeat constructor; eapply Incl; eauto.
    - rewrite ? map_fold_rename in H1. simpl_In. simpl_Forall.
      eapply fold_left_ind with (Pb:=fun x => In x nexts').
      2:eapply fold_left_ind with (Pb:=fun x => In x lasts'). 4,5:simpl_Forall; eauto.
      + intros * Sem1 In. destruct_conjs.
        eapply rename_trconstr_sem in Sem1; eauto.
        1,2:intros * Eq Find; inv Eq.
        eapply Fresh.fresh_idents_In' in H0 as InNext; eauto. simpl_In. simpl_Forall.
        destruct (Env.find _ _) eqn:Find1 in Find.
        1:{ exfalso. apply Env.from_list_find_In in Find1. simpl_In.
            eapply Fresh.fresh_idents_prefixed in H. simpl_Forall; subst.
            eapply Fresh.Facts.contradict_AtomOrGensym; eauto using stc_not_in_lustre_prefs.
        }
        destruct (Env.find _ _) eqn:Find2 in Find.
        1:{ exfalso. apply Env.from_list_find_In in Find2. simpl_In.
            eapply Fresh.fresh_idents_prefixed in H0. simpl_Forall; subst.
            eapply Fresh.Facts.contradict_AtomOrGensym; eauto using stc_not_in_lustre_prefs.
        }
        destruct (Env.find i0 _) eqn:Find3.
        1:{ exfalso.
            apply Env.from_list_find_In in Find3. simpl_In.
            apply Fresh.fresh_idents_In_ids in H. apply Fresh.fresh_idents_nIn_ids in H0.
            simpl_Forall. contradiction.
        }
        erewrite Env.find_In_from_list; eauto. solve_In.
      + intros * Sem1 In. destruct_conjs.
        eapply rename_trconstr_sem in Sem1; eauto.
        1,2:intros * Eq Find; inv Eq.
        erewrite Env.find_In_from_list; eauto. solve_In.
      + eapply sem_trconstr_incl; eauto.
        * intros * Lr; split; simpl_Forall.
          1,2:(edestruct LastCons as (Ir&_); [unfold Last_with_reset_in; solve_Exists|];
               take (In _ ckrs) and specialize (Ir it); unfold Is_reset_state_in in *; simpl_Exists; inv Ir).
          -- specialize (Wt' _ Hin). inv Wt'; auto.
          -- specialize (Sem' _ Hin). inv Sem'; eauto.
        * intros * Lr; split; simpl_Forall.
          1,2:(edestruct NextCons as (Ir&_); [unfold Next_with_reset_in; solve_Exists|];
               take (In _ ckrs) and specialize (Ir it); unfold Is_reset_state_in in *; simpl_Exists; inv Ir).
          -- specialize (Wt' _ Hin). inv Wt'; auto.
          -- specialize (Sem' _ Hin). inv Sem'; eauto.
        * intros * Lr; split; simpl_Forall.
          1,2:(edestruct InstCons as (Ir&_); [unfold Inst_with_reset_in; solve_Exists|];
               take (In _ ckrs) and specialize (Ir it); unfold Is_reset_inst_in in *; simpl_Exists; inv Ir).
          -- specialize (Wt' _ Hin). inv Wt'; auto.
          -- specialize (Sem' _ Hin). inv Sem'; eauto.

  Qed.

  Fact sem_clock_incl1 Γ R R' b : forall ck b',
      (forall x, InMembers x Γ -> exists vs, R (Var x) = vs /\ R' (Var x) = vs) ->
      wc_clock Γ ck ->
      sem_clock_instant b (var_env R) ck b' ->
      sem_clock_instant b (var_env R') ck b'.
  Proof.
    induction ck; intros * Incl Wc Sem; inv Wc; inv Sem.
    - constructor.
    - constructor; unfold sem_var_instant, var_env in *; eauto.
      edestruct Incl as (?&V&V'); eauto using In_InMembers. rewrite V in H6; subst; auto.
    - constructor; unfold sem_var_instant, var_env in *; eauto.
      edestruct Incl as (?&V&V'); eauto using In_InMembers. rewrite V in H6; subst; auto.
    - eapply Son_abs2; unfold sem_var_instant, var_env in *; eauto.
      edestruct Incl as (?&V&V'); eauto using In_InMembers. rewrite V in H6; subst; auto.
  Qed.

  Fact sem_clock_incl2 Γ R R' b : forall ck b',
      (forall x, InMembers x Γ -> exists vs, R (Var x) = vs /\ R' (Var x) = vs) ->
      wc_clock Γ ck ->
      sem_clock_instant b (var_env R') ck b' ->
      sem_clock_instant b (var_env R) ck b'.
  Proof.
    induction ck; intros * Incl Wc Sem; inv Wc; inv Sem.
    - constructor.
    - constructor; unfold sem_var_instant, var_env in *; eauto.
      edestruct Incl as (?&V&V'); eauto using In_InMembers. rewrite V' in H6; subst; auto.
    - constructor; unfold sem_var_instant, var_env in *; eauto.
      edestruct Incl as (?&V&V'); eauto using In_InMembers. rewrite V' in H6; subst; auto.
    - eapply Son_abs2; unfold sem_var_instant, var_env in *; eauto.
      edestruct Incl as (?&V&V'); eauto using In_InMembers. rewrite V' in H6; subst; auto.
  Qed.

  Theorem cut_cycles_sem_system : forall P f xs S S' ys,
      wt_program P ->
      wc_program P ->
      sem_system P f xs S S' ys ->
      sem_system (cut_cycles P) f xs S S' ys.
  Proof.
    intros * Wt Wc Sem.
    eapply sem_system_mult with
      (P_system := fun f S xs ys S' =>
                     sem_system (cut_cycles P) f S xs ys S')
      (P_trconstr := fun base R S I S' tc =>
                       sem_trconstr (cut_cycles P) base R S I S' tc)
      in Sem; eauto with stcsem.
    - intros * ???.
      econstructor; eauto.
      cases; eauto with stcsem.
    - intros * ?????????.
      eapply wt_program_find_unit in Wt as ((Wt1&_)&_); [|eauto].
      eapply wc_find_system in Wc as WcS; [|eauto]. destruct WcS as (Wc1&_&_&Wc4).
      match goal with H: find_system _ _ = _ |- _ => apply cut_cycles_find_system in H end.
      eapply cut_cycles_tcs_sem with (P2:=cut_cycles P) in Wt1 as (R'&Ref&SemTcs'); eauto using surjective_pairing.
      eapply SSystem with (I := I) (R := R'); simpl; eauto with stcsem; try eapply SemTcs'.
      1-3:unfold sem_vars_instant, sem_var_instant, sem_clocked_vars_instant, var_env in *; simpl_Forall.
      + eapply Ref; eauto. rewrite ? map_app, ? in_app_iff. left. left. solve_In.
      + eapply Ref; eauto. rewrite ? map_app, ? in_app_iff. left. right. right. solve_In.
      + split; auto. unfold sem_clocked_var_instant in *.
        unfold wc_env, idsnd in *. simpl_Forall.
        take (_ /\ _) and destruct it as (Abs1&Abs2).
        take (_ /\ _) and destruct it as (Pres1&Pres2).
        assert (forall x ty ck v, In (x, (ty, ck)) (s_in s) ->
                              R (Var x) = Some v -> R' (Var x) = Some v) as Rin.
        { intros. eapply Ref; eauto.
          rewrite ? map_app, ? in_app_iff. left. left. solve_In. }
        assert (forall x, InMembers x (map (fun xtc => (fst xtc, snd (snd xtc))) (s_in s)) ->
                     exists vs, R (Var x) = vs /\ R' (Var x) = vs) as RinIff.
        { intros * InM. simpl_In. eapply Forall2_ignore2 in H0. simpl_Forall. eauto. }
        split; split.
        * intros Sck. eapply sem_clock_incl2, Pres1 in Sck as (?&V); eauto.
          unfold sem_var_instant in *. eauto.
        * intros (?&Sv). unfold sem_var_instant in *.
          edestruct RinIff as (?&Sv1&Sv2); [solve_In|]; simpl in *.
          rewrite Sv in Sv2; inv Sv2.
          eapply sem_clock_incl1, Pres2; eauto.
        * intros Sck. eapply sem_clock_incl2, Abs1 in Sck as V; eauto.
          unfold sem_var_instant in *. eauto.
        * intros Sv. unfold sem_var_instant in *.
          edestruct RinIff as (?&Sv1&Sv2); [solve_In|]; simpl in *.
          rewrite Sv in Sv2; inv Sv2.
          eapply sem_clock_incl1, Abs2; eauto.
      (* + apply NoDupMembers_filter, s_nodup_lasts. *)
      (* + apply NoDupMembers_filter, s_nodup_nexts. *)
      + pose proof (s_good s) as Good. rewrite ? map_app, ? Forall_app in *.
        firstorder; simpl_Forall; auto.
      + pose proof (s_good s) as (_&_&Good&_).
        simpl_Forall. simpl_In. cases. inv Hf. now simpl_Forall.
      + apply s_last_consistency.
      + apply s_next_consistency.
      + apply s_inst_consistency.
      + intros * In. simpl_In. cases. inv Hf.
        assert (In x (map fst (s_lasts s))) as In by solve_In.
        rewrite s_lasts_in_tcs, <-lasts_of_In in In.
        unfold Is_update_last_in in *. simpl_Exists. simpl_Forall.
        inv In. take (wc_trconstr _ _ _) and inv it.
        rewrite ? in_app_iff in *. firstorder; simpl_In.
        eapply NoDupMembers_det in Hin; eauto using s_nodup_lasts. inv Hin. eauto.
      + intros * In. simpl_In. cases. inv Hf.
        assert (In x (map fst (s_nexts s))) as In by solve_In.
        rewrite s_nexts_in_tcs, <-nexts_of_In in In.
        unfold Is_update_next_in in *. simpl_Exists. simpl_Forall.
        inv In. take (wc_trconstr _ _ _) and inv it.
        rewrite ? in_app_iff in *. firstorder; simpl_In.
        1:{ exfalso.
            pose proof (s_nodup s) as ND. rewrite ? app_assoc, <- ? map_app, <- ? app_assoc in ND.
            eapply NoDup_app_In in ND; [|solve_In].
            eapply ND, in_or_app. right. solve_In. }
        eapply NoDupMembers_det in Hin; eauto using s_nodup_nexts. inv Hin. eauto.
  Qed.

  Global Hint Resolve cut_cycles_sem_system : stcsem.

  Corollary cut_cycles_loop :
    forall n P f xss yss S,
      wt_program P ->
      wc_program P ->
      loop P f xss yss S n ->
      loop (cut_cycles P) f xss yss S n.
  Proof.
    cofix COFIX; inversion_clear 3.
    econstructor; eauto with stcsem.
  Qed.

End CCCORRECTNESS.


Module CCCorrectnessFun
  (Ids   : IDS)
  (Op    : OPERATORS)
  (OpAux : OPERATORS_AUX   Ids Op)
  (ComTyp: COMMONTYPING    Ids Op OpAux)
  (Cks   : CLOCKS          Ids Op OpAux)
  (Str   : INDEXEDSTREAMS  Ids Op OpAux Cks)
  (CE           : COREEXPR        Ids Op OpAux ComTyp Cks Str)
  (Syn   : STCSYNTAX       Ids Op OpAux Cks CE.Syn)
  (Ord   : STCORDERED      Ids Op OpAux Cks CE.Syn Syn)
  (Ty    : STCTYPING       Ids Op OpAux Cks CE.Syn Syn CE.Typ)
  (Clo   : STCCLOCKING     Ids Op OpAux Cks CE.Syn Syn Ord CE.Clo)
  (Sem   : STCSEMANTICS    Ids Op OpAux Cks CE.Syn Syn Ord Str CE.Sem)
  (ECC   : EXT_CC          Ids Op OpAux Cks CE.Syn Syn)
  (CC    : CC              Ids Op OpAux Cks CE.Syn Syn ECC)
<: CCCORRECTNESS Ids Op OpAux ComTyp Cks Str CE Syn Ord Ty Clo Sem ECC CC.
  Include CCCORRECTNESS Ids Op OpAux ComTyp Cks Str CE Syn Ord Ty Clo Sem ECC CC.
End CCCorrectnessFun.
