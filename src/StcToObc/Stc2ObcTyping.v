From Velus Require Import Stc.
From Velus Require Import Obc.

From Velus Require Import StcToObc.Translation.

From Velus Require Import VelusMemory.
From Velus Require Import Common.
From Velus Require Import CommonTyping.

From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import Permutation.

Open Scope nat.
Open Scope list.

Module Type STC2OBCTYPING
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Ids Op)
       (Import ComTyp: COMMONTYPING    Ids Op OpAux)
       (Import Cks   : CLOCKS          Ids Op OpAux)
       (Import Str   : INDEXEDSTREAMS  Ids Op OpAux Cks)
       (Import CE    : COREEXPR    Ids Op OpAux ComTyp Cks Str)
       (Import Stc   : STC         Ids Op OpAux ComTyp Cks Str CE)
       (Import Obc   : OBC         Ids Op OpAux ComTyp)
       (Import Trans : TRANSLATION Ids Op OpAux Cks CE.Syn Stc.Syn Obc.Syn).

  Fact typeof_tovar:
    forall mems x t,
      typeof (tovar mems (x, t)) = t.
  Proof.
    unfold tovar; intros; cases.
  Qed.

  Lemma wt_stmt_fold_left_shift:
    forall A xs P insts mems vars (f: A -> stmt) acc,
      wt_stmt P insts mems vars (fold_left (fun s x => Comp (f x) s) xs acc) <->
      wt_stmt P insts mems vars (fold_left (fun s (x : A) => Comp (f x) s) xs Skip)
      /\ wt_stmt P insts mems vars acc.
  Proof.
    induction xs; simpl; split; try now intuition eauto using wt_stmt.
    - rewrite IHxs; intros (?& WT); inv WT.
      rewrite IHxs; intuition.
    - rewrite IHxs; intros ((?& WT) &?); inv WT.
      rewrite IHxs; intuition.
  Qed.

  Lemma wt_stmt_fold_left_lift:
    forall A xs P insts mems vars (f: A -> stmt) acc,
      wt_stmt P insts mems vars (fold_left (fun s x => Comp s (f x)) xs acc) <->
      wt_stmt P insts mems vars (fold_left (fun s (x : A) => Comp s (f x)) xs Skip)
      /\ wt_stmt P insts mems vars acc.
  Proof.
    induction xs; simpl; split; try now intuition eauto using wt_stmt.
    - rewrite IHxs; intros (?& WT); inv WT.
      rewrite IHxs; intuition.
    - rewrite IHxs; intros ((?& WT) &?); inv WT.
      rewrite IHxs; intuition.
  Qed.

  Section Expressions.

    Variable p      : program.
    Variable types  : list type.
    Variable Γ      : list (ident * (type * bool)).
    Variable Γm     : list (ident * type).
    Variable Γv     : list (ident * type).
    Variable memset : PS.t.

    Hypothesis TypesSpec:
      types = p.(Obc.Syn.types).

    Definition type_env_spec :=
      forall x ty islast,
        In (x, (ty, islast)) Γ ->
        if PS.mem x memset then In (x, ty) Γm else In (x, ty) Γv.

    Definition last_env_spec :=
      forall x ty,
        In (x, (ty, true)) Γ ->
        PS.In x memset.

    Hypothesis NvarsSpec: type_env_spec.
    Hypothesis NlastsSpec: last_env_spec.

    Ltac FromMemset :=
      match goal with
      (* | H: In (?x, _) nvars |- context [ bool_var memset ?x ] => *)
      (*   unfold bool_var; simpl; *)
      (*   apply NvarsSpec in H; cases *)
      | H: In (?x, _) Γ |- context [ PS.mem ?x memset ] =>
        apply NvarsSpec in H; cases
      end.

    Lemma typeof_correct:
      forall e,
        typeof (translate_exp memset e) = CE.Syn.typeof e.
    Proof.
      induction e; intros; simpl; auto; cases.
    Qed.

    Corollary typeof_arg_correct:
      forall clkvars ck e,
        typeof (translate_arg memset clkvars ck e) = CE.Syn.typeof e.
    Proof.
      unfold translate_arg; intros.
      cases; simpl; cases.
      apply typeof_correct.
    Qed.

    Lemma translate_exp_wt:
      forall e,
        CE.Typ.wt_exp types Γ e ->
        wt_exp p Γm Γv (translate_exp memset e).
    Proof.
      induction e; simpl; intro WTle; inv WTle; eauto using wt_exp.
      - FromMemset; eauto using wt_exp.
      - assert (PS.mem i memset = true) as Mem by (apply PSF.mem_1; eauto).
        apply NvarsSpec in H0. rewrite Mem in *. eauto using wt_exp.
      - econstructor; eauto; now rewrite typeof_correct.
      - econstructor; eauto; now rewrite 2 typeof_correct.
    Qed.
    Local Hint Resolve translate_exp_wt : obctyping.

    Corollary translate_arg_wt:
      forall e clkvars ck,
        CE.Typ.wt_exp types Γ e ->
        wt_exp p Γm Γv (translate_arg memset clkvars ck e).
    Proof.
      unfold translate_arg, var_on_base_clock; intros * WT.
      destruct e; try apply translate_exp_wt; simpl; auto.
      inv WT.
      take (In _ _) and apply NvarsSpec in it.
      destruct (PS.mem i memset); simpl; eauto using wt_exp.
      cases; eauto using wt_exp.
    Qed.
    Local Hint Resolve translate_arg_wt : obctyping.

    Lemma translate_cexp_wt:
      forall insts assign e,
        wt_cexp types Γ e ->
        (forall oe, wt_exp p Γm Γv oe -> typeof oe = typeofc e -> wt_stmt p insts Γm Γv (assign oe)) ->
        wt_stmt p insts Γm Γv (translate_cexp memset assign e).
    Proof.
      induction e using cexp_ind2'; simpl; intros WTe Hv; inversion WTe.
      - subst; unfold tovar.
        FromMemset; econstructor; simpl; eauto using wt_exp, wt_stmt; try rewrite map_length; auto;
          intros * Hin; apply in_map_iff in Hin as (? & E & Hin); inv E;
            repeat (take (Forall _ _) and eapply Forall_forall in it; eauto); subst; auto.
      - take (CE.Typ.wt_exp _ _ _) and apply translate_exp_wt in it.
        subst.
        econstructor; eauto using wt_stmt.
        + now rewrite typeof_correct.
        + now rewrite map_length.
        + intros * Hin; apply in_map_iff in Hin as (? & E & Hin);
            apply option_map_inv in E as (?&?&?); subst;
              repeat (take (Forall _ _) and eapply Forall_forall in it; eauto); subst; simpl in *; auto.
          apply it; auto.
          take (forall e, _ -> typeofc e = _) and rewrite it; auto.
      - eapply Hv; eauto using translate_exp_wt.
        now rewrite typeof_correct.
    Qed.

    Lemma Control_wt:
      forall insts ck s,
        wt_clock types Γ ck ->
        wt_stmt p insts Γm Γv s ->
        wt_stmt p insts Γm Γv (Control memset ck s).
    Proof.
      induction ck; intros s WTc WTs;
        inversion_clear WTc as [|?????? Hin]; auto.
      simpl; FromMemset; apply IHck; eauto;
        subst; econstructor; simpl; eauto using wt_exp; try rewrite skip_branches_with_length;
          eauto using wt_stmt.
      - clear - WTs. induction (length tn).
        + rewrite skip_branches_with_0; contradiction.
        + rewrite skip_branches_with_S; setoid_rewrite in_app; intros * [|Hin]; auto.
          inv Hin; cases; auto; contradiction.
      - clear - WTs. induction (length tn).
        + rewrite skip_branches_with_0; contradiction.
        + rewrite skip_branches_with_S; setoid_rewrite in_app; intros * [|Hin]; auto.
          inv Hin; cases; auto; contradiction.
    Qed.

    Lemma Control_wt_inv:
      forall insts ck s,
        wt_clock types Γ ck ->
        wt_stmt p insts Γm Γv (Control memset ck s) ->
        wt_stmt p insts Γm Γv s.
    Proof.
      clear TypesSpec.
      induction ck; simpl; intros s WTc WTcontrol; auto.
      inv WTc.
      apply IHck in WTcontrol; auto.
      inv WTcontrol.
      simpl in *. take (_ < _) and apply skip_branches_with_In with (s := s) in it; eauto.
    Qed.

  End Expressions.
  Local Hint Resolve translate_exp_wt translate_cexp_wt Control_wt : obctyping.

  Inductive trconstr_mems_spec (mems: PS.t) : trconstr -> Prop :=
  | tmsDef: forall x ck e,
      ~ PS.In x mems ->
      trconstr_mems_spec mems (TcDef ck x e)
  | tmsResetL: forall ckr x ty c,
      PS.In x mems ->
      trconstr_mems_spec mems (TcReset ckr (ResState x ty c))
  | tmsResetI: forall ckr s f,
      trconstr_mems_spec mems (TcReset ckr (ResInst s f))
  | tmsUpdL: forall x ck ckrs e,
      PS.In x mems ->
      trconstr_mems_spec mems (TcUpdate ck ckrs (UpdLast x e))
  | tmsUpdN: forall x ck ckrs e,
      PS.In x mems ->
      trconstr_mems_spec mems (TcUpdate ck ckrs (UpdNext x e))
  | tmsUpdI: forall ck ckrs s xs f es,
      Forall (fun x => ~ PS.In x mems) xs ->
      trconstr_mems_spec mems (TcUpdate ck ckrs (UpdInst s xs f es)).

  Inductive trconstr_insts_spec (insts: list (ident * ident)) : trconstr -> Prop :=
  | tisDef: forall x ck e,
      trconstr_insts_spec insts (TcDef ck x e)
  | tisReset: forall ckr x ty c,
      trconstr_insts_spec insts (TcReset ckr (ResState x ty c))
  | tisIReset: forall ckr s f,
      In (s, f) insts ->
      trconstr_insts_spec insts (TcReset ckr (ResInst s f))
  | tisUpdL: forall ck ckrs x e,
      trconstr_insts_spec insts (TcUpdate ck ckrs (UpdLast x e))
  | tisUpdN: forall ck ckrs x e,
      trconstr_insts_spec insts (TcUpdate ck ckrs (UpdNext x e))
  | tisUpdI: forall ck ckrs s xs f es,
      In (s, f) insts ->
      trconstr_insts_spec insts (TcUpdate ck ckrs (UpdInst s xs f es)).

  Lemma translate_tc_wt:
    forall P insts Γ Γm' Γv' memset clkvars tc,
      type_env_spec Γ Γm' Γv' memset ->
      last_env_spec Γ memset ->
      trconstr_mems_spec memset tc ->
      trconstr_insts_spec insts tc ->
      NoDup (variables_tc tc) ->
      wt_trconstr P Γ tc ->
      wt_stmt (translate P) insts Γm' Γv' (translate_tc memset clkvars tc).
  Proof.
    intros * TypeEnvSpec LastEnvSpec Spec_m Spec_i Nodup WT; induction WT; try (take (wt_rhs _ _ _ _) and inv it);
      inv Spec_m; inv Spec_i;
      try eapply Control_wt; eauto.
    - econstructor; eauto; simpl_Forall; eauto using translate_exp_wt.
      + now rewrite typeof_correct.
      + simpl in *. specialize (TypeEnvSpec x (Tprimitive tyout)).
        rewrite PSE.mem_3 in TypeEnvSpec; eauto.
    - eapply translate_cexp_wt; eauto.
      apply TypeEnvSpec in H. rewrite PSE.mem_3 in H; auto. simpl in *.
      intros; subst. econstructor; eauto.
      congruence.
    - eapply TypeEnvSpec in H. rewrite PSF.mem_1 in H; auto.
      take (wt_const _ _ _) and inv it; constructor; eauto using wt_exp.
    - eapply translate_cexp_wt; eauto.
      apply TypeEnvSpec in H. rewrite PSF.mem_1 in H; auto. simpl in *.
      intros; subst. econstructor; eauto.
      congruence.
    - econstructor; eauto; simpl_Forall; eauto using translate_exp_wt.
      + rewrite typeof_correct.
        specialize (TypeEnvSpec _ _ _ H).
        rewrite PSF.mem_1 in TypeEnvSpec; eauto.
    - take (find_system _ _ = _) and apply find_unit_transform_units_forward in it.
      econstructor; eauto.
      + apply exists_reset_method.
      + constructor.
      + constructor.
    - take (find_system _ _ = _) and apply find_unit_transform_units_forward in it.
      econstructor; eauto.
      + apply exists_step_method.
      + simpl.
        take (NoDup _) and clear it.
        unfold idfst. simpl_Forall.
        apply TypeEnvSpec in H7. rewrite PSE.mem_3 in H7; auto.
      + simpl.
        take (NoDup _) and clear it.
        unfold idfst. simpl_Forall.
        now rewrite typeof_arg_correct.
      + simpl_Forall.
        eapply translate_arg_wt; eauto.
  Qed.

  Lemma translate_tcs_wt:
    forall P insts Γ Γm' Γv' memset clkvars tcs,
      type_env_spec Γ Γm' Γv' memset ->
      last_env_spec Γ memset ->
      Forall (trconstr_mems_spec memset) tcs ->
      Forall (trconstr_insts_spec insts) tcs ->
      NoDup (variables tcs) ->
      Forall (wt_trconstr P Γ) tcs ->
      wt_stmt (translate P) insts Γm' Γv' (translate_tcs memset clkvars tcs).
  Proof.
    intros * TypeEnvSpec LastEnvSpec Spec_m Spec_i Nodup WT.
    cut (forall s,
            wt_stmt (translate P) insts Γm' Γv' s ->
            wt_stmt (translate P) insts Γm' Γv'
                    (fold_left (fun i tc => Comp (translate_tc memset clkvars tc) i) tcs s));
      unfold translate_tcs; eauto using wt_stmt.
    induction tcs; simpl; auto.
    inv Spec_m; inv Spec_i; inv WT; intros * WTs.
    unfold variables in *; simpl in Nodup; apply NoDup_app'_iff in Nodup as (?&?&?).
    apply IHtcs; auto.
    constructor; auto.
    eapply translate_tc_wt; eauto.
  Qed.

  Lemma s_trconstr_mems_spec {prefs} :
    forall (s: @system prefs),
      Forall (trconstr_mems_spec (ps_from_list (map fst (s_lasts s ++ s_nexts s)))) (s_tcs s).
  Proof.
    intro.
    pose proof (s_lasts_in_tcs s) as Last.
    pose proof (s_nexts_in_tcs s) as Next.
    pose proof (s_nodup_variables_lasts_nexts s) as Nodup1.
    apply Forall_forall; intros tc Hin; destruct tc as [|? []|?? []]; constructor.
    - rewrite ps_from_list_In.
      eapply NoDup_app_In; eauto. unfold variables. solve_In. simpl; auto.
    - rewrite ps_from_list_In, map_app, Last, Next, <-map_app.
      apply s_state_reset_incl, reset_states_of_In. exists c.
      apply Exists_exists; eauto using Is_reset_state_in_tc.
    - rewrite ps_from_list_In, map_app, Last, Next, in_app_iff. left.
      apply lasts_of_In, Exists_exists;
        eauto using Is_update_last_in_tc.
    - rewrite ps_from_list_In, map_app, Last, Next, in_app_iff. right.
      apply nexts_of_In, Exists_exists;
        eauto using Is_update_next_in_tc.
    - apply Forall_forall; intros * Hin'.
      rewrite ps_from_list_In.
      eapply NoDup_app_In; eauto.
      apply Is_variable_in_variables, Exists_exists;
        eauto using Is_variable_in_tc.
  Qed.
  Local Hint Resolve s_trconstr_mems_spec : obctyping.

  Lemma s_trconstr_insts_spec {prefs} :
    forall (s: @system prefs),
      Forall (trconstr_insts_spec (s_subs s)) (s_tcs s).
  Proof.
    intros.
    pose proof (s_subs_insts_of s) as P.
    apply Forall_forall; intros tc Hin; destruct tc as [|? []|?? []]; constructor.
    - rewrite P.
      apply s_inst_reset_incl.
      clear P; induction (s_tcs s); try contradiction.
      inv Hin; simpl; auto.
      cases; right; auto.
    - rewrite P.
      clear P; induction (s_tcs s); try contradiction.
      inv Hin; simpl; auto.
      cases; right; auto.
  Qed.
  Local Hint Resolve s_trconstr_insts_spec : obctyping.

  Lemma s_type_env_spec {prefs} :
    forall (s: @system prefs),
      type_env_spec
        (map (fun '(x, (ty, _)) => (x, (ty, false))) (s_in s ++ s_vars s ++ s_out s) ++
           map (fun '(x, (_, ty, _)) => (x, (ty, true))) (s_lasts s) ++ map (fun '(x, (_, ty, _)) => (x, (ty, false))) (s_nexts s))
        (map (fun xc : ident * (const * type * clock) => (fst xc, snd (fst (snd xc)))) (s_lasts s ++ s_nexts s))
        (idfst (s_in s) ++ idfst (s_vars s) ++ idfst (s_out s))
        (ps_from_list (map fst (s_lasts s ++ s_nexts s))).
  Proof.
    intros ???? Hin.
    cases_eqn E.
    - apply PSF.mem_2 in E; rewrite ps_from_list_In in E.
      pose proof (s_nodup s) as N.
      apply in_app_iff in Hin as [|]; simpl_In.
      + exfalso.
        rewrite <- ? map_app, ? app_assoc, <- ? map_app, <- app_assoc in N.
        eapply NoDup_app_In in N; [eapply N|]; solve_In.
      + clear - H. apply in_app_iff in H as [|]; solve_In; eauto with datatypes; auto.
    - apply PSE.mem_4 in E; rewrite ps_from_list_In in E.
      eapply not_In2_app in Hin.
      + clear - Hin. rewrite <-2 idfst_app. solve_In.
      + contradict E.
        apply in_app_iff in E as [|]; solve_In; eauto with datatypes; auto.
  Qed.

  Lemma s_last_env_spec {prefs} :
    forall (s: @system prefs),
      last_env_spec
        (map (fun '(x, (ty, _)) => (x, (ty, false))) (s_in s ++ s_vars s ++ s_out s) ++
           map (fun '(x, (_, ty, _)) => (x, (ty, true))) (s_lasts s) ++ map (fun '(x, (_, ty, _)) => (x, (ty, false))) (s_nexts s))
        (ps_from_list (map fst (s_lasts s++s_nexts s))).
  Proof.
    intros ??? Hin.
    apply ps_from_list_In. apply in_app_iff in Hin as [|]; [solve_In|].
    apply in_app_iff in H as [|]; solve_In; eauto with datatypes; auto.
  Qed.

  Lemma step_wt:
    forall P s,
      wt_system P s ->
      wt_method (translate P) (s_subs s)
                (map (fun xc => (fst xc, snd (fst (snd xc)))) (s_lasts s++s_nexts s))
                (step_method s).
  Proof.
    unfold wt_system, wt_method; intros * (WT &?& Htypes); simpl.
    split.
    - eapply translate_tcs_wt; eauto using s_nodup_variables with obctyping.
      + apply s_type_env_spec.
      + apply s_last_env_spec.
    - unfold meth_vars, step_method; simpl.
      intros * In. eapply Htypes.
      rewrite <- 2 idfst_app in In. apply in_app_iff; eauto.
  Qed.
  Local Hint Resolve step_wt : obctyping.

  Lemma reset_mems_wt:
    forall P insts Γm inits,
      (forall x c t ck, In (x, (c, t, ck)) inits -> In (x, t) Γm) ->
      wt_states P inits ->
      wt_stmt (translate P) insts Γm [] (reset_mems inits).
  Proof.
    unfold reset_mems; intros * Spec WT.
    induction inits as [|(x, ((c, t), ck))]; simpl; eauto with obctyping;
      inversion_clear WT as [|?? WTc].
    rewrite wt_stmt_fold_left_lift; split; auto.
    - apply IHinits; auto.
      intros; eapply Spec; right; eauto.
    - constructor; eauto with obctyping.
      cases; inv WTc; constructor; eauto with obctyping;
        eapply Spec; left; eauto.
  Qed.

  Lemma reset_insts_wt_permutation:
    forall subs subs' prog insts Γm Γv,
      Permutation subs' subs ->
      wt_stmt prog insts Γm Γv (reset_insts subs) ->
      wt_stmt prog insts Γm Γv (reset_insts subs').
  Proof.
    unfold reset_insts.
    induction 1; simpl; auto; intros * WT.
    - apply wt_stmt_fold_left_lift in WT as (? & ?);
        rewrite wt_stmt_fold_left_lift; split; auto.
    - apply wt_stmt_fold_left_lift in WT as (?& WT');
        rewrite wt_stmt_fold_left_lift; split; auto.
      inversion_clear WT' as [| | |?? WT| | |]; inv WT; eauto with obctyping.
  Qed.

  Lemma reset_insts_wt:
    forall P insts Γm s,
      wt_system P s ->
      incl (s_subs s) insts ->
      wt_stmt (translate P) insts Γm [] (reset_insts (s_subs s)).
  Proof.
    unfold wt_system; intros * (WT&?) Spec.
    eapply reset_insts_wt_permutation; try apply s_subs_insts_of.
    rewrite s_subs_insts_of in Spec.
    unfold reset_insts.
    induction (s_tcs s) as [|[|?[]|?? []] tcs]; simpl in *;
      inversion_clear WT as [|?? WTtc]; eauto with obctyping.
    apply incl_cons' in Spec as (? & ?).
    rewrite wt_stmt_fold_left_lift; split; auto.
    constructor; eauto with obctyping.
    inversion_clear WTtc as [| | | | |???????? Find].
    apply find_unit_transform_units_forward in Find.
    econstructor; eauto.
    - apply exists_reset_method.
    - constructor.
    - simpl; constructor.
    - simpl; constructor.
  Qed.

  Lemma reset_wt:
    forall P s,
      wt_system P s ->
      wt_method (translate P) (s_subs s)
                (map (fun xc => (fst xc, snd (fst (snd xc)))) (s_lasts s ++ s_nexts s))
                (reset_method s).
  Proof.
    unfold wt_system, wt_method; intros * (WT & WTinits & Htypes).
    unfold translate_tcs, meth_vars, translate_reset; simpl.
    split; try contradiction.
    constructor.
    - apply reset_mems_wt; auto.
      clear WT WTinits.
      intros * Hin. solve_In.
    - apply reset_insts_wt; try now constructor.
      apply incl_refl.
  Qed.
  Local Hint Resolve reset_wt : obctyping.

  Lemma translate_system_wt:
    forall P s,
      wt_system P s ->
      wt_class (translate P) (translate_system s).
  Proof.
    unfold wt_system; intros * WT; pose proof WT as WT'; destruct WT as (WT&?).
    constructor; simpl; eauto using Forall_cons with obctyping.
    rewrite s_subs_insts_of.
    remember (s_tcs s) as tcs; setoid_rewrite <-Heqtcs; clear Heqtcs.
    induction tcs as [|[|?|??[]]]; simpl; inversion_clear WT as [|?? WTtc]; auto;
      constructor; simpl; auto with obctyping.
    inversion_clear WTtc as [| | | | |???????? Find].
    apply find_unit_transform_units_forward in Find; setoid_rewrite Find; discriminate.
  Qed.

  Theorem translate_wt:
    forall P,
      Stc.Typ.wt_program P ->
      wt_program (translate P).
  Proof.
    intros; eapply transform_units_wt_program; eauto using translate_system_wt.
  Qed.

End STC2OBCTYPING.

Module Stc2ObcTypingFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Ids Op)
       (ComTyp: COMMONTYPING    Ids Op OpAux)
       (Cks   : CLOCKS          Ids Op OpAux)
       (Str   : INDEXEDSTREAMS  Ids Op OpAux Cks)
       (CE    : COREEXPR        Ids Op OpAux ComTyp Cks Str)
       (Stc   : STC             Ids Op OpAux ComTyp Cks Str CE)
       (Obc   : OBC             Ids Op OpAux ComTyp)
       (Trans : TRANSLATION     Ids Op OpAux Cks CE.Syn Stc.Syn Obc.Syn)
<: STC2OBCTYPING Ids Op OpAux ComTyp Cks Str CE Stc Obc Trans.
  Include STC2OBCTYPING Ids Op OpAux ComTyp Cks Str CE Stc Obc Trans.
End Stc2ObcTypingFun.
