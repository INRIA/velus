From Velus Require Import Stc.
From Velus Require Import Obc.

From Velus Require Import StcToObc.Translation.
From Velus Require Import StcToObc.Stc2ObcTyping.

From Velus Require Import VelusMemory.
From Velus Require Import Common.
From Velus Require Import CommonTyping.
From Velus Require Import Environment.

From Coq Require Import Lia.
From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import Setoid Morphisms.

Open Scope nat.
Open Scope list.

Module Type CORRECTNESS
       (Import Ids      : IDS)
       (Import Op       : OPERATORS)
       (Import OpAux    : OPERATORS_AUX   Ids Op)
       (Import ComTyp   : COMMONTYPING    Ids Op OpAux)
       (Import Cks      : CLOCKS          Ids Op OpAux)
       (Import Str      : INDEXEDSTREAMS  Ids Op OpAux Cks)
       (Import CE       : COREEXPR        Ids Op OpAux ComTyp Cks Str)
       (Import Stc      : STC             Ids Op OpAux ComTyp Cks Str CE)
       (Import Obc      : OBC             Ids Op OpAux ComTyp)
       (Import Trans    : TRANSLATION     Ids Op OpAux Cks CE.Syn Stc.Syn Obc.Syn)
       (Import TransTyp : STC2OBCTYPING   Ids Op OpAux ComTyp Cks Str CE Stc Obc Trans).

  Inductive eq_if_present: svalue -> option value -> Prop :=
  | EqP:
      forall v,
        eq_if_present (present v) (Some v)
  | EqA:
      forall v,
        eq_if_present absent v.
  Global Hint Constructors eq_if_present : obcsem.

  Definition value_to_option (v: svalue) : option value :=
    match v with
    | absent => None
    | present c => Some c
    end.

  Definition equiv_env (in_domain: ident -> Prop) (R: env)
             (mems: PS.t) (me: menv) (ve: venv) : Prop :=
    forall x v,
      in_domain x ->
      sem_var_instant R x v ->
      eq_if_present v (if PS.mem x mems then find_val x me else Env.find x ve).

  Lemma equiv_env_map:
    forall (in_dom1 in_dom2: ident -> Prop) R mems me ve,
      (forall x, in_dom2 x -> in_dom1 x) ->
      equiv_env in_dom1 R mems me ve ->
      equiv_env in_dom2 R mems me ve.
  Proof.
    unfold equiv_env; intros ??????? Eq ????. apply Eq; auto.
  Qed.

  Ltac weaken_equiv_env_with tac :=
    match goal with
      H: equiv_env ?in_dom1 ?R ?mems ?me ?ve
      |- equiv_env ?in_dom2 ?R ?mems ?me ?ve =>
      eapply equiv_env_map; [|exact H]; tac
    end.

  Tactic Notation "weaken_equiv_env" "with" tactic(tac) :=
    weaken_equiv_env_with tac.

  Tactic Notation "weaken_equiv_env" :=
    weaken_equiv_env with now (constructor; auto with stcfree).

  Global Hint Extern 4 (equiv_env _ _ _ _ _) => weaken_equiv_env : obcsem stcfree.

  Lemma eq_if_present_present:
    forall vo c,
      eq_if_present (present c) vo <-> vo = Some c.
  Proof.
    simpl; split.
    - now inversion 1.
    - intros ->; auto with obcsem.
  Qed.

  Ltac split_env_assumption :=
    match goal with
    | Equiv: context Is_free_in_exp [_],
             Hvar: sem_var_instant _ _ _ |- _ =>
      apply Equiv in Hvar; [|solve [constructor; auto]]
    | Equiv: context Is_free_in_clock [_],
             Hvar: sem_var_instant _ _ _ |- _ =>
      apply Equiv in Hvar; [|solve [constructor; auto]]
    end.

  Inductive Is_present_in (mems: PS.t) (me: menv) (ve: venv): clock -> Prop :=
  | IsCbase:
      Is_present_in mems me ve Cbase
  | IsCon:
      forall ck x b t,
        Is_present_in mems me ve ck ->
        exp_eval me ve (tovar mems (x, t)) (Some (Venum b)) ->
        Is_present_in mems me ve (Con ck x (t, b)).

  Inductive Is_absent_in (mems: PS.t) (me: menv) (ve: venv): clock -> Prop :=
  | IsAbs1:
      forall ck x v,
        Is_absent_in mems me ve ck ->
        Is_absent_in mems me ve (Con ck x v)
  | IsAbs2:
      forall ck x b b' t,
        Is_present_in mems me ve ck ->
        exp_eval me ve (tovar mems (x, t)) (Some (Venum b')) ->
        b' <> b ->
        Is_absent_in mems me ve (Con ck x (t, b)).

  Global Hint Constructors Is_present_in Is_absent_in : obcsem.

  Arguments tovar: simpl never.

  Section ExprClock.

    Variable mems: PS.t.

    Variable R: env.
    Variable (me: menv) (ve: venv).

    Lemma exp_correct:
      forall e c,
        sem_exp_instant true R e (present c) ->
        equiv_env (fun x => CE.IsF.Is_free_in_exp x e) R mems me ve ->
        exp_eval me ve (translate_exp mems e) (Some c).
    Proof.
      induction e; inversion_clear 1; simpl; intros; auto with obcsem.
      - match goal with H: _ = _ |- _ => inv H end.
        econstructor; congruence.
      - match goal with H: _ = _ |- _ => inv H end.
        econstructor; congruence.
      - unfold tovar.
        split_env_assumption; cases; try rewrite eq_if_present_present in *;
          eauto using exp_eval.
        take (Env.find _ _ = _) and rewrite <-it; constructor.
      - econstructor; eauto with obcsem; now rewrite typeof_correct.
      - econstructor; eauto with obcsem; now rewrite 2 typeof_correct.
    Qed.
    Hint Resolve exp_correct : obcsem.

    Lemma arg_correct:
      forall me ve cvars ck e c,
        exp_eval me ve (translate_exp mems e) (Some c) ->
        exp_eval me ve (translate_arg mems cvars ck e) (Some c).
    Proof.
      intros * Heval.
      unfold translate_arg.
      unfold var_on_base_clock.
      destruct e; auto; simpl in *.
      unfold tovar in *.
      destruct (PS.mem i mems); simpl; auto.
      inv Heval; cases; auto with obcsem.
      take (Env.find _ _ = _) and rewrite it; constructor; auto with obcsem.
    Qed.
    Hint Resolve arg_correct : obcsem.

    Lemma cexp_correct:
      forall e c prog x,
        sem_cexp_instant true R e (present c) ->
        equiv_env (fun x => Is_free_in_cexp x e) R mems me ve ->
        stmt_eval prog me ve (translate_cexp mems x e) (me, Env.add x c ve).
    Proof.
      induction e using cexp_ind2;
        inversion 1 as [????????? Hvar|???? Hvar| | |];
        subst; simpl; intros; eauto with obcsem.
      - split_env_assumption.
        econstructor; eauto.
        + unfold tovar; cases; try rewrite eq_if_present_present in Hvar;
            eauto using exp_eval.
          rewrite <-Hvar; constructor.
        + erewrite map_nth_error; eauto.
          rewrite nth_error_app3; eauto.
        + apply Forall_app in H as [? H]; inversion_clear H as [|?? IH].
          simpl; apply IH; auto.
          weaken_equiv_env with (constructor; apply Exists_app; auto).
      - take (Forall2 _ _ _) and apply Forall2_swap_args in it.
        edestruct (@nth_error_Forall2 value) as (?&?&?); eauto.
        econstructor; eauto with obcsem.
        + erewrite map_nth_error; eauto.
        + simpl in *.
          take (nth_error _ _ = _) and eapply nth_error_In in it.
          pose proof it as Hin.
          eapply Forall_forall in it; eauto; simpl in *.
          destruct x0; simpl in *; apply it; auto with stcfree obcsem;
            weaken_equiv_env with (intros; eapply FreeEcase_branches, Exists_exists; eauto).
    Qed.
    Hint Resolve cexp_correct : obcsem.

    Lemma clock_correct_true:
      forall types Γ base ck,
        wt_clock types Γ ck ->
        equiv_env (fun x => Is_free_in_clock x ck) R mems me ve ->
        sem_clock_instant base R ck true ->
        Is_present_in mems me ve ck.
    Proof.
      induction 1; eauto with obcsem.
      inversion_clear 2; subst.
      econstructor; eauto with obcsem.
      unfold tovar; split_env_assumption.
      cases; try rewrite eq_if_present_present in *; eauto with obcsem.
      take (Env.find _ _ = _) and rewrite <-it; auto with obcsem.
    Qed.

    Lemma clock_correct_false:
      forall types Γ ck,
        wt_clock types Γ ck ->
        equiv_env (fun x => Is_free_in_clock x ck) R mems me ve ->
        sem_clock_instant true R ck false ->
        Is_absent_in mems me ve ck.
    Proof.
      induction 1; [now inversion 2|].
      intro Henv.
      inversion_clear 1; auto with obcsem.
      econstructor 2; eauto.
      - eapply clock_correct_true; eauto with obcsem.
      - unfold tovar; split_env_assumption.
        cases; try rewrite eq_if_present_present in *; eauto with obcsem.
        take (Env.find _ _ = _) and rewrite <-it; auto with obcsem.
    Qed.

  End ExprClock.

  Lemma stmt_eval_Control_fwd:
    forall prog types Γ me ve mems ck s me' ve',
      wt_clock types Γ ck ->
      stmt_eval prog me ve (Control mems ck s) (me', ve') ->
      (Is_present_in mems me ve ck
       /\ stmt_eval prog me ve s (me', ve'))
      \/
      (Is_absent_in mems me ve ck
       /\ me' = me /\ ve' = ve).
  Proof.
    intros * WT StEval.
    revert dependent s.
    induction WT; intuition.
    simpl in *; apply IHWT in StEval as [[Hp Hs]|[Hp [Hmenv Henv]]];
      intuition; inv Hs.
    take (nth_error _ _ = _) and rewrite nth_error_skip_branches_with in it.
    cases; inv it; simpl in *; auto with obcsem.
    chase_skip; eauto with obcsem.
  Qed.

  Section StmtEvalControl.

    Variables (prog  : program)
              (types : list type)
              (Γ     : list (ident * type))
              (insts : list (ident * ident))
              (Γm    : list (ident * type))
              (Γv    : list (ident * type))
              (mems  : PS.t)
              (me    : menv)
              (ve    : venv)
              (ck    : clock)
              (s     : stmt).

    Hypotheses (TypesSpec   : types = prog.(Obc.Syn.types))
               (TypeEnvSpec : type_env_spec Γ Γm Γv mems)
               (WTmenv      : wt_env (values me) Γm)
               (WTvenv      : wt_env ve Γv)
               (WTck        : wt_clock types Γ ck)
               (WTs         : wt_stmt prog insts Γm Γv s).

    (* Conjunction required for simultaneous induction. *)
    Fact stmt_eval_Control:
      (Is_absent_in mems me ve ck ->
       stmt_eval prog me ve (Control mems ck s) (me, ve))
      /\
      (forall me' ve',
          Is_present_in mems me ve ck ->
          stmt_eval prog me ve s (me', ve') ->
          stmt_eval prog me ve (Control mems ck s) (me', ve')).
    Proof.
      revert dependent s; clear s WTs.
      induction ck; split; auto.
      - inversion 1.
      - pose proof (Control_wt _ _ _ _ _ _ TypesSpec TypeEnvSpec _ _ _ WTck WTs) as WTcontrol.
        inv WTck.
        inversion_clear 1 as [??? Hp|????? Hp]; simpl in *;
          eapply Control_wt_inv in WTcontrol; eauto;
            eapply IHc in Hp; eauto; simpl in *.
        econstructor; eauto.
        + rewrite nth_error_skip_branches_with.
          inv WTcontrol.
          take (wt_exp _ _ _ _) and eapply pres_sem_exp in it; eauto.
          rewrite typeof_tovar in it; inv it; simpl in *.
          destruct (Compare_dec.le_lt_dec (length tn) b'); try lia.
          destruct (Nat.eq_dec b' c0); try contradiction; eauto.
        + eauto with obcsem.
      - pose proof (Control_wt _ _ _ _ _ _ TypesSpec TypeEnvSpec _ _ _ WTck WTs) as WTcontrol.
        inv WTck.
        inversion_clear 1 as [|???? Hp]; simpl in *; intros.
        eapply Control_wt_inv in WTcontrol; eauto;
          eapply IHc in Hp; eauto; simpl in *.
        econstructor; eauto.
        + rewrite nth_error_skip_branches_with.
          destruct (Compare_dec.le_lt_dec (length tn) c0); try lia.
          destruct (Nat.eq_dec c0 c0); try contradiction; eauto.
        + eauto.
    Qed.

    (** If the clock is absent, then the controlled statement evaluates as
  a [Skip].  *)

    Corollary stmt_eval_Control_absent:
      Is_absent_in mems me ve ck ->
      stmt_eval prog me ve (Control mems ck s) (me, ve).
    Proof. apply stmt_eval_Control. Qed.

    (** If the clock is present, then the controlled statement evaluates
  as the underlying one.  *)

    Corollary stmt_eval_Control_present:
      forall me' ve',
        Is_present_in mems me ve ck ->
        stmt_eval prog me ve s (me', ve') ->
        stmt_eval prog me ve (Control mems ck s) (me', ve').
    Proof. apply stmt_eval_Control. Qed.

    Variable (R : env).
    Hypothesis Equiv: equiv_env (fun x => Is_free_in_clock x ck) R mems me ve.

    Corollary stmt_eval_Control_absent':
      sem_clock_instant true R ck false ->
      stmt_eval prog me ve (Control mems ck s) (me, ve).
    Proof.
      intros; eapply stmt_eval_Control_absent, clock_correct_false; eauto.
    Qed.

    Corollary stmt_eval_Control_present':
      forall base me' ve',
        sem_clock_instant base R ck true ->
        stmt_eval prog me ve s (me', ve') ->
        stmt_eval prog me ve (Control mems ck s) (me', ve').
    Proof.
      intros; eapply stmt_eval_Control_present; auto; eapply clock_correct_true; eauto.
    Qed.

  End StmtEvalControl.

  (** Reset correctness *)

  Definition add_mems (mems: list (ident * (const * type * clock))) (me: menv) : menv :=
    Mem (fold_left (fun vs '(x, (c, t, ck)) => Env.add x (sem_const c) vs) mems (values me))
        (instances me).

  Lemma find_inst_add_mems:
    forall x me xs,
      find_inst x (add_mems xs me) = find_inst x me.
  Proof. reflexivity. Qed.

  Lemma add_mems_cons:
    forall x c t ck xs me,
      add_mems ((x, (c, t, ck)) :: xs) me = add_mems xs (add_val x (sem_const c) me).
  Proof. reflexivity. Qed.

  Lemma add_mems_nil:
    forall me,
      add_mems [] me = me.
  Proof. destruct me; reflexivity. Qed.

  Lemma add_mems_gss:
    forall x c t ck xs me,
      ~ InMembers x xs ->
      find_val x (add_mems ((x, (c, t, ck)) :: xs) me) = Some (sem_const c).
  Proof.
    intros * Notin; rewrite add_mems_cons.
    revert me; induction xs as [|(?,((? & ?)& ?))]; intros.
    - now rewrite add_mems_nil, find_val_gss.
    - apply NotInMembers_cons in Notin as (? & ?).
      rewrite add_mems_cons, add_val_comm; auto.
  Qed.

  Lemma find_val_add_mems_in:
    forall x c t ck xs me,
      NoDupMembers xs ->
      In (x, (c, t, ck)) xs ->
      find_val x (add_mems xs me) = Some (sem_const c).
  Proof.
    intros * Nodup Hin.
    revert me; induction xs as [|(?,((? & ?)&?))]; intros.
    - inversion Hin.
    - inv Nodup.
      destruct Hin as [E|?].
      + inv E.
        now apply add_mems_gss.
      + rewrite add_mems_cons; auto.
  Qed.

  Lemma find_val_add_mems_inv:
    forall x xs me v,
      find_val x (add_mems xs me) = Some v ->
      (NoDupMembers xs -> InMembers x xs -> exists c t ck, v = sem_const c /\ In (x, (c, t, ck)) xs)
      /\
      (~ InMembers x xs -> find_val x me = Some v).
  Proof.
    intros * Find; split; [intros * Nodup Hin|intros * Hin].
    - revert dependent me; induction xs as [|(x', ((c, t), ck))]; intros;
        inv Hin; inv Nodup.
      + rewrite add_mems_gss in Find; auto; inv Find.
        exists c, t, ck; intuition.
      + rewrite add_mems_cons in Find.
        edestruct IHxs as (?&?&?&?&?); eauto.
        do 3 eexists; intuition; eauto; right; eauto.
    - revert dependent me; induction xs as [|(x', ((c', t'), ck'))]; intros.
      + now rewrite add_mems_nil in Find.
      + rewrite add_mems_cons in Find.
        apply NotInMembers_cons in Hin as (? & ?).
        apply IHxs in Find; auto.
        rewrite find_val_gso in Find; auto.
  Qed.

  Lemma reset_mems_spec:
    forall mems prog me ve,
      stmt_eval prog me ve (reset_mems mems) (add_mems mems me, ve).
  Proof.
    unfold reset_mems.
    induction mems as [|(x, ((c, t), ck))]; simpl; intros.
    - rewrite add_mems_nil; eauto using stmt_eval.
    - rewrite stmt_eval_fold_left_lift; setoid_rewrite stmt_eval_eq_Comp_Skip1.
      cases; do 2 eexists; split; eauto using stmt_eval, exp_eval;
        rewrite add_mems_cons; auto.
  Qed.

  Lemma translate_reset_comp:
    forall prog me ve s me' ve',
      stmt_eval prog me ve (translate_reset s) (me', ve')
      <-> stmt_eval prog me ve (reset_mems s.(s_nexts)) (add_mems s.(s_nexts) me, ve)
        /\ stmt_eval prog (add_mems s.(s_nexts) me) ve (reset_insts s.(s_subs)) (me', ve').
  Proof.
    unfold translate_reset; split.
    - inversion_clear 1 as [| | | |????????? StEval| |].
      pose proof (reset_mems_spec (s_nexts s) prog me ve) as StEval'.
      eapply stmt_eval_det with (2 := StEval') in StEval as (? & ?); subst.
      split; auto.
    - intros (? & ?); eauto using stmt_eval.
  Qed.

  Lemma add_mems_reset_nexts:
    forall s me,
      reset_nexts s (add_mems s.(s_nexts) me).
  Proof.
    unfold reset_nexts; intros.
    eapply find_val_add_mems_in; eauto.
    apply s_nodup_nexts.
  Qed.

  Lemma add_mems_state_closed_nexts:
    forall resets me,
      state_closed_nexts (map fst resets) me ->
      state_closed_nexts (map fst resets) (add_mems resets me).
  Proof.
    intros * Closed ? Find.
    apply not_None_is_Some in Find as (?& Find).
    apply find_val_add_mems_inv in Find.
    destruct (in_dec ident_eq_dec x (map fst resets)) as [|Hin]; auto.
    rewrite <-fst_InMembers in Hin; apply Find in Hin.
    apply Closed, not_None_is_Some; eauto.
  Qed.

  Lemma reset_insts_reset_nexts:
    forall subs prog me ve me' ve' s,
      stmt_eval prog me ve (reset_insts subs) (me', ve') ->
      reset_nexts s me ->
      reset_nexts s me'.
  Proof.
    unfold reset_insts.
    induction subs; simpl.
    - inversion_clear 1; auto.
    - intros * StEval Resets ??? Hin.
      apply stmt_eval_fold_left_lift in StEval as (?&?& StEval & StEvals).
      eapply IHsubs in StEvals; eauto.
      rewrite stmt_eval_eq_Comp_Skip1 in StEval; inv StEval.
      now apply reset_nexts_add_inst.
  Qed.

  Lemma reset_insts_state_closed_nexts:
    forall subs resets prog me ve me' ve',
      stmt_eval prog me ve (reset_insts subs) (me', ve') ->
      state_closed_nexts resets me ->
      state_closed_nexts resets me'.
  Proof.
    unfold reset_insts.
    induction subs; simpl.
    - inversion_clear 1; auto.
    - intros * StEval Resets ? Hin.
      apply stmt_eval_fold_left_lift in StEval as (?&?& StEval & StEvals).
      eapply IHsubs in StEvals; eauto.
      rewrite stmt_eval_eq_Comp_Skip1 in StEval; inv StEval.
      now apply state_closed_nexts_add_inst.
  Qed.

  Lemma reset_insts_same_venv:
    forall subs prog me ve me' ve',
      stmt_eval prog me ve (reset_insts subs) (me', ve') ->
      ve' = ve.
  Proof.
    unfold reset_insts.
    induction subs; simpl.
    - inversion_clear 1; auto.
    - intros * StEval.
      apply stmt_eval_fold_left_lift in StEval as (?&?& StEval & StEvals).
      eapply IHsubs in StEvals; eauto.
      rewrite stmt_eval_eq_Comp_Skip1 in StEval; inv StEval.
      apply Env.adds_opt_nil_l.
  Qed.

  Lemma call_reset_inv:
    forall f P s P' me me' rvs,
      find_system f P = Some (s, P') ->
      stmt_call_eval (translate P) me f reset [] me' rvs ->
      stmt_eval (translate P') me vempty (translate_reset s) (me', vempty)
      /\ rvs = [].
  Proof.
    intros * Find Rst.
    apply find_unit_transform_units_forward in Find.
    inversion_clear Rst as [??????????? Find' Find_m ? StEval Ret].
    setoid_rewrite Find in Find'; inv Find'.
    rewrite exists_reset_method in Find_m; inv Find_m; simpl in *.
    inv Ret; intuition.
    rewrite Env.adds_opt_nil_nil in StEval.
    apply translate_reset_comp in StEval as (?& Insts).
    rewrite translate_reset_comp; intuition.
    assert (ve' = vempty) as HH by (eapply reset_insts_same_venv; eauto).
    rewrite HH in Insts; auto.
  Qed.

  Lemma call_reset_reset_nexts:
    forall me' P me f s P',
      find_system f P = Some (s, P') ->
      stmt_call_eval (translate P) me f reset [] me' [] ->
      reset_nexts s me'.
  Proof.
    intros ?????? Find Rst ??? Hin.
    eapply call_reset_inv in Rst as (Rst & ?); eauto;
      apply translate_reset_comp in Rst as (? & ?).
    eapply reset_insts_reset_nexts; eauto.
    apply add_mems_reset_nexts; auto.
  Qed.

  Lemma call_reset_state_closed_nexts:
    forall me' P me f s P',
      find_system f P = Some (s, P') ->
      stmt_call_eval (translate P) me f reset [] me' [] ->
      state_closed_nexts (map fst s.(s_nexts)) me ->
      state_closed_nexts (map fst s.(s_nexts)) me'.
  Proof.
    intros ?????? Find Rst ?? Hin.
    eapply call_reset_inv in Rst as (Rst & ?); eauto;
      apply translate_reset_comp in Rst as (?& Rst).
    eapply reset_insts_state_closed_nexts in Rst; eauto.
    apply add_mems_state_closed_nexts; auto.
  Qed.

  Lemma reset_insts_not_InMembers:
    forall subs prog me ve me' ve' x,
      stmt_eval prog me ve (reset_insts subs) (me', ve') ->
      ~ InMembers x subs ->
      find_inst x me' = find_inst x me.
  Proof.
    unfold reset_insts.
    induction subs as [|(x', c')].
    - inversion 1; auto.
    - intros * StEval Notin; apply NotInMembers_cons in Notin as (? & ?); simpl in *.
      apply stmt_eval_fold_left_lift in StEval as (?&?& StEval & StEvals).
      eapply IHsubs in StEvals; eauto.
      rewrite stmt_eval_eq_Comp_Skip1 in StEval; inv StEval.
      rewrite StEvals, find_inst_gso; auto.
  Qed.

  Lemma reset_insts_in:
    forall s P P' me ve me' ve' i f g,
      find_system f P = Some (s, P') ->
      stmt_eval (translate P') me ve (reset_insts s.(s_subs)) (me', ve') ->
      In (i, g) s.(s_subs) ->
      find_system g P' <> None ->
      exists me_i,
        stmt_call_eval (translate P') (match find_inst i me with
                                       | Some om => om
                                       | None => mempty
                                       end)
                       g reset [] me_i []
        /\ find_inst i me' = Some me_i.
  Proof.
    unfold reset_insts.
    intro; pose proof (s_nodup_subs s) as Nodup.
    induction s.(s_subs) as [|(i', g')]; simpl; try now inversion 2.
    intros * Find StEval Hin Find'; inversion_clear Nodup as [|??? Notin].
    apply stmt_eval_fold_left_lift in StEval as (me_i' &?& StEval & StEvals).
    destruct Hin as [E|].
    - inv E.
      erewrite reset_insts_not_InMembers with (me' := me'); eauto.
      rewrite stmt_eval_eq_Comp_Skip1 in StEval; inv StEval.
      match goal with H: Forall2 _ _ _ |- _ => inv H end.
      rewrite find_inst_gss.
      cut (rvos = []).
      + intro Hrvos; rewrite Hrvos in *; eauto.
      + apply not_None_is_Some in Find' as ((? & ?) & ?).
        take (stmt_call_eval _ _ _ _ _ _ _) and eapply call_reset_inv in it as (? & ?); eauto.
    - assert (find_inst i me = find_inst i me_i') as ->; eauto.
      rewrite stmt_eval_eq_Comp_Skip1 in StEval; inv StEval.
      rewrite find_inst_gso; auto.
      intro; subst; eapply Notin, In_InMembers; eauto.
  Qed.

  Lemma find_inst_reset_insts_inv:
    forall subs prog me ve me' ve' x me_x,
      stmt_eval prog me ve (reset_insts subs) (me', ve') ->
      find_inst x me' = Some me_x ->
      InMembers x subs
      \/ find_inst x me = Some me_x.
  Proof.
    unfold reset_insts.
    induction subs as [|(x', b)]; simpl.
    - inversion_clear 1; auto.
    - intros * StEval Sub.
      apply stmt_eval_fold_left_lift in StEval as (me_x' &?& StEval & StEvals).
      eapply IHsubs in StEvals as [|Sub']; eauto.
      rewrite stmt_eval_eq_Comp_Skip1 in StEval.
      inv StEval.
      destruct (ident_eq_dec x x'); auto.
      rewrite find_inst_gso in Sub'; auto.
  Qed.

  Lemma call_reset_initial_state:
    forall me' P me f s P',
      Ordered_systems P ->
      find_system f P = Some (s, P') ->
      stmt_call_eval (translate P) me f reset [] me' [] ->
      initial_state P f me' /\ (state_closed P f me -> state_closed P f me').
  Proof.
    induction me' as [? IH] using memory_ind';
      intros * Ord Find Rst.
    pose proof Ord as Ord'.
    eapply Ordered_systems_find_system in Ord'; eauto.
    split.
    - econstructor; eauto.
      + eapply call_reset_reset_nexts; eauto.
      + intros * Hin.
        eapply call_reset_inv in Rst as (Rst & ?); eauto;
          apply  translate_reset_comp in Rst as (? & ?).
        eapply Ordered_systems_find_In_systems in Ord as (?&?& Find'); eauto.
        pose proof Hin as Hin'.
        eapply reset_insts_in in Hin as (me_x & ? & ?); eauto.
        * exists me_x; split; auto.
          eapply IH; eauto.
        * apply not_None_is_Some; eauto.
    - inversion_clear 1 as [????? Find' ? Insts]; rewrite Find' in Find; inv Find.
      econstructor; eauto.
      + eapply call_reset_state_closed_nexts; eauto.
      + intros * Sub.
        eapply call_reset_inv in Rst as (Rst & ?); eauto;
          apply  translate_reset_comp in Rst as (?& Rst).
        pose proof Rst.
        eapply find_inst_reset_insts_inv in Rst as [Hin|]; eauto.
        apply InMembers_In in Hin as (b' & Hin).
        eapply Ordered_systems_find_In_systems in Ord as (?&?& Find); eauto.
        pose proof Hin as Hin'.
        eapply reset_insts_in in Hin as (me_x & ? & Sub'); eauto.
        * eexists; split; eauto.
          rewrite Sub' in Sub; inv Sub.
          eapply IH; eauto.
          rewrite find_inst_add_mems.
          destruct (find_inst i me) eqn: E; [|eapply state_closed_empty; eauto].
          apply Insts in E as (b'' &?&?).
          assert (b' = b'') as ->; auto.
          eapply NoDupMembers_det in Hin'; eauto.
          apply s_nodup_subs.
        * apply not_None_is_Some; eauto.
  Qed.

  Lemma reset_insts_exists:
    forall s P me ve,
      (forall me' f s' P',
          find_system f P = Some (s', P') ->
          exists me'',
            stmt_call_eval (translate P) me' f reset [] me'' []) ->
      (forall i g,
          In (i, g) s.(s_subs) ->
          exists s P',
            find_system g P = Some (s, P')) ->
      exists me',
        stmt_eval (translate (P)) me ve (reset_insts s.(s_subs)) (me', ve).
  Proof.
    unfold reset_insts.
    intro; induction s.(s_subs) as [|(x, b')]; simpl in *;
      intros * IH Spec; eauto using stmt_eval.
    setoid_rewrite stmt_eval_fold_left_lift.
    edestruct Spec as (?&?& Find); eauto.
    eapply IH in Find as (?&?).
    edestruct IHl; eauto 7.
    do 3 eexists; split; eauto.
    econstructor; eauto with obcsem.
    change ve with (Env.adds_opt [] [] ve).
    econstructor; eauto.
  Qed.

  Lemma reset_exists:
    forall P f s P' me,
      Ordered_systems P ->
      find_system f P = Some (s, P') ->
      exists me',
        stmt_call_eval (translate P) me f reset [] me' [].
  Proof.
    intros []; induction systems0 as [|system]; try now inversion 2.
    intros * Ord Find.
    pose proof Find as Find';
      apply find_unit_transform_units_forward in Find'.
    eapply find_unit_cons in Find as [[E Find]|[E Find]]; simpl in *; eauto.
    - inv Find.
      edestruct reset_insts_exists; eauto.
      + inv Ord; eauto.
      + eapply Ordered_systems_find_In_systems; eauto.
        eapply find_unit_cons; simpl; eauto.
      + eexists; econstructor; eauto.
        * apply exists_reset_method.
        * simpl; auto.
        * simpl; rewrite Env.adds_opt_nil_nil.
          apply translate_reset_comp; split; eauto.
          apply reset_mems_spec.
        * simpl; auto.
    - unfold translate; simpl; inv Ord.
      edestruct IHsystems0; eauto.
      eexists; rewrite stmt_call_eval_cons; eauto.
  Qed.

 Theorem reset_spec:
    forall P me f s P',
      Ordered_systems P ->
      find_system f P = Some (s, P') ->
      exists me',
        stmt_call_eval (translate P) me f reset [] me' []
        /\ initial_state P f me'
        /\ (state_closed P f me -> state_closed P f me').
  Proof.
    intros.
    edestruct reset_exists; eauto.
    eexists; split; eauto.
    eapply call_reset_initial_state; eauto.
  Qed.

  (** Step correctness *)

  Lemma value_to_option_adds_opt:
    forall R ve x xs v vs,
      In x xs ->
      NoDup xs ->
      Forall (fun x => Env.find x ve = None) xs ->
      Forall2 (sem_var_instant R) xs vs ->
      sem_var_instant R x v ->
      Env.find x (Env.adds_opt xs (map value_to_option vs) ve) = value_to_option v.
  Proof.
    induction xs as [|x']; try now inversion 1.
    intros * Hin Hnodup Hnin Hvar Hxsem; inv Hnodup; inv Hnin.
    apply Forall2_left_cons in Hvar as (v' & vs' & Hyss & Hvs & ?); subst.
    destruct (ident_eq_dec x x') as [Heq|Hneq]; simpl.
    + subst.
      assert (v' = v) by (eapply sem_var_instant_det; eauto); subst.
      destruct v; simpl.
      * rewrite Env.adds_opt_cons_cons_None, Env.find_In_gsso_opt; auto.
      * apply Env.find_gsss_opt.
    + inv Hin; try congruence.
      rewrite Env.find_gsso_opt; simpl; auto.
  Qed.

  Lemma eq_if_present_adds_opt:
    forall R ve x xs c vs ovs,
      In x xs ->
      Forall2 (sem_var_instant R) xs vs ->
      Forall2 eq_if_present vs ovs ->
      sem_var_instant R x (present c) ->
      Env.find x (Env.adds_opt xs ovs ve) = Some c.
  Proof.
    induction xs as [|x']. now inversion 1.
    destruct (ident_eq_dec x x') as [Heq|Hneq];
      intros * Hin Hvar Hovals Hxsem.
    + subst.
      apply Forall2_left_cons in Hvar as (v & vs' & Hyss & Hvs & ?).
      rewrite Hyss in Hovals.
      apply Forall2_left_cons in Hovals
        as (ov & ovals' & Hovals & Heqp & ?).
      pose proof (sem_var_instant_det _ _ _ _ Hvs Hxsem) as Hpvc.
      subst; inv Heqp.
      now rewrite Env.find_gsss_opt.
    + pose proof (Forall2_length _ _ _ Hvar) as Hlenyss.
      pose proof (Forall2_length _ _ _ Hovals) as Hlenovals.
      destruct vs; try discriminate.
      destruct ovs; try discriminate.
      rewrite Env.find_gsso_opt; auto.
      inv Hin. now contradiction Hneq.
      inv Hvar; inv Hovals; eauto.
  Qed.

  Definition correct_system (P: Stc.Syn.program) (f: ident) : Prop :=
    forall S xs ys S' me ins s P',
      sem_system P f S xs ys S' ->
      find_system f P = Some (s, P') ->
      Forall2 eq_if_present xs ins ->
      Exists (fun v => v <> absent) xs ->
      wt_memory S P' (mems_of_nexts (s_nexts s)) (s_subs s) ->
      Forall2 (fun xt vo => wt_option_value vo (fst (snd xt))) (s_in s) ins ->
      me ≋ S ->
      exists me',
        stmt_call_eval (translate P) me f step ins me' (map value_to_option ys)
        /\ me' ≋ S'.

  Definition correct_program (P: Stc.Syn.program) : Prop :=
    forall f, correct_system P f.

  Lemma noops_exp_exp_eval:
    forall isub R mems me ve vars e v xck bck lck,
      sem_clocked_vars_instant true R vars ->
      equiv_env (fun x => CE.IsF.Is_free_in_exp x e) R mems me ve ->
      noops_exp xck e ->
      wc_exp vars e lck ->
      instck bck isub xck = Some lck ->
      sem_clock_instant true R bck true ->
      sem_exp_instant true R e v ->
      sem_clock_instant true R lck false ->
      (forall x, PS.In x mems -> find_val x me <> None) ->
      exists v, exp_eval me ve (translate_exp mems e) v.
  Proof.
    induction e; simpl;
      intros v1 nck ck lck Hcm EqEnv Hnoo Hwc Hinst Hbck He Hlck Hmems; eauto with obcsem.
    - (* Variables always evaluate (even if it is to None) *)
      unfold tovar.
      destruct (PS.mem i mems) eqn:Himems; eauto with obcsem.
      rewrite PS.mem_spec in Himems.
      apply Hmems in Himems.
      apply not_None_is_Some in Himems as (v' & Hv'); eauto with obcsem.
    - (* The reasoning around sampled expressions (e when i b) is slightly tricker... *)
      destruct lck.
      now inv Hwc (* lck cannot be Cbase if (e when i b) is well clocked. *).
      destruct nck.
      + (* interface clock = Cbase (base clock of node instantiation)
           Then lck = ck, ck is true (the node is active), and the
           hypothesis is false. *)
        inv Hinst. now apply sem_clock_instant_det with (1:=Hbck) in Hlck.
      + (* interface clock = Con nck i1 b1
           It is the underlying value e that must be calculated.
           Either e is absent and the result follows by induction
           (since e can only be absent if its clock is a (strict)
            subclock of the instantiated clock, and in this case
            it cannot contain a unary or binary operator thanks to
            noops_exp; it cannot contain Valid by construction; and
            variables always evalute to something).
           Or e is present with a value and its translation calculates
           the same value. *)
        simpl in *.
        destruct (instck ck isub nck) eqn:Heq; try discriminate.
        destruct (isub _); try discriminate.
        inv Hwc. inv Hinst. inv Hlck.
        * (* Con lck i0 b0 = false because lck = false,
             the goal follows form the induction hypothesis. *)
          now inv He; eauto with obcsem.
        * (* Con lck i0 b0 = false but its clock lck = true.
             The sampled expression e must thus be present, in which
             case we know that the translation calculates the same value. *)
          inv He; try match goal with
                        H:sem_exp_instant _ _ e (present _) |- _ =>
                        eapply exp_correct in H; eauto with obcsem end.
          (* an absent value would contradict the fact that clock lck = true *)
          match goal with Hle:sem_exp_instant _ _ e absent,
                              Hck:sem_clock_instant _ _ lck true |- _ =>
            apply clock_match_instant_exp_contradiction with (1:=Hcm) (3:=Hle) in Hck; eauto with obcsem
          end. intuition.
    - (* Unary operators: cannot be slower than the node base clock *)
      destruct nck.
      + (* lck = ck; one can't be true and the other false. *)
        inv Hinst. now apply sem_clock_instant_det with (1:=Hbck) in Hlck.
      + (* lck is a subclock of ck and ops are thus precluded by noops_exp. *)
        inv Hnoo.
    - (* Binary operators: reasoning as for unary operators. *)
      destruct nck.
      + inv Hinst. now apply sem_clock_instant_det with (1:=Hbck) in Hlck.
      + inv Hnoo.
  Qed.

  Lemma TcStep_check_args_translate_arg:
    forall P R mems clkvars me ve icks i ys ck rst f es ess,
      (forall x ck, In (x, ck) icks -> ~ PS.In x mems -> Env.find x clkvars = Some ck) ->
      sem_clocked_vars_instant true R icks ->
      equiv_env (fun x => CE.IsF.Is_free_in_aexps x ck es) R mems me ve ->
      (forall x, PS.In x mems -> find_val x me <> None) ->
      wc_trconstr P icks (TcStep i ys ck rst f es) ->
      normal_args_tc P (TcStep i ys ck rst f es) ->
      sem_exps_instant true R es ess ->
      sem_clock_instant true R ck true ->
      exists vos,
        Forall2 eq_if_present ess vos
        /\ Forall2 (exp_eval me ve) (map (translate_arg mems clkvars ck) es) vos.
  Proof.
    intros * Hcvars Hcm EqEnv Himems Hwc Hnorm Hles Hcksem.
    apply Forall2_Forall2_exists, Forall2_map_2, Forall2_swap_args.
    inversion_clear Hwc as [| | | |???????? sub Hfind Hwci Hwco].
    inversion_clear Hnorm as [| | | |???????? Hfind' Hnorm'].
    rewrite Hfind in Hfind'; inv Hfind'.
    rewrite Forall2_map_1, Forall2_swap_args in Hnorm'.
    apply Forall2_trans_ex with (1:=Hnorm'), Forall2_same in Hwci.
    clear Hwco Hfind Hnorm'.
    apply Forall2_impl_In with (2:=Hles).
    intros le v Hlein Hvin Hsem.
    apply Forall_forall with (2:=Hlein) in Hwci
      as ((x, (xty, xck)) & Hin & Hnorm & Hsubv & (lck & WClck & Hinst)).
    simpl in *.
    assert (WClck':=WClck).
    assert (equiv_env (fun x => CE.IsF.Is_free_in_exp x le) R mems me ve)
      by (weaken_equiv_env with constructor;
          apply Exists_exists; eauto).
    eapply clock_match_instant_exp in WClck'
      as [(Hsem' & Hcksem')|((c & Hsem') & Hcksem')]; eauto;
      apply sem_exp_instant_det with (1:=Hsem) in Hsem'; subst v.
    - eapply noops_exp_exp_eval in Hnorm as (v' & Hv'); eauto.
      simpl; exists v'; eauto.
      split; destruct le; eauto with obcsem.
      destruct xck.
      + inv Hinst. now apply sem_clock_instant_det with (1:=Hcksem) in Hcksem'.
      + simpl in Hinst.
        destruct (instck ck sub xck) eqn:Hck; try discriminate.
        match goal with H:context [sub ?i] |- _ =>
                        destruct (sub i) eqn:Hisub; try discriminate end.
        injection Hinst; intro; subst lck.
        inversion_clear WClck as [| |? ? ? Hicks| | |].
        simpl in Hv'; destruct (PS.mem i0 mems) eqn: E.
        * unfold translate_arg, var_on_base_clock; simpl; rewrite E; simpl; auto.
        *{ apply Hcvars in Hicks.
           - unfold translate_arg, var_on_base_clock; simpl; rewrite Hicks, E; simpl.
             now rewrite instck_subclock_not_clock_eq with (1:=Hck).
           - apply PSE.MP.Dec.F.not_mem_iff; auto.
         }
    - exists (Some c); simpl; split; eauto using arg_correct, exp_correct with obcsem.
  Qed.

  Lemma stmt_eval_translate_cexp_menv_inv:
    forall prog me ve mems x me' ve' e,
      stmt_eval prog me ve (translate_cexp mems x e) (me', ve') ->
      me' = me.
  Proof.
    induction e using cexp_ind2; simpl; inversion_clear 1; auto;
      take (nth_error _ _ = _) and apply map_nth_error_inv in it as (oe & Hin & ?);
      eauto; subst; eapply nth_error_In, Forall_forall in Hin; eauto; auto.
    destruct oe; simpl in *; auto.
  Qed.

  Lemma stmt_eval_translate_cexp_venv_inv:
    forall prog me ve mems x me' ve' e,
      stmt_eval prog me ve (translate_cexp mems x e) (me', ve') ->
      exists c, ve' = Env.add x c ve.
  Proof.
    induction e using cexp_ind2; simpl; inversion_clear 1; eauto;
      take (nth_error _ _ = _) and apply map_nth_error_inv in it as (oe & Hin & ?);
      eauto; subst; eapply nth_error_In, Forall_forall in Hin; eauto; auto.
    destruct oe; simpl in *; auto.
  Qed.

  Lemma not_Is_defined_in_tc_stmt_eval_menv_inv:
    forall tc x P Γv Γm me ve mems clkvars me' ve',
      wt_trconstr P Γv Γm tc ->
      ~ (exists ck, Is_reset_in_tc x ck tc) ->
      ~ Is_next_in_tc x tc ->
      stmt_eval (translate P) me ve (translate_tc mems clkvars tc) (me', ve') ->
      find_val x me' = find_val x me.
  Proof.
    destruct tc; simpl; intros ?????????? WT NIsReset NIsNext StEval;
      inv WT; try (take (wt_rhs _ _ _ _) and inv it); try (take (wt_const _ _ _) and inv it);
        eapply stmt_eval_Control_fwd in StEval; eauto;
          destruct StEval as [(?& StEval)|(?&?&?)]; try congruence.
    - now inv StEval.
    - now apply stmt_eval_translate_cexp_menv_inv in StEval as ->.
    - inv StEval.
      apply not_Is_reset_in_tc_TcReset in NIsReset.
      rewrite find_val_gso; auto.
    - inv StEval.
      apply not_Is_reset_in_tc_TcReset in NIsReset.
      rewrite find_val_gso; auto.
    - inv StEval.
      apply not_Is_next_in_tc_TcNext in NIsNext.
      rewrite find_val_gso; auto.
    - inv StEval; apply find_val_add_inst.
    - inv StEval; apply find_val_add_inst.
  Qed.

  Corollary not_Is_defined_in_stmt_eval_menv_inv:
    forall tcs x P Γv Γm me ve mems clkvars me' ve',
      Forall (wt_trconstr P Γv Γm) tcs ->
      ~ (exists ck, Is_reset_in x ck tcs) ->
      ~ Is_next_in x tcs ->
      stmt_eval (translate P) me ve (translate_tcs mems clkvars tcs) (me', ve') ->
      find_val x me' = find_val x me.
  Proof.
    unfold translate_tcs.
    induction tcs as [|tc]; simpl; intros ?????????? WT NIsReset NIsNext StEval.
    - now inv StEval.
    - apply stmt_eval_fold_left_shift in StEval as (me'' & ve'' &?& Hcomp);
        rewrite stmt_eval_eq_Comp_Skip2 in Hcomp.
      apply not_Is_reset_in_cons' in NIsReset as (?& Spec).
      apply not_Is_next_in_cons in NIsNext as (?& Next).
      inv WT. eapply IHtcs with (me' := me'') in Spec; eauto.
      rewrite <-Spec.
      eapply not_Is_defined_in_tc_stmt_eval_menv_inv; eauto.
  Qed.

  Lemma not_Is_defined_in_tc_stmt_eval_venv_inv:
    forall tc x P Γv Γm me ve mems clkvars me' ve',
      wt_trconstr P Γv Γm tc ->
      ~ Is_variable_in_tc x tc ->
      stmt_eval (translate P) me ve (translate_tc mems clkvars tc) (me', ve') ->
      Env.find x ve' = Env.find x ve.
  Proof.
    intros * WT Hnd Heval.
    destruct tc; simpl in Heval; inv WT;
      try (take (wt_rhs _ _ _ _) and inv it);
      try (take (wt_const _ _ _) and inv it);
      eapply stmt_eval_Control_fwd in Heval; eauto;
        destruct Heval as [[Hipi Heval]|[Habs [Hmenv Henv]]];
        subst; auto.
    - inv Heval. rewrite Env.gso; auto.
      intro; subst; apply Hnd; constructor.
    - apply stmt_eval_translate_cexp_venv_inv in Heval as (?&?); subst.
      rewrite Env.gso; auto.
      intro; subst; apply Hnd; constructor.
    - inv Heval; auto.
    - inv Heval; auto.
    - inv Heval; auto.
    - inv Heval; auto.
    - inv Heval.
      rewrite Env.find_In_gsso_opt; auto.
      intro; apply Hnd; constructor; auto.
  Qed.

  Corollary not_Is_defined_in_stmt_eval_venv_inv:
    forall tcs x P Γv Γm me ve mems clkvars me' ve',
      Forall (wt_trconstr P Γv Γm) tcs ->
      ~ Is_variable_in x tcs ->
      stmt_eval (translate P) me ve (translate_tcs mems clkvars tcs) (me', ve') ->
      Env.find x ve' = Env.find x ve.
  Proof.
    unfold translate_tcs.
    induction tcs as [|tc]; simpl; intros ?????????? WT NIsDef StEval; inv WT.
    - now inv StEval.
    - apply stmt_eval_fold_left_shift in StEval as (me'' & ve'' &?& Hcomp);
        rewrite stmt_eval_eq_Comp_Skip2 in Hcomp.
      apply not_Is_variable_in_cons in NIsDef as (?& Spec).
      eapply IHtcs with (ve' := ve'') in Spec; eauto.
      rewrite <-Spec.
      eapply not_Is_defined_in_tc_stmt_eval_venv_inv; eauto.
  Qed.

  (* Lemma sem_trconstrs_is_init_in: *)
  (*   forall tcs P base R S I S' x v, *)
  (*     Forall (sem_trconstr P base R S I S') tcs -> *)
  (*     Is_init_in x tcs -> *)
  (*     sem_var_instant R x (present v) -> *)
  (*     find_val x S = Some v. *)
  (* Proof. *)
  (*   induction tcs; inversion_clear 1 as [|?? Sem]; *)
  (*     inversion_clear 1 as [?? Init|]; eauto; intros. *)
  (*   inv Init; inv Sem. *)
  (*   cases; congruence. *)
  (* Qed. *)

  Lemma not_Is_variable_in_tc_stmt_eval_env_inv:
    forall prog P Γv Γm x tc me ve mems clkvars me' ve',
      wt_trconstr P Γv Γm tc ->
      ~ Is_variable_in_tc x tc ->
      stmt_eval prog me ve (translate_tc mems clkvars tc) (me', ve') ->
      Env.find x ve' = Env.find x ve.
  Proof.
    intros * WT Hnd Heval.
    destruct tc; simpl in Heval; inv WT;
      try (take (wt_rhs _ _ _ _) and inv it);
      try (take (wt_const _ _ _) and inv it);
      eapply stmt_eval_Control_fwd in Heval; eauto;
        destruct Heval as [[Hipi Heval]|[Habs [Hmenv Henv]]];
        subst; auto.
    - inv Heval. rewrite Env.gso; auto.
      intro; subst; apply Hnd; constructor.
    - apply stmt_eval_translate_cexp_venv_inv in Heval as (?&?); subst.
      rewrite Env.gso; auto.
      intro; subst; apply Hnd; constructor.
    - inv Heval; auto.
    - inv Heval; auto.
    - inv Heval; auto.
    - inv Heval.
      rewrite Env.adds_opt_nil_l; auto.
    - inv Heval.
      rewrite Env.find_In_gsso_opt; auto.
      intro; apply Hnd; constructor; auto.
  Qed.

  Section Trconstr.

    Variables (Γv   : list (ident * type))
              (Γm   : list (ident * type))
              (Γv'  : list (ident * type))
              (Γm'  : list (ident * type))
              (mems : PS.t).

    Hypotheses (TypeEnvSpec : type_env_spec (Γv ++ Γm) Γm' Γv' mems).

    Lemma trconstr_cons_correct:
      forall tc tcs P R S I S' inputs Ω clkvars insts me ve,
        correct_program P ->
        Stc.Typ.wt_program P ->
        sem_trconstr P true R S I S' tc ->
        Forall (sem_trconstr P true R S I S') tcs ->
        wc_trconstr P Ω tc ->
        wt_trconstr P Γv Γm tc ->
        trconstr_mems_spec mems tc ->
        trconstr_insts_spec insts tc ->
        normal_args_tc P tc ->
        Ordered_systems P ->
        Is_well_sch inputs mems (tc :: tcs) ->
        NoDup (inputs ++ variables (tc :: tcs)) ->
        NoDupMembers (steps_of (tc :: tcs)) ->
        reset_consistency (tc :: tcs) ->
        ireset_consistency (tc :: tcs) ->
        reset_clocks_have_sem true R (tc :: tcs) ->
        ireset_clocks_have_sem true R (tc :: tcs) ->
        (forall i f Si, In (i, f) (iresets_of (tc :: tcs)) -> find_inst i S = Some Si -> state_closed P f Si) ->
        (forall i f Ii, In (i, f) (iresets_of (tc :: tcs)) -> find_inst i I = Some Ii -> state_closed P f Ii) ->
        Memory_Corres R true tcs S I S' me ->
        equiv_env (fun x => Is_free_in_tc x tc) R mems me ve ->
        wt_memory me (translate P) Γm' insts ->
        wt_memory S P Γm' insts ->
        wt_env ve Γv' ->
        sem_clocked_vars_instant true R Ω ->
        (forall x ck, In (x, ck) Ω -> ~ PS.In x mems -> Env.find x clkvars = Some ck) ->
        (forall x, PS.In x mems -> find_val x me <> None) ->
        (forall x, ~ In x inputs -> ~ Is_variable_in x tcs -> Env.find x ve = None) ->
        exists me' ve',
          stmt_eval (translate P) me ve (translate_tc mems clkvars tc) (me', ve')
          /\ Memory_Corres R true (tc :: tcs) S I S' me'
          /\ forall x v,
              Is_variable_in_tc x tc ->
              sem_var_instant R x v ->
              Env.find x ve' = value_to_option v.
    Proof.
    intros * IH WTP Sem Sems Hwc Hwt Spec_m Spec_i Hnormal Ord Wsch Vars Calls Resets StepReset ResetCks IResetCks
                Closed TransClosed Corres Equiv WTmenv WTS WTvenv Hcm Hcvars Hmems Hve.
    assert (NoDup (variables_tc tc))
      by (rewrite Permutation.Permutation_app_comm in Vars;
          simpl in Vars; do 2 apply NoDup_app_weaken in Vars; auto).
    pose proof Hwt as Hwt'; eapply translate_tc_wt with (clkvars := clkvars) in Hwt'; eauto.
    inversion Sem as [????????? Hexp Hvar|
                      ?????????? Find Hvar FindI|
                      ????????????? Hexp|
                      ??????????? FindI Init|
                      ??????????????? ClockR Find_I Hexps Hck Hsystem Hvars];
      subst; simpl in *; inv Hwt;
      try (take (wt_rhs _ _ _ _) and inv it);
        try (take (wt_const _ _ _) and inv it);
        eapply Control_wt_inv in Hwt'; eauto.

    - (* TcDef external *)
      inv WTmenv; inv Hexp; take (sem_rhs_instant _ _ _ _) and inv it;
        exists me; eexists; split;
        try solve [eapply stmt_eval_Control_absent'; eauto; auto with obcsem].
      + eapply stmt_eval_Control_present'; eauto; auto with obcsem.
        econstructor; eauto; simpl_Forall.
        * rewrite typeof_correct; auto.
        * eapply exp_correct; eauto.
          eapply equiv_env_map; eauto. intros; repeat constructor; solve_Exists.
      + split.
        * apply Memory_Corres_Def; auto.
        * inversion_clear 1; intros Hvar'.
          eapply sem_var_instant_det in Hvar; eauto; subst.
          inv Hvar'; rewrite Env.gss; auto.
      + split.
        * apply Memory_Corres_Def; auto.
        * inversion_clear 1; intros Hvar'.
          eapply sem_var_instant_det in Hvar; eauto.
          unfold variables in Vars.
          subst; simpl in *; apply NoDup_app_cons in Vars as (Hnin & ?).
          apply Hve; auto using Is_variable_in_tc.
          intro; apply Hnin, in_app; auto.
          rewrite Is_variable_in_variables.
          intro; apply Hnin, in_app; auto.

    - (* TcDef *)
      inv WTmenv; inv Hexp; take (sem_rhs_instant _ _ _ _) and inv it;
        exists me; eexists; split;
        try solve [eapply stmt_eval_Control_absent'; eauto; auto with obcsem].
      + eapply stmt_eval_Control_present'; eauto; auto with obcsem.
        eapply cexp_correct; eauto with obcsem.
      + split.
        * apply Memory_Corres_Def; auto.
        * inversion_clear 1; intros Hvar'.
          eapply sem_var_instant_det in Hvar; eauto.
          inv Hvar; rewrite Env.gss; auto.
      + split.
        * apply Memory_Corres_Def; auto.
        * inversion_clear 1; intros Hvar'.
          eapply sem_var_instant_det in Hvar; eauto.
          unfold variables in Vars.
          subst; simpl in *; apply NoDup_app_cons in Vars as (Hnin & ?).
          apply Hve; auto using Is_variable_in_tc.
          intro; apply Hnin, in_app; auto.
          rewrite Is_variable_in_variables.
          intro; apply Hnin, in_app; auto.

    - (* TcReset *)
      inv WTmenv; destruct r; do 2 eexists; (split; [|split]); eauto;
        try solve [inversion 1].
      + eapply stmt_eval_Control_present'; eauto with obcsem;
        intuition. econstructor; eauto with obcsem.
      + eapply Memory_Corres_Reset_present; eauto.
        eapply Is_well_sch_Reset_Next; eauto.
      + eapply stmt_eval_Control_absent'; eauto using stmt_eval, exp_correct.
        intuition.
      + eapply Memory_Corres_Reset_absent; eauto.
    - inv WTmenv; destruct r; do 2 eexists; (split; [|split]); eauto;
        try solve [inversion 1].
      + eapply stmt_eval_Control_present'; eauto using stmt_eval, exp_correct.
        intuition. constructor; eauto with obcsem.
      + eapply Memory_Corres_Reset_present; eauto.
        eapply Is_well_sch_Reset_Next; eauto.
      + eapply stmt_eval_Control_absent'; eauto using stmt_eval, exp_correct.
        intuition.
      + eapply Memory_Corres_Reset_absent; eauto.

    - (* TcNext *)
      inv WTmenv; inv Hexp; eexists; exists ve; split;
        try solve [eapply stmt_eval_Control_absent'; eauto; auto with obcsem].
      + eapply stmt_eval_Control_present';
          eauto with obcsem; eauto with obcsem.
        econstructor; eauto 8 with obcsem. eapply exp_correct; eauto with obcsem.
      + split; try inversion 1.
        apply Memory_Corres_Next_present; auto.
      + split; try inversion 1.
        eapply Memory_Corres_Next_absent; auto.
        eapply ResetCks. left; eauto with stcsyntax.

    - (* TcInstReset *)
      inv WTmenv; destruct r.
      + pose proof Init.
        inversion_clear Init as [????? Find Rst].
        edestruct reset_spec as (me' &?&?& SpecInit); eauto.
        do 2 eexists; split; [|split].
        * eapply stmt_eval_Control_present'; eauto; auto with obcsem.
          econstructor; eauto.
        * { eapply Memory_Corres_InstReset_present; eauto.
            - eapply initial_state_det; eauto.
              + apply SpecInit.
                unfold instance_match in *.
                destruct (find_inst i me) eqn: E.
                * assert (~Is_step_in i tcs) as NStep.
                  { inversion_clear Wsch as [|?? (?&?&?)]; eauto using Is_ireset_in_tc. }
                  assert (state_corres i S me \/ state_corres i I me) as Scorres.
                  { eapply ireset_or_not_ireset_dec with (i:=i) in Sems as [NotReset|Reset].
                    - left. eapply Corres; eauto.
                    - right. eapply Corres; eauto.
                  }
                  unfold state_corres in Scorres.
                  rewrite E in Scorres.
                  destruct Scorres as [Scorres|Scorres]; apply orel_find_inst_Some in Scorres as (?&<-&?).
                  -- eapply Closed; simpl; eauto.
                  -- eapply TransClosed; simpl; eauto.
                * eapply state_closed_empty; eauto.
            - eapply Is_well_sch_IReset_Step; eauto.
         }
        * inversion 1.
      + exists me, ve; split; try eapply stmt_eval_Control_absent'; eauto; auto with obcsem.
        split; try inversion 1.
        eapply Memory_Corres_InstReset_absent; eauto.

    - (* TcStep *)
      assert (Forall (fun ckr : clock => exists r : bool, sem_clock_instant true R ckr r) ckrs) as ClockR1.
      { eapply IResetCks. left; eauto with stcsyntax. }
      destruct (clock_of_instant xs) eqn: E.
      + assert (Exists (fun v => v <> absent) xs) by (apply clock_of_instant_true; auto).
        assert (exists vos,
                   Forall2 eq_if_present xs vos
                   /\ Forall2 (exp_eval me ve)
                             (map (translate_arg mems clkvars ck) es) vos)
            as (ivals & Hivals & Hievals)
              by (eapply TcStep_check_args_translate_arg; eauto with obcsem).
        unfold correct_program, correct_system in IH.
        eapply IH in Hsystem as (me' &?&?); eauto.
        *{ inv WTmenv. do 2 eexists; split.
           - eapply stmt_eval_Control_present'; eauto; auto with obcsem.
             econstructor; eauto.
           - split.
             + eapply Memory_Corres_Step_present; eauto.
             + inversion_clear 1; intros Hvar.
               simpl in Vars; apply NoDup_swap in Vars.
               eapply value_to_option_adds_opt; eauto.
               apply Forall_forall; intros y Hin.
               assert (~ In y inputs) by
                   (rewrite app_assoc in Vars; apply NoDup_app_weaken in Vars;
                    eapply NoDup_app_In; eauto).
               assert (~Is_variable_in y tcs).
               { rewrite Permutation_swap in Vars; apply NoDup_app_r in Vars.
                 rewrite Is_variable_in_variables.
                 eapply NoDup_app_In; eauto. }
               apply Hve; auto.
         }
        * inv Spec_i.
          assert (~Is_step_in i tcs) as NotStep.
          { inv Calls. rewrite Step_in_steps_of; auto. }
          eapply ireset_or_not_ireset_dec in Sems as [NotReset|Reset].
          -- pose proof (conj NotStep NotReset) as Cor. eapply Corres in Cor.
             assert (exists Ii', Ii' ≋ Ii /\ find_inst i S = Some Ii') as (? & <- &?).
             { apply orel_find_inst_Some, ClockR.
               eapply Forall_forall; intros ? Hin; eapply NotReset.
               eapply StepReset in Hin; eauto. 2:left; eauto with stcsyntax. inv Hin; auto. inv H4. }
             inversion_clear WTS as [????? WTinsts].
             eapply Forall_forall in WTinsts; eauto.
             inv WTinsts; try congruence.
             match goal with H: find_inst i S = _, H': find_inst i S = _ |- _ => rewrite H in H'; inv H' end.
             match goal with H: find_system _ _ = _, H': find_unit _ _ = _ |- _ => setoid_rewrite H in H'; inv H' end; auto.
          -- pose proof (conj NotStep Reset) as Cor. eapply Corres in Cor.
             unfold state_corres in Cor.
             rewrite Find_I in Cor; symmetry in Cor.
             assert (exists Ii', Ii' ≋ Ii /\ find_inst i me = Some Ii') as (? & <- &?)
                 by (apply orel_find_inst_Some; auto).
             inversion_clear WTmenv as [????? WTinsts].
             eapply Forall_forall in WTinsts; eauto.
             inv WTinsts; try congruence.
             match goal with H: find_inst i me = _, H': find_inst i me = _ |- _ => rewrite H in H'; inv H' end.
             take (find_unit _ _ = _) and eapply find_unit_transform_units_backward in it as (?&?& Find &?&?); subst.
             match goal with H: find_system _ _ = _, H': find_unit _ _ = _ |- _ => setoid_rewrite H in H'; inv H' end; auto.
             (* TODO: why do I need to instantiate this theorem like that? *)
             pose proof (@transform_units_wt_memory' system class _ _ _ _ _ _ _ _) as Spec.
             apply Spec; auto.
        * inv WTmenv; eapply pres_sem_expos with (Γm := Γm') in Hievals; eauto.
          -- take (Forall2 _ _ (s_in _)) and rename it into Eexps.
             apply Forall2_map_1, Forall2_swap_args in Hievals.
             apply Forall2_trans_ex with (2 := Eexps) in Hievals.
             clear - Hievals; induction Hievals as [|? (?&(?&?))?? (?&?& WT &?)]; subst; simpl; constructor; auto.
             now rewrite typeof_arg_correct in WT.
          -- take (Forall _ es) and rename it into WTexps.
             apply Forall_map, Forall_forall; intros * Hin.
             eapply Forall_forall in WTexps; eauto.
             assert (Stc.Syn.types P = types (translate P)) by auto.
             eapply translate_arg_wt in WTexps; eauto.
        *{ inv WTmenv; unfold instance_match.
           assert (~Is_step_in i tcs) as NStep.
           { rewrite steps_of_In, <-fst_InMembers.
             simpl in Calls. inv Calls; auto. }
           assert (Step_with_ireset_in i ckrs (TcStep i ys ck ckrs f es :: tcs)) as SpecStep by (left; constructor).
           apply StepReset in SpecStep.
           apply reset_or_not_reset_dec' in ClockR1 as [NotReset|Reset].
           - assert (state_corres i S me) as Corres'.
             + eapply Corres; split; eauto.
               intros ? Res.
               eapply Forall_forall in NotReset; [eauto|].
               rewrite SpecStep. right; auto.
             + unfold state_corres in Corres'. rewrite ClockR in Corres'; auto.
               inv Corres'; symmetry; auto.
           - assert (state_corres i I me) as Corres'.
             + eapply Corres; split; eauto.
               eapply Exists_exists in Reset as (?&Hin&?).
               rewrite SpecStep in Hin. inv Hin. inv H7. eauto.
             + unfold state_corres in Corres'. rewrite Find_I in Corres'; auto.
               inv Corres'; symmetry; auto.
         }
      + inv WTmenv.
        assert (absent_list xs) by (apply clock_of_instant_false; auto).
        apply sem_system_absent in Hsystem as (? & ?); auto.
        exists me, ve; split; try eapply stmt_eval_Control_absent'; eauto; auto with obcsem.
        split; eauto using Memory_Corres_Step_absent.
        inversion_clear 1; intros Hvar.
        eapply Forall2_in_left in Hvars as (v' & Hin &?); eauto.
        eapply sem_var_instant_det in Hvar; eauto; subst v'.
        eapply Forall_forall in Hin; eauto.
        simpl in Hin; subst; simpl.
        unfold variables in Vars.
        simpl in *.
        apply Hve; auto using Is_defined_in_tc.
        * eapply NoDup_swap, NoDup_app_In in Vars; eauto.
          intro; apply Vars, in_app; auto.
        * apply NoDup_app_r in Vars.
          rewrite Is_variable_in_variables.
          eapply NoDup_app_In; eauto.
    Qed.

    Hypotheses (Hndupm : NoDupMembers Γm')
               (Hndupv : NoDupMembers Γv').

    Lemma trconstrs_app_correct:
      forall tcs' tcs P R S I S' inputs Ω clkvars insts me ve,
        let alltcs := tcs ++ tcs' in
        correct_program P ->
        NoDupMembers insts ->
        Stc.Typ.wt_program P ->
        Forall (sem_trconstr P true R S I S') alltcs ->
        Forall (wc_trconstr P Ω) alltcs ->
        Forall (wt_trconstr P Γv Γm) alltcs ->
        Forall (trconstr_mems_spec mems) alltcs ->
        Forall (trconstr_insts_spec insts) alltcs ->
        Forall (normal_args_tc P) alltcs ->
        sem_clocked_vars_instant true R Ω ->
        (forall x ck, In (x, ck) Ω -> ~ PS.In x mems -> Env.find x clkvars = Some ck) ->
        (forall x, PS.In x mems -> find_val x me <> None) ->
        (forall x v, PS.In x mems -> sem_var_instant R x (present v) -> find_val x I = Some v) ->
        Ordered_systems P ->
        Is_well_sch inputs mems alltcs ->
        NoDup (inputs ++ variables alltcs) ->
        NoDupMembers (steps_of alltcs) ->
        reset_consistency alltcs ->
        ireset_consistency alltcs ->
        reset_clocks_have_sem true R alltcs ->
        ireset_clocks_have_sem true R alltcs ->
        (forall i f Si, In (i, f) (iresets_of alltcs) -> find_inst i S = Some Si -> state_closed P f Si) ->
        (forall i f Ii, In (i, f) (iresets_of alltcs) -> find_inst i I = Some Ii -> state_closed P f Ii) ->
        (forall x, PS.In x mems -> Is_next_in x alltcs) ->
        (forall x, In x inputs -> ~ Is_variable_in x alltcs) ->
        (forall x c,
            In x inputs ->
            sem_var_instant R x (present c) ->
            Env.find x ve = Some c) ->
        (forall x, Env.find x ve <> None -> In x inputs) ->
        wt_memory me (translate P) Γm' insts ->
        wt_env ve Γv' ->
        me ≋ S ->
        exists me' ve',
          stmt_eval (translate P) me ve (translate_tcs mems clkvars tcs') (me', ve')
          /\ Memory_Corres R true tcs' S I S' me'
          /\ forall x v,
              Is_variable_in x tcs' ->
              sem_var_instant R x v ->
              Env.find x ve' = value_to_option v.
    Proof.
      induction tcs' as [|tc]; simpl;
        intros ?????????????
               Hndupi WT Htcs Hwc Hwt Spec_m Spec_i Hnormal Hcm Hcvars Hmems HmemsI Ord Wsch Vars Steps
               NextReset StepReset ResetCks IResetCks
               Closed TransClosed SpecMem SpecInput EquivInput EquivInput' WTm WTe Corres.
      - exists me, ve. split; eauto using stmt_eval; split; auto.
        + now apply Memory_Corres_empty_equal_memory.
        + inversion 1.
      - pose proof Wsch as Wsch'; apply Forall'_app_r in Wsch'.
        pose proof Vars as Vars'; rewrite variables_app in Vars'.
        rewrite NoDup_swap, Permutation.Permutation_app_comm in Vars';
          apply NoDup_app_weaken in Vars'.
        pose proof Steps as Steps'; rewrite steps_of_app in Steps'.
        rewrite Permutation.Permutation_app_comm in Steps';
          apply NoDupMembers_app_l in Steps'.
        pose proof NextReset as NextReset'; eapply reset_consistency_app in NextReset'; eauto.
        pose proof StepReset as StepReset'; eapply ireset_consistency_app in StepReset'; eauto.
        pose proof ResetCks as ResetCks'; eapply reset_clocks_have_sem_app in ResetCks'; eauto.
        pose proof IResetCks as IResetCks'; eapply ireset_clocks_have_sem_app in IResetCks'; eauto.
        pose proof Htcs as Htcs'; apply Forall_app_weaken in Htcs'; inv Htcs'.
        pose proof Hwc as Hwc'; apply Forall_app_weaken in Hwc'; inv Hwc'.
        pose proof Hwt as Hwt'; apply Forall_app_weaken in Hwt'; inv Hwt'.
        pose proof Spec_m as Spec_m'; apply Forall_app_weaken in Spec_m'; inv Spec_m'.
        pose proof Spec_i as Spec_i'; apply Forall_app_weaken in Spec_i'; inv Spec_i'.
        pose proof Hnormal as Hnormal'; apply Forall_app_weaken in Hnormal'; inv Hnormal'.
        rewrite List_shift_first in Wsch, Vars, Steps, NextReset, StepReset, ResetCks, IResetCks,
                                    Htcs, SpecMem, SpecInput,
                                    Closed, TransClosed, Hwc, Hwt, Spec_m, Spec_i, Hnormal.
        edestruct IHtcs' with (insts:=insts) as (me' & ve' &?&?& Env); eauto.
        take (stmt_eval _ _ _ _ _) and pose proof it as StmtEval.
        eapply pres_sem_stmt with (mems := Γm') (insts := insts) (Γv := Γv') in StmtEval as (WTmem & ?); eauto.
        + edestruct trconstr_cons_correct with (ve := ve') (me := me') as (me'' & ve'' &?&?&?); eauto.
          * intros; eapply Closed; eauto.
            rewrite <-List_shift_first, iresets_of_app, in_app; auto.
          * intros; eapply TransClosed; eauto.
            rewrite <-List_shift_first, iresets_of_app, in_app; auto.
          * intros x v Free Hvar.
            inversion_clear Wsch' as [|?? (FreeSpec&ResetSpec&_)].
            assert (Free':=Free). apply FreeSpec in Free.
            cases_eqn E.
            { destruct v; simpl; auto.
              eapply PSF.mem_2 in E; eauto with obcsem.
              specialize (HmemsI _ _ E Hvar).
              specialize (SpecMem _ E).
              eapply reset_or_not_reset_dec with (x:=x) in H3 as [NotReset|Reset].
              - assert (value_corres x S me') as Corres' by (eapply H1; eauto).
                rewrite <-Corres'.
                eapply Exists_exists in SpecMem as (?&Hin&Next); inv Next.
                eapply Forall_forall in Htcs; [|eauto].
                inversion_clear Htcs as [| |??????????? Find FindI _ _ _| |].
                rewrite Find, <-FindI, HmemsI; auto with obcsem.
                eapply Forall_forall. intros ? Hin'. eapply NotReset.
                assert (Next_with_reset_in x ckrs ((tcs ++ [tc]) ++ tcs')) as NextReset''.
                { eapply Exists_exists. eexists; split; eauto with stcsyntax. }
                eapply NextReset in NextReset''. rewrite NextReset'' in Hin'.
                apply Exists_app' in Hin' as [Hin'|?]; auto.
                exfalso. eapply Is_well_sch_free_Reset in Free'; eauto.
              - assert (value_corres x I me') as Corres' by (eapply H1; eauto).
                rewrite <-Corres', HmemsI; auto with obcsem.
         }
            { destruct Free as [IsVar|].
          - eapply Env in IsVar; eauto.
            destruct v; simpl; auto with obcsem.
            rewrite IsVar; simpl; auto with obcsem.
          - assert (~ Is_variable_in x tcs')
              by (intro; eapply SpecInput, Exists_app; eauto).
            erewrite not_Is_defined_in_stmt_eval_venv_inv; eauto.
            destruct v; simpl; auto with obcsem.
            assert (Env.find x ve = Some v) as ->; auto with obcsem. }
          * rewrite <-Corres.
            apply transform_units_wt_memory; auto.
          * intros; eapply stmt_eval_find_val_mono; eauto.
          * intros * Hnin ?; erewrite not_Is_defined_in_stmt_eval_venv_inv; eauto.
            apply not_Some_is_None; intros * E.
            apply Hnin, EquivInput', not_None_is_Some; eauto.
          * exists me'', ve''; split; [|split]; auto.
            -- unfold translate_tcs; simpl.
               rewrite stmt_eval_fold_left_shift; setoid_rewrite stmt_eval_eq_Comp_Skip2; eauto.
            -- intros x v IsVar Hvar.
               destruct (Is_variable_in_tc_dec x tc) as [|Nvar]; auto.
               erewrite not_Is_variable_in_tc_stmt_eval_env_inv; eauto.
               inv IsVar; auto.
               contradiction.
        + now apply translate_wt.
        + eapply translate_tcs_wt; eauto.
          unfold variables in *; simpl in *.
          rewrite app_assoc, Permutation.Permutation_app_comm in Vars'; apply NoDup_app_weaken in Vars'; auto.
    Qed.

    Corollary trconstrs_correct:
      forall tcs P R S I S' inputs Ω clkvars insts me ve,
        correct_program P ->
        NoDupMembers insts ->
        Stc.Typ.wt_program P ->
        Forall (sem_trconstr P true R S I S') tcs ->
        Forall (wc_trconstr P Ω) tcs ->
        Forall (wt_trconstr P Γv Γm) tcs ->
        Forall (trconstr_mems_spec mems) tcs ->
        Forall (trconstr_insts_spec insts) tcs ->
        Forall (normal_args_tc P) tcs ->
        sem_clocked_vars_instant true R Ω ->
        (forall x ck, In (x, ck) Ω -> ~ PS.In x mems -> Env.find x clkvars = Some ck) ->
        (forall x, PS.In x mems -> find_val x me <> None) ->
        (forall x v, PS.In x mems -> sem_var_instant R x (present v) -> find_val x I = Some v) ->
        Ordered_systems P ->
        (forall i f Si, In (i, f) (iresets_of tcs) -> find_inst i S = Some Si -> state_closed P f Si) ->
        (forall i f Ii, In (i, f) (iresets_of tcs) -> find_inst i I = Some Ii -> state_closed P f Ii) ->
        Is_well_sch inputs mems tcs ->
        NoDup (inputs ++ variables tcs) ->
        NoDupMembers (steps_of tcs) ->
        reset_consistency tcs ->
        ireset_consistency tcs ->
        reset_clocks_have_sem true R tcs ->
        ireset_clocks_have_sem true R tcs ->
        (forall x, PS.In x mems -> Is_next_in x tcs) ->
        (forall x, In x inputs -> ~ Is_variable_in x tcs) ->
        (forall x c,
            In x inputs ->
            sem_var_instant R x (present c) ->
            Env.find x ve = Some c) ->
        (forall x, Env.find x ve <> None -> In x inputs) ->
        wt_memory me (translate P) Γm' insts ->
        wt_env ve Γv' ->
        me ≋ S ->
        exists me' ve',
          stmt_eval (translate P) me ve (translate_tcs mems clkvars tcs) (me', ve')
          /\ Memory_Corres R true tcs S I S' me'
          /\ forall x v,
              Is_variable_in x tcs ->
              sem_var_instant R x v ->
              Env.find x ve' = value_to_option v.
    Proof.
      intros; eapply trconstrs_app_correct with (insts:=insts) (tcs := []); eauto.
    Qed.

  End Trconstr.

  Lemma state_closed_insts_InMembers:
    forall P subs S s Ss,
      state_closed_insts P subs S ->
      find_inst s S = Some Ss ->
      InMembers s subs.
  Proof.
    intros * Closed Sub; apply Closed in Sub as (?&?&?).
    eapply In_InMembers; eauto.
  Qed.

  Theorem correctness:
    forall P f,
      Well_defined P ->
      wc_program P ->
      Stc.Typ.wt_program P ->
      correct_system P f.
  Proof.
    intros []; induction systems0 as [|system]; unfold correct_system;
      intros b (Ord & WSCH & NormalArgs) WC WT ???????? Sem Find Tcs Spec WTS WTins E;
      pose proof Sem;
      inversion_clear Sem as [????????? Find' ? Outs Hscv Htcs Closed TransClosed Closed'];
      try now inv Find.
    rewrite Find in Find'; inv Find'.
    pose proof Find as Find'.
    pose proof Ord as Ord'.
    inv Ord'; inversion WSCH;
      inversion_clear NormalArgs as [|?? Hnormal];
      inversion_clear WC as [|?? WCb];
      inversion WT as [|?? [WTb]]; simpl in *; subst.
    assert (Well_defined (Stc.Syn.Program types0 externs0 systems0)) by (split; auto).
    assert (correct_program (Stc.Syn.Program types0 externs0 systems0)) by (unfold correct_program; intros; auto).
    destruct WCb as (?&?&?& WCtcs); rewrite 2 idck_app, <-2 app_assoc in WCtcs.
    destruct WTb as (WTtcs &?).
    eapply find_unit_cons in Find as [[E' Find]|[E' Find]]; simpl in *; eauto.
    - inv Find.
      assert (clock_of_instant xs = true) as Clock by now apply clock_of_instant_true.
      rewrite Clock in Htcs.
      assert (~ Is_system_in (s_name system) (s_tcs system)) as Notin
        by (eapply find_system_not_Is_system_in with (2 := Find'); eauto).
      assert (Forall (fun oc => snd oc <> s_name system) (s_subs system)).
      { apply Forall_forall; intros * Hin; apply in_map with (f := snd) in Hin.
        intro E'; rewrite E' in Hin.
        rewrite steps_iresets_of_Is_system_in, map_app, in_app_comm,
        <-incl_in_app, <-s_subs_steps_of in Notin; try contradiction.
        apply incl_map, s_ireset_incl.
      }
      apply sem_trconstrs_cons in Htcs; auto.
      pose proof (s_type_env_spec system) as TypeEnvSpec.
      pose proof (s_trconstr_insts_spec system) as Spec_i.
      edestruct trconstrs_correct
        with (1 := TypeEnvSpec)
             (11 := Spec_i)
             (me := me)
             (ve := Env.adds_opt (map fst (m_in (step_method system))) ins vempty)
             (clkvars := Env.adds_with snd system.(s_out)
                           (Env.adds_with snd system.(s_vars)
                             (Env.from_list_with snd system.(s_in))))
        as (me' & ve' &?&?& Equiv); eauto with stcsyntax stcsem.
      + pose proof (s_nodup_nexts system) as N; clear - N.
        induction N; simpl; constructor; auto.
        rewrite fst_InMembers.
        intro Hin; apply in_map_iff in Hin as ((?&?)&E& Hin); simpl in *; subst.
        apply in_map_iff in Hin as ((x&((c&t')&ck))&E&?); simpl in *; inv E.
        take (~ InMembers _ _) and apply it.
        apply fst_InMembers.
        change a with (fst (a, (c, t, ck))); now apply in_map.
      + rewrite <-2 idty_app, NoDupMembers_idty.
        apply s_nodup_vars.
      + apply s_nodup_subs.
      + apply s_trconstr_mems_spec.
      + apply Forall_forall.
        intros (y, ck) Hxin.
        apply in_app in Hxin as [Hxin|Hxin].
        * rewrite <-Clock; eapply Forall_forall in Hscv; eauto.
        * eapply sem_clocked_var_instant_tcs with (4 := Htcs); eauto.
          -- apply fst_NoDupMembers; rewrite 3 map_app, 4 map_fst_idck.
             apply s_nodup.
          -- rewrite s_defined, <-s_vars_out_in_tcs, <-s_nexts_in_tcs, mems_of_nexts_fst,
             <-app_assoc, 2 map_app, 3 map_fst_idck; auto.
      + intros y ? Hin Hnin.
        rewrite ps_from_list_In in Hnin.
        pose proof (s_nodup system) as Nodup.
        rewrite 3 in_app in Hin; destruct Hin as [Hin|[Hin|[Hin|Hin]]];
          apply In_idck_exists in Hin as (?&?).
        * apply (NoDup_app_In y) in Nodup.
          -- unfold Env.from_list_with.
             rewrite 2 Env.gsso_with.
             ++ erewrite Env.In_find_adds_with; eauto; simpl; auto.
                do 2 eapply NoDupMembers_app_l; rewrite <-app_assoc; apply s_nodup_vars.
             ++ intros Hin; apply Nodup, in_app; left; apply fst_InMembers; auto.
             ++ intros Hin; apply Nodup; rewrite 2 in_app; right; left; apply fst_InMembers; auto.
          -- apply in_map_iff; eexists; (intuition eauto); auto.
        * rewrite Permutation.Permutation_app_comm in Nodup.
          apply NoDup_app_weaken, (NoDup_app_In y) in Nodup.
          -- rewrite Env.gsso_with.
             ++ erewrite Env.In_find_adds_with; eauto; simpl; auto.
                eapply NoDupMembers_app_l; eapply NoDupMembers_app_r; apply s_nodup_vars.
             ++ intros Hin; apply Nodup, in_app; left; apply fst_InMembers; auto.
          -- apply in_map_iff; eexists; (intuition eauto); auto.
        * erewrite Env.In_find_adds_with; eauto; simpl; auto.
          do 2 eapply NoDupMembers_app_r; apply s_nodup_vars.
        * exfalso; apply Hnin, in_map_iff; eexists; (intuition eauto); auto.
      + setoid_rewrite ps_from_list_In; intros.
        rewrite E; eapply sem_system_find_val; eauto.
      + setoid_rewrite ps_from_list_In; intros.
        eapply sem_system_find_valI; eauto.
      + inversion_clear Closed as [????? Find ? Insts]; rewrite Find in Find'; inv Find'.
        intros ? b' ? Hin Sub.
        apply Insts in Sub as (b'' &?&?).
        apply s_ireset_incl in Hin.
        rewrite <-s_subs_steps_of in Hin.
        assert (b' = b'') as ->; auto.
        eapply NoDupMembers_det in Hin; eauto.
        apply s_nodup_subs.
      + inversion_clear TransClosed as [????? Find ? Insts]; rewrite Find in Find'; inv Find'.
        intros ? b' ? Hin Sub.
        apply Insts in Sub as (b'' &?&?).
        apply s_ireset_incl in Hin.
        rewrite <-s_subs_steps_of in Hin.
        assert (b' = b'') as ->; auto.
        eapply NoDupMembers_det in Hin; eauto.
        apply s_nodup_subs.
      + rewrite <-s_vars_out_in_tcs, <-2 map_app, <-fst_NoDupMembers.
        apply s_nodup_vars.
      + rewrite <-s_subs_steps_of. apply s_nodup_subs.
      + apply s_reset_consistency.
      + apply s_ireset_consistency.
      + eapply sem_trconstrs_reset_clocks; eauto using s_reset_consistency.
      + eapply sem_trconstrs_ireset_clocks; eauto using s_ireset_consistency.
      + intro. now rewrite ps_from_list_In, s_nexts_in_tcs_fst, nexts_of_In.
      + intros; apply s_ins_not_var, fst_InMembers; auto.
      + simpl; intros; eapply eq_if_present_adds_opt; eauto; rewrite map_fst_idty; auto.
      + simpl; rewrite map_fst_idty; intros * Find.
        apply not_None_is_Some in Find as (?& Find); apply Env.find_adds_opt_spec_Some in Find.
        * rewrite Env.gempty in Find; destruct Find as [Hin|]; try discriminate.
          eapply in_combine_l; eauto.
        * transitivity (length xs); eapply Forall2_length; eauto.
      + rewrite E; simpl in *.
        now apply transform_units_wt_memory in WTS.
      + eapply wt_env_adds_opt.
        * rewrite <-2 idty_app, NoDupMembers_idty.
          apply s_nodup_vars.
        * apply fst_NoDupMembers, m_nodupin.
        * apply wt_env_empty.
        * unfold step_method; simpl.
          apply Forall2_map_1, Forall2_same, Forall_forall.
          intros (x, t) Hin; simpl.
          apply in_app; auto.
        * unfold idty; apply Forall2_swap_args, Forall2_map_1; auto.
      + exists me'; split.
        * apply find_unit_transform_units_forward in Find'.
          econstructor; eauto.
          -- apply exists_step_method.
          -- simpl; transitivity (length xs).
             ++ symmetry; eapply Forall2_length; eauto.
             ++ rewrite length_idty, <-map_length with (f := fst);
                  symmetry; eapply Forall2_length; eauto.
          -- simpl; eauto.
          -- simpl; rewrite map_fst_idty.
             clear - Outs Equiv.
             rewrite Forall2_map_2.
             eapply Forall2_impl_In; eauto; intros.
             apply Equiv; auto.
             apply Is_variable_in_variables.
             rewrite <-s_vars_out_in_tcs, in_app; auto.
        * inv Closed; inv Closed';
            repeat match goal with
                     H: find_system ?b ?P = _, H': find_system ?b ?P = _ |- _ =>
                     rewrite H in H'; inv H'
                   end.
          { eapply Memory_Corres_equal_memory; eauto.
            - intro; now rewrite s_nexts_in_tcs_fst, nexts_of_In.
            - intros ?? Reset.
              rewrite s_nexts_in_tcs_fst. apply s_reset_incl, resets_of_In; eauto.
            - intro. now rewrite fst_InMembers, s_subs_steps_of, steps_of_In.
            - intros * Rst. eapply steps_of_In, incl_map. eapply s_ireset_incl.
              eapply iresets_of_In; eauto.
          }
    - pose proof Ord; eapply find_unit_other_not_Is_called_in in Ord; simpl; eauto; simpl; eauto.
      apply sem_trconstrs_cons in Htcs; auto.
      + apply state_closed_other in Closed;
          apply state_closed_other in TransClosed;
          apply state_closed_other in Closed'; auto.
        assert (Forall (fun oc => snd oc <> s_name system) (s_subs s0)).
        { apply Forall_forall; intros * Hin; apply in_map with (f := snd) in Hin.
          intro E''; rewrite E'' in Hin; contradiction.
        }
        edestruct IHsystems0 as (me' &?&?); eauto using sem_system.
        exists me'; split; auto.
        apply stmt_call_eval_cons; auto.
      + rewrite steps_iresets_of_Is_system_in, map_app,
        Permutation.Permutation_app_comm, <- incl_in_app, <- s_subs_steps_of; auto.
        apply incl_map, s_ireset_incl.
  Qed.

  Corollary correctness_loop_call:
    forall P f s P' xss yss ins S0,
      Well_defined P ->
      wc_program P ->
      Stc.Typ.wt_program P ->
      initial_state P f S0 ->
      find_system f P = Some (s, P') ->
      wt_memory S0 P' (mems_of_nexts (s_nexts s)) (s_subs s) ->
      (forall n, Forall2 (fun xt vo => wt_option_value vo (fst (snd xt))) (s_in s) (ins n)) ->
      loop P f xss yss S0 0 ->
      (forall n, Forall2 eq_if_present (xss n) (ins n)) ->
      (forall n, Exists (fun v => v <> absent) (xss n)) ->
      exists me0,
        stmt_call_eval (translate P) mempty f reset [] me0 []
        /\ loop_call (translate P) f step ins (fun n => map value_to_option (yss n)) 0 me0
        /\ me0 ≋ S0.
  Proof.
    intros * Wdef WC WT Init Find WTS0 WTins Loop Spec Clock.
    pose proof Loop as Loop'; inversion_clear Loop' as [??????? Sem].
    inv Sem.
    assert (Ordered_systems P) as Ord by apply Wdef.
    eapply reset_spec with (me := mempty) in Ord as (me' &?&?& Closed); eauto.
    assert (me' ≋ S0) as Eq
        by (eapply initial_state_det; eauto;
            eapply Closed, state_closed_empty; eauto).
    exists me'; split; [|split]; auto.
    clear - Find Loop Wdef WC WT WTS0 WTins Eq Spec Clock.
    revert Loop Eq; revert dependent S0; revert me'.
    generalize 0.
    cofix COFIX; intros.
    inversion_clear Loop as [??????? Sem].
    pose proof Wdef; destruct Wdef as (?&?&?).
    edestruct sem_system_wt; eauto with typing.
    - clear - WTins Spec.
      specialize (WTins n); specialize (Spec n).
      apply Forall2_swap_args in Spec; apply Forall2_trans_ex with (2 := Spec) in WTins; clear Spec.
      induction WTins as [|???? (?&?&WT&E)]; constructor; auto.
      inv E; simpl; auto.
    - eapply correctness in Sem as (?&?&?); eauto.
      econstructor; eauto.
  Qed.

End CORRECTNESS.

Module CorrectnessFun
       (Ids      : IDS)
       (Op       : OPERATORS)
       (OpAux    : OPERATORS_AUX   Ids Op)
       (ComTyp   : COMMONTYPING    Ids Op OpAux)
       (Cks      : CLOCKS          Ids Op OpAux)
       (Str      : INDEXEDSTREAMS  Ids Op OpAux Cks)
       (CE       : COREEXPR        Ids Op OpAux ComTyp Cks Str)
       (Stc      : STC             Ids Op OpAux ComTyp Cks Str CE)
       (Obc      : OBC             Ids Op OpAux ComTyp)
       (Trans    : TRANSLATION     Ids Op OpAux Cks     CE.Syn Stc.Syn Obc.Syn)
       (TransTyp : STC2OBCTYPING   Ids Op OpAux ComTyp Cks Str CE Stc Obc Trans)
<: CORRECTNESS Ids Op OpAux ComTyp Cks Str CE Stc Obc Trans TransTyp.
  Include CORRECTNESS Ids Op OpAux ComTyp Cks Str CE Stc Obc Trans TransTyp.
End CorrectnessFun.
