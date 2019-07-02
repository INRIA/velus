From Velus Require Import SyBloc.
From Velus Require Import Obc.

From Velus Require Import SyBlocToObc.Translation.
From Velus Require Import SyBlocToObc.SBMemoryCorres.

From Velus Require Import RMemory.
From Velus Require Import Common.
From Velus Require Import Environment.

From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import Setoid Morphisms.

Open Scope nat.
Open Scope list.

Module Type CORRECTNESS
       (Import Ids    : IDS)
       (Import Op     : OPERATORS)
       (Import OpAux  : OPERATORS_AUX      Op)
       (Import Str    : STREAM             Op OpAux)
       (Import CE     : COREEXPR       Ids Op OpAux Str)
       (Import SB     : SYBLOC         Ids Op OpAux Str CE)
       (Import Obc    : OBC            Ids Op OpAux)
       (Import Trans  : TRANSLATION    Ids Op OpAux CE.Syn SB.Syn Obc.Syn)
       (Import Corres : SBMEMORYCORRES Ids Op       CE.Syn SB.Syn SB.Last).

  Definition eq_if_present (x: value) (oy: option val) : Prop :=
    match x, oy with
    | present xv, Some yv => xv = yv
    | absent, _ => True
    | _, _ => False
    end.

  Definition value_to_option (v: value) : option val :=
    match v with
    | absent => None
    | present c => Some c
    end.

  Definition equiv_env (in_domain: ident -> Prop) (R: env)
             (inputs: list ident) (mems: PS.t) (me: menv) (ve: venv) : Prop :=
    forall x v,
      in_domain x ->
      sem_var_instant R x v ->
      if PS.mem x mems
      then eq_if_present v (find_val x me)
      else if In_dec ident_eq_dec x inputs
           then eq_if_present v (Env.find x ve)
           else Env.find x ve = value_to_option v.

  Lemma equiv_env_map:
    forall (in_dom1 in_dom2: ident -> Prop) R inputs mems me ve,
      (forall x, in_dom2 x -> in_dom1 x) ->
      equiv_env in_dom1 R inputs mems me ve ->
      equiv_env in_dom2 R inputs mems me ve.
  Proof.
    unfold equiv_env; intros ???????? Eq ????. apply Eq; auto.
  Qed.

  Ltac weaken_equiv_env_with tac :=
    match goal with
      H: equiv_env ?in_dom1 ?R ?inputs ?mems ?me ?ve
      |- equiv_env ?in_dom2 ?R ?inputs ?mems ?me ?ve =>
      eapply equiv_env_map; [|exact H]; tac
    end.

  Tactic Notation "weaken_equiv_env" "with" tactic(tac) :=
    weaken_equiv_env_with tac.

  Tactic Notation "weaken_equiv_env" :=
    weaken_equiv_env with now (constructor; auto).

  Hint Extern 4 (equiv_env _ _ _ _ _ _) => weaken_equiv_env.

  Lemma eq_if_present_present:
    forall vo c,
      eq_if_present (present c) vo <-> vo = Some c.
  Proof.
    simpl; split.
    - cases; inversion 1; auto.
    - intros ->; auto.
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
      forall ck x v b,
        Is_present_in mems me ve ck ->
        exp_eval me ve (tovar mems (x, bool_type)) (Some v) ->
        val_to_bool v = Some b ->
        Is_present_in mems me ve (Con ck x b).

  Inductive Is_absent_in (mems: PS.t) (me: menv) (ve: venv): clock -> Prop :=
  | IsAbs1:
      forall ck x v,
        Is_absent_in mems me ve ck ->
        Is_absent_in mems me ve (Con ck x v)
  | IsAbs2:
      forall ck x v b,
        Is_present_in mems me ve ck ->
        exp_eval me ve (tovar mems (x, bool_type)) (Some v) ->
        val_to_bool v = Some b ->
        Is_absent_in mems me ve (Con ck x (negb b)).

  Hint Constructors Is_present_in Is_absent_in.

  Lemma stmt_eval_Control_fwd:
    forall prog me ve mems ck s me' ve',
      stmt_eval prog me ve (Control mems ck s) (me', ve') ->
      (Is_present_in mems me ve ck
       /\ stmt_eval prog me ve s (me', ve'))
      \/
      (Is_absent_in mems me ve ck
       /\ me' = me /\ ve' = ve).
  Proof.
    intros * StEval.
    revert dependent s.
    induction ck; intuition.
    simpl in *; cases; apply IHck in StEval as [[Hp Hs]|[Hp [Hmenv Henv]]];
      intuition; inv Hs.
    - cases; intuition; eauto.
      chase_skip.
      assert (true = negb false) as -> by reflexivity;
        eauto.
    - cases; intuition; eauto.
      chase_skip.
      assert (false = negb true) as -> by reflexivity;
        eauto.
  Qed.

  (* Conjunction required for simultaneous induction. *)
  Fact stmt_eval_Control:
    forall prog mems me ve ck s,
      (Is_absent_in mems me ve ck ->
       stmt_eval prog me ve (Control mems ck s) (me, ve))
      /\
      (forall me' ve',
          Is_present_in mems me ve ck ->
          stmt_eval prog me ve s (me', ve') ->
          stmt_eval prog me ve (Control mems ck s) (me', ve')).
  Proof.
    Hint Constructors stmt_eval.
    intros; revert s; induction ck; split; auto.
    - inversion 1.
    - inversion_clear 1 as [??? Hp|???? Hp]; simpl;
        cases; apply IHck with (1 := Hp); eauto.
    - inversion_clear 1 as [|???? Hp]; simpl; intros;
        cases; apply IHck with (1 := Hp); eauto.
  Qed.

  (** If the clock is absent, then the controlled statement evaluates as
  a [Skip].  *)

  Lemma stmt_eval_Control_absent:
    forall prog mems me ve ck s,
      Is_absent_in mems me ve ck ->
      stmt_eval prog me ve (Control mems ck s) (me, ve).
  Proof. apply stmt_eval_Control. Qed.

  (** If the clock is present, then the controlled statement evaluates
  as the underlying one.  *)

  Lemma stmt_eval_Control_present:
    forall prog mems me ve ck s me' ve',
      Is_present_in mems me ve ck ->
      stmt_eval prog me ve s (me', ve') ->
      stmt_eval prog me ve (Control mems ck s) (me', ve').
  Proof. apply stmt_eval_Control. Qed.

  Section ExprClock.

    Variable inputs: list ident.
    Variable mems: PS.t.

    Variable R: env.
    Variable (me: menv) (ve: venv).

    Lemma exp_correct:
      forall e c,
        sem_exp_instant true R e (present c) ->
        equiv_env (fun x => CE.IsF.Is_free_in_exp x e) R inputs mems me ve ->
        exp_eval me ve (translate_exp mems e) (Some c).
    Proof.
      induction e; inversion_clear 1; simpl; intros; auto.
      - match goal with H: _ = _ |- _ => inv H end.
        econstructor; congruence.
      - split_env_assumption; cases; try rewrite eq_if_present_present in *;
          eauto using exp_eval.
      - econstructor; eauto; now rewrite typeof_correct.
      - econstructor; eauto; now rewrite 2 typeof_correct.
    Qed.
    Hint Resolve exp_correct.

    Lemma arg_correct:
      forall me ve mems cvars ck e c,
        exp_eval me ve (translate_exp mems e) (Some c) ->
        exp_eval me ve (translate_arg mems cvars ck e) (Some c).
    Proof.
      intros * Heval.
      unfold translate_arg.
      destruct (var_on_base_clock mems0 cvars ck e); auto.
    Qed.
    Hint Resolve arg_correct.

    Lemma cexp_correct:
      forall e c prog x,
        sem_cexp_instant true R e (present c) ->
        equiv_env (fun x => Is_free_in_cexp x e) R inputs mems me ve ->
        stmt_eval prog me ve (translate_cexp mems x e) (me, Env.add x c ve).
    Proof.
      induction e;
        inversion 1 as [???? Hvar|???? Hvar| | | |];
        subst; simpl; intros; eauto using stmt_eval.
      - split_env_assumption.
        econstructor; eauto.
        + unfold bool_var, tovar; cases; try rewrite eq_if_present_present in Hvar;
            eauto using exp_eval.
        + apply val_to_bool_true.
        + simpl; auto.
      - split_env_assumption.
        econstructor; eauto.
        + unfold bool_var, tovar; cases; try rewrite eq_if_present_present in Hvar;
            eauto using exp_eval.
        + apply val_to_bool_false.
        + simpl; auto.
      - econstructor; eauto; cases.
    Qed.
    Hint Resolve cexp_correct.

    Lemma clock_correct_true:
      forall base ck,
        equiv_env (fun x => Is_free_in_clock x ck) R inputs mems me ve ->
        sem_clock_instant base R ck true ->
        Is_present_in mems me ve ck.
    Proof.
      induction ck; eauto.
      inversion_clear 2; subst.
      econstructor; eauto.
      unfold tovar; split_env_assumption.
      cases; try rewrite eq_if_present_present in *; eauto using exp_eval.
    Qed.

    Lemma clock_correct_false:
      forall ck,
        equiv_env (fun x => Is_free_in_clock x ck) R inputs mems me ve ->
        sem_clock_instant true R ck false ->
        Is_absent_in mems me ve ck.
    Proof.
      induction ck as [|?? x]; [now inversion 2|].
      intro Henv.
      inversion_clear 1; auto.
      econstructor 2; eauto.
      - eapply clock_correct_true; eauto.
      - unfold tovar; split_env_assumption.
        cases; try rewrite eq_if_present_present in *; eauto using exp_eval.
    Qed.

    Variable ck: clock.
    Hypothesis Equiv: equiv_env (fun x => Is_free_in_clock x ck) R inputs mems me ve.

    Corollary stmt_eval_Control_absent':
      forall prog s,
        sem_clock_instant true R ck false ->
        stmt_eval prog me ve (Control mems ck s) (me, ve).
    Proof.
      intros; eapply stmt_eval_Control_absent, clock_correct_false; eauto.
    Qed.

    Corollary stmt_eval_Control_present':
      forall base prog s me' ve',
        sem_clock_instant base R ck true ->
        stmt_eval prog me ve s (me', ve') ->
        stmt_eval prog me ve (Control mems ck s) (me', ve').
    Proof.
      intros; apply stmt_eval_Control_present; auto.
      eapply clock_correct_true; eauto.
    Qed.

  End ExprClock.

  (** Reset correctness *)

  Definition add_mems (mems: list (ident * (const * clock))) (me: menv) : menv :=
    Mem (fold_left (fun vs xc => Env.add (fst xc) (sem_const (fst (snd xc))) vs) mems (values me))
        (instances me).

  Lemma find_inst_add_mems:
    forall x me xs,
      find_inst x (add_mems xs me) = find_inst x me.
  Proof. reflexivity. Qed.

  Lemma add_mems_cons:
    forall x c ck xs me,
      add_mems ((x, (c, ck)) :: xs) me = add_mems xs (add_val x (sem_const c) me).
  Proof. reflexivity. Qed.

  Lemma add_mems_nil:
    forall me,
      add_mems [] me = me.
  Proof. destruct me; reflexivity. Qed.

  Lemma add_mems_gss:
    forall x c ck xs me,
      ~ InMembers x xs ->
      find_val x (add_mems ((x, (c, ck)) :: xs) me) = Some (sem_const c).
  Proof.
    intros * Notin; rewrite add_mems_cons.
    revert me; induction xs as [|(?,(? & ?))]; intros.
    - now rewrite add_mems_nil, find_val_gss.
    - apply NotInMembers_cons in Notin as (? & ?).
      rewrite add_mems_cons, add_val_comm; auto.
  Qed.

  Lemma find_val_add_mems_in:
    forall x c ck xs me,
      NoDupMembers xs ->
      In (x, (c, ck)) xs ->
      find_val x (add_mems xs me) = Some (sem_const c).
  Proof.
    intros * Nodup Hin.
    revert me; induction xs as [|(?,(? & ?))]; intros.
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
      (NoDupMembers xs -> InMembers x xs -> exists c ck, v = sem_const c /\ In (x, (c, ck)) xs)
      /\
      (~ InMembers x xs -> find_val x me = Some v).
  Proof.
    intros * Find; split; [intros * Nodup Hin|intros * Hin].
    - revert dependent me; induction xs as [|(x', (c, ck))]; intros;
        inv Hin; inv Nodup.
      + rewrite add_mems_gss in Find; auto; inv Find.
        exists c, ck; intuition.
      + rewrite add_mems_cons in Find.
        edestruct IHxs as (?&?&?&?); eauto.
        do 2 eexists; intuition; eauto; right; eauto.
    - revert dependent me; induction xs as [|(x', (c', ck'))]; intros.
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
    induction mems as [|(x, (c, ck))]; simpl; intros.
    - rewrite add_mems_nil; eauto using stmt_eval.
    - rewrite stmt_eval_fold_left_lift; setoid_rewrite stmt_eval_eq_Comp_Skip1.
      do 2 eexists; split; eauto using stmt_eval, exp_eval.
      rewrite add_mems_cons; auto.
  Qed.

  Lemma translate_reset_comp:
    forall prog me ve bl me' ve',
      stmt_eval prog me ve (translate_reset bl) (me', ve')
      <-> stmt_eval prog me ve (reset_mems bl.(b_lasts)) (add_mems bl.(b_lasts) me, ve)
        /\ stmt_eval prog (add_mems bl.(b_lasts) me) ve (reset_insts bl.(b_blocks)) (me', ve').
  Proof.
    unfold translate_reset; split.
    - inversion_clear 1 as [| | |????????? StEval| |].
      pose proof (reset_mems_spec (b_lasts bl) prog me ve) as StEval'.
      eapply stmt_eval_det with (2 := StEval') in StEval as (? & ?); subst.
      split; auto.
    - intros (? & ?); eauto using stmt_eval.
  Qed.

  Lemma add_mems_reset_lasts:
    forall bl me,
      reset_lasts bl (add_mems bl.(b_lasts) me).
  Proof.
    unfold reset_lasts; intros.
    eapply find_val_add_mems_in; eauto.
    apply b_nodup_lasts.
  Qed.

  Lemma add_mems_state_closed_lasts:
    forall lasts me,
      state_closed_lasts (map fst lasts) me ->
      state_closed_lasts (map fst lasts) (add_mems lasts me).
  Proof.
    intros * Closed ? Find.
    apply not_None_is_Some in Find as (?& Find).
    apply find_val_add_mems_inv in Find.
    destruct (in_dec ident_eq_dec x (map fst lasts)) as [|Hin]; auto.
    rewrite <-fst_InMembers in Hin; apply Find in Hin.
    apply Closed, not_None_is_Some; eauto.
  Qed.

  Lemma add_mems_state_closed:
    forall P b bl P' me,
      state_closed P b me ->
      find_block b P = Some (bl, P') ->
      state_closed P b (add_mems bl.(b_lasts) me).
  Proof.
    inversion_clear 1 as [????? Find]; intros * Find';
      rewrite Find in Find'; inv Find'.
    econstructor; eauto.
    now apply add_mems_state_closed_lasts.
  Qed.

  Lemma reset_insts_reset_lasts:
    forall blocks prog me ve me' ve' bl,
      stmt_eval prog me ve (reset_insts blocks) (me', ve') ->
      reset_lasts bl me ->
      reset_lasts bl me'.
  Proof.
    unfold reset_insts.
    induction blocks; simpl.
    - inversion_clear 1; auto.
    - intros * StEval Lasts ??? Hin.
      apply stmt_eval_fold_left_lift in StEval as (?&?& StEval & StEvals).
      eapply IHblocks in StEvals; eauto.
      rewrite stmt_eval_eq_Comp_Skip1 in StEval; inv StEval.
      now apply reset_lasts_add_inst.
  Qed.

  Lemma reset_insts_state_closed_lasts:
    forall blocks lasts prog me ve me' ve',
      stmt_eval prog me ve (reset_insts blocks) (me', ve') ->
      state_closed_lasts lasts me ->
      state_closed_lasts lasts me'.
  Proof.
    unfold reset_insts.
    induction blocks; simpl.
    - inversion_clear 1; auto.
    - intros * StEval Lasts ? Hin.
      apply stmt_eval_fold_left_lift in StEval as (?&?& StEval & StEvals).
      eapply IHblocks in StEvals; eauto.
      rewrite stmt_eval_eq_Comp_Skip1 in StEval; inv StEval.
      now apply state_closed_lasts_add_inst.
  Qed.

  Lemma reset_insts_same_venv:
    forall blocks prog me ve me' ve',
      stmt_eval prog me ve (reset_insts blocks) (me', ve') ->
      ve' = ve.
  Proof.
    unfold reset_insts.
    induction blocks; simpl.
    - inversion_clear 1; auto.
    - intros * StEval.
      apply stmt_eval_fold_left_lift in StEval as (?&?& StEval & StEvals).
      eapply IHblocks in StEvals; eauto.
      rewrite stmt_eval_eq_Comp_Skip1 in StEval; inv StEval.
      apply Env.updates_nil_l.
  Qed.

  Lemma call_reset_inv:
    forall b P bl P' me me' rvs,
      find_block b P = Some (bl, P') ->
      stmt_call_eval (translate P) me b reset [] me' rvs ->
      stmt_eval (translate P') me vempty (translate_reset bl) (me', vempty)
      /\ rvs = [].
  Proof.
    intros * Find Rst.
    apply find_block_translate in Find as (?&?& Find &?&?); subst.
    inversion_clear Rst as [??????????? Find' Find_m ? StEval Ret].
    rewrite Find in Find'; inv Find'.
    rewrite exists_reset_method in Find_m; inv Find_m; simpl in *.
    inv Ret; intuition.
    rewrite Env.adds_opt_nil_nil in StEval.
    apply translate_reset_comp in StEval as (?& Insts).
    rewrite translate_reset_comp; intuition.
    assert (ve' = vempty) as HH by (eapply reset_insts_same_venv; eauto).
    rewrite HH in Insts; auto.
  Qed.

  Lemma call_reset_reset_lasts:
    forall me' P me b bl P',
      find_block b P = Some (bl, P') ->
      stmt_call_eval (translate P) me b reset [] me' [] ->
      reset_lasts bl me'.
  Proof.
    intros ?????? Find Rst ??? Hin.
    eapply call_reset_inv in Rst as (Rst & ?); eauto;
      apply translate_reset_comp in Rst as (? & ?).
    eapply reset_insts_reset_lasts; eauto.
    apply add_mems_reset_lasts; auto.
  Qed.

  Lemma call_reset_state_closed_lasts:
    forall me' P me b bl P',
      find_block b P = Some (bl, P') ->
      stmt_call_eval (translate P) me b reset [] me' [] ->
      state_closed_lasts (map fst bl.(b_lasts)) me ->
      state_closed_lasts (map fst bl.(b_lasts)) me'.
  Proof.
    intros ?????? Find Rst ?? Hin.
    eapply call_reset_inv in Rst as (Rst & ?); eauto;
      apply translate_reset_comp in Rst as (?& Rst).
    eapply reset_insts_state_closed_lasts in Rst; eauto.
    apply add_mems_state_closed_lasts; auto.
  Qed.

  Lemma reset_insts_not_InMembers:
    forall blocks prog me ve me' ve' x,
      stmt_eval prog me ve (reset_insts blocks) (me', ve') ->
      ~ InMembers x blocks ->
      find_inst x me' = find_inst x me.
  Proof.
    unfold reset_insts.
    induction blocks as [|(x', c')].
    - inversion 1; auto.
    - intros * StEval Notin; apply NotInMembers_cons in Notin as (? & ?); simpl in *.
      apply stmt_eval_fold_left_lift in StEval as (?&?& StEval & StEvals).
      eapply IHblocks in StEvals; eauto.
      rewrite stmt_eval_eq_Comp_Skip1 in StEval; inv StEval.
      rewrite StEvals, find_inst_gso; auto.
  Qed.

  Lemma reset_insts_in:
    forall bl P P' me ve me' ve' x b b',
      find_block b P = Some (bl, P') ->
      stmt_eval (translate P') me ve (reset_insts bl.(b_blocks)) (me', ve') ->
      In (x, b') bl.(b_blocks) ->
      find_block b' P' <> None ->
      exists me_x,
        stmt_call_eval (translate P') (match find_inst x me with
                                       | Some om => om
                                       | None => mempty
                                       end)
                       b' reset [] me_x []
        /\ find_inst x me' = Some me_x.
  Proof.
    unfold reset_insts.
    intro; pose proof (b_nodup_blocks bl) as Nodup.
    induction bl.(b_blocks) as [|(x', b'')]; simpl; try now inversion 2.
    intros * Find StEval Hin Find'; inversion_clear Nodup as [|??? Notin].
    apply stmt_eval_fold_left_lift in StEval as (me_x' &?& StEval & StEvals).
    destruct Hin as [E|].
    - inv E.
      erewrite reset_insts_not_InMembers with (me' := me'); eauto.
      rewrite stmt_eval_eq_Comp_Skip1 in StEval; inv StEval.
      match goal with H: Forall2 _ _ _ |- _ => inv H end.
      rewrite find_inst_gss.
      cut (rvos = []).
      + intro Hrvos; rewrite Hrvos in *; eauto.
      + apply not_None_is_Some in Find' as ((? & ?) & ?).
        eapply call_reset_inv in H12 as (? & ?); eauto.
    - assert (find_inst x me = find_inst x me_x') as ->; eauto.
      rewrite stmt_eval_eq_Comp_Skip1 in StEval; inv StEval.
      rewrite find_inst_gso; auto.
      intro; subst; eapply Notin, In_InMembers; eauto.
  Qed.

  Lemma find_inst_reset_insts_inv:
    forall blocks prog me ve me' ve' x me_x,
      stmt_eval prog me ve (reset_insts blocks) (me', ve') ->
      find_inst x me' = Some me_x ->
      InMembers x blocks
      \/ find_inst x me = Some me_x.
  Proof.
    unfold reset_insts.
    induction blocks as [|(x', b)]; simpl.
    - inversion_clear 1; auto.
    - intros * StEval Sub.
      apply stmt_eval_fold_left_lift in StEval as (me_x' &?& StEval & StEvals).
      eapply IHblocks in StEvals as [|Sub']; eauto.
      rewrite stmt_eval_eq_Comp_Skip1 in StEval.
      inv StEval.
      destruct (ident_eq_dec x x'); auto.
      rewrite find_inst_gso in Sub'; auto.
  Qed.

  Lemma call_reset_initial_state:
    forall me' P me b bl P',
      Ordered_blocks P ->
      find_block b P = Some (bl, P') ->
      stmt_call_eval (translate P) me b reset [] me' [] ->
      initial_state P b me' /\ (state_closed P b me -> state_closed P b me').
  Proof.
    induction me' as [? IH] using memory_ind';
      intros * Ord Find Rst.
    pose proof Ord as Ord'.
    eapply Ordered_blocks_find_block in Ord'; eauto.
    split.
    - econstructor; eauto.
      + eapply call_reset_reset_lasts; eauto.
      + intros * Hin.
        eapply call_reset_inv in Rst as (Rst & ?); eauto;
          apply  translate_reset_comp in Rst as (? & ?).
        eapply Ordered_blocks_find_In_blocks in Ord as (?&?& Find'); eauto.
        pose proof Hin as Hin'.
        eapply reset_insts_in in Hin as (me_x & ? & ?); eauto.
        * exists me_x; split; auto.
          eapply IH; eauto.
        * apply not_None_is_Some; eauto.
    - inversion_clear 1 as [????? Find' ? Insts]; rewrite Find' in Find; inv Find.
      econstructor; eauto.
      + eapply call_reset_state_closed_lasts; eauto.
      + intros * Sub.
        eapply call_reset_inv in Rst as (Rst & ?); eauto;
          apply  translate_reset_comp in Rst as (?& Rst).
        pose proof Rst.
        eapply find_inst_reset_insts_inv in Rst as [Hin|]; eauto.
        apply InMembers_In in Hin as (b' & Hin).
        eapply Ordered_blocks_find_In_blocks in Ord as (?&?& Find); eauto.
        pose proof Hin as Hin'.
        eapply reset_insts_in in Hin as (me_x & ? & Sub'); eauto.
        * eexists; split; eauto.
          rewrite Sub' in Sub; inv Sub.
          eapply IH; eauto.
          rewrite find_inst_add_mems.
          destruct (find_inst x me) eqn: E; [|eapply state_closed_empty; eauto].
          apply Insts in E as (b'' &?&?).
          assert (b' = b'') as ->; auto.
          eapply NoDupMembers_det in Hin'; eauto.
          apply b_nodup_blocks.
        * apply not_None_is_Some; eauto.
  Qed.

  Lemma reset_insts_exists:
    forall bl P me ve,
      (forall me' b' bl' P',
          find_block b' P = Some (bl', P') ->
          exists me'',
            stmt_call_eval (translate P) me' b' reset [] me'' []) ->
      (forall x b,
          In (x, b) bl.(b_blocks) ->
          exists bl P',
            find_block b P = Some (bl, P')) ->
      exists me',
        stmt_eval (translate (P)) me ve (reset_insts bl.(b_blocks)) (me', ve).
  Proof.
    unfold reset_insts.
    intro; induction bl.(b_blocks) as [|(x, b')]; simpl in *;
      intros * IH Spec; eauto using stmt_eval.
    setoid_rewrite stmt_eval_fold_left_lift.
    edestruct Spec as (?&?& Find); eauto.
    eapply IH in Find as (?&?).
    edestruct IHl; eauto 7.
  Qed.

  Lemma reset_exists:
    forall P b bl P' me,
      Ordered_blocks P ->
      find_block b P = Some (bl, P') ->
      exists me',
        stmt_call_eval (translate P) me b reset [] me' [].
  Proof.
    induction P as [|block]; try now inversion 2.
    intros * Ord Find.
    pose proof Find as Find';
      apply find_block_translate in Find' as (?&?& Find' &?&?); subst.
    simpl in Find; destruct (ident_eqb (b_name block) b) eqn: E.
    - inv Find.
      edestruct reset_insts_exists; eauto using Ordered_blocks.
      + inv Ord; eauto.
      + eapply Ordered_blocks_find_In_blocks; eauto.
        simpl; now rewrite ident_eqb_refl.
      + eexists; econstructor; eauto.
        * apply exists_reset_method.
        * simpl; auto.
        * simpl; rewrite Env.adds_opt_nil_nil.
          apply translate_reset_comp; split; eauto.
          apply reset_mems_spec.
        * simpl; auto.
    - simpl; inv Ord.
      edestruct IHP; eauto.
      eexists; rewrite stmt_call_eval_cons; eauto.
      apply ident_eqb_neq in E; auto.
  Qed.

 Lemma reset_spec:
    forall P me b bl P',
      Ordered_blocks P ->
      find_block b P = Some (bl, P') ->
      exists me',
        stmt_call_eval (translate P) me b reset [] me' []
        /\ initial_state P b me'
        /\ (state_closed P b me -> state_closed P b me').
  Proof.
    intros.
    edestruct reset_exists; eauto.
    eexists; split; eauto.
    eapply call_reset_initial_state; eauto.
  Qed.

  (** Step correctness *)

  Lemma eq_if_present_value_to_option:
    forall v,
      eq_if_present v (value_to_option v).
  Proof.
    destruct v; simpl; auto.
  Qed.

  Corollary eq_if_present_value_to_option_Forall2:
    forall vs,
      Forall2 eq_if_present vs (map value_to_option vs).
  Proof.
    induction vs; constructor; auto.
    apply eq_if_present_value_to_option.
  Qed.

  Lemma value_to_option_updates:
    forall R ve x xs v vs,
      In x xs ->
      Forall2 (sem_var_instant R) xs vs ->
      sem_var_instant R x v ->
      Env.find x (Env.updates xs (map value_to_option vs) ve) = value_to_option v.
  Proof.
    induction xs as [|x']; try now inversion 1.
    intros * Hin Hvar Hxsem.
    apply Forall2_left_cons in Hvar as (v' & vs' & Hyss & Hvs & ?); subst.
    destruct (ident_eq_dec x x') as [Heq|Hneq]; simpl.
    + subst.
      assert (v' = v) by (eapply sem_var_instant_det; eauto); subst.
      destruct v; simpl.
      * apply Env.find_gurs.
      * apply Env.find_guss.
    + inv Hin; try congruence.
      rewrite Env.find_guso; simpl; auto.
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
      subst. destruct ov; try contradiction.
      now simpl in Heqp; subst; rewrite Env.find_gsss_opt.
    + pose proof (Forall2_length _ _ _ Hvar) as Hlenyss.
      pose proof (Forall2_length _ _ _ Hovals) as Hlenovals.
      destruct vs; try discriminate.
      destruct ovs; try discriminate.
      rewrite Env.find_gsso_opt; auto.
      inv Hin. now contradiction Hneq.
      inv Hvar; inv Hovals; eauto.
  Qed.

  Definition correct_block (P: SB.Syn.program) (b: ident) : Prop :=
    forall S xs ys S' me ins,
      sem_block P b S xs ys S' ->
      Forall2 eq_if_present xs ins ->
      Exists (fun v => v <> absent) xs ->
      me ≋ S ->
      exists me',
        stmt_call_eval (translate P) me b step ins me' (map value_to_option ys)
        /\ me' ≋ S'.
        (* /\ Forall2 eq_if_present ys outs. *)

  Definition correct_program (P: SB.Syn.program) : Prop :=
    forall b, correct_block P b.

  Lemma noops_exp_exp_eval:
    forall isub R inputs mems me ve vars e v xck bck lck,
      Forall (clock_match_instant true R) vars ->
      equiv_env (fun x => CE.IsF.Is_free_in_exp x e) R inputs mems me ve ->
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
      intros v nck ck lck Hcm EqEnv Hnoo Hwc Hinst Hbck He Hlck Hmems; eauto.
    - (* Variables always evaluate (even if it is to None) *)
      destruct (PS.mem i mems) eqn:Himems; eauto.
      rewrite PS.mem_spec in Himems.
      apply Hmems in Himems.
      apply not_None_is_Some in Himems as (v' & Hv'); eauto.
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
        destruct (isub i1); try discriminate.
        inv Hwc. inv Hinst. inv Hlck.
        * (* Con lck i0 b0 = false because lck = false,
             the goal follows form the induction hypothesis. *)
          now inv He; eauto.
        * (* Con lck i0 b0 = false but its clock lck = true.
             The sampled expression e must thus be present, in which
             case we know that the translation calculates the same value. *)
          inv He; try match goal with
                        H:sem_exp_instant _ _ e (present _) |- _ =>
                        eapply exp_correct with (inputs := inputs) in H; eauto end.
          (* an absent value would contradict the fact that clock lck = true *)
          match goal with Hle:sem_exp_instant _ _ e absent,
                              Hck:sem_clock_instant _ _ lck true |- _ =>
            apply clock_match_instant_exp_contradiction with (1:=Hcm) (3:=Hle) in Hck; auto
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

  Lemma EqApp_check_args_translate_arg:
    forall P R inputs mems clkvars me ve icks s ys ck rst f es ess,
      (forall x ck, In (x, ck) icks -> ~ PS.In x mems -> Env.find x clkvars = Some ck) ->
      Forall (clock_match_instant true R) icks ->
      equiv_env (fun x => CE.IsF.Is_free_in_aexps x ck es) R inputs mems me ve ->
      (forall x, PS.In x mems -> find_val x me <> None) ->
      wc_equation P icks (EqCall s ys ck rst f es) ->
      normal_args_eq P (EqCall s ys ck rst f es) ->
      sem_exps_instant true R es ess ->
      sem_clock_instant true R ck true ->
      exists vos,
        Forall2 eq_if_present ess vos
        /\ Forall2 (exp_eval me ve) (map (translate_arg mems clkvars ck) es) vos.
  Proof.
    intros * Hcvars Hcm EqEnv Himems Hwc Hnorm Hles Hcksem.
    apply Forall2_Forall2_exists, Forall2_map_2, Forall2_swap_args.
    inversion_clear Hwc as [| | |???????? Hfind (isub & osub & Hwci & Hwco)].
    inversion_clear Hnorm as [| | |???????? Hfind' Hnorm'].
    rewrite Hfind in Hfind'; inv Hfind'.
    rewrite Forall2_map_1, Forall2_swap_args in Hnorm'.
    apply Forall2_trans_ex with (1:=Hnorm'), Forall2_same in Hwci.
    clear Hwco Hfind Hnorm'.
    apply Forall2_impl_In with (2:=Hles).
    intros le v Hlein Hvin Hsem.
    apply Forall_forall with (2:=Hlein) in Hwci
      as ((x, (xty, xck)) & Hin & Hnorm & Hsubv & (lck & WClck & Hinst)).
    unfold dck in *; simpl in *.
    assert (WClck':=WClck).
    assert (equiv_env (fun x => CE.IsF.Is_free_in_exp x le) R inputs mems me ve)
      by (weaken_equiv_env with constructor;
          apply Exists_exists; eauto).
    eapply clock_match_instant_exp in WClck'
      as [(Hsem' & Hcksem')|((c & Hsem') & Hcksem')]; eauto;
      apply sem_exp_instant_det with (1:=Hsem) in Hsem'; subst v.
    - eapply noops_exp_exp_eval in Hnorm as (v' & Hv'); eauto.
      simpl; exists v'; eauto.
      split; destruct le; eauto using exp_eval.
      destruct xck.
      + inv Hinst. now apply sem_clock_instant_det with (1:=Hcksem) in Hcksem'.
      + simpl in Hinst.
        destruct (instck ck isub xck) eqn:Hck; try discriminate.
        match goal with H:context [isub ?i] |- _ =>
                        destruct (isub i) eqn:Hisub; try discriminate end.
        injection Hinst; intro; subst lck.
        inversion_clear WClck as [|? ? ? Hicks| | |].
        simpl in Hv'; destruct (PS.mem i mems) eqn: E.
        * unfold translate_arg; simpl; rewrite E; simpl; auto.
        *{ apply Hcvars in Hicks.
           - unfold translate_arg; simpl; rewrite Hicks, E; simpl.
             now rewrite instck_subclock_not_clock_eq with (1:=Hck).
           - apply PSE.MP.Dec.F.not_mem_iff; auto.
         }
    - exists (Some c); simpl; split; eauto using arg_correct, exp_correct.
  Qed.

  Lemma equation_cons_correct:
    forall eq eqs P R S I S' me ve inputs mems icks clkvars,
      correct_program P ->
      sem_equation P true R S I S' eq ->
      wc_equation P icks eq ->
      normal_args_eq P eq ->
      Ordered_blocks P ->
      Is_well_sch inputs mems (eq :: eqs) ->
      NoDup (inputs ++ variables (eq :: eqs)) ->
      Step_with_reset_spec (eq :: eqs) ->
      (forall s b Ss, In (s, b) (resets_of (eq :: eqs)) -> find_inst s S = Some Ss -> state_closed P b Ss) ->
      transient_states_closed P (resets_of (eq :: eqs)) I ->
      Memory_Corres_eqs eqs S I S' me ->
      equiv_env (fun x => Is_free_in_eq x eq) R inputs mems me ve ->
      Forall (clock_match_instant true R) icks ->
      (forall x ck, In (x, ck) icks -> ~ PS.In x mems -> Env.find x clkvars = Some ck) ->
      (forall x, PS.In x mems -> find_val x me <> None) ->
      (forall x, ~ In x inputs -> ~ Is_defined_in x eqs -> Env.find x ve = None) ->
      exists me' ve',
        stmt_eval (translate P) me ve (translate_eqn mems clkvars eq) (me', ve')
        /\ Memory_Corres_eqs (eq :: eqs) S I S' me'
        /\ forall x v,
            Is_variable_in_eq x eq ->
            sem_var_instant R x v ->
            Env.find x ve' = value_to_option v.
  Proof.
    intros * IH Sem Hwc Hnormal Ord Wsch Vars StepReset
           Closed TransClosed Corres Equiv Hcm Hcvars Hmems Hve;
      inversion Sem as [????????? Hexp Hvar|
                        ??????????? Hvar Hexp|
                        ???????????? Init|
                        ??????????????? Hexps Hck Find_S Find_I Hblock Hvars];
      subst; simpl.

    - inv Hexp; exists me; eexists; split;
        try solve [eapply (stmt_eval_Control_absent' inputs); eauto; auto].
      + eapply (stmt_eval_Control_present' inputs); eauto; auto.
        eapply (cexp_correct inputs); eauto.
      + split.
        * apply Memory_Corres_eqs_Def; auto.
        * inversion_clear 1; intros Hvar'.
          eapply sem_var_instant_det in Hvar; eauto.
          inv Hvar; apply Env.gss.
      + split.
        * apply Memory_Corres_eqs_Def; auto.
        * inversion_clear 1; intros Hvar'.
          eapply sem_var_instant_det in Hvar; eauto.
          unfold variables in Vars.
          subst; simpl in *; apply NoDup_app_cons in Vars as (Hnin & ?).
          inv Wsch.
          apply Hve; auto using Is_defined_in_eq.
          intro; apply Hnin, in_app; auto.

    - inv Hexp; eexists; exists ve; split;
        try solve [eapply (stmt_eval_Control_absent' inputs); eauto; auto].
      + eapply (stmt_eval_Control_present' inputs);
          eauto using stmt_eval, (exp_correct inputs); auto.
      + split; try inversion 1.
        apply Memory_Corres_eqs_Next_present; auto.
      + split; try inversion 1.
        apply Memory_Corres_eqs_Next_absent; auto; congruence.

    - destruct r.
      + pose proof Init.
        inversion_clear Init as [????? Find Rst].
        edestruct reset_spec as (me' &?&?& SpecInit); eauto.
        do 2 eexists; split.
        * eapply (stmt_eval_Control_present' inputs); eauto; auto.
        *{ split; try inversion 1.
           eapply Memory_Corres_eqs_Reset_present; eauto.
           - eapply initial_state_det; eauto.
             + apply SpecInit.
               destruct (find_inst s me) eqn: E.
               * assert (state_corres s  S me) as Scorres.
                 { apply Corres; split.
                   - eapply Reset_not_Step_in; eauto.
                   - eapply Reset_not_Reset_in; eauto.
                 }
                 unfold state_corres in Scorres.
                 rewrite E in Scorres.
                 apply orel_find_inst_Some in Scorres as (?&<-&?).
                 eapply Closed; simpl; eauto.
               * eapply state_closed_empty; eauto.
             + inv TransClosed; auto.
           - eapply Reset_not_Step_in; eauto.
         }
      + exists me, ve; split; try eapply (stmt_eval_Control_absent' inputs); eauto; auto.
        split; try inversion 1.
        apply orel_find_inst_Some in Init as (?&?&?).
        eapply Memory_Corres_eqs_Reset_absent; try symmetry; eauto.
        eapply Reset_not_Reset_in; eauto.

    - pose proof Wsch as Wsch'.
      apply Step_not_Step_Reset_in in Wsch; auto.
      destruct (clock_of_instant xs) eqn: E.
      + assert (Exists (fun v => v <> absent) xs) by (apply clock_of_instant_true; auto).
        assert (exists vos,
                   Forall2 eq_if_present xs vos
                   /\ Forall2 (exp_eval me ve)
                             (map (translate_arg mems clkvars ck) es) vos)
            as (ivals & Hivals & Hievals)
              by (eapply EqApp_check_args_translate_arg with (inputs := inputs); eauto).
        unfold correct_program, correct_block in IH.
        eapply IH in Hblock as (me' &?&?); eauto.
        *{ do 2 eexists; split.
           - eapply (stmt_eval_Control_present' inputs); eauto; auto.
           - split.
             + eapply Memory_Corres_eqs_Call_present; eauto.
             + inversion_clear 1; intros Hvar.
               eapply value_to_option_updates; eauto.
         }
        *{ destruct rst; apply Corres in Wsch.
           - unfold transient_state_corres in Wsch; rewrite Find_I in Wsch.
             symmetry in Wsch; apply orel_find_inst_Some in Wsch as (?&?& ->); auto.
           - unfold state_corres in Wsch; rewrite Find_S in Wsch; auto.
             symmetry in Wsch; apply orel_find_inst_Some in Wsch as (?&?& ->); auto.
         }
      + assert (absent_list xs) by (apply clock_of_instant_false; auto).
        apply sem_block_absent in Hblock as (? & ?); auto.
        exists me, ve; split; try eapply (stmt_eval_Control_absent' inputs); eauto; auto.
        split; eauto using Memory_Corres_eqs_Call_absent.
        inversion_clear 1; intros Hvar.
        eapply Forall2_in_left in Hvars as (v' & Hin &?); eauto.
        eapply sem_var_instant_det in Hvar; eauto; subst v'.
        eapply Forall_forall in Hin; eauto.
        simpl in Hin; subst; simpl.
        unfold variables in Vars.
        simpl in *.
        inv Wsch'.
        apply Hve; auto using Is_defined_in_eq.
        eapply NoDup_swap, NoDup_app_In in Vars; eauto.
        intro; apply Vars, in_app; auto.
  Qed.

  Lemma stmt_eval_translate_cexp_menv_inv:
    forall prog me ve mems x me' ve' e,
      stmt_eval prog me ve (translate_cexp mems x e) (me', ve') ->
      me' = me.
  Proof.
    induction e; simpl; inversion_clear 1; auto; cases.
  Qed.

  Lemma stmt_eval_translate_cexp_venv_inv:
    forall prog me ve mems x me' ve' e,
      stmt_eval prog me ve (translate_cexp mems x e) (me', ve') ->
      exists c, ve' = Env.add x c ve.
  Proof.
    induction e; inversion_clear 1; cases; eauto.
  Qed.

  Lemma not_Is_defined_in_eq_stmt_eval_menv_inv:
    forall eq x P me ve mems clkvars me' ve',
      ~ Is_defined_in_eq x eq ->
      stmt_eval (translate P) me ve (translate_eqn mems clkvars eq) (me', ve') ->
      find_val x me' = find_val x me.
  Proof.
    destruct eq; simpl; intros ? ? ? ? ? ? ? ? NIsDef StEval;
      apply stmt_eval_Control_fwd in StEval;
      destruct StEval as [(?& StEval)|(?&?&?)]; try congruence.
    - now apply stmt_eval_translate_cexp_menv_inv in StEval as ->.
    - inv StEval.
      apply not_Is_defined_in_eq_EqNext in NIsDef.
      rewrite find_val_gso; auto.
    - inv StEval; apply find_val_add_inst.
    - inv StEval; apply find_val_add_inst.
  Qed.

  Corollary not_Is_defined_in_stmt_eval_menv_inv:
    forall eqs x P me ve mems clkvars me' ve',
      ~ Is_defined_in x eqs ->
      stmt_eval (translate P) me ve (translate_eqns mems clkvars eqs) (me', ve') ->
      find_val x me' = find_val x me.
  Proof.
    unfold translate_eqns.
    induction eqs as [|eq]; simpl; intros ? ? ? ? ? ? ? ? NIsDef StEval.
    - now inv StEval.
    - apply stmt_eval_fold_left_shift in StEval as (me'' & ve'' &?& Hcomp);
        rewrite stmt_eval_eq_Comp_Skip2 in Hcomp.
      apply not_Is_defined_in_cons in NIsDef as (?& Spec).
      eapply IHeqs with (me' := me'') in Spec; eauto.
      rewrite <-Spec.
      eapply not_Is_defined_in_eq_stmt_eval_menv_inv; eauto.
  Qed.

  Lemma not_Is_defined_in_eq_stmt_eval_venv_inv:
    forall eq x P me ve mems clkvars me' ve',
      ~ Is_defined_in_eq x eq ->
      stmt_eval (translate P) me ve (translate_eqn mems clkvars eq) (me', ve') ->
      Env.find x ve' = Env.find x ve.
  Proof.
    intros * Hnd Heval.
    destruct eq; simpl in Heval;
      apply stmt_eval_Control_fwd in Heval;
      destruct Heval as [[Hipi Heval]|[Habs [Hmenv Henv]]];
      subst; auto.
    - apply stmt_eval_translate_cexp_venv_inv in Heval as (?&?); subst.
      apply not_Is_defined_in_eq_EqDef in Hnd.
      rewrite Env.gso; auto.
    - inv Heval; auto.
    - inv Heval.
      rewrite Env.updates_nil_l; auto.
    - inv Heval.
      apply Env.find_In_guso.
      intro; apply Hnd; constructor; auto.
  Qed.

  Corollary not_Is_defined_in_stmt_eval_venv_inv:
    forall eqs x P me ve mems clkvars me' ve',
      ~ Is_defined_in x eqs ->
      stmt_eval (translate P) me ve (translate_eqns mems clkvars eqs) (me', ve') ->
      Env.find x ve' = Env.find x ve.
  Proof.
    unfold translate_eqns.
    induction eqs as [|eq]; simpl; intros ? ? ? ? ? ? ? ? NIsDef StEval.
    - now inv StEval.
    - apply stmt_eval_fold_left_shift in StEval as (me'' & ve'' &?& Hcomp);
        rewrite stmt_eval_eq_Comp_Skip2 in Hcomp.
      apply not_Is_defined_in_cons in NIsDef as (?& Spec).
      eapply IHeqs with (ve' := ve'') in Spec; eauto.
      rewrite <-Spec.
      eapply not_Is_defined_in_eq_stmt_eval_venv_inv; eauto.
  Qed.

  Lemma value_corres_equal_memory:
    forall x S me,
      S ≋ me ->
      value_corres x S me.
  Proof.
    intros * E; unfold value_corres; now rewrite E.
  Qed.

  Lemma state_corres_equal_memory:
    forall s S me,
      S ≋ me ->
      state_corres s S me.
  Proof.
    intros * E; unfold state_corres; now rewrite E.
  Qed.

  Lemma Memory_Corres_eqs_empty_equal_memory:
    forall S I S' me,
      S ≋ me ->
      Memory_Corres_eqs [] S I S' me.
  Proof.
    split.
    - split; intros Last.
      + inv Last.
      + now apply value_corres_equal_memory.
    - split; [|split]; intros StpRst.
      + now apply state_corres_equal_memory.
      + destruct StpRst as (?& Rst); inv Rst.
      + inv StpRst.
  Qed.

  Lemma sem_equations_is_last_in:
    forall eqs P base R S I S' x v,
      Forall (sem_equation P base R S I S') eqs ->
      Is_last_in x eqs ->
      sem_var_instant R x (present v) ->
      find_val x S = Some v.
  Proof.
    induction eqs; inversion_clear 1 as [|?? Sem];
      inversion_clear 1 as [?? Last|]; eauto; intros.
    inv Last; inv Sem.
    cases; congruence.
  Qed.

  Lemma not_Is_variable_in_eq_stmt_eval_env_inv:
    forall prog x eq me ve mems clkvars me' ve',
      ~ Is_variable_in_eq x eq ->
      stmt_eval prog me ve (translate_eqn mems clkvars eq) (me', ve') ->
      Env.find x ve' = Env.find x ve.
  Proof.
    intros * Hnd Heval.
    destruct eq; simpl in Heval;
      apply stmt_eval_Control_fwd in Heval;
      destruct Heval as [[Hipi Heval]|[Habs [Hmenv Henv]]];
      subst; auto.
    - apply stmt_eval_translate_cexp_venv_inv in Heval as (?&?); subst.
      rewrite Env.gso; auto.
      intro; subst; apply Hnd; constructor.
    - inv Heval; auto.
    - inv Heval.
      rewrite Env.updates_nil_l; auto.
    - inv Heval.
      rewrite Env.find_In_guso; auto.
      intro; apply Hnd; constructor; auto.
  Qed.

  Lemma equations_app_correct:
    forall eqs' eqs P R S I S' me ve inputs mems clkvars icks,
      let alleqs := eqs ++ eqs' in
      correct_program P ->
      Forall (sem_equation P true R S I S') alleqs ->
      Forall (wc_equation P icks) alleqs ->
      Forall (normal_args_eq P) alleqs ->
      Forall (clock_match_instant true R) icks ->
      (forall x ck, In (x, ck) icks -> ~ PS.In x mems -> Env.find x clkvars = Some ck) ->
      (forall x, PS.In x mems -> find_val x me <> None) ->
      Ordered_blocks P ->
      Is_well_sch inputs mems alleqs ->
      NoDup (inputs ++ variables alleqs) ->
      Step_with_reset_spec alleqs ->
      (forall s b Ss, In (s, b) (resets_of alleqs) -> find_inst s S = Some Ss -> state_closed P b Ss) ->
      transient_states_closed P (resets_of alleqs) I ->
      (forall x, PS.In x mems -> Is_last_in x alleqs) ->
      (forall x, In x inputs -> ~ Is_defined_in x alleqs) ->
      (forall x c,
          In x inputs ->
          sem_var_instant R x (present c) ->
          Env.find x ve = Some c) ->
      (forall x, Env.find x ve <> None -> In x inputs) ->
      me ≋ S ->
      exists me' ve',
        stmt_eval (translate P) me ve (translate_eqns mems clkvars eqs') (me', ve')
        /\ Memory_Corres_eqs eqs' S I S' me'
        /\ forall x v,
            Is_variable_in x eqs' ->
            sem_var_instant R x v ->
            Env.find x ve' = value_to_option v.
  Proof.
    induction eqs' as [|eq]; simpl;
      intros ? ? ? ? ? ? ? ? ? ? ? ? ?
             Heqs Hwc Hnormal Hcm Hcvars Hmems Ord Wsch Vars StepReset
             Closed TransClosed SpecLast SpecInput EquivInput EquivInput' Corres.
    - exists me, ve. split; eauto using stmt_eval; split; auto.
      + now apply Memory_Corres_eqs_empty_equal_memory.
      + inversion 1.
    - pose proof Wsch as Wsch'; apply Is_well_sch_app in Wsch'.
      pose proof Vars as Vars'; rewrite variables_app in Vars'.
      rewrite NoDup_swap, Permutation.Permutation_app_comm in Vars';
        apply NoDup_app_weaken in Vars'.
      pose proof StepReset as StepReset'; apply Step_with_reset_spec_app in StepReset'.
      pose proof Heqs as Heqs'; apply Forall_app_weaken in Heqs'; inv Heqs'.
      pose proof Hwc as Hwc'; apply Forall_app_weaken in Hwc'; inv Hwc'.
      pose proof Hnormal as Hnormal'; apply Forall_app_weaken in Hnormal'; inv Hnormal'.
      rewrite List_shift_first in Wsch, Vars, StepReset, Heqs, SpecLast, SpecInput,
                                  Closed, TransClosed, Hwc, Hnormal.
      edestruct IHeqs' with (ve := ve) (me := me) as (me' & ve' &?&?&?); eauto.
      edestruct equation_cons_correct with (ve := ve') (me := me') as (me'' & ve'' &?&?&?);
        eauto using Is_well_sch.
      + intros; eapply Closed; eauto.
        rewrite <-List_shift_first, resets_of_app, in_app; auto.
      + unfold transient_states_closed in *.
        rewrite <-List_shift_first, resets_of_app, Forall_app in TransClosed; tauto.
      + intros x v Free Hvar.
        inversion_clear Wsch' as [|??? FreeSpec].
        apply FreeSpec in Free.
        cases_eqn E.
        * erewrite not_Is_defined_in_stmt_eval_menv_inv; eauto.
          rewrite Corres.
          destruct v; simpl; auto.
          eapply sem_equations_is_last_in in Heqs; eauto; rewrite Heqs; auto.
        * assert (~ Is_defined_in x eqs')
            by (intro; eapply SpecInput, Exists_app; eauto).
          erewrite not_Is_defined_in_stmt_eval_venv_inv; eauto.
          destruct v; simpl; auto.
          assert (Env.find x ve = Some c) as ->; auto.
        * destruct Free; auto; contradiction.
      + intros; eapply stmt_eval_find_val_mono; eauto.
      + intros * Hnin ?; erewrite not_Is_defined_in_stmt_eval_venv_inv; eauto.
        apply not_Some_is_None; intros * E.
        apply Hnin, EquivInput', not_None_is_Some; eauto.
      + exists me'', ve''; split; [|split]; auto.
        * unfold translate_eqns; simpl.
          rewrite stmt_eval_fold_left_shift; setoid_rewrite stmt_eval_eq_Comp_Skip2; eauto.
        * intros x v IsVar Hvar.
          destruct (Is_variable_in_eq_dec x eq) as [|Nvar]; auto.
          erewrite not_Is_variable_in_eq_stmt_eval_env_inv; eauto.
          inv IsVar; auto.
          contradiction.
  Qed.

  Corollary equations_correct:
    forall eqs P R S I S' me ve inputs mems clkvars icks,
      correct_program P ->
      Forall (sem_equation P true R S I S') eqs ->
      Forall (wc_equation P icks) eqs ->
      Forall (normal_args_eq P) eqs ->
      Forall (clock_match_instant true R) icks ->
      (forall x ck, In (x, ck) icks -> ~ PS.In x mems -> Env.find x clkvars = Some ck) ->
      (forall x, PS.In x mems -> find_val x me <> None) ->
      Ordered_blocks P ->
      (forall s b Ss, In (s, b) (resets_of eqs) -> find_inst s S = Some Ss -> state_closed P b Ss) ->
      transient_states_closed P (resets_of eqs) I ->
      Is_well_sch inputs mems eqs ->
      NoDup (inputs ++ variables eqs) ->
      Step_with_reset_spec eqs ->
      (forall x, PS.In x mems -> Is_last_in x eqs) ->
      (forall x, In x inputs -> ~ Is_defined_in x eqs) ->
      (forall x c,
          In x inputs ->
          sem_var_instant R x (present c) ->
          Env.find x ve = Some c) ->
      (forall x, Env.find x ve <> None -> In x inputs) ->
      me ≋ S ->
      exists me' ve',
        stmt_eval (translate P) me ve (translate_eqns mems clkvars eqs) (me', ve')
        /\ Memory_Corres_eqs eqs S I S' me'
        /\ forall x v,
            Is_variable_in x eqs ->
            sem_var_instant R x v ->
            Env.find x ve' = value_to_option v.
  Proof.
    intros; eapply equations_app_correct with (eqs := []); eauto.
  Qed.

  Lemma state_closed_insts_InMembers:
    forall P blocks S s Ss,
      state_closed_insts P blocks S ->
      find_inst s S = Some Ss ->
      InMembers s blocks.
  Proof.
    intros * Closed Sub; apply Closed in Sub as (?&?&?).
    eapply In_InMembers; eauto.
  Qed.

 Lemma Memory_Corres_eqs_equal_memory:
    forall P R eqs S I S' me lasts blocks,
      Memory_Corres_eqs eqs S I S' me ->
      Forall (sem_equation P true R S I S') eqs ->
      state_closed_lasts lasts S ->
      state_closed_insts P blocks S ->
      state_closed_lasts lasts S' ->
      state_closed_insts P blocks S' ->
      (forall x, In x lasts <-> Is_last_in x eqs) ->
      (forall s, InMembers s blocks -> exists k, Is_state_in s k eqs) ->
      (forall s, Reset_in s eqs -> Step_in s eqs) ->
      me ≋ S'.
  Proof.
    intros * (Lasts & Insts) Heqs LastClosed InstsClosed LastClosed' InstsClosed'
           SpecLast SpecInst WSCH.
    split.
    - intro x; destruct (Is_last_in_dec x eqs) as [Last|Nlast].
      + apply Lasts in Last; auto.
      + assert (find_val x S = None).
        { apply not_Some_is_None; intros * Find;
            apply Nlast, SpecLast, LastClosed.
          apply not_None_is_Some; eauto.
        }
        assert (find_val x S' = None) as E'.
        { apply not_Some_is_None; intros * Find;
            apply Nlast, SpecLast, LastClosed'.
          apply not_None_is_Some; eauto.
        }
        unfold value_corres, find_val in *.
        apply Lasts in Nlast.
        rewrite E'; rewrite <-Nlast; auto.
    - split.
      + setoid_rewrite Env.In_find; intro s.
        destruct (Step_in_dec s eqs) as [Step|Nstep].
        * apply Insts in Step.
          unfold state_corres, find_inst in Step.
          split; intros (?& Find); rewrite Find in Step.
          -- apply orel_find_inst_Some in Step as (?&?&?); eauto.
          -- symmetry in Step; apply orel_find_inst_Some in Step as (?&?&?); eauto.
        * destruct (Reset_in_dec s eqs) as [Rst|Nrst].
          -- apply WSCH in Rst; contradiction.
          -- assert (~ exists k, Is_state_in s k eqs) as Nstate.
             { intros (?& State).
               apply Exists_exists in State as (?&?& State).
               inv State.
               - apply Nrst, Exists_exists; eauto using Is_state_in_eq.
               - apply Nstep, Exists_exists; eauto using Is_state_in_eq.
             }
             assert (state_corres s S me) as Corres by (apply Insts; auto).
             assert (find_inst s S = None).
             { apply not_Some_is_None; intros * Find;
                 apply Nstate, SpecInst.
               eapply state_closed_insts_InMembers in InstsClosed; eauto.
             }
             assert (find_inst s S' = None) as E'.
             { apply not_Some_is_None; intros * Find;
                 apply Nstate, SpecInst.
               eapply state_closed_insts_InMembers in InstsClosed'; eauto.
             }
             assert (find_inst s me = None) as E.
             { apply not_Some_is_None; intros * Find.
               unfold state_corres in Corres; rewrite Find in Corres.
               apply orel_find_inst_Some in Corres as (?&?&?).
               congruence.
             }
             setoid_rewrite E'; setoid_rewrite E; reflexivity.
      + setoid_rewrite Env.Props.P.F.find_mapsto_iff.
        intros s me_s Ss' Find Find'.
        destruct (Step_in_dec s eqs) as [Step|Nstep].
        * apply Insts in Step.
          unfold state_corres, find_inst in Step.
          rewrite Find, Find' in Step.
          inv Step; symmetry; auto.
        * destruct (Reset_in_dec s eqs) as [Rst|Nrst].
          -- apply WSCH in Rst; contradiction.
          -- assert (~ (Step_in s eqs \/ Reset_in s eqs)) as NstpRst by tauto.
             assert (~ exists k, Is_state_in s k eqs) as Nstate.
             { intros (?& State).
               apply Exists_exists in State as (?&?& State).
               inv State.
               - apply Nrst, Exists_exists; eauto using Is_state_in_eq.
               - apply Nstep, Exists_exists; eauto using Is_state_in_eq.
             }
             exfalso.
             apply Nstate, SpecInst.
             eapply state_closed_insts_InMembers in InstsClosed'; eauto.
  Qed.

  Theorem correctness:
    forall P b,
      Well_defined P ->
      wc_program P ->
      correct_block P b.
  Proof.
    induction P as [|block]; unfold correct_block;
      intros b (Ord & WSCH & NormalArgs) WC ?????? Sem Eqs Spec E;
      pose proof Sem;
      inversion_clear Sem as [????????? Find ? Outs Hscv Heqs Closed TransClosed Closed'];
      try now inv Find.
    pose proof Find as Find'.
    simpl in Find.
    pose proof Ord.
    inv Ord; inv WSCH; destruct NormalArgs as (Hnormal&?);
      inversion_clear WC as [|??? WCb].
    assert (Well_defined P) by (split; auto).
    assert (correct_program P) by (unfold correct_program; intros; auto).
    destruct WCb as (?&?&?& WCeqs); rewrite 2 idck_app, <-2 app_assoc in WCeqs.
    destruct (ident_eqb (b_name block) b) eqn: Eq.
    - inv Find.
      assert (clock_of_instant xs = true) as Clock by now apply clock_of_instant_true.
      rewrite Clock in Heqs.
      assert (~ Is_block_in (b_name bl) (b_eqs bl))
        by (eapply find_block_not_Is_block_in; eauto).
      apply normal_args_block_cons in Hnormal; auto.
      apply sem_equations_cons in Heqs; auto.
      edestruct equations_correct
        with (ve := Env.adds_opt (map fst (m_in (step_method bl))) ins vempty)
             (clkvars := Env.adds_with snd bl.(b_out)
                           (Env.adds_with snd bl.(b_vars)
                             (Env.from_list_with snd bl.(b_in))))
        as (me' & ve' &?&?& Equiv); eauto.
      + apply Forall_forall.
        intros (x, ck) Hxin.
        apply in_app in Hxin as [Hxin|Hxin].
        *{ eapply sem_clocked_vars_instant_clock_match_instant in Hscv; eauto.
           - eapply Forall_forall in Hscv; eauto.
             rewrite <-Clock; auto.
           - rewrite map_fst_idck; eauto.
         }
        *{ eapply clock_match_instant_eqs with (P := P') (eqs := b_eqs bl); eauto.
           - apply fst_NoDupMembers; rewrite 3 map_app, 4 map_fst_idck.
             apply b_nodup.
           - rewrite b_defined, <-b_vars_out_in_eqs, <-b_lasts_in_eqs,
             <-app_assoc, 2 map_app, 3 map_fst_idck; auto.
         }
      + intros * Hin Hnin.
        rewrite ps_from_list_In in Hnin.
        pose proof (b_nodup bl) as Nodup.
        rewrite 3 in_app in Hin; destruct Hin as [Hin|[Hin|[Hin|Hin]]];
          apply In_idck_exists in Hin as (?&?).
        *{ apply (NoDup_app_In x) in Nodup.
           - unfold Env.from_list_with.
             rewrite 2 Env.gsso_with.
             + erewrite Env.In_find_adds_with; eauto; simpl; auto.
               do 2 eapply NoDupMembers_app_l; rewrite <-app_assoc; apply b_nodup_vars.
             + intros Hin; apply Nodup, in_app; left; apply fst_InMembers; auto.
             + intros Hin; apply Nodup; rewrite 2 in_app; right; left; apply fst_InMembers; auto.
           - apply in_map_iff; eexists; (intuition eauto); auto.
         }
        *{ rewrite Permutation.Permutation_app_comm in Nodup.
           apply NoDup_app_weaken, (NoDup_app_In x) in Nodup.
           - rewrite Env.gsso_with.
             + erewrite Env.In_find_adds_with; eauto; simpl; auto.
               eapply NoDupMembers_app_l; eapply NoDupMembers_app_r; apply b_nodup_vars.
             + intros Hin; apply Nodup, in_app; left; apply fst_InMembers; auto.
           - apply in_map_iff; eexists; (intuition eauto); auto.
         }
        * erewrite Env.In_find_adds_with; eauto; simpl; auto.
          do 2 eapply NoDupMembers_app_r; apply b_nodup_vars.
        * exfalso; apply Hnin, in_map_iff; eexists; (intuition eauto); auto.
      + setoid_rewrite ps_from_list_In; intros.
        rewrite E; eapply sem_block_find_val; eauto.
      + inversion_clear Closed as [????? Find ? Insts]; rewrite Find in Find'; inv Find'.
        intros ? b' ? Hin Sub.
        apply Insts in Sub as (b'' &?&?).
        apply b_reset_incl in Hin.
        rewrite <-b_blocks_calls_of in Hin.
        assert (b' = b'') as ->; auto.
        eapply NoDupMembers_det in Hin; eauto.
        apply b_nodup_blocks.
      + eapply Forall_incl.
        * eapply transient_states_closed_In; eauto.
          intros (? & ?); now setoid_rewrite b_blocks_calls_of.
        * apply b_reset_incl.
      + rewrite <-b_vars_out_in_eqs, <-2 map_app, <-fst_NoDupMembers.
        apply b_nodup_vars.
      + eapply Is_well_sch_Step_with_reset_spec; eauto.
        apply b_reset_in.
      + intros; apply lasts_of_In, ps_from_list_In; auto.
        rewrite <-b_lasts_in_eqs; auto.
      + intros; apply b_ins_not_def, fst_InMembers; auto.
      + simpl; intros; eapply eq_if_present_adds_opt; eauto; rewrite map_fst_idty; auto.
      + simpl; rewrite map_fst_idty; intros * Find.
        apply not_None_is_Some in Find as (?& Find); apply Env.find_adds_opt_spec_Some in Find.
        * rewrite Env.gempty in Find; destruct Find as [Hin|]; try discriminate.
          eapply in_combine_l; eauto.
        * transitivity (length xs); eapply Forall2_length; eauto.
      + exists me'; split.
        *{ apply find_block_translate in Find' as (?&?&?&?&?); subst.
           econstructor; eauto.
           - apply exists_step_method.
           - simpl; transitivity (length xs).
             + symmetry; eapply Forall2_length; eauto.
             + rewrite length_idty, <-map_length with (f := fst);
                 symmetry; eapply Forall2_length; eauto.
           - simpl; eauto.
           - simpl; rewrite map_fst_idty.
             clear - Outs Equiv.
             rewrite Forall2_map_2.
             eapply Forall2_impl_In; eauto; intros.
             apply Equiv; auto.
             apply Is_variable_in_variables.
             rewrite <-b_vars_out_in_eqs, in_app; auto.
         }
         *{ inv Closed; inv Closed';
            repeat match goal with
                     H: find_block ?b ?P = _, H': find_block ?b ?P = _ |- _ =>
                     rewrite H in H'; inv H'
                   end.
            eapply Memory_Corres_eqs_equal_memory; eauto.
            - intro; now rewrite b_lasts_in_eqs, lasts_of_In.
            - setoid_rewrite b_blocks_calls_of; apply calls_of_Is_state_in.
            - intros * Rst; apply b_no_single_reset, Step_with_reset_in_Step_in in Rst; auto.
          }
    - apply sem_equations_cons in Heqs; auto.
      + apply ident_eqb_neq in Eq.
        apply state_closed_other in Closed;
          apply state_closed_other in Closed'; auto.
        edestruct IHP as (me' &?&?); eauto using sem_block.
        exists me'; split; auto.
        apply stmt_call_eval_cons; auto.
      + eapply find_block_later_not_Is_block_in; eauto.
  Qed.

  Corollary correctness_loop_call:
    forall P f xss yss ins S0,
      Well_defined P ->
      wc_program P ->
      loop P f xss yss S0 0 ->
      (forall n, Forall2 eq_if_present (xss n) (ins n)) ->
      (forall n, Exists (fun v => v <> absent) (xss n)) ->
      exists me0,
        stmt_call_eval (translate P) mempty f reset [] me0 []
        /\ loop_call (translate P) f step ins (fun n => map value_to_option (yss n)) 0 me0
        /\ me0 ≋ S0.
  Proof.
    intros * Wdef WC Loop Spec Clock.
    pose proof Loop as Loop'; inversion_clear Loop' as [???????? Sem].
    inv Sem.
    assert (Ordered_blocks P) as Ord by apply Wdef.
    eapply reset_spec with (me := mempty) in Ord as (me' &?&?& Closed); eauto.
    assert (me' ≋ S0) as Eq
        by (eapply initial_state_det; eauto;
            eapply Closed, state_closed_empty; eauto).
    exists me'; split; [|split]; auto.
    clear - Loop Wdef WC Eq Spec Clock.
    revert Loop Eq; revert me' S0.
    generalize 0.
    cofix COFIX; intros.
    inversion_clear Loop as [???????? Sem].
    eapply correctness in Sem as (?&?&?); eauto.
    econstructor; eauto.
  Qed.

End CORRECTNESS.

Module CorrectnessFun
       (Ids    : IDS)
       (Op     : OPERATORS)
       (OpAux  : OPERATORS_AUX      Op)
       (Str    : STREAM             Op OpAux)
       (CE     : COREEXPR       Ids Op OpAux Str)
       (SB     : SYBLOC         Ids Op OpAux Str CE)
       (Obc    : OBC            Ids Op OpAux)
       (Trans  : TRANSLATION    Ids Op OpAux CE.Syn SB.Syn Obc.Syn)
       (Corres : SBMEMORYCORRES Ids Op       CE.Syn SB.Syn SB.Last)
<: CORRECTNESS Ids Op OpAux Str CE SB Obc Trans Corres.
  Include CORRECTNESS Ids Op OpAux Str CE SB Obc Trans Corres.
End CorrectnessFun.
