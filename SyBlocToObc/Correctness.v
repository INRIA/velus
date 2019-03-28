Require Import Velus.SyBloc.
Require Import Velus.Obc.

Require Import Velus.SyBlocToObc.Translation.
Require Import Velus.SyBlocToObc.SBMemoryCorres.

Require Import Velus.RMemory.
Require Import Velus.Common.

Require Import List.
Import List.ListNotations.
Require Import Setoid.

Open Scope nat.
Open Scope list.

Module Type CORRECTNESS
       (Import Ids    : IDS)
       (Import Op     : OPERATORS)
       (Import OpAux  : OPERATORS_AUX      Op)
       (Import Clks   : CLOCKS         Ids)
       (Import Str    : STREAM             Op OpAux)
       (Import CE     : COREEXPR       Ids Op OpAux Clks Str)
       (Import SB     : SYBLOC         Ids Op OpAux Clks Str CE)
       (Import Obc    : OBC            Ids Op OpAux)
       (Import Trans  : TRANSLATION    Ids Op OpAux Clks CE.Syn SB.Syn Obc.Syn)
       (Import Corres : SBMEMORYCORRES Ids Op       Clks CE.Syn SB.Syn SB.Last).

  Definition equiv_env
             (in_domain: ident -> Prop) (R: env) (mems: PS.t) (me: menv) (ve: venv) : Prop :=
    forall x c,
      in_domain x ->
      sem_var_instant R x (present c) ->
      if PS.mem x mems
      then find_val x me = Some c
      else Env.find x ve = Some c.

  Lemma equiv_env_map:
    forall (in_dom1 in_dom2: ident -> Prop) R mems me ve,
      (forall x, in_dom2 x -> in_dom1 x) ->
      equiv_env in_dom1 R mems me ve ->
      equiv_env in_dom2 R mems me ve.
  Proof.
    unfold equiv_env; intros ** Eq ????; apply Eq; auto.
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
    weaken_equiv_env with constructor (now auto).

  Hint Extern 4 (equiv_env _ _ _ _ _) => weaken_equiv_env.

  Ltac split_env_assumption :=
    match goal with
    | Equiv: context Is_free_in_lexp [_],
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
        exp_eval me ve (tovar mems (x, bool_type)) v ->
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
        exp_eval me ve (tovar mems (x, bool_type)) v ->
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
    intros ** StEval.
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

  Section Expr.

    Variable (mems: PS.t).

    Variable (R: env).
    Variable (me: menv) (ve: venv).

    Lemma lexp_correct:
      forall e c,
        sem_lexp_instant true R e (present c) ->
        equiv_env (fun x => Is_free_in_lexp x e) R mems me ve ->
        exp_eval me ve (translate_lexp mems e) c.
    Proof.
      induction e; inversion_clear 1; simpl; intros; auto.
      - constructor; congruence.
      - split_env_assumption; cases; eauto using exp_eval.
      - econstructor; eauto; now rewrite typeof_correct.
      - econstructor; eauto; now rewrite 2 typeof_correct.
    Qed.
    Hint Resolve lexp_correct.

    Corollary lexps_correct:
      forall es cs,
        sem_lexps_instant true R es (map present cs) ->
        equiv_env (fun x => Exists (Is_free_in_lexp x) es) R mems me ve ->
        Forall2 (exp_eval me ve) (map (translate_lexp mems) es) cs.
    Proof.
      setoid_rewrite Forall2_map_1; setoid_rewrite Forall2_map_2;
        intros; eapply Forall2_impl_In; eauto.
      intros; apply lexp_correct; auto.
      weaken_equiv_env with (setoid_rewrite Exists_exists; eauto).
    Qed.
    Hint Resolve lexps_correct.

    Lemma cexp_correct:
      forall e c prog x,
        sem_cexp_instant true R e (present c) ->
        equiv_env (fun x => Is_free_in_cexp x e) R mems me ve ->
        stmt_eval prog me ve (translate_cexp mems x e) (me, Env.add x c ve).
    Proof.
      induction e;
        inversion 1 as [???? Hvar|???? Hvar| | | |];
        subst; simpl; intros; eauto using stmt_eval.
      - split_env_assumption.
        econstructor; eauto.
        + unfold bool_var, tovar; cases; eauto using exp_eval.
        + apply val_to_bool_true.
        + simpl; auto.
      - split_env_assumption.
        econstructor; eauto.
        + unfold bool_var, tovar; cases; eauto using exp_eval.
        + apply val_to_bool_false.
        + simpl; auto.
      - econstructor; eauto; cases.
    Qed.
    Hint Resolve cexp_correct.

  End Expr.

  Lemma clock_correct_true:
    forall base R mems me ve ck,
      equiv_env (fun x => Is_free_in_clock x ck) R mems me ve ->
      sem_clock_instant base R ck true ->
      Is_present_in mems me ve ck.
  Proof.
    intros until ve.
    induction ck; eauto.
    inversion_clear 2; subst.
    econstructor; eauto.
    unfold tovar; split_env_assumption.
    cases; eauto using exp_eval.
  Qed.

  Lemma clock_correct_false:
    forall R mems me ve ck,
      equiv_env (fun x => Is_free_in_clock x ck) R mems me ve ->
      sem_clock_instant true R ck false ->
      Is_absent_in mems me ve ck.
  Proof.
    intros until ve.
    induction ck as [|?? x]; [now inversion 2|].
    intro Henv.
    inversion_clear 1; auto.
    econstructor 2; eauto.
    - eapply clock_correct_true; eauto.
      weaken_equiv_env.
    - unfold tovar; split_env_assumption.
      cases; eauto using exp_eval.
  Qed.

  Corollary stmt_eval_Control_absent':
    forall R ck prog me ve mems s,
      equiv_env (fun x => Is_free_in_clock x ck) R mems me ve ->
      sem_clock_instant true R ck false ->
      stmt_eval prog me ve (Control mems ck s) (me, ve).
  Proof.
    intros; eapply stmt_eval_Control_absent, clock_correct_false; eauto.
  Qed.

  Corollary stmt_eval_Control_present':
    forall base R ck prog me ve mems s me' ve',
      equiv_env (fun x : ident => Is_free_in_clock x ck) R mems me ve ->
      sem_clock_instant base R ck true ->
      stmt_eval prog me ve s (me', ve') ->
      stmt_eval prog me ve (Control mems ck s) (me', ve').
  Proof.
    intros; apply stmt_eval_Control_present; auto.
    eapply clock_correct_true; eauto.
  Qed.

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
    intros ** Notin; rewrite add_mems_cons.
    revert me; induction xs as [|(?,())]; intros.
    - now rewrite add_mems_nil, find_val_gss.
    - apply NotInMembers_cons in Notin as ().
      rewrite add_mems_cons, add_val_comm; auto.
  Qed.

  Lemma find_val_add_mems_in:
    forall x c ck xs me,
      NoDupMembers xs ->
      In (x, (c, ck)) xs ->
      find_val x (add_mems xs me) = Some (sem_const c).
  Proof.
    intros ** Nodup Hin.
    revert me; induction xs as [|(?,())]; intros.
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
    intros ** Find; split; [intros ** Nodup Hin|intros ** Hin].
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
        apply NotInMembers_cons in Hin as ().
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
      eapply stmt_eval_det with (2 := StEval') in StEval as (); subst.
      split; auto.
    - intros (); eauto using stmt_eval.
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
    intros ** Closed ? Find.
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
    inversion_clear 1 as [????? Find]; intros ** Find';
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
    - intros ** StEval Lasts ??? Hin.
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
    - intros ** StEval Lasts ? Hin.
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
    - intros ** StEval.
      apply stmt_eval_fold_left_lift in StEval as (?&?& StEval & StEvals).
      eapply IHblocks in StEvals; eauto.
      rewrite stmt_eval_eq_Comp_Skip1 in StEval; inv StEval.
      apply Env.adds_nil_l.
  Qed.

  Lemma call_reset_inv:
    forall b P bl P' me me' rvs,
      find_block b P = Some (bl, P') ->
      stmt_call_eval (translate P) me b reset [] me' rvs ->
      stmt_eval (translate P') me vempty (translate_reset bl) (me', vempty)
      /\ rvs = [].
  Proof.
    intros ** Find Rst.
    apply find_block_translate in Find as (?&?& Find &?&?); subst.
    inversion_clear Rst as [??????????? Find' Find_m StEval Ret].
    rewrite Find in Find'; inv Find'.
    rewrite exists_reset_method in Find_m; inv Find_m; simpl in *.
    inv Ret; intuition.
    rewrite Env.adds_nil_nil in StEval.
    apply translate_reset_comp in StEval as (?& Insts).
    rewrite translate_reset_comp; intuition.
    assert (ve' = vempty) as <- by (eapply reset_insts_same_venv; eauto); auto.
  Qed.

  Lemma call_reset_reset_lasts:
    forall me' P me b bl P',
      find_block b P = Some (bl, P') ->
      stmt_call_eval (translate P) me b reset [] me' [] ->
      reset_lasts bl me'.
  Proof.
    intros ** Find Spec Rst ??? Hin.
    eapply call_reset_inv in Rst as (Rst); eauto;
      apply translate_reset_comp in Rst as ().
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
    intros ** Find Spec Rst ?? Hin.
    eapply call_reset_inv in Rst as (Rst); eauto;
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
    - intros ** StEval Notin; apply NotInMembers_cons in Notin as (); simpl in *.
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
        /\ sub_inst x me' me_x.
  Proof.
    unfold reset_insts.
    intro; pose proof (b_nodup_blocks bl) as Nodup.
    induction bl.(b_blocks) as [|(x', b'')]; simpl; try now inversion 2.
    intros ** Find StEval Hin Find'; inversion_clear Nodup as [|??? Notin].
    apply stmt_eval_fold_left_lift in StEval as (me_x' &?& StEval & StEvals).
    destruct Hin as [E|].
    - inv E.
      unfold sub_inst.
      erewrite reset_insts_not_InMembers with (me' := me'); eauto.
      rewrite stmt_eval_eq_Comp_Skip1 in StEval; inv StEval.
      match goal with H: Forall2 _ _ _ |- _ => inv H end.
      rewrite find_inst_gss.
      assert (rvs = []) as <-; eauto.
      apply not_None_is_Some in Find' as (()).
      eapply call_reset_inv; eauto.
    - assert (find_inst x me = find_inst x me_x') as ->; eauto.
      rewrite stmt_eval_eq_Comp_Skip1 in StEval; inv StEval.
      rewrite find_inst_gso; auto.
      intro; subst; eapply Notin, In_InMembers; eauto.
  Qed.

  Lemma sub_inst_reset_insts_inv:
    forall blocks prog me ve me' ve' x me_x,
      stmt_eval prog me ve (reset_insts blocks) (me', ve') ->
      sub_inst x me' me_x ->
      InMembers x blocks
      \/ sub_inst x me me_x.
  Proof.
    unfold reset_insts.
    induction blocks as [|(x', b)]; simpl.
    - inversion_clear 1; auto.
    - intros ** StEval Sub.
      apply stmt_eval_fold_left_lift in StEval as (me_x' &?& StEval & StEvals).
      eapply IHblocks in StEvals as [|Sub']; eauto.
      rewrite stmt_eval_eq_Comp_Skip1 in StEval.
      inv StEval.
      destruct (ident_eq_dec x x'); auto.
      unfold sub_inst in Sub'; rewrite find_inst_gso in Sub'; auto.
  Qed.

  Lemma call_reset_initial_state:
    forall me' P me b bl P',
      Ordered_blocks P ->
      find_block b P = Some (bl, P') ->
      stmt_call_eval (translate P) me b reset [] me' [] ->
      initial_state P b me' /\ (state_closed P b me -> state_closed P b me').
  Proof.
    induction me' as [? IH] using memory_ind';
      intros ** Ord Find Rst.
    pose proof Ord as Ord'.
    eapply Ordered_blocks_find_block in Ord'; eauto.
    split.
    - econstructor; eauto.
      + eapply call_reset_reset_lasts; eauto.
      + intros ** Hin.
        eapply call_reset_inv in Rst as (Rst); eauto;
          apply  translate_reset_comp in Rst as ().
        eapply Ordered_blocks_find_In_blocks in Ord as (?&?& Find'); eauto.
        pose proof Hin as Hin'.
        eapply reset_insts_in in Hin as (me_x & ? & ?); eauto.
        * exists me_x; split; auto.
          eapply IH; eauto.
        * apply not_None_is_Some; eauto.
    - inversion_clear 1 as [????? Find' ? Insts]; rewrite Find' in Find; inv Find.
      econstructor; eauto.
      + eapply call_reset_state_closed_lasts; eauto.
      + intros ** Sub.
        eapply call_reset_inv in Rst as (Rst); eauto;
          apply  translate_reset_comp in Rst as (?& Rst).
        pose proof Rst.
        eapply sub_inst_reset_insts_inv in Rst as [Hin|]; eauto.
        apply InMembers_In in Hin as (b' & Hin).
        eapply Ordered_blocks_find_In_blocks in Ord as (?&?& Find); eauto.
        pose proof Hin as Hin'.
        eapply reset_insts_in in Hin as (me_x & ? & Sub'); eauto.
        * eexists; split; eauto.
          unfold sub_inst in *; rewrite Sub' in Sub; inv Sub.
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
      intros ** IH Spec; eauto using stmt_eval.
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
    intros ** Ord Find.
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
        * simpl; rewrite Env.adds_nil_nil.
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

  Lemma equation_cons_correct:
    forall eq eqs P R S I S' me ve inputs mems,
      (forall b S xs ys S' me,
          sem_block P b S (map present xs) (map present ys) S' ->
          me ≋ S ->
          exists me',
            stmt_call_eval (translate P) me b step xs me' ys
            /\ me' ≋ S') ->
      sem_equation P true R S I S' eq ->
      Ordered_blocks P ->
      Is_well_sch inputs mems (eq :: eqs) ->
      NoDup (variables (eq :: eqs)) ->
      Step_with_reset_spec (eq :: eqs) ->
      (forall s b Ss, In (s, b) (resets_of (eq :: eqs)) -> sub_inst s S Ss -> state_closed P b Ss) ->
      transient_states_closed P (resets_of (eq :: eqs)) I ->
      Memory_Corres_eqs eqs S I S' me ->
      equiv_env (fun x => Is_free_in_eq x eq) R mems me ve ->
      exists me' ve',
        stmt_eval (translate P) me ve (translate_eqn mems eq) (me', ve')
        /\ Memory_Corres_eqs (eq :: eqs) S I S' me'
        /\ forall x c,
            Is_variable_in_eq x eq ->
            sem_var_instant R x (present c) ->
            Env.find x ve' = Some c.
  Proof.
    intros ** IH Sem Ord Wsch Vars StepReset Closed TransClosed Corres Equiv;
      inversion Sem as [????????? Hexp Hvar|
                        ??????????? Hvar Hexp|
                        ???????????? Init|
                        ??????????????? Hexps Find_S Find_I Hblock Hvars];
      subst; simpl.

    - inv Hexp; exists me; eexists; split;
        try solve [eapply stmt_eval_Control_absent'; eauto; auto].
      + eapply stmt_eval_Control_present'; eauto; auto.
        eapply cexp_correct; eauto.
      + split.
        * apply Memory_Corres_eqs_Def; auto.
        * inversion_clear 1; intros Hvar'.
          eapply sem_var_instant_det in Hvar; eauto.
          inv Hvar; apply Env.gss.
      + split.
        * apply Memory_Corres_eqs_Def; auto.
        * inversion_clear 1; intros Hvar'.
          eapply sem_var_instant_det in Hvar; eauto.
          discriminate.

    - inv Hexp; eexists; exists ve; split;
        try solve [eapply stmt_eval_Control_absent'; eauto; auto].
      + eapply stmt_eval_Control_present'; eauto using stmt_eval, lexp_correct; auto.
      + split; try inversion 1.
        apply Memory_Corres_eqs_Next_present; auto.
      + split; try inversion 1.
        apply Memory_Corres_eqs_Next_absent; auto; congruence.

    - destruct r.
      + pose proof Init.
        inversion_clear Init as [????? Find Rst].
        edestruct reset_spec as (me' &?&?& SpecInit); eauto.
        do 2 eexists; split.
        * eapply stmt_eval_Control_present'; eauto; auto.
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
                 pose proof E as E'.
                 apply Scorres in E as (Ss & E).
                 pose proof E as Sub.
                 apply Scorres in E as (?& E & Eq).
                 rewrite E in E'; inv E'; rewrite Eq.
                 eapply Closed; eauto.
                 simpl; auto.
               * eapply state_closed_empty; eauto.
             + inv TransClosed; auto.
           - eapply Reset_not_Step_in; eauto.
         }
      + exists me, ve; split; try eapply stmt_eval_Control_absent'; eauto; auto.
        split; try inversion 1.
        destruct Init as (?&?&?).
        eapply Memory_Corres_eqs_Reset_absent; eauto.
        eapply Reset_not_Reset_in; eauto.

    - apply Step_not_Step_Reset_in in Wsch; auto.
      inv Hexps.
      + assert (exists cs', os = map present cs') as (cs' & ?).
        { apply present_list_spec.
          apply sem_block_present in Hblock; auto.
          apply present_list_spec; eauto.
        }
        subst.
        eapply IH in Hblock as (me' &?&?).
        *{ do 2 eexists; split.
           - eapply stmt_eval_Control_present'; eauto; auto.
             econstructor; eauto using lexps_correct.
           - split.
             + eapply Memory_Corres_eqs_Call_present; eauto.
             + inversion_clear 1; intros Hvar.
               apply Env.In_find_adds.
               * unfold variables, concatMap in Vars; simpl in Vars.
                 apply NoDup_app_weaken in Vars; auto.
               * eapply Forall2_in_left_combine in Hvars as (?& Hin &?); eauto.
                 eapply sem_var_instant_det in Hvar; eauto; inv Hvar.
                 rewrite combine_map_snd, in_map_iff in Hin.
                 destruct Hin as ((?&?)&E&?); inv E; auto.
         }
        *{ destruct rst; apply Corres in Wsch as (Inst).
           - apply Inst in Find_I as (?& -> &?); auto.
           - destruct Find_S as (?& Find_S & E); auto.
             apply Inst in Find_S as (?& -> &?); rewrite E; auto.
         }
      + exists me, ve; split; try eapply stmt_eval_Control_absent'; eauto; auto.
        split.
        * apply sem_block_absent in Hblock as (); try apply all_absent_spec.
          eapply Memory_Corres_eqs_Call_absent; eauto.
        * assert (os = all_absent os) as Abs.
          { inversion_clear Hblock as [???????????????? Abs].
            apply absent_list_spec, Abs, all_absent_spec; auto.
          }
          rewrite Abs in Hvars.
          inversion_clear 1; intros Hvar.
          eapply Forall2_in_left in Hvars as (v & Hin &?); eauto.
          eapply sem_var_instant_det in Hvar; eauto; subst v.
          clear - Hin; exfalso.
          induction os; inv Hin; try discriminate; auto.
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
    forall eq x P me ve mems me' ve',
      ~ Is_defined_in_eq x eq ->
      stmt_eval (translate P) me ve (translate_eqn mems eq) (me', ve') ->
      find_val x me' = find_val x me.
  Proof.
    destruct eq; simpl; intros ** NIsDef StEval;
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
    forall eqs x P me ve mems me' ve',
      ~ Is_defined_in x eqs ->
      stmt_eval (translate P) me ve (translate_eqns mems eqs) (me', ve') ->
      find_val x me' = find_val x me.
  Proof.
    unfold translate_eqns.
    induction eqs as [|eq]; simpl; intros ** NIsDef StEval.
    - now inv StEval.
    - apply stmt_eval_fold_left_shift in StEval as (me'' & ve'' &?& Hcomp);
        rewrite stmt_eval_eq_Comp_Skip2 in Hcomp.
      apply not_Is_defined_in_cons in NIsDef as (?& Spec).
      eapply IHeqs with (me' := me'') in Spec; eauto.
      rewrite <-Spec.
      eapply not_Is_defined_in_eq_stmt_eval_menv_inv; eauto.
  Qed.

  Lemma not_Is_defined_in_eq_stmt_eval_venv_inv:
    forall eq x P me ve mems me' ve',
      ~ Is_defined_in_eq x eq ->
      stmt_eval (translate P) me ve (translate_eqn mems eq) (me', ve') ->
      Env.find x ve' = Env.find x ve.
  Proof.
    intros ** Hnd Heval.
    destruct eq; simpl in Heval;
      apply stmt_eval_Control_fwd in Heval;
      destruct Heval as [[Hipi Heval]|[Habs [Hmenv Henv]]];
      subst; auto.
    - apply stmt_eval_translate_cexp_venv_inv in Heval as (?&?); subst.
      apply not_Is_defined_in_eq_EqDef in Hnd.
      rewrite Env.gso; auto.
    - inv Heval; auto.
    - inv Heval.
      rewrite Env.adds_nil_l; auto.
    - inv Heval.
      rewrite Env.find_In_gsso; auto.
      intro; apply Hnd; constructor; auto.
  Qed.

  Corollary not_Is_defined_in_stmt_eval_venv_inv:
    forall eqs x P me ve mems me' ve',
      ~ Is_defined_in x eqs ->
      stmt_eval (translate P) me ve (translate_eqns mems eqs) (me', ve') ->
      Env.find x ve' = Env.find x ve.
  Proof.
    unfold translate_eqns.
    induction eqs as [|eq]; simpl; intros ** NIsDef StEval.
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
    intros ** E; unfold value_corres; now rewrite E.
  Qed.

  Lemma state_corres_equal_memory:
    forall s S me,
      S ≋ me ->
      state_corres s S me.
  Proof.
    intros ** E; split; unfold sub_inst; intros ** Find;
      pose proof (find_inst_equal_memory s E) as E';
      rewrite Find in E'.
    - destruct (find_inst s me); try contradiction.
      exists m; intuition.
    - destruct (find_inst s S); try contradiction.
      exists m; intuition.
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
    forall prog x eq me ve mems me' ve',
      ~ Is_variable_in_eq x eq ->
      stmt_eval prog me ve (translate_eqn mems eq) (me', ve') ->
      Env.find x ve' = Env.find x ve.
  Proof.
    intros ** Hnd Heval.
    destruct eq; simpl in Heval;
      apply stmt_eval_Control_fwd in Heval;
      destruct Heval as [[Hipi Heval]|[Habs [Hmenv Henv]]];
      subst; auto.
    - apply stmt_eval_translate_cexp_venv_inv in Heval as (?&?); subst.
      rewrite Env.gso; auto.
      intro; subst; apply Hnd; constructor.
    - inv Heval; auto.
    - inv Heval.
      rewrite Env.adds_nil_l; auto.
    - inv Heval.
      rewrite Env.find_In_gsso; auto.
      intro; apply Hnd; constructor; auto.
  Qed.

  Lemma equations_app_correct:
    forall eqs' eqs P R S I S' me ve inputs mems,
      (forall b S xs ys S' me,
          sem_block P b S (map present xs) (map present ys) S' ->
          me ≋ S ->
          exists me',
            stmt_call_eval (translate P) me b step xs me' ys
            /\ me' ≋ S') ->
      Forall (sem_equation P true R S I S') (eqs ++ eqs') ->
      Ordered_blocks P ->
      Is_well_sch inputs mems (eqs ++ eqs') ->
      NoDup (variables (eqs ++ eqs')) ->
      Step_with_reset_spec (eqs ++ eqs') ->
      (forall s b Ss, In (s, b) (resets_of (eqs ++ eqs')) -> sub_inst s S Ss -> state_closed P b Ss) ->
      transient_states_closed P (resets_of (eqs ++ eqs')) I ->
      (forall x, PS.In x mems -> Is_last_in x (eqs ++ eqs')) ->
      (forall x, In x inputs -> ~ Is_defined_in x (eqs ++ eqs')) ->
      (forall x c,
          In x inputs ->
          sem_var_instant R x (present c) ->
          Env.find x ve = Some c) ->
      me ≋ S ->
      exists me' ve',
        stmt_eval (translate P) me ve (translate_eqns mems eqs') (me', ve')
        /\ Memory_Corres_eqs eqs' S I S' me'
        /\ forall x c,
            Is_variable_in x eqs' ->
            sem_var_instant R x (present c) ->
            Env.find x ve' = Some c.
  Proof.
    induction eqs' as [|eq]; simpl;
      intros ** Heqs Ord Wsch Vars StepReset Closed TransClosed SpecLast SpecInput EquivInput Corres.
    - exists me, ve. split; eauto using stmt_eval; split; auto.
      + now apply Memory_Corres_eqs_empty_equal_memory.
      + inversion 1.
    - pose proof Wsch as Wsch'; apply Is_well_sch_app in Wsch'.
      pose proof Vars as Vars'; rewrite variables_app in Vars';
        apply NoDup_comm, NoDup_app_weaken in Vars'.
      pose proof StepReset as StepReset'; apply Step_with_reset_spec_app in StepReset'.
      pose proof Heqs as Heqs'; apply Forall_app_weaken in Heqs'; inv Heqs'.
      rewrite List_shift_first in Wsch, Vars, StepReset, Heqs, SpecLast, SpecInput, Closed, TransClosed.
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
          eapply sem_equations_is_last_in in Heqs; eauto.
        * destruct Free as [|Input]; auto.
          assert (~ Is_defined_in x eqs')
            by (intro; eapply SpecInput, Exists_app; eauto).
          erewrite not_Is_defined_in_stmt_eval_venv_inv; eauto.
      + exists me'', ve''; split; [|split]; auto.
        * unfold translate_eqns; simpl.
          rewrite stmt_eval_fold_left_shift; setoid_rewrite stmt_eval_eq_Comp_Skip2; eauto.
        * intros x v IsVar Hvar.
          destruct (Is_variable_in_eq_dec x eq) as [|Nvar]; auto.
          erewrite not_Is_variable_in_eq_stmt_eval_env_inv; eauto.
          inv IsVar; auto.
          contradiction.
  Qed.

  Lemma equations_correct:
    forall eqs P R S I S' me ve inputs mems,
      (forall b S xs ys S' me,
          sem_block P b S (map present xs) (map present ys) S' ->
          me ≋ S ->
          exists me',
            stmt_call_eval (translate P) me b step xs me' ys
            /\ me' ≋ S') ->
      Forall (sem_equation P true R S I S') eqs ->
      Ordered_blocks P ->
      (forall s b Ss, In (s, b) (resets_of eqs) -> sub_inst s S Ss -> state_closed P b Ss) ->
      transient_states_closed P (resets_of eqs) I ->
      Is_well_sch inputs mems eqs ->
      NoDup (variables eqs) ->
      Step_with_reset_spec eqs ->
      (forall x, PS.In x mems -> Is_last_in x eqs) ->
      (forall x, In x inputs -> ~ Is_defined_in x eqs) ->
      (forall x c,
          In x inputs ->
          sem_var_instant R x (present c) ->
          Env.find x ve = Some c) ->
      me ≋ S ->
      exists me' ve',
        stmt_eval (translate P) me ve (translate_eqns mems eqs) (me', ve')
        /\ Memory_Corres_eqs eqs S I S' me'
        /\ forall x c,
            Is_variable_in x eqs ->
            sem_var_instant R x (present c) ->
            Env.find x ve' = Some c.
  Proof.
    intros; eapply equations_app_correct with (eqs := []); eauto.
  Qed.

  Lemma state_closed_insts_InMembers:
    forall P blocks S s Ss,
      state_closed_insts P blocks S ->
      sub_inst s S Ss ->
      InMembers s blocks.
  Proof.
    intros ** Closed Sub; apply Closed in Sub as (?&?&?).
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
    intros ** (Lasts & Insts) Heqs LastClosed InstsClosed LastClosed' InstsClosed'
           SpecLast SpecInst WSCH.
    split.
    - intro x; destruct (Is_last_in_dec x eqs) as [Last|Nlast].
      + apply Lasts in Last; auto.
      + assert (find_val x S = None).
        { apply not_Some_is_None; intros ** Find;
            apply Nlast, SpecLast, LastClosed.
          apply not_None_is_Some; eauto.
        }
        assert (find_val x S' = None) as E'.
        { apply not_Some_is_None; intros ** Find;
            apply Nlast, SpecLast, LastClosed'.
          apply not_None_is_Some; eauto.
        }
        unfold value_corres, find_val in *.
        apply Lasts in Nlast.
        rewrite E'; rewrite <-Nlast; auto.
    - split.
      + setoid_rewrite Env.In_find; intro s.
        destruct (Step_in_dec s eqs) as [Step|Nstep].
        * apply Insts in Step as (Inst & Inst').
          unfold sub_inst, find_inst in *; split; intros (?&?); eauto.
          edestruct Inst as (?&?&?); eauto.
        *{ destruct (Reset_in_dec s eqs) as [Rst|Nrst].
           - apply WSCH in Rst; contradiction.
           - assert (~ exists k, Is_state_in s k eqs) as Nstate.
             { intros (?& State).
               apply Exists_exists in State as (?&?& State).
               inv State.
               - apply Nrst, Exists_exists; eauto using Is_state_in_eq.
               - apply Nstep, Exists_exists; eauto using Is_state_in_eq.
             }
             assert (state_corres s S me) as (?& Inst') by (apply Insts; auto).
             assert (find_inst s S = None).
             { apply not_Some_is_None; intros ** Find;
                 apply Nstate, SpecInst.
               eapply state_closed_insts_InMembers in InstsClosed; eauto.
             }
             assert (find_inst s S' = None) as E'.
             { apply not_Some_is_None; intros ** Find;
                 apply Nstate, SpecInst.
               eapply state_closed_insts_InMembers in InstsClosed'; eauto.
             }
             unfold sub_inst in *.
             assert (find_inst s me = None) as E.
             { apply not_Some_is_None; intros ** Find;
                 apply Inst' in Find as (?&?).
               congruence.
             }
             setoid_rewrite E'; setoid_rewrite E; reflexivity.
         }
      + setoid_rewrite Env.Props.P.F.find_mapsto_iff.
        intros s me_s Ss' Find Find'.
        destruct (Step_in_dec s eqs) as [Step|Nstep].
        * apply Insts in Step as (Inst).
          unfold sub_inst, find_inst in *.
          apply Inst in Find' as (?& Find' &?).
          rewrite Find' in Find; inv Find; auto.
        *{ destruct (Reset_in_dec s eqs) as [Rst|Nrst].
           - apply WSCH in Rst; contradiction.
           - assert (~ (Step_in s eqs \/ Reset_in s eqs)) as NstpRst by tauto.
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
         }
  Qed.

  Theorem correctness:
    forall P b S xs ys S' me,
      Well_defined P ->
      sem_block P b S (map present xs) (map present ys) S' ->
      me ≋ S ->
      exists me',
        stmt_call_eval (translate P) me b step xs me' ys
        /\ me' ≋ S'.
  Proof.
    induction P as [|block]; intros ** (Ord & WSCH) Sem E;
      inversion_clear Sem as [?????????? Clock Find ? Outs ??? Heqs Closed TransClosed Closed'];
      try now inv Find.
    pose proof Find as Find'.
    simpl in Find.
    pose proof Ord.
    inv Ord; inv WSCH.
    assert (Well_defined P) by (split; auto).
    destruct (ident_eqb (b_name block) b) eqn: Eq.
    - inv Find.
      assert (base = true) by (apply Clock; rewrite present_list_spec; eauto); subst.
      apply sem_equations_cons in Heqs; eauto.
      + edestruct equations_correct with (ve := Env.adds (map fst (m_in (step_method bl))) xs vempty)
          as (me' & ve' &?&?& Equiv); eauto.
        * inversion_clear Closed as [????? Find ? Insts]; rewrite Find in Find'; inv Find'.
          intros ** b' ? Hin Sub.
          apply Insts in Sub as (b'' &?&?).
          apply b_reset_incl in Hin.
          rewrite <-b_blocks_calls_of in Hin.
          assert (b' = b'') as ->; auto.
          eapply NoDupMembers_det in Hin; eauto.
          apply b_nodup_blocks.
        *{ eapply Forall_incl.
           - eapply transient_states_closed_In; eauto.
             intros (); now setoid_rewrite b_blocks_calls_of.
           - apply b_reset_incl.
         }
        * apply b_nodup_variables.
        * eapply Is_well_sch_Step_with_reset_spec; eauto.
          apply b_reset_in.
        * intros; apply lasts_of_In, ps_from_list_In; auto.
          rewrite <-b_lasts_in_eqs; auto.
        * intros; apply b_ins_not_def, fst_InMembers; auto.
        *{ intros ** Hin Hvar; apply Env.In_find_adds; simpl; rewrite map_fst_idty.
           - pose proof (b_nodup bl) as Nodup.
             apply NoDup_app_weaken in Nodup; auto.
           - eapply Forall2_in_left_combine in Hin; eauto.
             destruct Hin as (?& Hin &?); eapply sem_var_instant_det in Hvar; eauto.
             subst; rewrite combine_map_snd, in_map_iff in Hin.
             destruct Hin as ((?&?)& E' &?); inv E'; auto.
         }
         *{ exists me'; split.
            - apply find_block_translate in Find' as (?&?&?&?&?); subst.
              econstructor; eauto.
              + apply exists_step_method.
              + eauto.
              + simpl.
                unfold sem_vars_instant in Outs; rewrite Forall2_map_2 in Outs.
                apply Forall2_forall in Outs as (Outs & Length).
                apply Forall2_forall; split; rewrite map_fst_idty; auto.
                intros ** Hin.
                apply Equiv; auto.
                apply Is_variable_in_variables; rewrite <-b_vars_out_in_eqs, in_app.
                right; apply in_combine_l in Hin; auto.
            - inv Closed; inv Closed';
                repeat match goal with
                         H: find_block ?b ?P = _, H': find_block ?b ?P = _ |- _ =>
                         rewrite H in H'; inv H'
                       end.
              eapply Memory_Corres_eqs_equal_memory; eauto.
              + intro; now rewrite b_lasts_in_eqs, lasts_of_In.
              + setoid_rewrite b_blocks_calls_of; apply calls_of_Is_state_in.
              + intros ** Rst; apply b_no_single_reset, Step_with_reset_in_Step_in in Rst; auto.
          }
      + eapply find_block_not_Is_block_in; eauto.
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
    forall P f ins outs S0,
      Well_defined P ->
      loop P f (vstr ins) (vstr outs) S0 0 ->
      exists me0,
        stmt_call_eval (translate P) mempty f reset [] me0 []
        /\ loop_call (translate P) f step ins outs 0 me0
        /\ me0 ≋ S0.
  Proof.
    intros ** Wdef Loop.
    pose proof Loop as Loop'; inversion_clear Loop' as [???????? Sem].
    inv Sem.
    assert (Ordered_blocks P) as Ord by apply Wdef.
    eapply reset_spec with (me := mempty) in Ord as (me' &?&?& Closed); eauto.
    assert (me' ≋ S0) as Eq
        by (eapply initial_state_det; eauto;
            eapply Closed, state_closed_empty; eauto).
    exists me'; intuition.
    clear - Loop Wdef Eq.
    revert Loop Eq; revert me' S0.
    generalize 0.
    cofix COFIX; intros.
    inversion_clear Loop as [???????? Sem].
    unfold vstr in Sem; rewrite <-2 map_map with (g := present) (f := sem_const) in Sem.
    eapply correctness with (1:= Wdef) (3 := Eq) in Sem as (?&?&?).
    econstructor; eauto.
  Qed.

End CORRECTNESS.

Module CorrectnessFun
       (Ids    : IDS)
       (Op     : OPERATORS)
       (OpAux  : OPERATORS_AUX      Op)
       (Clks   : CLOCKS         Ids)
       (Str    : STREAM             Op OpAux)
       (CE     : COREEXPR       Ids Op OpAux Clks Str)
       (SB     : SYBLOC         Ids Op OpAux Clks Str CE)
       (Obc    : OBC            Ids Op OpAux)
       (Trans  : TRANSLATION    Ids Op OpAux Clks CE.Syn SB.Syn Obc.Syn)
       (Corres : SBMEMORYCORRES Ids Op       Clks CE.Syn SB.Syn SB.Last)
<: CORRECTNESS Ids Op OpAux Clks Str CE SB Obc Trans Corres.
  Include CORRECTNESS Ids Op OpAux Clks Str CE SB Obc Trans Corres.
End CorrectnessFun.
