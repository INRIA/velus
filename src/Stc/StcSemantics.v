From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Permutation.
From Coq Require Import Setoid.
From Coq Require Import Morphisms.

From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import Environment.
From Velus Require Import FunctionalEnvironment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import VelusMemory.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Stc.StcOrdered.
From Velus Require Import IndexedStreams.
From Velus Require Import CoreExpr.CESemantics.

Module Type STCSEMANTICS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Ids Op)
       (Import Cks   : CLOCKS      Ids Op OpAux)
       (Import CESyn : CESYNTAX    Ids Op OpAux Cks)
       (Import Syn   : STCSYNTAX   Ids Op OpAux Cks CESyn)
       (Import Ord   : STCORDERED  Ids Op OpAux Cks CESyn Syn)
       (Import Str   : INDEXEDSTREAMS Ids Op OpAux Cks)
       (Import CESem : CESEMANTICS Ids Op OpAux Cks CESyn Str).

  Definition state := memory value.

  Definition state_closed_states (states : list ident) (S: state) : Prop :=
    forall x, find_val x S <> None -> In x states.

  Inductive state_closed {prefs} : @program prefs -> ident -> state -> Prop :=
    state_closed_intro:
      forall P f S s P',
        find_system f P = Some (s, P') ->
        state_closed_states (map fst (s.(s_lasts) ++ s.(s_nexts))) S ->
        (forall i S',
            find_inst i S = Some S' ->
            exists g,
              In (i, g) (s_subs s)
              /\ state_closed P' g S') ->
        state_closed P f S.

  Definition state_closed_insts {prefs} (P: @program prefs) (subs: list (ident * ident)) (S: state) : Prop :=
    forall i Si,
      find_inst i S = Some Si ->
      exists g, In (i, g) subs
           /\ state_closed P g Si.

  Definition reset_states {prefs} (s: @system prefs) (S0: state) : Prop :=
    forall x c t ck,
      In (x, (c, t, ck)) (s.(s_lasts) ++ s.(s_nexts)) ->
      find_val x S0 = Some (sem_const c).

  Inductive initial_state {prefs} : (@program prefs) -> ident -> state -> Prop :=
    initial_state_intro:
      forall P f S0 s P',
        find_system f P = Some (s, P') ->
        reset_states s S0 ->
        (forall i g,
            In (i, g) s.(s_subs) ->
            exists Si0,
              find_inst i S0 = Some Si0
              /\ initial_state P' g Si0) ->
        initial_state P f S0.

  Section Semantics.

    Context {prefs : PS.t}.
    Variable P: @program prefs.

    Inductive sem_trconstr: bool -> env -> state -> state -> state -> trconstr -> Prop :=
    | STcDef:
        forall base R S I S' x v ck ce,
          sem_arhs_instant base R ck ce v ->
          sem_var_instant R (Var x) v ->
          sem_trconstr base R S I S' (TcDef ck x ce)
    | STcResetState:
        forall base R S I S' x ckr ty c0 r c,
          find_val x S = Some c ->
          sem_clock_instant base (var_env R) ckr r ->
          (if r then find_val x I = Some (sem_const c0) else True) ->
          sem_trconstr base R S I S' (TcReset ckr (ResState x ty c0))
    | STcResetInst:
        forall base R S I S' ckr f i r Ii,
          find_inst i I = Some Ii ->
          sem_clock_instant base (var_env R) ckr r ->
          (if r then initial_state P f Ii else True) ->
          sem_trconstr base R S I S' (TcReset ckr (ResInst i f))
    | STcUpdateLast:
        forall base R S I S' x ck e ckrs c v',
          (Forall (fun ckr => sem_clock_instant base (var_env R) ckr false) ckrs -> find_val x S = Some c) ->
          find_val x I = Some c ->
          sem_caexp_instant base R ck e v' ->
          sem_var_instant R (Last x) (match v' with present _ => present c | absent => absent end) ->
          sem_var_instant R (Var x) v' ->
          find_val x S' = Some (match v' with present c' => c' | absent => c end) ->
          sem_trconstr base R S I S' (TcUpdate ck ckrs (UpdLast x e))
    | STcUpdateNext:
        forall base R S I S' x ck e ckrs c v',
          (Forall (fun ckr => sem_clock_instant base (var_env R) ckr false) ckrs -> find_val x S = Some c) ->
          find_val x I = Some c ->
          sem_aexp_instant base R ck e v' ->
          sem_var_instant R (Var x) (match v' with present _ => present c | absent => absent end) ->
          find_val x S' = Some (match v' with present c' => c' | absent => c end) ->
          sem_trconstr base R S I S' (TcUpdate ck ckrs (UpdNext x e))
    | STcUpdateInst:
        forall base R S I S' ys ck ckrs f i es xs Ii os Si',
          (Forall (fun ckr => sem_clock_instant base (var_env R) ckr false) ckrs -> find_inst i S ⌈≋⌉ Some Ii) ->
          find_inst i I = Some Ii ->
          sem_exps_instant base R es xs ->
          sem_clock_instant base (var_env R) ck (clock_of_instant xs) ->
          sem_system f Ii xs os Si' ->
          sem_vars_instant R ys os ->
          find_inst i S' = Some Si' ->
          sem_trconstr base R S I S' (TcUpdate ck ckrs (UpdInst i ys f es))

    with sem_system: ident -> state -> list svalue -> list svalue -> state -> Prop :=
           SSystem:
             forall f s P' S I S' R xs ys,
               find_system f P = Some (s, P') ->
               sem_vars_instant R (map fst s.(s_in)) xs ->
               sem_vars_instant R (map fst s.(s_out)) ys ->
               sem_clocked_vars_instant (clock_of_instant xs) R (map (fun '(x, (_, ck)) => (x, (ck, false))) s.(s_in)) ->
               Forall (sem_trconstr (clock_of_instant xs) R S I S') s.(s_tcs) ->
               state_closed P f S ->
               state_closed P f I ->
               state_closed P f S' ->
               sem_system f S xs ys S'.

  End Semantics.

  Global Hint Constructors sem_trconstr sem_system state_closed : stcsem.

  Section sem_system_mult.
    Context {prefs : PS.t}.
    Variable P: @program prefs.

    Variable P_trconstr: bool -> env -> state -> state -> state -> trconstr -> Prop.
    Variable P_system: ident -> state -> list svalue -> list svalue -> state -> Prop.

    Hypothesis TcDefCase:
      forall base R S I S' x v ck ce,
        sem_arhs_instant base R ck ce v ->
        sem_var_instant R (Var x) v ->
        P_trconstr base R S I S' (TcDef ck x ce).

    Hypothesis TcResetStateCase:
      forall base R S I S' x ckr ty c0 r c,
        find_val x S = Some c ->
        sem_clock_instant base (var_env R) ckr r ->
        (if r then find_val x I = Some (sem_const c0) else True) ->
        P_trconstr base R S I S' (TcReset ckr (ResState x ty c0)).

    Hypothesis TcUpdateLastCase:
      forall base R S I S' x ck e ckrs c v',
        (Forall (fun ckr => sem_clock_instant base (var_env R) ckr false) ckrs -> find_val x S = Some c) ->
        find_val x I = Some c ->
        sem_caexp_instant base R ck e v' ->
        sem_var_instant R (Last x) (match v' with present _ => present c | absent => absent end) ->
        sem_var_instant R (Var x) v' ->
        find_val x S' = Some (match v' with present c' => c' | absent => c end) ->
        P_trconstr base R S I S' (TcUpdate ck ckrs (UpdLast x e)).

    Hypothesis TcUpdateNextCase:
      forall base R S I S' x ck e ckrs c v',
        (Forall (fun ckr => sem_clock_instant base (var_env R) ckr false) ckrs -> find_val x S = Some c) ->
        find_val x I = Some c ->
        sem_aexp_instant base R ck e v' ->
        sem_var_instant R (Var x) (match v' with present _ => present c | absent => absent end) ->
        find_val x S' = Some (match v' with present c' => c' | absent => c end) ->
        P_trconstr base R S I S' (TcUpdate ck ckrs (UpdNext x e)).

    Hypothesis TcResetInstCase:
      forall base R S I S' ck f i r Ii,
        sem_clock_instant base (var_env R) ck r ->
        find_inst i I = Some Ii ->
        (if r then initial_state P f Ii else True) ->
        P_trconstr base R S I S' (TcReset ck (ResInst i f)).

    Hypothesis TcUpdateInstCase:
      forall base R S I S' ys ck ckrs f i es xs Ii os Si',
        (Forall (fun ckr => sem_clock_instant base (var_env R) ckr false) ckrs -> find_inst i S ⌈≋⌉ Some Ii) ->
        find_inst i I = Some Ii ->
        sem_exps_instant base R es xs ->
        sem_clock_instant base (var_env R) ck (clock_of_instant xs) ->
        sem_system P f Ii xs os Si' ->
        sem_vars_instant R ys os ->
        find_inst i S' = Some Si' ->
        P_system f Ii xs os Si' ->
        P_trconstr base R S I S' (TcUpdate ck ckrs (UpdInst i ys f es)).

    Hypothesis SystemCase:
      forall f s P' R S I S' xs ys,
        find_system f P = Some (s, P') ->
        sem_vars_instant R (map fst s.(s_in)) xs ->
        sem_vars_instant R (map fst s.(s_out)) ys ->
        sem_clocked_vars_instant (clock_of_instant xs) R (map (fun '(x, (_, ck)) => (x, (ck, false))) s.(s_in)) ->
        Forall (sem_trconstr P (clock_of_instant xs) R S I S') s.(s_tcs) ->
        state_closed P f S ->
        state_closed P f I ->
        state_closed P f S' ->
        Forall (P_trconstr (clock_of_instant xs) R S I S') s.(s_tcs) ->
        P_system f S xs ys S'.

    Fixpoint sem_trconstr_mult
             (base: bool) (R: env) (S: state) (I: state) (S': state) (e: trconstr)
             (Sem: sem_trconstr P base R S I S' e) {struct Sem}
      : P_trconstr base R S I S' e
    with sem_system_mult
           (f: ident) (S: state) (xs ys: list svalue) (S': state)
           (Sem: sem_system P f S xs ys S') {struct Sem}
         : P_system f S xs ys S'.
    Proof.
      - destruct Sem; eauto.
      - destruct Sem.
        eapply SystemCase; eauto.
        match goal with H: Forall _ _ |- _ => induction H; auto end.
    Qed.

  End sem_system_mult.

  CoInductive loop {prefs}: (@program prefs) -> ident -> stream (list svalue) -> stream (list svalue) -> state -> nat -> Prop :=
    loop_intro:
      forall P f xss yss Sn Sn' n,
        sem_system P f Sn (xss n) (yss n) Sn' ->
        loop P f xss yss Sn' (S n) ->
        loop P f xss yss Sn n.

  Section LoopCoind.
    Context {prefs : PS.t}.
    Variable R: (@program prefs) -> ident -> stream (list svalue) -> stream (list svalue) -> state -> nat -> Prop.

    Hypothesis Loop:
      forall P f xss yss Sn n,
        R P f xss yss Sn n ->
        exists Sn', sem_system P f Sn (xss n) (yss n) Sn'
               /\ R P f xss yss Sn' (S n).

    Lemma loop_coind:
      forall P f xss yss S n,
        R P f xss yss S n ->
        loop P f xss yss S n.
    Proof.
      cofix COFIX; intros * HR.
      apply Loop in HR as (?&?&?).
      econstructor; eauto.
    Qed.

  End LoopCoind.

  Add Parametric Morphism {prefs} system : (@reset_states prefs system)
      with signature equal_memory ==> Basics.impl
        as reset_states_equal_memory.
  Proof.
    intros * E Rst ???? Hin.
    rewrite <-E; apply Rst in Hin; auto.
  Qed.

  Add Parametric Morphism {prefs} P f : (@initial_state prefs P f)
      with signature equal_memory ==> Basics.impl
        as initial_state_equal_memory.
  Proof.
    intros * E Init.
    revert dependent P; revert dependent f; revert dependent y.
    induction x as [? IH] using memory_ind'; intros.
    inversion_clear Init as [??????? Spec].
    econstructor; eauto.
    - now rewrite <-E.
    - intros * Hin.
      apply Spec in Hin as (?& Sub &?).
      pose (Sub' := Sub).
      apply orel_eq in Sub'.
      setoid_rewrite (@eq_subrelation _ equal_memory) in Sub'; auto with memory.
      setoid_rewrite E in Sub'.
      apply orel_find_inst_Some in Sub' as (v' & Hv' & ->).
      symmetry in Hv'. eauto.
  Qed.

  Add Parametric Morphism states : (state_closed_states states)
      with signature equal_memory ==> Basics.impl
        as state_closed_states_equal_memory.
  Proof.
    unfold state_closed_states.
    intros * E Closed ? Find.
    apply Closed; rewrite E; auto.
  Qed.

  Add Parametric Morphism {prefs} P b : (@state_closed prefs P b)
      with signature equal_memory ==> Basics.impl
        as state_closed_equal_memory.
  Proof.
    intros m m' E Closed; revert dependent m'; revert dependent b; revert P ;
      induction m as [? IH] using memory_ind'; intros.
    inversion_clear Closed as [??????? Insts].
    econstructor; eauto.
    - now setoid_rewrite <-E.
    - intros * Sub.
      apply orel_eq in Sub.
      setoid_rewrite (@eq_subrelation _ equal_memory) in Sub; auto with memory.
      setoid_rewrite <-E in Sub.
      apply orel_find_inst_Some in Sub as (S & HS & Sub').
      specialize (Insts _ _ Sub') as (b' & ? & ?). eauto.
  Qed.

  Add Parametric Morphism {prefs} P : (@state_closed_insts prefs P)
      with signature @Permutation (ident * ident) ==> eq ==> Basics.impl
        as state_closed_insts_Permutation.
  Proof.
    intros * E ? Closed ?? Find; apply Closed in Find as (g&?&?).
    exists g; split; auto.
    now rewrite <-E.
  Qed.

  Add Parametric Morphism {prefs} P f: (@sem_system prefs P f)
      with signature equal_memory ==> eq ==> eq ==> equal_memory ==> Basics.impl
        as sem_system_equal_memory.
  Proof.
    intros S1 S2 ??? S1' S2' ** Sem.
    eapply sem_system_mult with
      (P_system := fun f S1 xs ys S1' =>
                     forall S2 S2',
                       S1 ≋ S2 ->
                       S1' ≋ S2' ->
                       sem_system P f S2 xs ys S2')
      (P_trconstr := fun base R S1 I1 S1' tc =>
                       forall S2 S2' I2,
                         S1 ≋ S2 ->
                         I1 ≋ I2 ->
                         S1' ≋ S2' ->
                         sem_trconstr P base R S2 I2 S2' tc) in Sem; eauto.
    - intros * ??? * E EI E'.
      econstructor; eauto.
    - intros * ??? * E EI E'.
      econstructor; eauto.
      + rewrite <-E; eauto.
      + destruct r; try rewrite <-EI; eauto.
    - intros * ?????? * E EI E'.
      econstructor; eauto.
      + rewrite <-E; eauto.
      + rewrite <-EI; eauto.
      + rewrite <-E'; eauto.
    - intros * ????? * E EI E'.
      econstructor; eauto.
      + rewrite <-E; eauto.
      + rewrite <-EI; eauto.
      + rewrite <-E'; eauto.
    - intros * ? Find ? * E EI E'.
      apply orel_eq in Find;
        setoid_rewrite (@eq_subrelation _ equal_memory) in Find; auto with memory.
      rewrite EI in Find.
      apply Env.orel_find_Some in Find as (Is' & Eq & Find').
      destruct r.
      + econstructor; eauto; simpl. rewrite Eq; eauto.
      + econstructor; eauto; simpl.
    - intros * ? Find ? Spec ?? Sub Ind * E EI E'.
      apply orel_eq in Find;
        setoid_rewrite (@eq_subrelation _ equal_memory) in Find; auto with memory.
      rewrite EI in Find.
      apply Env.orel_find_Some in Find as (? & Eq & ?).
      apply orel_eq in Sub;
        setoid_rewrite (@eq_subrelation _ equal_memory) in Sub; auto with memory.
      rewrite E' in Sub.
      apply orel_find_inst_Some in Sub as (? & Eq' & ?).
      symmetry in Eq, Eq'.
      econstructor; eauto.
      rewrite <-E, <-Eq; eauto.
    - intros * ????????? * E E'.
      eapply SSystem with (I := I); eauto.
      + induction (s_tcs s); auto;
          repeat match goal with H: Forall ?P (_ :: _) |- _ => inv H end.
        constructor; auto.
        assert (I ≋ I) by reflexivity;
          auto.
      + now rewrite <-E.
      + now rewrite <-E'.
  Qed.

  Add Parametric Morphism : (state_closed_states)
      with signature (@Permutation ident) ==> eq ==> Basics.impl
        as state_closed_states_permutation.
  Proof.
    unfold state_closed_states.
    intros * E ? Closed ? Find.
    rewrite <-E; auto.
  Qed.

  Add Parametric Morphism {prefs} P b xss yss : (@loop prefs P b xss yss)
      with signature equal_memory ==> eq ==> Basics.impl
        as loop_equal_memory.
  Proof.
    cofix COFIX.
    intros * E n Loop.
    inv Loop.
    econstructor; eauto.
    intros; rewrite <-E; auto.
  Qed.

  Lemma initial_state_other {prefs}:
    forall S0 s (P : list (@system prefs)) enums externs f,
      s_name s <> f ->
      (initial_state (Program enums externs P) f S0 <->
      initial_state (Program enums externs (s :: P)) f S0).
  Proof.
    split; inversion_clear 1 as [????? Find]; econstructor; eauto.
    - rewrite find_system_other; eauto.
    - rewrite find_system_other in Find; eauto.
  Qed.

  Fact reset_states_add_inst {prefs}:
    forall (s: @system prefs) S0 i Si0,
      reset_states s S0 ->
      reset_states s (add_inst i Si0 S0).
  Proof.
    unfold reset_states;
      setoid_rewrite find_val_add_inst; auto.
  Qed.

  Fact state_closed_states_add:
    forall states S x v,
      state_closed_states states S ->
      state_closed_states (x::states) (add_val x v S).
  Proof.
    unfold state_closed_states.
    intros * Hfind1 * Hfind2.
    destruct (ident_eq_dec x0 x); subst; [left|right]; auto.
    rewrite find_val_gso in Hfind2; auto.
  Qed.

  Fact state_closed_states_add_inst:
    forall states S i Si,
      state_closed_states states S ->
      state_closed_states states (add_inst i Si S).
  Proof.
    unfold state_closed_states;
      setoid_rewrite find_val_add_inst; auto.
  Qed.

  Lemma state_closed_insts_InMembers {prefs}:
    forall (P: @program prefs) subs S s Ss,
      state_closed_insts P subs S ->
      find_inst s S = Some Ss ->
      InMembers s subs.
  Proof.
    intros * Closed Sub; apply Closed in Sub as (?&?&?).
    eapply In_InMembers; eauto.
  Qed.

  Lemma state_closed_other {prefs}:
    forall S s (P: list (@system prefs)) f enums externs,
      s_name s <> f ->
      (state_closed (Program enums externs P) f S <->
      state_closed (Program enums externs (s :: P)) f S).
  Proof.
    split; inversion_clear 1 as [????? Find]; econstructor; eauto.
    - rewrite find_system_other; eauto.
    - rewrite find_system_other in Find; eauto.
  Qed.

  Lemma state_closed_find_system_other {prefs}:
    forall S i (P: @program prefs) P' f s g,
      Ordered_systems P ->
      find_system f P = Some (s, P') ->
      In (i, g) s.(s_subs) ->
      state_closed P g S ->
      state_closed P' g S.
  Proof.
    intros ?? [] * Ord Find Hin Closed; inversion_clear Closed as [????? Find'].
    econstructor; eauto.
    assert (types0 = types P') as Enums
        by (apply find_unit_equiv_program in Find; specialize (Find nil); inv Find; auto).
    assert (externs0 = externs P') as Externs
        by (apply find_unit_equiv_program in Find; specialize (Find nil); inv Find; auto).
    apply find_unit_spec in Find as (?&?& E &?); simpl in E; subst.
    apply Ordered_systems_split in Ord.
    eapply Forall_forall in Ord as (FindNone & Neq &?&?&?); eauto; simpl in *.
    setoid_rewrite find_unit_app in Find'; simpl in *; eauto.
    setoid_rewrite FindNone in Find'.
    eapply find_unit_cons in Find' as [[]|[]]; simpl in *; eauto; auto; contradiction.
  Qed.

  Lemma state_closed_insts_find_system_other {prefs}:
    forall I (s: @system prefs) P P' f,
      Ordered_systems P ->
      find_system f P = Some (s, P') ->
      state_closed_insts P s.(s_subs) I ->
      state_closed_insts P' s.(s_subs) I.
  Proof.
    intros * Ord ? Closed.
    intros ?? Find; apply Closed in Find as (g &?&?).
    exists g; split; auto.
    eapply state_closed_find_system_other; eauto.
  Qed.

  Lemma state_closed_insts_cons {prefs}:
    forall I (s: @system prefs) P enums externs,
      Ordered_systems (Program enums externs (s :: P)) ->
      state_closed_insts (Program enums externs P) s.(s_subs) I ->
      state_closed_insts (Program enums externs (s :: P)) s.(s_subs) I.
  Proof.
    intros * Ord Closed; inversion_clear Ord as [|?? [Spec ?]].
    intros ?? Find; apply Closed in Find as (g & Hin &?).
    exists g; split; auto.
    apply state_closed_other; auto.
    apply in_map with (f := snd) in Hin.
    apply Spec in Hin; intuition.
  Qed.

  Lemma sem_system_cons {prefs}:
    forall (P: list (@system prefs)) enums externs s f xs S S' ys,
      Ordered_systems (Program enums externs (s :: P)) ->
      sem_system (Program enums externs (s :: P)) f xs S S' ys ->
      s.(s_name) <> f ->
      sem_system (Program enums externs P) f xs S S' ys.
  Proof.
    intros ? enums externs * Hord Hsem Hnf.
    revert Hnf.
    eapply sem_system_mult with
      (P_system := fun f S xs ys S' =>
                     s_name s <> f ->
                     sem_system (Program enums externs P) f S xs ys S')
      (P_trconstr := fun bk H S I S' tc =>
                       ~Is_system_in_tc s.(s_name) tc ->
                       sem_trconstr (Program enums externs P) bk H S I S' tc) in Hsem;
      eauto with stcsem.
    - intros * ??? Hnin; econstructor; eauto.
      destruct r; eauto.
      rewrite initial_state_other; eauto.
      intro E; apply Hnin; rewrite E; constructor.
    - intros * ??????? IH Hnin; econstructor; eauto.
      apply IH; intro E; apply Hnin; rewrite E; constructor.
    - intros * Hf ???? Closed ClosedI Closed' IH Hneq.
      pose proof Hf.
      rewrite find_system_other in Hf; auto.
      rewrite <-state_closed_other in Closed, ClosedI, Closed'; auto.
      eapply SSystem with (I := I); eauto.
      eapply find_system_other_not_Is_system_in in Hord; eauto.
      apply Forall_forall; intros.
      eapply Forall_forall in IH; eauto.
      apply IH.
      intro; apply Hord.
      apply Exists_exists; eauto.
  Qed.

  Lemma sem_system_cons2 {prefs}:
    forall (s: @system prefs) P enums externs f xs S S' ys,
      Ordered_systems (Program enums externs (s :: P)) ->
      sem_system (Program enums externs P) f xs S S' ys ->
      sem_system (Program enums externs (s :: P)) f xs S S' ys.
  Proof.
    intros ?? enums externs * Hord Hsem.
    eapply sem_system_mult with
      (P_system := fun f S xs ys S' =>
                     sem_system (Program enums externs (s :: P)) f S xs ys S')
      (P_trconstr := fun bk H S I S' tc =>
                       ~Is_system_in_tc s.(s_name) tc ->
                       sem_trconstr (Program enums externs (s :: P)) bk H S I S' tc) in Hsem;
      eauto with stcsem.

    - intros * ??? Notin; econstructor; eauto.
      destruct r; eauto.
      apply initial_state_other; auto.
      intro E; apply Notin; rewrite E; constructor.
    - intros * Hfind ???? Closed ClosedI Closed' IHtcs.
      pose proof Hfind as Hfind'; apply find_unit_spec in Hfind' as (?&?& E & FindNone); simpl in *; subst.
      pose proof Hord as Hord'; rewrite app_comm_cons in Hord';
        apply Ordered_systems_split in Hord'.
      pose proof Hord.
      inversion_clear Hord as [|?? [? Hnin]].
      assert (s_name s <> s_name s0) as Hnf.
      { intro Hnf.
        rewrite Hnf in *.
        apply find_unit_spec in Hfind as (?&?& Hp &?); simpl in *; subst.
        apply Forall_app in Hnin.
        destruct Hnin as [H' Hfg]; clear H'.
        inv Hfg. congruence.
      }
      rewrite state_closed_other in Closed, ClosedI, Closed'; eauto.
      eapply SSystem with (I := I); eauto.
      + rewrite find_system_other; eauto.
      + apply Forall_forall.
        rewrite Forall_forall in IHtcs.
        intros * Hin; apply IHtcs; auto.
        rewrite Forall_forall in Hord'.
        pose proof (s_subs_in_tcs s) as SystemsIn.
        intro.
        eapply find_system_other_not_Is_system_in; eauto.
        apply Exists_exists; eauto.
  Qed.

  Global Hint Resolve sem_system_cons sem_system_cons2 : stcsem.

  Lemma sem_trconstrs_cons {prefs}:
    forall (P: list (@system prefs)) enums externs bk H S I S' tcs s,
      Ordered_systems (Program enums externs (s :: P)) ->
      ~ Is_system_in s.(s_name) tcs ->
      (Forall (sem_trconstr (Program enums externs P) bk H S I S') tcs <->
       Forall (sem_trconstr (Program enums externs (s :: P)) bk H S I S') tcs).
  Proof.
    intros * Hord Hnini.
    induction tcs as [|tc tcs IH]; [now constructor|].
    apply not_Is_system_in_cons in Hnini as [Hnini Hninis].
    split; intros Hsem; apply Forall_cons2 in Hsem as [Htc Htcs];
      apply IH in Htcs; auto; constructor; auto.
    - destruct Htc; eauto with stcsem.
      + econstructor; eauto.
        destruct r; eauto.
        apply initial_state_other; auto.
        intro E; apply Hnini; rewrite E; constructor.
    - destruct Htc; eauto with stcsem.
      + econstructor; eauto.
        destruct r; auto.
        rewrite initial_state_other; eauto.
        intro E; apply Hnini; rewrite E; constructor.
      + econstructor; eauto.
        eapply sem_system_cons; eauto.
        intro E; apply Hnini; rewrite E; constructor.
  Qed.

  Lemma reset_states_det {prefs}:
    forall (P: @program prefs) f S S' s P',
      state_closed P f S ->
      state_closed P f S' ->
      find_system f P = Some (s, P') ->
      reset_states s S ->
      reset_states s S' ->
      Env.Equal (values S) (values S').
  Proof.
    intros * Closed Closed' Find Rst Rst' x.
    inversion_clear Closed as [????? Find' Spec];
      rewrite Find' in Find; inv Find.
    inversion_clear Closed' as [????? Find Spec'];
      rewrite Find' in Find; inv Find.
    unfold state_closed_states, reset_states, find_val in *.
    destruct (Env.find x (values S)) eqn: E, (Env.find x (values S')) eqn: E'; auto.
    - assert (Env.find x (values S) <> None) as E1 by (apply not_None_is_Some; eauto).
      apply Spec, fst_InMembers, InMembers_In in E1 as (((? & ?) & ?) & Hin).
      pose proof Hin as Hin'.
      eapply Rst in Hin; eapply Rst' in Hin'.
      congruence.
    - assert (Env.find x (values S) <> None) as E1 by (apply not_None_is_Some; eauto).
      apply Spec, fst_InMembers, InMembers_In in E1 as (((? & ?) & ?) & Hin).
      eapply Rst' in Hin.
      congruence.
    - assert (Env.find x (values S') <> None) as E1 by (apply not_None_is_Some; eauto).
      apply Spec', fst_InMembers, InMembers_In in E1 as (((? & ?) & ?) & Hin).
      eapply Rst in Hin.
      congruence.
  Qed.

  Lemma initial_state_det {prefs}:
    forall S S' (P: @program prefs) f,
      state_closed P f S ->
      state_closed P f S' ->
      initial_state P f S ->
      initial_state P f S' ->
      S ≋ S'.
  Proof.
    induction S as [? IH] using memory_ind'.
    inversion_clear 1 as [??????? Insts2];
      inversion_clear 1 as [??????? Insts2'];
      inversion_clear 1 as [??????? Insts1];
      inversion_clear 1 as [??????? Insts1'].
    repeat match goal with
             H: find_system ?b ?P = _, H': find_system ?b ?P = _ |- _ =>
             rewrite H in H'; inv H'
           end.
    constructor.
    - eapply reset_states_det; eauto with stcsem.
    - unfold find_inst in *.
      split.
      + setoid_rewrite Env.In_find.
        split; intros (?& Find).
        * apply Insts2 in Find as (?& Hin &?).
          apply Insts1' in Hin as (?&?&?); eauto.
        * apply Insts2' in Find as (?& Hin &?).
          apply Insts1 in Hin as (?&?&?); eauto.
      + setoid_rewrite Env.Props.P.F.find_mapsto_iff.
        intros * Find Find'.
        pose proof Find as Find1; pose proof Find' as Find1'.
        apply Insts2 in Find as (?& Hin &?); apply Insts2' in Find' as (?& Hin' &?).
        pose proof Hin; pose proof Hin'.
        apply Insts1 in Hin as (?& Find2 &?); apply Insts1' in Hin' as (?& Find2' & ?).
        rewrite Find2 in Find1; inv Find1; rewrite Find2' in Find1'; inv Find1'.
        assert (x = x0) as E
            by (eapply NoDupMembers_det; eauto; apply s_nodup_subs).
        eapply IH; subst; eauto.
  Qed.

  Definition last_reset_clocks_have_sem b R tcs :=
    forall x ckrs,
      Last_with_reset_in x ckrs tcs ->
      Forall (fun ckr => exists r, sem_clock_instant b R ckr r) ckrs.

  Lemma last_reset_clocks_have_sem_cons: forall b R tc tcs,
      last_reset_clocks_have_sem b R (tc::tcs) ->
      last_reset_clocks_have_sem b R tcs.
  Proof.
    intros * Reset.
    unfold last_reset_clocks_have_sem in *.
    intros * Hin. eapply Reset. right; eauto.
  Qed.

  Corollary last_reset_clocks_have_sem_app: forall b R tcs tcs',
      last_reset_clocks_have_sem b R (tcs' ++ tcs) ->
      last_reset_clocks_have_sem b R tcs.
  Proof.
    induction tcs'; intros * Resets; auto.
    apply last_reset_clocks_have_sem_cons in Resets; auto.
  Qed.

  Lemma sem_trconstrs_last_reset_clocks' {prefs}:
    forall S I S' (P: @program prefs) R b tcs tcs',
      Forall (sem_trconstr P b R S I S') (tcs' ++ tcs) ->
      last_consistency (tcs' ++ tcs) ->
      last_reset_clocks_have_sem b (var_env R) tcs.
  Proof.
    unfold last_reset_clocks_have_sem.
    induction tcs; intros * Sem Reset * Hin; inv Hin.
    - inv H0.
      unfold last_consistency in Reset.
      assert (Last_with_reset_in x ckrs (tcs' ++ TcUpdate ck ckrs (UpdLast x e) :: tcs)) as LastWithReset.
      { apply Exists_app. left. constructor. }
      eapply Forall_forall. intros ? Hin.
      eapply Reset in LastWithReset as (Reset'&_). specialize (Reset' Hin).
      eapply Exists_exists in Reset' as (?&Hin'&Reset'). inv Reset'.
      eapply Forall_forall in Sem; eauto. inv Sem; eauto.
    - specialize (IHtcs (tcs' ++ [a])).
      rewrite <-app_assoc in IHtcs; simpl in IHtcs; eauto.
  Qed.

  Corollary sem_trconstrs_last_reset_clocks {prefs}:
    forall S I S' (P: @program prefs) R b tcs,
      Forall (sem_trconstr P b R S I S') tcs ->
      last_consistency tcs ->
      last_reset_clocks_have_sem b (var_env R) tcs.
  Proof.
    intros.
    eapply sem_trconstrs_last_reset_clocks' with (tcs':=[]); simpl; eauto.
  Qed.

  Definition next_reset_clocks_have_sem b R tcs :=
    forall x ckrs,
      Next_with_reset_in x ckrs tcs ->
      Forall (fun ckr => exists r, sem_clock_instant b R ckr r) ckrs.

  Lemma next_reset_clocks_have_sem_cons: forall b R tc tcs,
      next_reset_clocks_have_sem b R (tc::tcs) ->
      next_reset_clocks_have_sem b R tcs.
  Proof.
    intros * Reset.
    unfold next_reset_clocks_have_sem in *.
    intros * Hin. eapply Reset. right; eauto.
  Qed.

  Corollary next_reset_clocks_have_sem_app: forall b R tcs tcs',
      next_reset_clocks_have_sem b R (tcs' ++ tcs) ->
      next_reset_clocks_have_sem b R tcs.
  Proof.
    induction tcs'; intros * Resets; auto.
    apply next_reset_clocks_have_sem_cons in Resets; auto.
  Qed.

  Lemma sem_trconstrs_next_reset_clocks' {prefs}:
    forall S I S' (P: @program prefs) R b tcs tcs',
      Forall (sem_trconstr P b R S I S') (tcs' ++ tcs) ->
      next_consistency (tcs' ++ tcs) ->
      next_reset_clocks_have_sem b (var_env R) tcs.
  Proof.
    unfold next_reset_clocks_have_sem.
    induction tcs; intros * Sem Reset * Hin; inv Hin.
    - inv H0.
      unfold next_consistency in Reset.
      assert (Next_with_reset_in x ckrs (tcs' ++ TcUpdate ck ckrs (UpdNext x e) :: tcs)) as NextWithReset.
      { apply Exists_app. left. constructor. }
      eapply Forall_forall. intros ? Hin.
      eapply Reset in NextWithReset as (Reset'&_). specialize (Reset' Hin).
      eapply Exists_exists in Reset' as (?&Hin'&Reset'). inv Reset'.
      eapply Forall_forall in Sem; eauto. inv Sem; eauto.
    - specialize (IHtcs (tcs' ++ [a])).
      rewrite <-app_assoc in IHtcs; simpl in IHtcs; eauto.
  Qed.

  Corollary sem_trconstrs_next_reset_clocks {prefs}:
    forall S I S' (P: @program prefs) R b tcs,
      Forall (sem_trconstr P b R S I S') tcs ->
      next_consistency tcs ->
      next_reset_clocks_have_sem b (var_env R) tcs.
  Proof.
    intros.
    eapply sem_trconstrs_next_reset_clocks' with (tcs':=[]); simpl; eauto.
  Qed.

  Definition inst_reset_clocks_have_sem b R tcs :=
    forall i ckrs,
      Inst_with_reset_in i ckrs tcs ->
      Forall (fun ckr => exists r, sem_clock_instant b R ckr r) ckrs.

  Lemma inst_reset_clocks_have_sem_cons: forall b R tc tcs,
      inst_reset_clocks_have_sem b R (tc::tcs) ->
      inst_reset_clocks_have_sem b R tcs.
  Proof.
    intros * Reset.
    unfold inst_reset_clocks_have_sem in *.
    intros * Hin. eapply Reset. right; eauto.
  Qed.

  Corollary inst_reset_clocks_have_sem_app: forall b R tcs tcs',
      inst_reset_clocks_have_sem b R (tcs' ++ tcs) ->
      inst_reset_clocks_have_sem b R tcs.
  Proof.
    induction tcs'; intros * Resets; auto.
    apply inst_reset_clocks_have_sem_cons in Resets; auto.
  Qed.

  Lemma sem_trconstrs_inst_reset_clocks' {prefs}:
    forall S I S' (P: @program prefs) R b tcs tcs',
      Forall (sem_trconstr P b R S I S') (tcs' ++ tcs) ->
      inst_consistency (tcs' ++ tcs) ->
      inst_reset_clocks_have_sem b (var_env R) tcs.
  Proof.
    unfold inst_reset_clocks_have_sem.
    induction tcs; intros * Sem Reset * Hin; inv Hin.
    - inv H0.
      unfold inst_consistency in Reset.
      assert (Inst_with_reset_in i ckrs (tcs' ++ TcUpdate ck ckrs (UpdInst i ys f es) :: tcs)) as StepWithReset.
      { apply Exists_app. left. constructor. }
      eapply Forall_forall. intros ? Hin.
      eapply Reset in StepWithReset as (Reset'&_). specialize (Reset' Hin).
      eapply Exists_exists in Reset' as (?&Hin'&Reset'). inv Reset'.
      eapply Forall_forall in Sem; eauto. inv Sem; eauto.
    - specialize (IHtcs (tcs' ++ [a])).
      rewrite <-app_assoc in IHtcs; simpl in IHtcs; eauto.
  Qed.

  Corollary sem_trconstrs_inst_reset_clocks {prefs}:
    forall S I S' (P: @program prefs) R b tcs,
      Forall (sem_trconstr P b R S I S') tcs ->
      inst_consistency tcs ->
      inst_reset_clocks_have_sem b (var_env R) tcs.
  Proof.
    intros.
    eapply sem_trconstrs_inst_reset_clocks' with (tcs':=[]); simpl; eauto.
  Qed.

  Lemma sem_trconstrs_absent_states {prefs}:
    forall S I S' (P: @program prefs) tcs R,
    (forall f xs S ys S',
        sem_system P f S xs ys S' ->
        absent_list xs ->
        S' ≋ S) ->
    state_closed_states (map fst (lasts_of tcs ++ nexts_of tcs)) S ->
    state_closed_states (map fst (lasts_of tcs ++ nexts_of tcs)) S' ->
    state_closed_insts P (insts_of tcs) S ->
    state_closed_insts P (insts_of tcs) S' ->
    last_reset_clocks_have_sem false (var_env R) tcs ->
    next_reset_clocks_have_sem false (var_env R) tcs ->
    inst_reset_clocks_have_sem false (var_env R) tcs ->
    Forall (sem_trconstr P false R S I S') tcs ->
    S' ≋ S.
  Proof.
    intros * IH States States' Insts Insts' LResets NResets IResets Htcs.
    constructor.

    - clear Insts Insts' IResets.
      intros x.
      unfold state_closed_states, find_val in *.
      specialize (States x); specialize (States' x).
      assert (In x (map fst (lasts_of tcs ++ nexts_of tcs)) ->
              Env.find x (values S') = Env.find x (values S)) as In.
      { intros * Hin.
        clear States States'.
        rewrite map_app, in_app_iff in Hin. destruct Hin as [Hin|Hin].
        - clear NResets.
          induction tcs as [|[|? []|?? []]]; simpl in Hin; try contradiction;
            assert (Resets':=LResets); apply last_reset_clocks_have_sem_cons in Resets';
            inversion_clear Htcs as [|?? Htc]; auto.
          destruct Hin; auto; subst.
          inversion_clear Htc as [| | |??????????? ClockR Find Exp _ _ Find'| |]; unfold find_val in *.
          inversion Exp as [???? Clock|];
            [contradict Clock; apply not_subrate_clock|]; subst.
          rewrite Find', ClockR; try congruence.
          eapply Forall_impl; [|eapply LResets]. 2:left; auto with stcsyntax.
          intros ? (?&Clock).
          assert (Clock':=Clock). apply not_subrate_clock_impl in Clock; subst; auto.
        - clear LResets.
          induction tcs as [|[|? []|?? []]]; simpl in Hin; try contradiction;
            assert (Resets':=NResets); apply next_reset_clocks_have_sem_cons in Resets';
            inversion_clear Htcs as [|?? Htc]; auto.
          destruct Hin; auto; subst.
          inversion_clear Htc as [| | | |??????????? ClockR Find Exp _ Find'|]; unfold find_val in *.
          inversion Exp as [???? Clock|];
            [contradict Clock; apply not_subrate_clock|]; subst.
          rewrite Find', ClockR; try congruence.
          eapply Forall_impl; [|eapply NResets]. 2:left; auto with stcsyntax.
          intros ? (?&Clock).
          assert (Clock':=Clock). apply not_subrate_clock_impl in Clock; subst; auto.
      }
      destruct (Env.find x (values S)) eqn: Find;
        destruct (Env.find x (values S')) eqn: Find'; auto.
      all:eapply In.
      + apply States. congruence.
      + apply States. congruence.
      + apply States'. congruence.

    - clear States States' LResets NResets.
      constructor.
      + setoid_rewrite Env.In_find.
        unfold state_closed_insts in *.
        intro s; split; intros (?& Find).
        *{ apply Insts' in Find as (b & Hin &?).
           apply insts_of_In' in Hin as (?&?& cks &?& Hin).
           pose proof Htcs as Htcs'.
           eapply Forall_forall in Htcs; eauto.
           inversion_clear Htcs as [| | | | |??????????????? ClockR].
           destruct (find_inst s S) eqn:Hfind; eauto.
           assert (None ⌈≋⌉ Some Ii) as contra. 2:inv contra.
           apply ClockR.
           eapply Forall_impl; [|eapply IResets]. 2:eapply Exists_exists; eexists; split; eauto with stcsyntax.
           intros ? (?&Clock).
           assert (Clock':=Clock). apply not_subrate_clock_impl in Clock; subst; auto.
         }
        * apply Insts in Find as (b & Hin &?).
          apply insts_of_In' in Hin as (?&?&?&?& Hin).
          eapply Forall_forall in Htcs; eauto.
          inv Htcs; eauto.
      + setoid_rewrite Env.Props.P.F.find_mapsto_iff.
        intros s e e' Find' Find.
        pose proof Find as Hin.
        apply Insts in Hin as (b & Hin &?).
        apply insts_of_In' in Hin as (?&?& rst &?& Hin).
        pose proof Htcs as Htcs'.
        eapply Forall_forall in Htcs; eauto.
        inversion_clear Htcs as [| | | | |??????????????? ClockR FindI' Exps Clk SemSystem ? Find1'].
        unfold find_inst in *; rewrite Find1' in Find'; inv Find'.
        assert (absent_list xs) by (eapply clock_of_instant_false, not_subrate_clock_impl; eauto).
        apply IH in SemSystem; auto.
        assert (Env.find s (instances S) ⌈≋⌉ Some Ii) as FindI.
        { apply ClockR. eapply Forall_impl; [|eapply IResets]. 2:eapply Exists_exists; eexists; split; eauto with stcsyntax.
          intros ? (?&Clock).
          assert (Clock':=Clock). apply not_subrate_clock_impl in Clock; subst; auto.
        } clear ClockR.
        rewrite SemSystem. rewrite Find in FindI. inv FindI.
        symmetry; auto.
  Qed.

  Lemma sem_trconstrs_absent_vars {prefs}:
    forall tcs S I S' (P: @program prefs) R x,
    (forall f xs S ys S',
        sem_system P f S xs ys S' ->
        absent_list xs ->
        absent_list ys) ->
    In x (variables tcs) ->
    Forall (sem_trconstr P false R S I S') tcs ->
    sem_var_instant R (Var x) absent.
  Proof.
    unfold variables.
    induction tcs as [|[|? []|?? []]]; simpl; intros * IH Spec Htcs; try contradiction;
      inversion_clear Htcs as [|?? Htc];
      inversion_clear Htc as [????????? Exp| | | | |]; eauto.
    - destruct Spec; eauto; subst.
      apply sem_arhs_instant_absent in Exp; subst; auto.
    - assert (absent_list xs) as Abs
          by (eapply clock_of_instant_false, not_subrate_clock_impl; eauto).
      eapply IH in Abs; eauto.
      apply in_app in Spec as [Hin|]; eauto.
      eapply Forall2_in_left in Hin; eauto.
      destruct Hin as (v &?&?).
      eapply Forall_forall in Abs; eauto.
      subst; auto.
  Qed.

  Lemma sem_system_absent {prefs}:
    forall (P: @program prefs) f xs S ys S',
      Ordered_systems P ->
      sem_system P f S xs ys S' ->
      absent_list xs ->
      absent_list ys /\ S' ≋ S.
  Proof.
    intros [] * Ord Sem Abs.
    revert dependent xs; revert f S S' ys.
    induction systems0 as [|system]; intros;
      inversion_clear Sem as [????????? Find Ins ?? Htcs Closed ClosedI Closed'];
      try now inv Find.
    pose proof Find.
    eapply find_unit_cons in Find as [[E Find]|[E Find]]; simpl; eauto.
    - inv Find.
      assert ( ~ Is_system_in (s_name system) (s_tcs system))
        by (eapply find_system_not_Is_system_in; eauto).
      apply sem_trconstrs_cons in Htcs; auto.
      assert (clock_of_instant xs = false) as E by (apply clock_of_instant_false; auto);
        rewrite E in *.
      inv Ord; split.
      + apply Forall_forall; intros v Hin.
        eapply Forall2_in_right in Hin; eauto.
        destruct Hin as (x & ?&?).
        eapply sem_var_instant_det; eauto.
        eapply sem_trconstrs_absent_vars; eauto.
        * intros; eapply IHsystems0; eauto.
        * rewrite <-s_vars_out_in_tcs.
          apply in_app; auto.
      + inversion_clear Closed as [?????? States Insts];
          inversion_clear Closed' as [?????? States' Insts'];
          inversion_clear ClosedI as [?????? StatesI _].
        repeat match goal with
                 H: find_system ?b ?P = _, H': find_system ?b ?P = _ |- _ =>
                 rewrite H in H'; inv H'
               end.
        rewrite map_app, s_lasts_in_tcs, s_nexts_in_tcs, <-map_app in States, States', StatesI.
        setoid_rewrite s_subs_insts_of in Insts;
          setoid_rewrite s_subs_insts_of in Insts'.
        eapply sem_trconstrs_absent_states in Htcs; eauto.
        * intros; eapply IHsystems0; eauto.
        * eapply sem_trconstrs_last_reset_clocks; eauto using s_last_consistency.
        * eapply sem_trconstrs_next_reset_clocks; eauto using s_next_consistency.
        * eapply sem_trconstrs_inst_reset_clocks; eauto using s_inst_consistency.
    - pose proof Ord; inv Ord; eapply IHsystems0; eauto.
      rewrite <-state_closed_other in Closed, ClosedI, Closed'; eauto.
      eapply SSystem with (I := I); eauto.
      apply sem_trconstrs_cons in Htcs; eauto.
      eapply find_system_other_not_Is_system_in; eauto.
  Qed.

  Lemma state_closed_states_empty:
    forall states,
      state_closed_states states (empty_memory _).
  Proof.
    unfold state_closed_states; setoid_rewrite find_val_gempty; intuition.
  Qed.

  Lemma state_closed_empty {prefs}:
    forall (P: @program prefs) f s P',
      find_system f P = Some (s, P') ->
      state_closed P f (empty_memory _).
  Proof.
    intros * Find.
    econstructor; eauto.
    - apply state_closed_states_empty.
    - setoid_rewrite find_inst_gempty; congruence.
  Qed.

  Lemma reset_or_not_reset_dec : forall b R ckrs,
      Forall (fun ckr => exists r, sem_clock_instant b R ckr r) ckrs ->
      Forall (fun ckr => sem_clock_instant b R ckr false) ckrs \/
      Exists (fun ckr => sem_clock_instant b R ckr true) ckrs.
  Proof.
    intros * Hf.
    induction Hf as [|??([|]&?)]; auto.
    destruct IHHf; auto.
  Qed.

  Lemma sem_system_find_val {prefs}:
    forall (P: @program prefs) f S xs ys S' x s P',
      sem_system P f S xs ys S' ->
      find_system f P = Some (s, P') ->
      In x (map fst (s_lasts s ++ s_nexts s)) ->
      find_val x S <> None.
  Proof.
    inversion_clear 1 as [????????? Find ??? Htcs]; intros Find' Hin.
    rewrite Find in Find'; inv Find'.
     assert (forall ckrs ck, Last_with_reset_in x ckrs (s_tcs s) -> In ck ckrs -> find_val x S <> None) as LastReset.
    { clear Hin. intros * Hlast Hin.
      apply s_last_consistency in Hlast. rewrite Hlast in Hin. clear Hlast.
      induction Htcs as [|[] ? Htc]; simpl in *;
        inversion_clear Hin as [?? Hin'|?? Hin']; auto; inv Hin'.
      inversion_clear Htc as [|??????????? Find'| | | |].
      congruence.
    }
    assert (last_reset_clocks_have_sem (clock_of_instant xs) (var_env R) (s_tcs s)) as LResets.
    { eapply sem_trconstrs_last_reset_clocks; eauto using s_last_consistency. }
    assert (forall ckrs ck, Next_with_reset_in x ckrs (s_tcs s) -> In ck ckrs -> find_val x S <> None) as NextReset.
    { clear Hin. intros * Hnext Hin.
      apply s_next_consistency in Hnext. rewrite Hnext in Hin. clear Hnext LastReset LResets.
      induction Htcs as [|[] ? Htc]; simpl in *;
        inversion_clear Hin as [?? Hin'|?? Hin']; auto; inv Hin'.
      inversion_clear Htc as [|??????????? Find'| | | |].
      congruence.
    }
    assert (next_reset_clocks_have_sem (clock_of_instant xs) (var_env R) (s_tcs s)) as NResets.
    { eapply sem_trconstrs_next_reset_clocks; eauto using s_next_consistency. }

    rewrite map_app, s_lasts_in_tcs, s_nexts_in_tcs in Hin.
    apply in_app_iff in Hin as [Hin|Hin].
    - apply lasts_of_In, Exists_exists in Hin as (?&?&Upd). inv Upd.
      assert (Last_with_reset_in x ckrs (s_tcs s)) as LR
          by (apply Exists_exists; do 2 esplit; eauto; constructor).
      eapply reset_or_not_reset_dec in LResets as [NotReset|Reset]; eauto.
      + simpl_Forall. inv Htcs. eapply not_None_is_Some; eauto.
      + simpl_Exists. apply s_last_consistency in LR.
        apply LR, Exists_exists in Hin as (?&?&Res). inv Res.
        simpl_Forall. inv Htcs.
        eapply sem_clock_instant_det in Reset; eauto; subst. eapply not_None_is_Some; eauto.
    - apply nexts_of_In, Exists_exists in Hin as (?&?&Upd). inv Upd.
      assert (Next_with_reset_in x ckrs (s_tcs s)) as LR
          by (apply Exists_exists; do 2 esplit; eauto; constructor).
      eapply reset_or_not_reset_dec in NResets as [NotReset|Reset]; eauto.
      + simpl_Forall. inv Htcs. eapply not_None_is_Some; eauto.
      + simpl_Exists. apply s_next_consistency in LR.
        apply LR, Exists_exists in Hin as (?&?&Res). inv Res.
        simpl_Forall. inv Htcs.
        eapply sem_clock_instant_det in Reset; eauto; subst. eapply not_None_is_Some; eauto.
  Qed.

  Lemma sem_system_find_valI {prefs}:
    forall (P: @program prefs) (s: @system prefs) b R S I S' x v,
      Forall (sem_trconstr P b R S I S') (s_tcs s) ->
      In x (map fst (s_lasts s)) ->
      sem_var_instant R (Last x) (present v) ->
      find_val x I = Some v.
  Proof.
    intros * Sem Hin Var.
    rewrite s_lasts_in_tcs, <-lasts_of_In in Hin.
    eapply Exists_exists in Hin as (?&Hin&Last). inv Last.
    eapply Forall_forall in Sem; eauto. inv Sem.
    eapply sem_var_instant_det in Var; [|eauto].
    destruct v'; inv Var; auto.
  Qed.

End STCSEMANTICS.

Module StcSemanticsFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Ids Op)
       (Cks   : CLOCKS      Ids Op OpAux)
       (CESyn : CESYNTAX    Ids Op OpAux Cks)
       (Syn   : STCSYNTAX   Ids Op OpAux Cks CESyn)
       (Ord   : STCORDERED  Ids Op OpAux Cks CESyn Syn)
       (Str   : INDEXEDSTREAMS  Ids Op OpAux Cks)
       (CESem : CESEMANTICS Ids Op OpAux Cks CESyn Str)
<: STCSEMANTICS Ids Op OpAux Cks CESyn Syn Ord Str CESem.
  Include STCSEMANTICS Ids Op OpAux Cks CESyn Syn Ord Str CESem.
End StcSemanticsFun.
