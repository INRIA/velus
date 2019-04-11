Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Permutation.
Require Import Setoid.
Require Import Morphisms.

Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.CoreExpr.CESyntax.
Require Import Velus.RMemory.
Require Import Velus.SyBloc.SBSyntax.
Require Import Velus.SyBloc.SBIsBlock.
Require Import Velus.SyBloc.SBOrdered.
Require Import Velus.CoreExpr.Stream.
Require Import Velus.CoreExpr.CESemantics.

Module Type SBSEMANTICS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Op)
       (Import CESyn : CESYNTAX        Op)
       (Import Syn   : SBSYNTAX    Ids Op       CESyn)
       (Import Block : SBISBLOCK   Ids Op       CESyn Syn)
       (Import Ord   : SBORDERED   Ids Op       CESyn Syn Block)
       (Import Str   : STREAM          Op OpAux)
       (Import CESem : CESEMANTICS Ids Op OpAux CESyn Str).

  Definition state := memory val.
  Definition transient_states := Env.t state.

  Definition state_closed_lasts (lasts: list ident) (S: state) : Prop :=
    forall x, find_val x S <> None -> In x lasts.

  Inductive state_closed: program -> ident -> state -> Prop :=
    state_closed_intro:
      forall P b S bl P',
        find_block b P = Some (bl, P') ->
        state_closed_lasts (map fst bl.(b_lasts)) S ->
        (forall x S',
            find_inst x S = Some S' ->
            exists b',
              In (x, b') (b_blocks bl)
              /\ state_closed P' b' S') ->
        state_closed P b S.

  Definition state_closed_insts (P: program) (blocks: list (ident * ident)) (S: state) : Prop :=
    forall s Ss,
      find_inst s S = Some Ss ->
      exists b, In (s, b) blocks
           /\ state_closed P b Ss.

  Definition transient_states_closed (P: program) (blocks: list (ident * ident)) (I: transient_states) : Prop :=
    Forall (fun sb =>
              forall Is,
                Env.find (fst sb) I = Some Is ->
                state_closed P (snd sb) Is)
           blocks.

  Definition reset_lasts (bl: block) (S0: state) : Prop :=
    forall x c ck,
      In (x, (c, ck)) bl.(b_lasts) ->
      find_val x S0 = Some (sem_const c).

  Inductive initial_state: program -> ident -> state -> Prop :=
    initial_state_intro:
      forall P b S0 bl P',
        find_block b P = Some (bl, P') ->
        reset_lasts bl S0 ->
        (forall x b',
            In (x, b') bl.(b_blocks) ->
            exists S0',
              find_inst x S0 = Some S0'
              /\ initial_state P' b' S0') ->
        initial_state P b S0.

  Definition same_clock (vs: list value) : Prop :=
    absent_list vs \/ present_list vs.

  Section Semantics.

    Variable P: program.

    Inductive sem_equation: bool -> env -> state -> transient_states -> state -> equation -> Prop :=
    | SEqDef:
        forall base R S I S' x v ck ce,
          sem_caexp_instant base R ck ce v ->
          sem_var_instant R x v ->
          sem_equation base R S I S' (EqDef x ck ce)
    | SEqNext:
        forall base R S I S' x ck e c v',
          find_val x S = Some c ->
          sem_var_instant R x (match v' with present _ => present c | absent => absent end) ->
          sem_laexp_instant base R ck e v' ->
          find_val x S' = Some (match v' with present c' => c' | absent => c end) ->
          sem_equation base R S I S' (EqNext x ck e)
    | SEqReset:
        forall base R S I S' ck b s r Is,
          sem_clock_instant base R ck r ->
          Env.find s I = Some Is ->
          (if r
           then initial_state P b Is
           else exists Ss, find_inst s S = Some Ss /\ Is ≋ Ss) ->
          sem_equation base R S I S' (EqReset s ck b)
    | SEqCall:
        forall base R S I S' ys rst ck b s es xs Is os Ss',
          sem_lexps_instant base R es xs ->
          sem_clock_instant base R ck (clock_of_instant xs) ->
          (rst = false -> exists Ss, find_inst s S = Some Ss /\ Is ≋ Ss) ->
          Env.find s I = Some Is ->
          sem_block b Is xs os Ss' ->
          sem_vars_instant R ys os ->
          find_inst s S' = Some Ss' ->
          sem_equation base R S I S' (EqCall s ys ck rst b es)

    with sem_block: ident -> state -> list value -> list value -> state -> Prop :=
           SBlock:
             forall b bl P' S I S' R xs ys,
               find_block b P = Some (bl, P') ->
               sem_vars_instant R (map fst bl.(b_in)) xs ->
               sem_vars_instant R (map fst bl.(b_out)) ys ->
               sem_clocked_vars_instant (clock_of_instant xs) R (idck bl.(b_in)) ->
               Forall (sem_equation (clock_of_instant xs) R S I S') bl.(b_eqs) ->
               state_closed P b S ->
               transient_states_closed P' bl.(b_blocks) I ->
               state_closed P b S' ->
               sem_block b S xs ys S'.

  End Semantics.

  Section sem_block_mult.
    Variable P: program.

    Variable P_equation: bool -> env -> state -> transient_states -> state -> equation -> Prop.
    Variable P_block: ident -> state -> list value -> list value -> state -> Prop.

    Hypothesis EqDefCase:
      forall base R S I S' x v ck ce,
        sem_caexp_instant base R ck ce v ->
        sem_var_instant R x v ->
        P_equation base R S I S' (EqDef x ck ce).

    Hypothesis EqNextCase:
      forall base R S I S' x ck e c v',
        find_val x S = Some c ->
        sem_var_instant R x (match v' with present _ => present c | absent => absent end) ->
        sem_laexp_instant base R ck e v' ->
        find_val x S' = Some (match v' with present c' => c' | absent => c end) ->
        P_equation base R S I S' (EqNext x ck e).

    Hypothesis EqResetCase:
      forall base R S I S' ck b s r Is,
        sem_clock_instant base R ck r ->
        Env.find s I = Some Is ->
        (if r
         then initial_state P b Is
         else exists Ss, find_inst s S = Some Ss /\ Is ≋ Ss) ->
        P_equation base R S I S' (EqReset s ck b).

    Hypothesis EqCallCase:
      forall base R S I S' s ys ck rst b es xs Is os Ss',
        sem_lexps_instant base R es xs ->
        sem_clock_instant base R ck (clock_of_instant xs) ->
        (rst = false -> exists Ss, find_inst s S = Some Ss /\ Is ≋ Ss) ->
        Env.find s I = Some Is ->
        sem_block P b Is xs os Ss' ->
        sem_vars_instant R ys os ->
        find_inst s S' = Some Ss' ->
        P_block b Is xs os Ss' ->
        P_equation base R S I S' (EqCall s ys ck rst b es).

    Hypothesis BlockCase:
      forall b bl P' R S I S' xs ys,
        find_block b P = Some (bl, P') ->
        sem_vars_instant R (map fst bl.(b_in)) xs ->
        sem_vars_instant R (map fst bl.(b_out)) ys ->
        sem_clocked_vars_instant (clock_of_instant xs) R (idck bl.(b_in)) ->
        Forall (sem_equation P (clock_of_instant xs) R S I S') bl.(b_eqs) ->
        state_closed P b S ->
        transient_states_closed P' bl.(b_blocks) I ->
        state_closed P b S' ->
        Forall (P_equation (clock_of_instant xs) R S I S') bl.(b_eqs) ->
        P_block b S xs ys S'.

    Fixpoint sem_equation_mult
             (base: bool) (R: env) (S: state) (I: transient_states) (S': state) (e: equation)
             (Sem: sem_equation P base R S I S' e) {struct Sem}
      : P_equation base R S I S' e
    with sem_block_mult
           (f: ident) (S: state) (xs ys: list value) (S': state)
           (Sem: sem_block P f S xs ys S') {struct Sem}
         : P_block f S xs ys S'.
    Proof.
      - destruct Sem; eauto.
      - destruct Sem.
        eapply BlockCase; eauto.
        match goal with H: Forall _ _ |- _ => induction H; auto end.
    Qed.

    Combined Scheme sem_equation_block_ind from
             sem_equation_mult, sem_block_mult.

  End sem_block_mult.

  CoInductive loop: program -> ident -> stream (list value) -> stream (list value) -> state -> nat -> Prop :=
    loop_intro:
      forall P b xss yss Sn Sn' n,
        (n = 0 -> initial_state P b Sn) ->
        sem_block P b Sn (xss n) (yss n) Sn' ->
        loop P b xss yss Sn' (S n) ->
        loop P b xss yss Sn n.

  Section LoopCoind.

    Variable R: program -> ident -> stream (list value) -> stream (list value) -> state -> nat -> Prop.

    Hypothesis Loop:
      forall P b xss yss Sn n,
        R P b xss yss Sn n ->
        (n = 0 -> initial_state P b Sn)
        /\ exists Sn', sem_block P b Sn (xss n) (yss n) Sn'
                 /\ R P b xss yss Sn' (S n).

    Lemma loop_coind:
      forall P b xss yss S n,
        R P b xss yss S n ->
        loop P b xss yss S n.
    Proof.
      cofix COFIX; intros ** HR.
      apply Loop in HR as (?&?&?&?).
      econstructor; eauto.
    Qed.

  End LoopCoind.

  Add Parametric Morphism block : (reset_lasts block)
      with signature equal_memory ==> Basics.impl
        as reset_lasts_equal_memory.
  Proof.
    intros ** E Rst ??? Hin.
    rewrite <-E; apply Rst in Hin; auto.
  Qed.

  Add Parametric Morphism P f : (initial_state P f)
      with signature equal_memory ==> Basics.impl
        as initial_state_equal_memory.
  Proof.
    intros ** E Init.
    revert dependent P; revert dependent f; revert dependent y.
    induction x as [? IH] using memory_ind'; intros.
    inversion_clear Init as [??????? Spec].
    econstructor; eauto.
    - now rewrite <-E.
    - intros ** Hin.
      apply Spec in Hin as (?& Sub &?).
      pose proof (find_inst_equal_memory x0 E) as Eq;
        rewrite Sub in Eq; simpl in Eq.
      destruct (find_inst x0 y); try contradiction.
      eexists; split; eauto.
  Qed.

  Add Parametric Morphism lasts : (state_closed_lasts lasts)
      with signature equal_memory ==> Basics.impl
        as state_closed_lasts_equal_memory.
  Proof.
    unfold state_closed_lasts.
    intros ** E Closed ? Find.
    apply Closed; rewrite E; auto.
  Qed.

  Add Parametric Morphism P b : (state_closed P b)
      with signature equal_memory ==> Basics.impl
        as state_closed_equal_memory.
  Proof.
    intros m m' E Closed; revert dependent m'; revert dependent b; revert P ;
      induction m as [? IH] using memory_ind'; intros.
    inversion_clear Closed as [??????? Insts].
    econstructor; eauto.
    - now setoid_rewrite <-E.
    - intros ** Sub.
      pose proof (find_inst_equal_memory x E) as Eq.
      rewrite Sub in Eq.
      destruct (find_inst x m) eqn: Find; try contradiction.
      pose proof Find as Find'.
      apply Insts in Find' as (?&?&?).
      eexists; intuition; eauto.
  Qed.

  Add Parametric Morphism P : (transient_states_closed P)
      with signature (fun xs xs' => forall x, In x xs <-> In x xs') ==> eq ==> Basics.impl
        as transient_states_closed_In.
  Proof.
    intros ** E ? Closed.
    apply Forall_forall; intros ** Hin ? Find.
    eapply E, Forall_forall in Hin; eauto.
    auto.
  Qed.

  Add Parametric Morphism P : (transient_states_closed P)
      with signature @Permutation (ident * ident) ==> eq ==> Basics.impl
        as transient_states_closed_Permutation.
  Proof.
    intros ** E ? Closed.
    apply Forall_forall; intros ** Hin ? Find.
    rewrite <-E in Hin; eapply Forall_forall in Hin; eauto.
    auto.
  Qed.

  Add Parametric Morphism P f: (sem_block P f)
      with signature equal_memory ==> eq ==> eq ==> equal_memory ==> Basics.impl
        as sem_block_equal_memory.
  Proof.
    intros S1 S2 ??? S1' S2' ** Sem.
    revert dependent S2; revert dependent S2'.
    induction Sem as [| |??????????? Find Init|
                      ????????????????? Spec Find ?? Sub|] using sem_block_mult with
                   (P_equation := fun base R S1 I1 S1' eq =>
                                    forall S2 S2' I2,
                                      S1 ≋ S2 ->
                                      Env.Equiv equal_memory I1 I2 ->
                                      S1' ≋ S2' ->
                                      sem_equation P base R S2 I2 S2' eq);
      eauto using sem_equation.
    - intros ** E EI E'.
      econstructor; eauto.
      + now rewrite <-E.
      + now rewrite <-E'.
    - intros ** E EI E'.
      pose proof (find_equiv_memory s EI) as Eq;
        setoid_rewrite Find in Eq; simpl in Eq.
      destruct (Env.find s I2) eqn: Find'; try contradiction.
      destruct r.
      + econstructor; eauto; simpl.
        now rewrite <-Eq.
      + destruct Init as (?& Sub &?).
        pose proof (find_inst_equal_memory s E) as Eq'.
        rewrite Sub in Eq'.
        destruct (find_inst s S2) eqn: Init'; try contradiction.
        econstructor; eauto; simpl.
        eexists; split; eauto.
        now rewrite <-Eq, <-Eq'.
    - intros ** E EI E'.
      pose proof (find_equiv_memory s EI) as Eq.
      rewrite Find in Eq.
      destruct (Env.find s I2) eqn: Find'; try contradiction.
      pose proof (find_inst_equal_memory s E') as Eq'.
      rewrite Sub in Eq'.
      destruct (find_inst s S2') eqn: Sub'; try contradiction.
      destruct rst.
      + econstructor; eauto.
        discriminate.
      + pose proof (find_inst_equal_memory s E) as Eq''.
        destruct Spec as (?& Sub_i &?); auto.
        rewrite Sub_i in Eq''.
        destruct (find_inst s S2) eqn: FInd; try contradiction.
        eapply SEqCall with (Is := m); eauto.
        eexists; split; eauto. now rewrite <-Eq, <-Eq''.
    - intros ? E ? E'.
      econstructor; eauto.
      + induction (b_eqs bl); auto;
          repeat match goal with H: Forall ?P (_ :: _) |- _ => inv H end.
        constructor; auto.
        assert (Env.Equiv equal_memory I I) by reflexivity;
          auto.
      + now rewrite <-E'.
      + now rewrite <-E.
  Qed.

  Add Parametric Morphism : (state_closed_lasts)
      with signature (@Permutation ident) ==> eq ==> Basics.impl
        as state_closed_lasts_permutation.
  Proof.
    unfold state_closed_lasts.
    intros ** E ? Closed ? Find.
    rewrite <-E; auto.
  Qed.

  Add Parametric Morphism P b xss yss : (loop P b xss yss)
      with signature equal_memory ==> eq ==> Basics.impl
        as loop_equal_memory.
  Proof.
    cofix COFIX.
    intros ** E n Loop.
    inv Loop.
    econstructor; eauto.
    - intros; rewrite <-E; auto.
    - eapply sem_block_equal_memory; eauto.
      reflexivity.
  Qed.

  Lemma initial_state_other:
    forall S0 bl P b,
      b_name bl <> b ->
      (initial_state P b S0 <->
      initial_state (bl :: P) b S0).
  Proof.
    split; inversion_clear 1 as [????? Find]; econstructor; eauto.
    - rewrite find_block_other; eauto.
    - rewrite find_block_other in Find; eauto.
  Qed.

  Fact reset_lasts_add_inst:
    forall bl S0 x S0x,
      reset_lasts bl S0 ->
      reset_lasts bl (add_inst x S0x S0).
  Proof.
    unfold reset_lasts;
      setoid_rewrite find_val_add_inst; auto.
  Qed.

  Fact state_closed_lasts_add_inst:
    forall lasts S x Sx,
      state_closed_lasts lasts S ->
      state_closed_lasts lasts (add_inst x Sx S).
  Proof.
    unfold state_closed_lasts;
      setoid_rewrite find_val_add_inst; auto.
  Qed.

  Lemma state_closed_other:
    forall S bl P b,
      b_name bl <> b ->
      (state_closed P b S <->
      state_closed (bl :: P) b S).
  Proof.
    split; inversion_clear 1 as [????? Find]; econstructor; eauto.
    - rewrite find_block_other; eauto.
    - rewrite find_block_other in Find; eauto.
  Qed.

  Lemma state_closed_find_block_other:
    forall S bl P P' b s b',
      Ordered_blocks P ->
      find_block b P = Some (bl, P') ->
      In (s, b') bl.(b_blocks) ->
      state_closed P b' S ->
      state_closed P' b' S.
  Proof.
    intros ** Ord Find Hin Closed; inversion_clear Closed as [????? Find'].
    econstructor; eauto.
    apply find_block_app in Find as (?&?&?); subst.
    apply Ordered_blocks_split in Ord.
    eapply Forall_forall in Ord as (FindNone & Neq &?&?&?); eauto; simpl in *.
    rewrite find_block_app', FindNone in Find'.
    simpl in Find'; destruct (ident_eqb (b_name bl) b') eqn:Eq; auto.
    apply ident_eqb_eq in Eq; congruence.
  Qed.

  Lemma transient_states_closed_find_block_other:
    forall I bl P P' b,
      Ordered_blocks P ->
      find_block b P = Some (bl, P') ->
      transient_states_closed P bl.(b_blocks) I ->
      transient_states_closed P' bl.(b_blocks) I.
  Proof.
    intros ** Ord Find Closed.
    apply Forall_forall; intros ** () ???.
    eapply Forall_forall in Closed; eauto.
    eapply state_closed_find_block_other; eauto.
  Qed.

  Lemma transient_states_closed_cons:
    forall I bl P,
      Ordered_blocks (bl :: P) ->
      transient_states_closed P bl.(b_blocks) I ->
      transient_states_closed (bl :: P) bl.(b_blocks) I.
  Proof.
    intros ** Ord Closed; inversion_clear Ord as [|??? Blocks].
    apply Forall_forall; intros ** () Hin ? Find.
    eapply Forall_forall in Closed; eauto.
    eapply Forall_forall in Blocks as (?&?); eauto.
    apply state_closed_other; auto.
  Qed.

  Lemma sem_block_cons:
    forall P b f xs S S' ys,
      Ordered_blocks (b :: P) ->
      sem_block (b :: P) f xs S S' ys ->
      b.(b_name) <> f ->
      sem_block P f xs S S' ys.
  Proof.
    intros ** Hord Hsem Hnf.
    revert Hnf.
    induction Hsem as [| | |?????????????????????? IH|
                       ????????? Hf ???? Closed ? Closed' IH]
                        using sem_block_mult
      with (P_equation := fun bk H S I S' eq =>
                            ~Is_block_in_eq b.(b_name) eq ->
                            sem_equation P bk H S I S' eq);
      eauto using sem_equation.
    - intro Hnin; econstructor; eauto.
      destruct r; eauto.
      rewrite initial_state_other; eauto.
      intro E; apply Hnin; rewrite E; constructor.
    - intro Hnin; econstructor; eauto.
      apply IH; intro E; apply Hnin; rewrite E; constructor.
    - intros.
      pose proof Hf.
      rewrite find_block_other in Hf; auto.
      rewrite <-state_closed_other in Closed, Closed'; auto.
      econstructor; eauto.
      eapply find_block_later_not_Is_block_in in Hord; eauto.
      apply Forall_forall; intros.
      eapply Forall_forall in IH; eauto.
      apply IH.
      intro; apply Hord.
      apply Exists_exists; eauto.
  Qed.

  Lemma sem_block_cons2:
    forall b P f xs S S' ys,
      Ordered_blocks (b :: P) ->
      sem_block P f xs S S' ys ->
      sem_block (b :: P) f xs S S' ys.
  Proof.
    intros ** Hord Hsem.
    induction Hsem as [| | | |
                       ????????? Hfind ???? Closed ? Closed' IHeqs] using sem_block_mult
      with (P_equation := fun bk H S I S' eq =>
                            ~Is_block_in_eq b.(b_name) eq ->
                            sem_equation (b :: P) bk H S I S' eq);
      eauto using sem_equation.
    - intros Notin; econstructor; eauto.
      destruct r; eauto.
      apply initial_state_other; auto.
      intro E; apply Notin; rewrite E; constructor.
    - pose proof Hfind as Hfind'; apply find_block_app in Hfind' as (?& E & FindNone).
      pose proof Hord as Hord'; rewrite E, app_comm_cons in Hord';
        apply Ordered_blocks_split in Hord'.
      inversion_clear Hord as [|???? Hnin].
      assert (b.(b_name) <> b0) as Hnf.
      { intro Hnf.
        rewrite Hnf in *.
        pose proof (find_block_name _ _ _ _ Hfind).
        apply find_block_app in Hfind as (?& Hp &?); subst.
        apply Forall_app in Hnin.
        destruct Hnin as [H' Hfg]; clear H'.
        inv Hfg; congruence.
      }
      rewrite state_closed_other in Closed, Closed'; eauto.
      econstructor; eauto.
      + rewrite find_block_other; eauto.
      + apply Forall_forall.
        rewrite Forall_forall in IHeqs.
        intros ** Hin; apply IHeqs; auto.
        rewrite Forall_forall in Hord'.
        pose proof (b_blocks_in_eqs bl) as BlocksIn.
        intro.
        eapply find_block_later_not_Is_block_in; eauto using Ordered_blocks.
        apply Exists_exists; eauto.
  Qed.

  Lemma sem_equations_cons:
    forall P bk H S I S' eqs b,
      Ordered_blocks (b :: P) ->
      ~ Is_block_in b.(b_name) eqs ->
      (Forall (sem_equation P bk H S I S') eqs <->
       Forall (sem_equation (b :: P) bk H S I S') eqs).
  Proof.
    intros ** Hord Hnini.
    induction eqs as [|eq eqs IH]; [now constructor|].
    apply not_Is_block_in_cons in Hnini as [Hnini Hninis].
    split; intros Hsem; apply Forall_cons2 in Hsem as [Heq Heqs];
      apply IH in Heqs; auto; constructor; auto.
    - destruct Heq; eauto using sem_equation.
      + econstructor; eauto.
        destruct r; eauto.
        apply initial_state_other; auto.
        intro E; apply Hnini; rewrite E; constructor.
      + eauto using sem_equation, sem_block_cons2.
    - destruct Heq; eauto using sem_equation.
      + econstructor; eauto.
        destruct r; auto.
        rewrite initial_state_other; eauto.
        intro E; apply Hnini; rewrite E; constructor.
      + econstructor; eauto.
        eapply sem_block_cons; eauto.
        intro E; apply Hnini; rewrite E; constructor.
  Qed.

  Lemma reset_lasts_det:
    forall P b S S' bl P',
      state_closed P b S ->
      state_closed P b S' ->
      find_block b P = Some (bl, P') ->
      reset_lasts bl S ->
      reset_lasts bl S' ->
      Env.Equal (values S) (values S').
  Proof.
    intros ** Closed Closed' Find Rst Rst' x.
    inversion_clear Closed as [????? Find' Spec];
      rewrite Find' in Find; inv Find.
    inversion_clear Closed' as [????? Find Spec'];
      rewrite Find' in Find; inv Find.
    unfold state_closed_lasts, reset_lasts, find_val in *.
    destruct (Env.find x (values S)) eqn: E, (Env.find x (values S')) eqn: E'; auto.
    - assert (Env.find x (values S) <> None) as E1 by (apply not_None_is_Some; eauto).
      apply Spec, fst_InMembers, InMembers_In in E1 as (()& Hin).
      pose proof Hin as Hin'.
      apply Rst in Hin; apply Rst' in Hin'.
      congruence.
    - assert (Env.find x (values S) <> None) as E1 by (apply not_None_is_Some; eauto).
      apply Spec, fst_InMembers, InMembers_In in E1 as (()& Hin).
      apply Rst' in Hin.
      congruence.
    - assert (Env.find x (values S') <> None) as E1 by (apply not_None_is_Some; eauto).
      apply Spec', fst_InMembers, InMembers_In in E1 as (()& Hin).
      apply Rst in Hin.
      congruence.
  Qed.

  Lemma initial_state_det:
    forall S S' P b,
      state_closed P b S ->
      state_closed P b S' ->
      initial_state P b S ->
      initial_state P b S' ->
      S ≋ S'.
  Proof.
    induction S as [? IH] using memory_ind'.
    inversion_clear 1 as [??????? Insts2];
      inversion_clear 1 as [??????? Insts2'];
      inversion_clear 1 as [??????? Insts1];
      inversion_clear 1 as [??????? Insts1'].
    repeat match goal with
             H: find_block ?b ?P = _, H': find_block ?b ?P = _ |- _ =>
             rewrite H in H'; inv H'
           end.
    constructor.
    - eapply reset_lasts_det; eauto using state_closed.
    - unfold find_inst in *.
      split.
      + setoid_rewrite Env.In_find.
        split; intros (?& Find).
        * apply Insts2 in Find as (?& Hin &?).
          apply Insts1' in Hin as (?&?&?); eauto.
        * apply Insts2' in Find as (?& Hin &?).
          apply Insts1 in Hin as (?&?&?); eauto.
      + setoid_rewrite Env.Props.P.F.find_mapsto_iff.
        intros ** Find Find'.
        pose proof Find as Find1; pose proof Find' as Find1'.
        apply Insts2 in Find as (?& Hin &?); apply Insts2' in Find' as (?& Hin' &?).
        pose proof Hin; pose proof Hin'.
        apply Insts1 in Hin as (?& Find2 &?); apply Insts1' in Hin' as (?& Find2' & ?).
        rewrite Find2 in Find1; inv Find1; rewrite Find2' in Find1'; inv Find1'.
        assert (x = x0) as E
            by (eapply NoDupMembers_det; eauto; apply b_nodup_blocks).
        eapply IH; subst; eauto.
  Qed.

  (* Lemma sem_block_present: *)
  (*   forall P b S xs ys S', *)
  (*     sem_block P b S xs ys S' -> *)
  (*     present_list xs -> *)
  (*     present_list ys. *)
  (* Proof. *)
  (*   inversion_clear 1 as [???????????? Ins ?? Same AbsEq]; *)
  (*     intros ** Pres. *)
  (*   destruct Same as [Abs|]; auto. *)
  (*   apply AbsEq in Abs. *)
  (*   apply Forall2_length in Ins. *)
  (*   pose proof (b_ingt0 bl) as Length. *)
  (*   rewrite map_length in Ins; rewrite Ins in Length. *)
  (*   clear - Abs Pres Length; destruct xs; simpl in *. *)
  (*   - omega. *)
  (*   - inv Abs; inv Pres; congruence. *)
  (* Qed. *)

  Lemma sem_equations_absent_states:
    forall S I S' P eqs R,
    (forall b xs S ys S',
        sem_block P b S xs ys S' ->
        absent_list xs ->
        S' ≋ S) ->
    state_closed_lasts (lasts_of eqs) S ->
    state_closed_lasts (lasts_of eqs) S' ->
    state_closed_insts P (calls_of eqs) S ->
    state_closed_insts P (calls_of eqs) S' ->
    (forall s rst, Step_with_reset_in s rst eqs ->
              if rst then Reset_in s eqs else ~ Reset_in s eqs) ->
    Forall (sem_equation P false R S I S') eqs ->
    S' ≋ S.
  Proof.
    intros ** IH Lasts Lasts' Insts Insts' Spec Heqs.
    constructor.

    - clear Insts Insts' Spec.
      intros x.
      unfold state_closed_lasts, find_val in *.
      specialize (Lasts x); specialize (Lasts' x).
      destruct (Env.find x (values S)) eqn: Find;
        destruct (Env.find x (values S')) eqn: Find'; auto.
      + assert (In x (lasts_of eqs)) as Hin by (apply Lasts; congruence).
        clear Lasts Lasts'.
        induction eqs as [|[]]; simpl in Hin; try contradiction;
          inversion_clear Heqs as [|?? Heq]; auto.
        destruct Hin; auto; subst.
        inversion_clear Heq as [|?????????? Find1 ? Exp Find1'| |]; unfold find_val in *.
        rewrite Find1 in Find; inv Find.
        inversion Exp as [???? Clock|];
          [contradict Clock; apply not_subrate_clock|]; subst.
        congruence.
      + assert (In x (lasts_of eqs)) as Hin by (apply Lasts; congruence).
        clear Lasts Lasts'.
        induction eqs as [|[]]; simpl in Hin; try contradiction;
          inversion_clear Heqs as [|?? Heq]; auto.
        destruct Hin; auto; subst.
        inversion_clear Heq as [|?????????? Find1 ? Exp Find1'| |]; unfold find_val in *.
        rewrite Find1 in Find; inv Find.
        inversion Exp as [???? Clock|];
          [contradict Clock; apply not_subrate_clock|]; subst.
        congruence.
      + assert (In x (lasts_of eqs)) as Hin by (apply Lasts'; congruence).
        clear Lasts Lasts'.
        induction eqs as [|[]]; simpl in Hin; try contradiction;
          inversion_clear Heqs as [|?? Heq]; auto.
        destruct Hin; auto; subst.
        inversion_clear Heq as [|?????????? Find1 ? Exp Find1'| |]; unfold find_val in *.
        congruence.

    - clear Lasts Lasts'.
      constructor.
      + setoid_rewrite Env.In_find.
        unfold state_closed_insts, find_inst in *.
        intro s; split; intros (?& Find).
        *{ apply Insts' in Find as (b & Hin &?).
           apply calls_of_In in Hin as (?&?& rst &?& Hin).
           pose proof Heqs as Heqs'.
           eapply Forall_forall in Heqs; eauto.
           assert (Step_with_reset_in s rst eqs) as Spec'
               by (apply Exists_exists; eexists; split; eauto; constructor).
           apply Spec in Spec'.
           destruct rst.
           - apply Exists_exists in Spec' as (?& Rst & E); inv E.
             eapply Forall_forall in Rst; eauto.
             inversion_clear Rst as [| |?????????? Clock FindI Init|].
             assert (r = false)
               by (rewrite <-Bool.not_true_iff_false;
                   intro E; subst; contradict Clock; apply not_subrate_clock); subst.
             destruct Init as (?&?&?); eauto.
           - inversion_clear Heqs as [| | |????????????????? Rst].
             destruct Rst as (?&?&?); eauto.
         }
        * apply Insts in Find as (b & Hin &?).
          apply calls_of_In in Hin as (?&?&?&?& Hin).
          eapply Forall_forall in Heqs; eauto.
          inv Heqs; eauto.
      + setoid_rewrite Env.Props.P.F.find_mapsto_iff.
        intros s ** Find' Find.
        pose proof Find as Hin.
        apply Insts in Hin as (b & Hin &?).
        apply calls_of_In in Hin as (?&?& rst &?& Hin).
        pose proof Heqs as Heqs'.
        eapply Forall_forall in Heqs; eauto.
        assert (Step_with_reset_in s rst eqs) as Spec'
               by (apply Exists_exists; eexists; split; eauto; constructor).
        apply Spec in Spec'.
        inversion_clear Heqs as [| | |??????????????? Exps Clk Rst' FindI' SemBlock ? Find1'].
        unfold find_inst in *; rewrite Find1' in Find'; inv Find'.
        assert (absent_list xs) by (eapply clock_of_instant_false, not_subrate_clock_impl; eauto).
        apply IH in SemBlock; auto.
        rewrite SemBlock.
        destruct rst.
        * apply Exists_exists in Spec' as (?& Rst & E); inv E.
          eapply Forall_forall in Rst; eauto.
          inversion_clear Rst as [| |?????????? Clock FindI Init|];
            setoid_rewrite FindI' in FindI; inv FindI.
          assert (r = false)
            by (rewrite <-Bool.not_true_iff_false;
                intro E; subst; contradict Clock; apply not_subrate_clock); subst.
          destruct Init as (?& Find1 &?); eauto.
          unfold find_inst in *; rewrite Find1 in Find; inv Find; auto.
        * destruct Rst' as (?& Find1 &?); auto.
          rewrite Find1 in Find; inv Find; auto.
  Qed.

  Lemma sem_equations_absent_vars:
    forall eqs S I S' P R x,
    (forall b xs S ys S',
        sem_block P b S xs ys S' ->
        absent_list xs ->
        absent_list ys) ->
    In x (variables eqs) ->
    Forall (sem_equation P false R S I S') eqs ->
    sem_var_instant R x absent.
  Proof.
    unfold variables, concatMap.
    induction eqs as [|[]]; simpl; intros ** IH Spec Heqs; try contradiction;
      inversion_clear Heqs as [|?? Heq];
      inversion_clear Heq as [????????? Exp| | |]; eauto.
    - destruct Spec; eauto; subst.
      apply sem_caexp_instant_absent in Exp; subst; auto.
    - assert (absent_list xs) as Abs
          by (eapply clock_of_instant_false, not_subrate_clock_impl; eauto).
      eapply IH in Abs; eauto.
      apply in_app in Spec as [Hin|]; eauto.
      eapply Forall2_in_left in Hin; eauto.
      destruct Hin as (v &?&?).
      eapply Forall_forall in Abs; eauto.
      subst; auto.
  Qed.

  Lemma sem_block_absent:
    forall P b xs S ys S',
      Ordered_blocks P ->
      sem_block P b S xs ys S' ->
      absent_list xs ->
      absent_list ys /\ S' ≋ S.
  Proof.
    intros ** Ord Sem Abs.
    revert dependent xs; revert b S S' ys.
    induction P as [|block]; intros;
      inversion_clear Sem as [????????? Find Ins ?? Heqs Closed ? Closed'];
      try now inv Find.
    pose proof Find; simpl in Find.
    destruct (ident_eqb (b_name block) b) eqn: Eq.
    - inv Find.
      assert ( ~ Is_block_in (b_name bl) (b_eqs bl))
        by (eapply find_block_not_Is_block_in; eauto).
      apply sem_equations_cons in Heqs; auto.
      assert (clock_of_instant xs = false) as E by (apply clock_of_instant_false; auto);
        rewrite E in *.
      inv Ord; split.
      + apply Forall_forall; intros v Hin.
        eapply Forall2_in_right in Hin; eauto.
        destruct Hin as (x & ?&?).
        eapply sem_var_instant_det; eauto.
        eapply sem_equations_absent_vars; eauto.
        * intros; eapply IHP; eauto.
        * rewrite <-b_vars_out_in_eqs.
          apply in_app; auto.
      + inversion_clear Closed as [?????? Lasts Insts];
          inversion_clear Closed' as [?????? Lasts' Insts'].
        repeat match goal with
                 H: find_block ?b ?P = _, H': find_block ?b ?P = _ |- _ =>
                 rewrite H in H'; inv H'
               end.
        rewrite b_lasts_in_eqs in Lasts, Lasts'.
        setoid_rewrite b_blocks_calls_of in Insts;
          setoid_rewrite b_blocks_calls_of in Insts'.
        eapply sem_equations_absent_states; eauto.
        * intros; eapply IHP; eauto.
        * apply b_reset_in.
    - inv Ord; eapply IHP; eauto.
      apply ident_eqb_neq in Eq.
      rewrite <-state_closed_other in Closed, Closed'; eauto.
      econstructor; eauto.
      apply sem_equations_cons in Heqs; eauto using Ordered_blocks.
      eapply find_block_later_not_Is_block_in; eauto using Ordered_blocks.
  Qed.

  Lemma state_closed_lasts_empty:
    forall lasts,
      state_closed_lasts lasts (empty_memory _).
  Proof.
    unfold state_closed_lasts; setoid_rewrite find_val_gempty; intuition.
  Qed.

  Lemma state_closed_empty:
    forall P b bl P',
      find_block b P = Some (bl, P') ->
      state_closed P b (empty_memory _).
  Proof.
    intros ** Find.
    econstructor; eauto.
    - apply state_closed_lasts_empty.
    - setoid_rewrite find_inst_gempty; congruence.
  Qed.

  Lemma sem_block_find_val:
    forall P f S xs ys S' x bl P',
      sem_block P f S xs ys S' ->
      find_block f P = Some (bl, P') ->
      In x (map fst (b_lasts bl)) ->
      find_val x S <> None.
  Proof.
    inversion_clear 1 as [????????? Find ??? Heqs]; intros Find' Hin.
    rewrite Find in Find'; inv Find'.
    rewrite b_lasts_in_eqs in Hin.
    induction Heqs as [|[] ? Heq]; simpl in *; try contradiction; auto.
    destruct Hin; subst; auto.
    inv Heq; congruence.
  Qed.

End SBSEMANTICS.

Module SBSemanticsFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Op)
       (CESyn : CESYNTAX        Op)
       (Syn   : SBSYNTAX    Ids Op       CESyn)
       (Block : SBISBLOCK   Ids Op       CESyn Syn)
       (Ord   : SBORDERED   Ids Op       CESyn Syn Block)
       (Str   : STREAM          Op OpAux)
       (CESem : CESEMANTICS Ids Op OpAux CESyn Str)
<: SBSEMANTICS Ids Op OpAux CESyn Syn Block Ord Str CESem.
  Include SBSEMANTICS Ids Op OpAux CESyn Syn Block Ord Str CESem.
End SBSemanticsFun.
