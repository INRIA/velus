Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Permutation.
Require Import Setoid.
Require Import Morphisms.

Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.NLustre.NLExprSyntax.
Require Import Velus.RMemory.
Require Import Velus.SyBloc.SBSyntax.
Require Import Velus.NLustre.Stream.
Require Import Velus.NLustre.NLExprSemantics.

Module Type SBSEMANTICS
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import OpAux   : OPERATORS_AUX       Op)
       (Import Clks    : CLOCKS          Ids)
       (Import ExprSyn : NLEXPRSYNTAX        Op)
       (Import Syn     : SBSYNTAX        Ids Op       Clks ExprSyn)
       (Import Str     : STREAM              Op OpAux)
       (Import ExprSem : NLEXPRSEMANTICS Ids Op OpAux Clks ExprSyn Str).

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
            sub_inst x S S' ->
            exists b',
              In (x, b') (b_blocks bl)
              /\ state_closed P' b' S') ->
        state_closed P b S.

  Definition state_closed_insts (P: program) (blocks: list (ident * ident)) (S: state) : Prop :=
    forall s Ss,
      sub_inst s S Ss ->
      exists b, In (s, b) blocks
           /\ state_closed P b Ss.

  Definition transient_states_closed (P: program) (blocks: list (ident * ident)) (I: transient_states) : Prop :=
    Forall (fun sb =>
              forall Is,
                Env.find (fst sb) I = Some Is ->
                state_closed P (snd sb) Is)
           blocks.

  (* Definition state_closed' (S: state) (lasts: list ident) (blocks: list ident) : Prop := *)
  (*   state_closed_lasts lasts S *)
  (*   /\ forall s, find_inst s S <> None -> In s blocks. *)

  Definition reset_lasts (bl: block) (S0: state) : Prop :=
    forall x c,
      In (x, c) bl.(b_lasts) ->
      find_val x S0 = Some (sem_const c).

  Inductive initial_state: program -> ident -> state -> Prop :=
    initial_state_intro:
      forall P b S0 bl P',
        find_block b P = Some (bl, P') ->
        reset_lasts bl S0 ->
        (forall x b',
            In (x, b') bl.(b_blocks) ->
            exists S0',
              sub_inst x S0 S0'
              /\ initial_state P' b' S0') ->
        initial_state P b S0.

  Definition same_clock (vs: list value) : Prop :=
    absent_list vs \/ present_list vs.

  Definition clock_of (vs: list value) (b: bool): Prop :=
    present_list vs <-> b = true.

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
           else exists Ss, sub_inst s S Ss /\ Is ≋ Ss) ->
          sem_equation base R S I S' (EqReset s ck b)
    | SEqCall:
        forall base R S I S' ys rst ck b s es xs Is os Ss',
          sem_laexps_instant base R ck es xs ->
          (rst = false -> exists Ss, sub_inst s S Ss /\ Is ≋ Ss) ->
          Env.find s I = Some Is ->
          sem_block b Is xs os Ss' ->
          sem_vars_instant R ys os ->
          sub_inst s S' Ss' ->
          sem_equation base R S I S' (EqCall s ys ck rst b es)

    with sem_block: ident -> state -> list value -> list value -> state -> Prop :=
           SBlock:
             forall b bl P' S I S' R xs ys base,
               clock_of xs base ->
               find_block b P = Some (bl, P') ->
               sem_vars_instant R (map fst bl.(b_in)) xs ->
               sem_vars_instant R (map fst bl.(b_out)) ys ->
               same_clock xs ->
               same_clock ys ->
               (absent_list xs <-> absent_list ys) ->
               Forall (sem_equation base R S I S') bl.(b_eqs) ->
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
         else exists Ss, sub_inst s S Ss /\ Is ≋ Ss) ->
        P_equation base R S I S' (EqReset s ck b).

    Hypothesis EqCallCase:
      forall base R S I S' s ys ck rst b es xs Is os Ss',
        sem_laexps_instant base R ck es xs ->
        (rst = false -> exists Ss, sub_inst s S Ss /\ Is ≋ Ss) ->
        Env.find s I = Some Is ->
        sem_block P b Is xs os Ss' ->
        sem_vars_instant R ys os ->
        sub_inst s S' Ss' ->
        P_block b Is xs os Ss' ->
        P_equation base R S I S' (EqCall s ys ck rst b es).

    Hypothesis BlockCase:
      forall b bl P' R S I S' xs ys base,
        clock_of xs base ->
        find_block b P = Some (bl, P') ->
        sem_vars_instant R (map fst bl.(b_in)) xs ->
        sem_vars_instant R (map fst bl.(b_out)) ys ->
        same_clock xs ->
        same_clock ys ->
        (absent_list xs <-> absent_list ys) ->
        Forall (sem_equation P base R S I S') bl.(b_eqs) ->
        state_closed P b S ->
        transient_states_closed P' bl.(b_blocks) I ->
        state_closed P b S' ->
        Forall (P_equation base R S I S') bl.(b_eqs) ->
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

  Add Parametric Morphism block : (reset_lasts block)
      with signature equal_memory ==> Basics.impl
        as reset_lasts_equal_memory.
  Proof.
    intros ** E Rst ?? Hin.
    rewrite <-E; auto.
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
      unfold sub_inst in *.
      pose proof (find_inst_equal_memory x0 E) as Eq;
        rewrite Sub in Eq; simpl in Eq.
      destruct (find_inst x0 y); try contradiction.
      eexists; split; eauto.
  Qed.

  Lemma sem_equation_equal_memory:
    forall P bk R eq S1 I1 S1' S2 I2 S2',
      (forall f xs ys S1 S1' S2 S2',
          S1 ≋ S2 ->
          S1' ≋ S2' ->
          sem_block P f S1 xs ys S1' ->
          sem_block P f S2 xs ys S2') ->
      S1 ≋ S2 ->
      Env.Equiv equal_memory I1 I2 ->
      S1' ≋ S2' ->
      sem_equation P bk R S1 I1 S1' eq ->
      sem_equation P bk R S2 I2 S2' eq.
  Proof.
    intros ** IH E EI E' Sem.
    inversion_clear Sem as [| |??????????? Find Init|
                            ???????????????? Spec Find ?? Sub];
      eauto using sem_equation.
    - econstructor; eauto.
      + now rewrite <-E.
      + now rewrite <-E'.
    - pose proof (find_equiv_memory s EI) as Eq;
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
    - pose proof (find_equiv_memory s EI) as Eq.
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
        eexists; split; eauto.
        now rewrite <-Eq, <-Eq''.
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
    - intros ** Sub; unfold sub_inst in *.
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

  (* Add Parametric Morphism lasts blocks : (fun S => state_closed' S lasts blocks) *)
  (*     with signature equal_memory ==> Basics.impl *)
  (*       as state_closed_equal_memory'. *)
  (* Proof. *)
  (*   intros ?? E (Lasts & Blocks); split. *)
  (*   - now setoid_rewrite <-E. *)
  (*   - intros ** Find. *)
  (*     apply Blocks. *)
  (*     apply not_None_is_Some in Find as (?& Find). *)
  (*     pose proof (find_inst_equal_memory s E) as E'. *)
  (*     rewrite Find in E'. *)
  (*     destruct (find_inst s x); congruence. *)
  (* Qed. *)

  Add Parametric Morphism P f xs ys : (fun S S' => sem_block P f S xs ys S')
      with signature equal_memory ==> equal_memory ==> Basics.impl
        as sem_block_equal_memory.
  Proof.
    intros ** Sem.
    revert dependent y; revert dependent y0.
    induction Sem as [| |??????????? Find Init|
                      ???????????????? Spec Find ?? Sub|] using sem_block_mult with
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

  (* Add Parametric Morphism S : (state_closed' S) *)
  (*     with signature (@Permutation ident) ==> (@Permutation ident) ==> Basics.impl *)
  (*       as state_closed_permutation'. *)
  (* Proof. *)
  (*   intros ?? E ?? E' (Lasts & Blocks); split. *)
  (*   - now rewrite <-E. *)
  (*   - now setoid_rewrite <-E'. *)
  (* Qed. *)

  Inductive Ordered_blocks: program -> Prop :=
  | Ordered_nil:
      Ordered_blocks []
  | Ordered_cons:
      forall bl P,
        Ordered_blocks P ->
        Forall (fun xb =>
                  snd xb <> bl.(b_name)
                  /\ exists bl' P', find_block (snd xb) P = Some (bl', P'))
               bl.(b_blocks) ->
        Forall (fun bl' => bl.(b_name) <> bl'.(b_name)) P ->
        Ordered_blocks (bl :: P).

  Remark Ordered_blocks_nodup:
    forall P,
      Ordered_blocks P ->
      NoDup (map b_name P).
  Proof.
    induction 1 as [|??? Ord Blocks NoDup]; simpl; constructor; auto.
    clear - NoDup; induction P; inv NoDup; simpl; auto.
    intros [|]; try congruence.
    now apply IHP.
  Qed.

  Remark Ordered_blocks_split:
    forall P1 bl P,
      Ordered_blocks (P1 ++ bl :: P) ->
      Forall (fun xb =>
                  find_block (snd xb) P1 = None
                  /\ snd xb <> bl.(b_name)
                  /\ exists bl' P', find_block (snd xb) P = Some (bl', P'))
             bl.(b_blocks).
  Proof.
    induction P1; inversion_clear 1 as [|?? Ord]; apply Forall_Forall; auto.
    - apply Forall_forall; auto.
    - apply IHP1 in Ord; apply Forall_forall; intros.
      eapply Forall_forall in Ord as (?&?&(bl' &?& Find)); eauto.
      rewrite find_block_other; auto.
      pose proof Find as Find'; apply find_block_name in Find'.
      apply find_block_In in Find.
      assert (In bl' (P1 ++ bl :: P)) as Hin
          by (apply in_app; right; right; auto).
      eapply Forall_forall in Hin; eauto.
      congruence.
    - apply IHP1 in Ord; apply Forall_forall; intros.
      eapply Forall_forall in Ord as (?&?&?); eauto.
  Qed.

  Lemma Ordered_blocks_find_In_blocks:
    forall P b bl P',
      Ordered_blocks P ->
      find_block b P = Some (bl, P') ->
      forall x b,
        In (x, b) bl.(b_blocks) ->
        exists bl P'', find_block b P' = Some (bl, P'').
  Proof.
    induction P as [|block]; try now inversion 2.
    intros ** Ord Find ?? Hin.
    inv Ord.
    simpl in Find.
    destruct (ident_eqb (b_name block) b) eqn: E; eauto.
    inv Find.
    eapply Forall_forall in Hin; eauto.
    destruct Hin; eauto.
  Qed.

  Lemma Ordered_blocks_find_block:
    forall P b bl P',
      Ordered_blocks P ->
      find_block b P = Some (bl, P') ->
      Ordered_blocks P'.
  Proof.
    induction P as [|block]; try now inversion 2.
    intros ** Ord Find.
    inv Ord.
    simpl in Find.
    destruct (ident_eqb (b_name block) b) eqn: E; eauto.
    inv Find; auto.
  Qed.

  Lemma initial_state_other:
    forall S0 bl P b,
      (* Ordered_blocks (bl :: P) -> *)
      b_name bl <> b ->
      (initial_state P b S0 <->
      initial_state (bl :: P) b S0).
  Proof.
    split; inversion_clear 1 as [????? Find]; econstructor; eauto.
    - rewrite find_block_other; eauto.
    - rewrite find_block_other in Find; eauto.
  Qed.

  (*   inversion_clear 1. econstructor; eauto. *)
  (*   econstructor.  *)
  (*   induction S0 as [? IH] using memory_ind'; *)
  (*     intros ** Ord ?; split; intro Init; inversion_clear Init as [???? Find ? Spec]. *)
  (*   - econstructor; eauto. *)
  (*     rewrite find_block_other; eauto. *)
  (*     + intros ** Find'. *)
  (*       specialize (Spec _ _ Find'); destruct Spec as (S0' & Sub & Init). *)
  (*       exists S0'; split; auto. *)
  (*       rewrite <-IH; eauto. *)
  (*       apply find_block_split in Find as (P1 & E). *)
  (*       rewrite E in Ord. *)
  (*       pose proof Ord as Ord'. *)
  (*       rewrite app_comm_cons in Ord. *)
  (*       apply Ordered_blocks_split in Ord. *)
  (*       eapply Forall_forall in Ord as (?&?&?&?& Find); eauto; simpl in Find. *)
  (*       apply Ordered_blocks_nodup in Ord'; simpl in Ord'. *)
  (*       inversion_clear Ord' as [|?? NotIn]. *)
  (*       pose proof Find as Find''. *)
  (*       apply find_block_name in Find. *)
  (*       apply find_block_In in Find''. *)
  (*       intro Eq; subst; apply NotIn. *)
  (*       rewrite Eq. *)
  (*       apply in_map, in_app; intuition. *)
  (*   - econstructor; eauto. *)
  (*     + rewrite find_block_other in Find; eauto. *)
  (*     + intros ** Find'. *)
  (*       specialize (Spec _ _ Find'); destruct Spec as (S0' & Sub & Init). *)
  (*       exists S0'; split; auto. *)
  (*       rewrite IH; eauto. *)
  (*       rewrite find_block_other in Find; auto. *)
  (*       apply find_block_split in Find as (? & Eq). *)
  (*       rewrite Eq in Ord; pose proof Ord as Ord'; rewrite app_comm_cons in Ord. *)
  (*       apply Ordered_blocks_split in Ord. *)
  (*       eapply Forall_forall in Ord as (?&?&?&?& Find); eauto; simpl in Find. *)
  (*       pose proof Find as Find''. *)
  (*       apply find_block_name in Find. *)
  (*       apply find_block_In in Find''. *)
  (*       apply Ordered_blocks_nodup in Ord'. *)
  (*       inversion_clear Ord' as [|?? NotIn]. *)
  (*       intro E; subst; apply NotIn. *)
  (*       rewrite E. *)
  (*       apply in_map, in_app; intuition. *)
  (* Qed. *)

  Lemma initial_state_other_app:
    forall S0 P P' b bl,
      find_block b P = None ->
      b <> b_name bl ->
      (initial_state (P ++ bl :: P') b S0 <-> initial_state P' b S0).
  Proof.
    split; inversion_clear 1 as [????? Find]; econstructor; eauto.
    - rewrite find_block_other_app in Find; eauto.
    - rewrite find_block_other_app; eauto.
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
  (* Lemma find_block_initial_state: *)
  (*   forall P b bl P', *)
  (*     Ordered_blocks P -> *)
  (*     find_block b P = Some (bl, P') -> *)
  (*     exists S0, initial_state P b S0. *)
  (* Proof. *)
  (*   induction P as [|bl']; simpl; try discriminate. *)
  (*   inversion_clear 1 as [|??? Subs]. *)
  (*   destruct (ident_eqb (b_name bl') b) eqn: E. *)
  (*   - intros E'; inv E'. *)
  (*     destruct bl; simpl in *. *)
  (*     induction b_blocks0 as [|(x, b')]; intros. *)
  (*     + set (xs := fst (split b_lasts0)). *)
  (*       set (vs := map sem_const (snd (split b_lasts0))). *)
  (*       assert (combine xs vs = List.map (fun (xc: ident * const) => (fst xc, sem_const (snd xc))) b_lasts0) *)
  (*         as Eq. *)
  (*       { pose proof (split_combine b_lasts0) as Eq. *)
  (*         destruct (split b_lasts0). *)
  (*         subst xs vs; simpl. *)
  (*         rewrite combine_map_snd, Eq; auto. *)
  (*       } *)
  (*       exists (add_vals xs vs (@empty_memory val)). *)
  (*       econstructor; eauto; simpl. *)
  (*       * rewrite E; eauto. *)
  (*       *{ unfold reset_lasts; simpl; intros. *)
  (*          unfold find_val, add_vals; simpl. *)
  (*          split; intros ** Hin. *)
  (*          - apply Env.find_adds. *)
  (*            + subst xs; rewrite split_fst_map, <-fst_NoDupMembers. *)
  (*              apply b_nodup_lasts0. *)
  (*            + setoid_rewrite Eq. *)
  (*              change (x, sem_const c) with ((fun x => (fst x, sem_const (snd x))) (x, c)). *)
  (*              apply in_map; auto. *)
  (*          - apply Env.find_adds' in Hin; auto. *)
  (*            + setoid_rewrite Eq in Hin; apply in_map_iff in Hin as ((x', c) & Ex & Hin); inv Ex; eauto. *)
  (*            + subst xs; rewrite split_fst_map, <-fst_NoDupMembers. *)
  (*              apply b_nodup_lasts0. *)
  (*            + apply Env.gempty. *)
  (*        } *)
  (*       * contradiction. *)
  (*     + inversion Subs as [|?? (?&?&?& Find) Subs' E1]; destruct x0; subst; inv E1; simpl in *. *)
  (*       apply IHP in Find as (S0x); auto. *)
  (*       inversion_clear b_nodup_blocks0 as [|???? Nodup]. *)
  (*       assert (forall f, (exists i, In (i, f) b_blocks0) <-> Is_block_in f b_eqs0) as BlocksIn. *)
  (*       split; [intros (?& Hin)|intros Hin]. *)
  (*       apply b_blocks_in_eqs0. eauto. *)
  (*       apply b_blocks_in_eqs0 in Hin as (? & [Eq|]); eauto.  *)
  (*           by (intros ** Hin; eapply b_blocks_in_eqs0; eauto). *)
  (*       destruct (IHb_blocks0 Nodup BlocksIn) as (S0 & Init); eauto. *)
  (*       exists (add_inst x S0x S0). *)
  (*       econstructor; eauto; simpl. *)
  (*       * rewrite E; eauto. *)
  (*       * apply reset_lasts_add_inst. *)
  (*         inversion_clear Init as [???? Find Reset]. *)
  (*         unfold find_block in Find; simpl in Find; rewrite E in Find; inv Find. *)
  (*         unfold reset_lasts in *; eauto. *)
  (*       *{ simpl; intros x' b'' [Eq|Hin]. *)
  (*          - inv Eq. *)
  (*            unfold sub_inst. *)
  (*            rewrite find_inst_gss. *)
  (*            exists S0x; split; auto. *)
  (*            apply initial_state_tail; auto using Ordered_blocks. *)
  (*          - assert (x' <> x). *)
  (*            { inv b_nodup_blocks0. *)
  (*              eapply InMembers_neq; eauto. *)
  (*              eapply In_InMembers; eauto. *)
  (*            } *)
  (*            unfold sub_inst; rewrite find_inst_gso; auto. *)
  (*            inversion_clear Init as [???? Find Reset Spec]. *)
  (*            unfold find_block in Find; simpl in Find; rewrite E in Find; inv Find; simpl in *. *)
  (*            specialize (Spec _ _ Hin); destruct Spec as (S0' &?& Init). *)
  (*            exists S0'; split; auto. *)
  (*            assert (b_name0 <> b'') *)
  (*              by (eapply In_Forall in Subs'; eauto; intuition). *)
  (*            apply initial_state_tail; auto using Ordered_blocks; simpl. *)
  (*            apply initial_state_tail in Init; eauto using Ordered_blocks. *)
  (*        } *)
  (*   - apply ident_eqb_neq in E. *)
  (*     intros Find. *)
  (*     edestruct IHP; eauto. *)
  (*     eexists; apply initial_state_tail; eauto using Ordered_blocks. *)
  (* Qed. *)

  Lemma find_block_later_not_Is_block_in:
    forall f bl P bl' P',
      Ordered_blocks (bl :: P) ->
      find_block f P = Some (bl', P') ->
      ~ Is_block_in bl.(b_name) bl'.(b_eqs).
  Proof.
    intros ** Hord Hfind Hini.
    apply find_block_split in Hfind as (? & E); rewrite E, app_comm_cons in Hord.
    pose proof Hord as Hord'; inversion_clear Hord' as [|??? Sub Hnin]; clear Sub.
    apply Ordered_blocks_split in Hord.
    pose proof (b_blocks_in_eqs bl') as BlocksIn.
    apply BlocksIn in Hini as (? & Hin).
    eapply Forall_forall in Hin; eauto; destruct Hin as (?&?&?&?& Find); simpl in Find.
    apply Forall_app_weaken in Hnin; inversion_clear Hnin as [|??? Hnin'].
    pose proof Find as Find'; apply find_block_name in Find'.
    apply find_block_In in Find.
    eapply Forall_forall in Find; eauto.
    congruence.
  Qed.

  Lemma find_block_not_Is_block_in:
    forall f bl P P',
      Ordered_blocks P ->
      find_block f P = Some (bl, P') ->
      ~ Is_block_in bl.(b_name) bl.(b_eqs).
  Proof.
    intros ** Hord Hfind Hini.
    apply find_block_split in Hfind as (?& E); rewrite E in Hord.
    apply Ordered_blocks_split in Hord.
    pose proof (b_blocks_in_eqs bl) as BlocksIn.
    apply BlocksIn in Hini as (? & Hin).
    eapply Forall_forall in Hin; eauto; destruct Hin as (?&?&?); auto.
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
    induction Hsem as [| | |????????????????????? IH|
                       ??????????? Hf ?????? Closed ? Closed' IH]
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
                       ??????????? Hfind ?????? Closed ? Closed' IHeqs] using sem_block_mult
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
        apply find_block_split in Hfind as (?& Hp); subst.
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
      apply Spec, fst_InMembers, InMembers_In in E1 as (?& Hin).
      pose proof Hin as Hin'.
      apply Rst in Hin; apply Rst' in Hin'.
      congruence.
    - assert (Env.find x (values S) <> None) as E1 by (apply not_None_is_Some; eauto).
      apply Spec, fst_InMembers, InMembers_In in E1 as (?& Hin).
      apply Rst' in Hin.
      congruence.
    - assert (Env.find x (values S') <> None) as E1 by (apply not_None_is_Some; eauto).
      apply Spec', fst_InMembers, InMembers_In in E1 as (?& Hin).
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
    - unfold sub_inst, find_inst in *.
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

  Lemma sem_block_present:
    forall P b S xs ys S',
      sem_block P b S xs ys S' ->
      present_list xs ->
      present_list ys.
  Proof.
    inversion_clear 1 as [???????????? Ins ?? Same AbsEq];
      intros ** Pres.
    destruct Same as [Abs|]; auto.
    apply AbsEq in Abs.
    apply Forall2_length in Ins.
    pose proof (b_ingt0 bl) as Length.
    rewrite map_length in Ins; rewrite Ins in Length.
    clear - Abs Pres Length; destruct xs; simpl in *.
    - omega.
    - inv Abs; inv Pres; congruence.
  Qed.

  Lemma not_in_nil:
    forall A (l: list A),
      (forall x, ~ In x l) ->
      l = [].
  Proof.
    induction l as [|y]; auto; intros Notin.
    exfalso; apply (Notin y); constructor; auto.
  Qed.

  (* Lemma state_closed'_empty: *)
  (*   forall S, *)
  (*     state_closed' S [] [] -> *)
  (*     S ≋ @empty_memory _. *)
  (* Proof. *)
  (*   intros ** (Vals & Insts); simpl in *. *)
  (*   constructor. *)
  (*   - unfold find_val, empty_memory in *. *)
  (*     intro; simpl. *)
  (*     rewrite Env.gempty. *)
  (*     apply not_Some_is_None; intros ** Find. *)
  (*     eapply Vals, not_None_is_Some; eauto. *)
  (*   - unfold find_inst, empty_memory in *; simpl. *)
  (*     split. *)
  (*     + setoid_rewrite Env.Props.P.F.empty_in_iff; *)
  (*         setoid_rewrite Env.In_find. *)
  (*       split; try contradiction. *)
  (*       intros (?& Find); eapply Insts, not_None_is_Some; eauto. *)
  (*     + setoid_rewrite Env.Props.P.F.empty_mapsto_iff; *)
  (*         contradiction. *)
  (* Qed. *)

  Lemma sem_equation_remove_val:
    forall P base eqs R S I S' x,
      ~ Is_last_in x eqs ->
      Forall (sem_equation P base R S I S') eqs ->
      Forall (sem_equation P base R (remove_val x S) I (remove_val x S')) eqs.
  Proof.
    induction eqs as [|[]]; intros ** Hnotin Sems;
      inversion_clear Sems as [|?? Sem]; auto;
        inversion_clear Sem;
          apply not_Is_last_in_cons in Hnotin as (Hnotin &?);
          constructor; eauto using sem_equation.
    assert (x <> i) by (intro E; subst; apply Hnotin; constructor).
    econstructor; eauto; rewrite find_val_gro; auto.
  Qed.

  Lemma sem_equation_remove_inst:
    forall P base eqs R S I S' s,
      (forall k, ~ Is_state_in s k eqs) ->
      Forall (sem_equation P base R S I S') eqs ->
      Forall (sem_equation P base R (remove_inst s S) I (remove_inst s S')) eqs.
  Proof.
    induction eqs as [|[]]; intros ** Hnotin Sems;
      inversion_clear Sems as [|?? Sem]; auto;
        inversion_clear Sem;
        apply not_Is_state_in_cons' in Hnotin as (Hnotin &?);
        constructor; eauto using sem_equation.
    - econstructor; eauto.
      destruct r; auto.
      assert (s <> i) by (intro E; subst; eapply Hnotin; constructor).
      unfold sub_inst; rewrite find_inst_gro; auto.
    - assert (s <> i) by (intro E; subst; eapply Hnotin; constructor).
      econstructor; eauto; unfold sub_inst; rewrite find_inst_gro; auto.
  Qed.

  Lemma state_closed_lasts_Next:
    forall S eqs x ck e,
      state_closed_lasts (lasts_of (EqNext x ck e :: eqs)) S ->
      state_closed_lasts (lasts_of eqs) (remove_val x S).
  Proof.
    unfold state_closed_lasts.
    intros ** Vals y Find.
    apply not_None_is_Some in Find as (?& Find).
    destruct (ident_eq_dec y x).
    - subst; rewrite find_val_grs in Find; discriminate.
    - rewrite find_val_gro in Find; auto.
      edestruct Vals; eauto; try congruence.
      congruence.
  Qed.

  Lemma state_closed_insts_Reset:
    forall P S eqs s ck b,
      state_closed_insts P (states_of (EqReset s ck b :: eqs)) S ->
      state_closed_insts P (states_of eqs) (remove_inst s S).
  Proof.
    unfold state_closed_insts, sub_inst.
    intros ** Blocks s' ? Find.
    destruct (ident_eq_dec s' s).
    - subst; rewrite find_inst_grs in Find; discriminate.
    - rewrite find_inst_gro in Find; auto.
      edestruct Blocks as (?& Hin &?); eauto.
      eexists; split; eauto.
      inversion_clear Hin as [E|]; auto.
      inv E; congruence.
  Qed.

  Lemma state_closed_insts_Call:
    forall P S eqs s xs ck rst b es,
      state_closed_insts P (states_of (EqCall s xs ck rst b es :: eqs)) S ->
      state_closed_insts P (states_of eqs) (remove_inst s S).
  Proof.
    unfold state_closed_insts, sub_inst.
    intros ** Blocks s' ? Find.
    destruct (ident_eq_dec s' s).
    - subst; rewrite find_inst_grs in Find; discriminate.
    - rewrite find_inst_gro in Find; auto.
      edestruct Blocks as (?& Hin &?); eauto.
      eexists; split; eauto.
      inversion_clear Hin as [E|]; auto.
      inv E; congruence.
  Qed.

  Lemma state_closed_lasts_nil:
    forall S,
      state_closed_lasts [] S ->
      Env.Equal (values S) (Env.empty _).
  Proof.
    unfold state_closed_lasts, find_val.
    intros ** Lasts x; rewrite Env.gempty.
    apply not_Some_is_None; intros ??.
    eapply Lasts, not_None_is_Some; eauto.
  Qed.

  (* TODO: constructor sur equal_memory + inversion sur la semantique + predicats sur la syntaxe *)

  Lemma sem_equations_absent:
    forall S I S' P eqs base R,
    (forall b xs S ys S',
        sem_block P b S xs ys S' ->
        absent_list xs ->
        S' ≋ S) ->
    (* Ordered_nodes G -> *)
    base = false ->
    (* NoDup_defs eqs -> *)
    state_closed_lasts (lasts_of eqs) S ->
    state_closed_lasts (lasts_of eqs) S' ->
    state_closed_insts P (states_of eqs) S ->
    state_closed_insts P (states_of eqs) S' ->
    transient_states_closed P (states_of eqs) I ->
    (* (forall s b, In (s, b) (states_of eqs) ->  *)
    Forall (sem_equation P base R S I S') eqs ->
    S' ≋ S.
  Proof.
    intros ** IH (* Hord *) Abs (* Nodup *) Lasts Lasts' Insts Insts' Trans Heqs.
    revert dependent S; revert dependent S'.
    induction eqs as [|[] ? IHeqs]; intros;
      inversion_clear Heqs as [|?? Sem Sems];
      try inversion_clear Sem as [|?????????? Find ? Exp Find'|
                                  ?????????? Clock FindI Init|
                                 ??????????????? Exps Rst ? SemBlock ? Find'];
      eauto.

    - apply state_closed_lasts_nil in Lasts; apply state_closed_lasts_nil in Lasts'.
      constructor.
      + now rewrite Lasts, Lasts'.
      + assert (forall s, find_inst s S = None) as Find
          by (setoid_rewrite <-not_Some_is_None; intros ** Find;
              apply Insts in Find as (?&?&?); auto).
        assert (forall s, find_inst s S' = None) as Find'
          by (setoid_rewrite <-not_Some_is_None; intros ** Find';
              apply Insts' in Find' as (?&?&?); auto).
        unfold find_inst in *.
        eapply Env.Equiv_empty in Find; eapply Env.Equiv_empty in Find'.
        now rewrite Find, Find'.

    - apply sem_equation_remove_val with (x := i) in Sems; auto.
      + apply IHeqs in Sems; try eapply state_closed_lasts_Next; eauto.
        apply add_remove_val_same in Find; apply add_remove_val_same in Find'.
        rewrite Abs in Exp; inversion Exp as [???? Clock|];
          [contradict Clock; apply not_subrate_clock|]; subst.
        now rewrite Find, Find', Sems.
      + admit.

    - apply sem_equation_remove_inst with (s := i) in Sems.
      + inversion_clear Trans as [|?? Closed]; apply IHeqs in Sems;
          try eapply state_closed_insts_Reset; eauto.
        rewrite Abs in Clock.
        assert (r = false) as E
            by (rewrite <-Bool.not_true_iff_false;
                intro E; subst; contradict Clock; apply not_subrate_clock).
        rewrite E in Init; destruct Init as (?& Find &?).
        unfold sub_inst in Find; apply add_remove_inst_same in Find.
        rewrite Find.
        apply Closed in FindI.
        admit.
      + admit.

    - apply sem_equation_remove_inst with (s := i) in Sems.
      + inversion_clear Trans as [|?? Closed]; apply IHeqs in Sems;
          try eapply state_closed_insts_Call; eauto.
        assert (absent_list xs).
        { rewrite Abs in Exps; inversion_clear Exps as [?????? Clock|];
            [contradict Clock; apply not_subrate_clock|].
          subst; apply all_absent_spec.
        }
        apply IH in SemBlock; auto.
        unfold sub_inst in *; apply add_remove_inst_same in Find'.
        rewrite Find', SemBlock.
        destruct b.
        * admit.
        * destruct Rst as (?& Find & E); auto.
          apply add_remove_inst_same in Find.
          now rewrite Find, E, Sems.
      + admit.
  Qed.

  Lemma sem_block_absent:
    forall P b xs S ys S',
      sem_block P b S xs ys S' ->
      absent_list xs ->
      absent_list ys /\ (Ordered_blocks P -> S' ≋ S).
  Proof.
    intros ** Sem Abs; split.
    - inversion_clear Sem; intuition.
    - intro Ord.
      revert dependent xs; revert b S S' ys.
      induction P as [|block]; intros;
        inversion_clear Sem as [?????????? Clock Find Ins ???? Heqs Closed ? Closed'];
        try now inv Find.
      pose proof Find; simpl in Find.
      destruct (ident_eqb (b_name block) b) eqn: Eq.
      + inv Find.
        assert ( ~ Is_block_in (b_name bl) (b_eqs bl))
          by (eapply find_block_not_Is_block_in; eauto).
        apply sem_equations_cons in Heqs; auto.
        assert (base = false).
        { rewrite <-Bool.not_true_iff_false.
          intro E; apply Clock in E.
          apply Forall2_length in Ins.
          destruct xs.
          - rewrite map_length in Ins; simpl in Ins.
            pose proof (b_ingt0 bl); omega.
          - inv E; inv Abs; congruence.
        }
        inversion_clear Closed as [?????? Lasts Insts];
          inversion_clear Closed' as [?????? Lasts' Insts'].
        repeat match goal with
                 H: find_block ?b ?P = _, H': find_block ?b ?P = _ |- _ =>
                 rewrite H in H'; inv H'
               end.
        rewrite b_lasts_in_eqs in Lasts, Lasts'.
        setoid_rewrite b_states_in_eqs in Insts;
          setoid_rewrite b_states_in_eqs in Insts'.
        (* rewrite b_states_in_eqs in Insts.  *)
        (* inv Ord. *)
        (* eapply sem_equations_absent; eauto. *)
        admit.
      + inv Ord; eapply IHP; eauto.
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
    - unfold sub_inst; setoid_rewrite find_inst_gempty; congruence.
  Qed.

  (* Lemma sem_reset_false: *)
  (*   forall P S b bl P', *)
  (*     find_block b P = Some (bl, P') -> *)
  (*     well_formed_state P S -> *)
  (*     sem_reset P b false S S. *)
  (* Proof. *)
  (*   induction S as [?? IH] using memory_ind'; intros ** Find WF. *)
  (*   inversion_clear WF as [?? Spec]. *)
  (*   econstructor; eauto. *)
  (*   - unfold reset_lasts, reset_last; simpl. *)
  (*     induction xvs as [|(i, Si)]; simpl; auto. *)
  (*     rewrite <-IHxvs; auto. *)
  (*   - intros ** Sub. *)
  (*     exists S'; split; auto. *)
  (*     pose proof Sub as WF; apply Spec in WF as (?&?&?&?). *)
  (*     unfold sub_inst, find_inst in Sub. *)
  (*     apply Environment.find_in, in_map with (f := snd) in Sub. *)
  (*     simpl in Sub. *)
  (*     eapply In_Forall in IH; eauto. *)
  (* Qed. *)


 (*  (** ** Liftings of instantaneous semantics *) *)

(*   Section LiftSemantics. *)

(*     Variable base : stream bool. *)
(*     Variable H : history. *)
(*     Variable E : evolution. *)

(*     Definition sample {A} (n: nat) (xs: stream A) := xs n. *)
(*     Hint Unfold sample. *)

(*     Definition restr_evol (n: nat): state := *)
(*       mmap (sample n) E. *)

(*     Definition restr_hist (n: nat): env := *)
(*       PM.map (sample n) H. *)
(*     Hint Unfold restr_hist. *)

(*     Definition lift {A B} (sem: bool -> env -> state -> clock -> A -> B -> Prop) *)
(*                ck x (ys: stream B): Prop := *)
(*       forall n, sem (bk n) (restr_hist n) (restr_evol n) ck x (ys n). *)
(*     Hint Unfold lift. *)

(*     Definition lift' {A B} (sem: env -> state -> clock -> A -> B -> Prop) ck x (ys: stream B): Prop := *)
(*       forall n, sem (restr_hist n) (restr_evol n) ck x (ys n). *)
(*     Hint Unfold lift'. *)

(*     Definition lift'' {A B} (sem: env -> clock -> A -> B -> Prop) ck x (ys: stream B): Prop := *)
(*       forall n, sem (restr_hist n) ck x (ys n). *)
(*     Hint Unfold lift''. *)

(*     Definition lift''' {A B} (sem: state -> clock -> A -> B -> Prop) ck x (ys: stream B): Prop := *)
(*       forall n, sem (restr_evol n) ck x (ys n). *)
(*     Hint Unfold lift'''. *)

(*     Definition lift'''' {A B} (sem: bool -> env -> state -> A -> B -> Prop) *)
(*                x (ys: stream B): Prop := *)
(*       forall n, sem (bk n) (restr_hist n) (restr_evol n) x (ys n). *)
(*     Hint Unfold lift''''. *)

(*     Definition lift''''' {A B} (sem: env -> A -> B -> Prop) *)
(*                x (ys: stream B): Prop := *)
(*       forall n, sem (restr_hist n) x (ys n). *)
(*     Hint Unfold lift'''''. *)
(*     (* Definition lift''' {A B} (sem: bool -> env -> A -> B -> Prop) x (ys: stream B): Prop := *) *)
(*     (*   forall n, sem (bk n) (restr_hist n) x (ys n). *) *)
(*     (* Hint Unfold lift'''. *) *)

(*     Definition sem_clock (ck: clock) (xs: stream bool): Prop := *)
(*       lift'''' sem_clock ck xs. *)

(*     Definition sem_var ck (x: var) (xs: stream value): Prop := *)
(*       lift sem_var ck x xs. *)

(*     (* Definition sem_last (x: ident) (xs: stream value): Prop := *) *)
(*     (*   lift'' sem_last x xs. *) *)

(*     Definition sem_var_var (x: ident) (xs: stream value): Prop := *)
(*       lift''''' sem_var_var x xs. *)

(*     Definition sem_state_var ck (x: ident) (xs: stream value): Prop := *)
(*       lift sem_state_var ck x xs. *)

(*     Definition sem_vars (x: idents) (xs: stream (list value)): Prop := *)
(*       lift''''' sem_vars x xs. *)

(*     Definition sem_laexp ck (e: lexp) (xs: stream value): Prop := *)
(*       lift'''' (fun base R S => sem_laexp base R S ck) e xs. *)

(*     Definition sem_laexps (ck: clock) (e: list lexp) (xs: stream (list value)): Prop := *)
(*       lift'''' (fun base R S => sem_laexps base R S ck) e xs. *)

(*     Definition sem_lexp ck (e: lexp) (xs: stream value): Prop := *)
(*       lift sem_lexp ck e xs. *)

(*     Definition sem_lexps ck (e: list lexp) (xs: stream (list value)): Prop := *)
(*       lift sem_lexps ck e xs. *)

(*     Definition sem_caexp ck (c: cexp) (xs: stream value): Prop := *)
(*       lift'''' (fun base R S => sem_caexp base R S ck) c xs. *)

(*     Definition sem_cexp ck (c: cexp) (xs: stream value): Prop := *)
(*       lift sem_cexp ck c xs. *)

(*   End LiftSemantics. *)

(*   (** ** Time-dependent semantics *) *)

(*   Definition instant_same_clock (l : list value) : Prop := *)
(*     absent_list l \/ present_list l. *)

(*   Definition same_clock (l_s : stream (list value)) : Prop := *)
(*     forall n, instant_same_clock (l_s n). *)

(*   Definition clock_of (xss: stream (list value))(bs: stream bool): Prop := *)
(*     forall n, *)
(*       present_list (xss n) <-> bs n = true. *)

(*   Definition clock_of' (xss: stream (list value)) : stream bool := *)
(*     fun n => forallb (fun v => negb (v ==b absent)) (xss n). *)

(*   Lemma clock_of_equiv: *)
(*     forall xss, clock_of xss (clock_of' xss). *)
(*   Proof. *)
(*     split; intros H. *)
(*     - unfold clock_of'. *)
(*       rewrite forallb_forall. *)
(*       intros; rewrite Bool.negb_true_iff. *)
(*       rewrite not_equiv_decb_equiv. *)
(*       eapply In_Forall in H; eauto. *)
(*     - unfold clock_of' in H. *)
(*       rewrite forallb_forall in H. *)
(*       apply all_In_Forall; intros ** Hin E. *)
(*       specialize (H _ Hin). *)
(*       rewrite Bool.negb_true_iff, not_equiv_decb_equiv in H. *)
(*       apply H; eauto. *)
(*   Qed. *)

(*   Lemma clock_of_equiv': *)
(*     forall xss bk, *)
(*       clock_of xss bk -> *)
(*       bk ≈ clock_of' xss. *)
(*   Proof. *)
(*     intros ** H n; specialize (H n). *)
(*     unfold clock_of'. *)
(*     induction (xss n) as [|v]; simpl. *)
(*     - apply H; constructor. *)
(*     - destruct v. *)
(*       + simpl. *)
(*         rewrite <-Bool.not_true_iff_false, <-H. *)
(*         inversion 1; auto. *)
(*       + simpl. *)
(*         apply IHl; rewrite <-H. *)
(*         split; intro P. *)
(*         * constructor; auto. *)
(*           intro; discriminate. *)
(*         * inv P; auto. *)
(*   Qed. *)

(*   (* Record mvalues := *) *)
(*   (*   Mvalues { content: stream val; *) *)
(*   (*             reset: stream bool *) *)
(*   (*           }. *) *)

(*   (* (* Definition memory := RMemory.memory mvalue. *) *) *)
(*   (* Definition memories := RMemory.memory mvalues. *) *)

(*   (* Inductive reset_regs: stream bool -> memories -> Prop := *) *)
(*   (*   reset_regs_intro: *) *)
(*   (*     forall M rs, *) *)
(*   (*       (forall x mvs, *) *)
(*   (*           find_val x M = Some mvs -> *) *)
(*   (*           forall n, rs n = true -> mvs.(reset) n = true) -> *) *)
(*   (*       (forall x M', *) *)
(*   (*           sub_inst x M M' -> *) *)
(*   (*           reset_regs rs M') -> *) *)
(*   (*       reset_regs rs M. *) *)

(*   (* (* Definition next (n: nat) (mvs: mvalues) (v0 v: val) : Prop := *) *) *)
(*   (* (*   mvs.(content) (S n) = (if mvs.(reset) (S n) then v0 else v). *) *) *)

(*   (* (* Inductive fby_spec: nat -> val -> value -> mvalues -> value -> Prop := *) *) *)
(*   (* (* | fby_spec_present: *) *) *)
(*   (* (*     forall n v0 v mvs, *) *) *)
(*   (* (*       next n mvs v0 v -> *) *) *)
(*   (* (*       fby_spec n v0 (present v) mv (mv.(content) n) *) *) *)
(*   (* (* | fby_spec_absent: *) *) *)
(*   (* (*     forall n v0 v mvs, *) *) *)
(*   (* (*       next n mvs v0 (mvs.(content) n) -> *) *) *)
(*   (* (*       fby_spec n v0 absent mvs absent. *) *) *)

(*   (* Inductive mfby: ident -> val -> stream value -> memories -> stream value -> Prop := *) *)
(*   (*   mfby_intro: *) *)
(*   (*     forall x mvs v0 ls M xs, *) *)
(*   (*       find_val x M = Some mvs -> *) *)
(*   (*       mvs.(content) 0 = v0 -> *) *)
(*   (*       (forall n, match ls n with *) *)
(*   (*             | absent => *) *)
(*   (*               mvs.(content) (S n) = (if mvs.(reset) (S n) then v0 else mvs.(content) n) *) *)
(*   (*               /\ xs n = absent *) *)
(*   (*             | present v => *) *)
(*   (*               mvs.(content) (S n) = (if mvs.(reset) (S n) then v0 else v) *) *)
(*   (*               /\ xs n = present (mvs.(content) n) *) *)
(*   (*             end) -> *) *)
(*   (*       mfby x v0 ls M xs. *) *)

(*   (* Definition fby_eq (mems: PS.t) (eq: equation) : PS.t := *) *)
(*   (*   match eq with *) *)
(*   (*   | EqFby x _ _ _ => PS.add x mems *) *)
(*   (*   | _ => mems *) *)
(*   (*   end. *) *)

(*   (* Definition fbys (eqs: list equation) : PS.t := *) *)
(*   (*   fold_left fby_eq eqs PS.empty. *) *)

(*   (* Definition inst_eq (insts: PS.t) (eq: equation) : PS.t := *) *)
(*   (*   match eq with *) *)
(*   (*   | EqReset _ _ i _ => PS.add i insts *) *)
(*   (*   | EqCall _ _ _ i _ => PS.add i insts *) *)
(*   (*   | _ => insts *) *)
(*   (*   end. *) *)

(*   (* Definition insts (eqs: list equation) : PS.t := *) *)
(*   (*   fold_left inst_eq eqs PS.empty. *) *)

(*   (* Definition well_structured_memories (eqs: list equation) (M: memories) := *) *)
(*   (*   (forall x, *) *)
(*   (*       find_val x M <> None <-> PS.In x (fbys eqs)) *) *)
(*   (*   /\ forall x, *) *)
(*   (*     find_inst x M <> None <-> PS.In x (insts eqs). *) *)

(*   Definition reset_of_value (v: value) : bool := *)
(*     match v with *)
(*     | present x => x ==b true_val *)
(*     | absent => false *)
(*     end. *)

(*   Definition reset_of (xs: stream value) : stream bool := *)
(*     fun n => reset_of_value (xs n). *)

(*   Definition reset_last (bl: block) (r: stream bool) (x: ident) (xs: stream val) := *)
(*     fun n => *)
(*       if r n then *)
(*         match find_init x bl with *)
(*         | Some c => sem_const c *)
(*         | None => false_val *)
(*         end *)
(*       else xs n. *)

(*   Definition reset_lasts (bl: block) (r: stream bool) (E E0: evolution) := *)
(*     values E0 = Env.mapi (reset_last bl r) (values E). *)

(*   Section BlockSemantics. *)

(*     Variable P: program. *)

(*     Inductive sem_reset: ident -> stream bool -> evolution -> evolution -> Prop := *)
(*       SReset: *)
(*         forall b (r: stream bool) E E0 bl P', *)
(*           find_block b P = Some (bl, P') -> *)
(*           reset_lasts bl r E E0 -> *)
(*           (forall b' E', *)
(*               sub_inst b' E E' -> *)
(*               exists E0', *)
(*                 sub_inst b' E0 E0' *)
(*                 /\ sem_reset b' r E' E0') -> *)
(*           sem_reset b r E E0. *)

(*     Inductive sem_equation: stream bool -> history -> evolution -> transient_evolutions -> evolution -> equation -> Prop := *)
(*     | SEqDef: *)
(*         forall bk H E T E' x xs ck ce, *)
(*           sem_var_var H x xs -> *)
(*           sem_caexp bk H E ck ce xs -> *)
(*           sem_equation bk H E T E' (EqDef x ck ce) *)
(*     | SEqNext: *)
(*         forall bk H E T E' x ck e xs ls, *)
(*           sem_state_var bk H E' ck x xs -> *)
(*           sem_laexp bk H E ck e ls -> *)
(*           sem_equation bk H E T E' (EqNext x ck e) *)
(*     | SEqTransient: *)
(*         forall bk H E T E' s ck Es, *)
(*           sub_inst s E Es -> *)
(*           PM.find s T = Some Es -> *)
(*           sem_equation bk H E T E' (EqTransient s ck) *)
(*     | SEqReset: *)
(*         forall bk H E T E' ck b s r rs Es E0, *)
(*           sem_var bk H E ck r rs -> *)
(*           sub_inst s E Es -> *)
(*           sem_reset b (reset_of rs) Es E0 -> *)
(*           PM.find s T = Some E0 -> *)
(*           sem_equation bk H E T E' (EqReset s ck b r) *)
(*     | SEqCall: *)
(*         forall bk H E T E' ys ck b s es ess Es oss Es', *)
(*           sem_laexps bk H E ck es ess -> *)
(*           PM.find s T = Some Es -> *)
(*           sem_block b Es ess oss Es' -> *)
(*           sem_vars H ys oss -> *)
(*           sub_inst s E' Es' -> *)
(*           sem_equation bk H E T E' (EqCall s ys ck b es) *)

(*     with sem_block: ident -> evolution -> stream (list value) -> stream (list value) -> evolution -> Prop := *)
(*            SBlock: *)
(*              forall b bl P' E T E' H xss yss bk, *)
(*                clock_of xss bk -> *)
(*                find_block b P = Some (bl, P') -> *)
(*                sem_vars H (map fst bl.(b_in)) xss -> *)
(*                sem_vars H (map fst bl.(b_out)) yss -> *)
(*                same_clock xss -> *)
(*                same_clock yss -> *)
(*                (forall n, absent_list (xss n) <-> absent_list (yss n)) -> *)
(*                Forall (sem_equation bk H E T E') bl.(b_eqs) -> *)
(*                (* well_structured_memories bl.(b_eqs) M -> *) *)
(*                sem_block b E xss yss E'. *)

(*   End BlockSemantics. *)

(*   Section sem_block_mult. *)
(*     Variable P: program. *)

(*     Variable P_equation: stream bool -> history -> evolution -> transient_evolutions -> evolution -> equation -> Prop. *)
(*     Variable P_block: ident -> evolution -> stream (list value) -> stream (list value) -> evolution -> Prop. *)

(*     Hypothesis EqDefCase: *)
(*       forall bk H E T E' x xs ck ce, *)
(*         sem_var_var H x xs -> *)
(*         sem_caexp bk H E ck ce xs -> *)
(*         P_equation bk H E T E' (EqDef x ck ce). *)

(*     Hypothesis EqNextCase: *)
(*       forall bk H E T E' x ck e xs ls, *)
(*         sem_state_var bk H E' ck x xs -> *)
(*         sem_laexp bk H E ck e ls -> *)
(*         P_equation bk H E T E' (EqNext x ck e). *)

(*     Hypothesis EqTransientCase: *)
(*       forall bk H E T E' s ck Es, *)
(*         sub_inst s E Es -> *)
(*         PM.find s T = Some Es -> *)
(*         P_equation bk H E T E' (EqTransient s ck). *)

(*     Hypothesis EqResetCase: *)
(*       forall bk H E T E' ck b s r rs Es E0, *)
(*         sem_var bk H E ck r rs -> *)
(*         sub_inst s E Es -> *)
(*         sem_reset P b (reset_of rs) Es E0 -> *)
(*         PM.find s T = Some E0 -> *)
(*         P_equation bk H E T E' (EqReset s ck b r). *)

(*     Hypothesis EqCallCase: *)
(*       forall bk H E T E' s ys ck b es ess Es oss Es', *)
(*         sem_laexps bk H E ck es ess -> *)
(*         PM.find s T = Some Es -> *)
(*         sem_block P b Es ess oss Es' -> *)
(*         sem_vars H ys oss -> *)
(*         sub_inst s E' Es' -> *)
(*         P_block b Es ess oss Es' -> *)
(*         P_equation bk H E T E' (EqCall s ys ck b es). *)

(*     Hypothesis BlockCase: *)
(*       forall b bl P' H E T E' xss yss bk, *)
(*         clock_of xss bk -> *)
(*         find_block b P = Some (bl, P') -> *)
(*         sem_vars H (map fst bl.(b_in)) xss -> *)
(*         sem_vars H (map fst bl.(b_out)) yss -> *)
(*         same_clock xss -> *)
(*         same_clock yss -> *)
(*         (forall n, absent_list (xss n) <-> absent_list (yss n)) -> *)
(*         Forall (sem_equation P bk H E T E') bl.(b_eqs) -> *)
(*         Forall (P_equation bk H E T E') bl.(b_eqs) -> *)
(*         P_block b E xss yss E'. *)

(*     Fixpoint sem_equation_mult *)
(*             (b: stream bool) (H: history) (E: evolution) (T: transient_evolutions) (E': evolution) (e: equation) *)
(*             (Sem: sem_equation P b H E T E' e) {struct Sem} *)
(*       : P_equation b H E T E' e *)
(*     with sem_block_mult *)
(*            (f: ident) (E: evolution) (xss oss: stream (list value)) (E': evolution) *)
(*            (Sem: sem_block P f E xss oss E') {struct Sem} *)
(*          : P_block f E xss oss E'. *)
(*     Proof. *)
(*       - destruct Sem; eauto. *)
(*       - destruct Sem. *)
(*         eapply BlockCase; eauto. *)
(*         match goal with H: Forall _ _ |- _ => induction H; auto end. *)
(*     Qed. *)

(*     Combined Scheme sem_equation_block_ind from *)
(*              sem_equation_mult, sem_block_mult. *)

(*   End sem_block_mult. *)

(*   (** Morphisms properties *) *)

(*   (* Add Parametric Morphism b A B sem H E : (@lift b H E A B sem) *) *)
(*   (*     with signature eq ==> @eq_str B ==> Basics.impl *) *)
(*   (*       as lift_eq_str. *) *)
(*   (* Proof. *) *)
(*   (*   intros x xs xs' Eq Lift n. *) *)
(*   (*   rewrite <-Eq; auto. *) *)
(*   (* Qed. *) *)

(*   (* Add Parametric Morphism A B sem H E : (@lift' H E A B sem) *) *)
(*   (*     with signature eq ==> @eq_str B ==> Basics.impl *) *)
(*   (*       as lift'_eq_str. *) *)
(*   (* Proof. *) *)
(*   (*   intros x xs xs' Eq Lift n. *) *)
(*   (*   rewrite <-Eq; auto. *) *)
(*   (* Qed. *) *)

(*   (* Add Parametric Morphism A B sem E : (@lift'' E A B sem) *) *)
(*   (*     with signature eq ==> @eq_str B ==> Basics.impl *) *)
(*   (*       as lift''_eq_str. *) *)
(*   (* Proof. *) *)
(*   (*   intros x xs xs' Eq Lift n. *) *)
(*   (*   rewrite <-Eq; auto. *) *)
(*   (* Qed. *) *)

(*   (* Add Parametric Morphism A B sem H : (@lift''' H A B sem) *) *)
(*   (*     with signature eq ==> @eq_str B ==> Basics.impl *) *)
(*   (*       as lift'''_eq_str. *) *)
(*   (* Proof. *) *)
(*   (*   intros x xs xs' Eq Lift n. *) *)
(*   (*   rewrite <-Eq; auto. *) *)
(*   (* Qed. *) *)

(*   (* Add Parametric Morphism : clock_of *) *)
(*   (*     with signature eq_str ==> eq ==> Basics.impl *) *)
(*   (*       as clock_of_eq_str. *) *)
(*   (* Proof. *) *)
(*   (*   unfold clock_of. intros ** E b Pres n. *) *)
(*   (*   split; intros H. *) *)
(*   (*   - apply Pres. *) *)
(*   (*     specialize (E n). *) *)
(*   (*     induction H; rewrite E; constructor; auto. *) *)
(*   (*   - apply Pres in H. *) *)
(*   (*     specialize (E n). *) *)
(*   (*     induction H; rewrite <-E; constructor; auto. *) *)
(*   (* Qed. *) *)

(*   (* Add Parametric Morphism : reset_of *) *)
(*   (*     with signature eq_str ==> eq_str *) *)
(*   (*       as reset_of_eq_str. *) *)
(*   (* Proof. *) *)
(*   (*   unfold reset_of. intros ** E n. *) *)
(*   (*   now rewrite E. *) *)
(*   (* Qed. *) *)

(*   (* Add Parametric Morphism : reset_regs *) *)
(*   (*     with signature eq_str ==> eq ==> Basics.impl *) *)
(*   (*       as reset_regs_eq_str. *) *)
(*   (* Proof. *) *)
(*   (*   intros ** E M Rst. *) *)
(*   (*   induction Rst; constructor; eauto. *) *)
(*   (* Qed. *) *)

(*   Add Parametric Morphism : same_clock *)
(*       with signature eq_str ==> Basics.impl *)
(*         as same_clock_eq_str. *)
(*   Proof. *)
(*     unfold same_clock; intros ** E ? ?; rewrite <-E; auto. *)
(*   Qed. *)

(*   (** ** Clocking property *) *)

(*   Lemma not_subrate_clock: *)
(*     forall R S ck, *)
(*       ~ sem_clock_instant false R S ck true. *)
(*   Proof. *)
(*     intros ** Sem; induction ck; inv Sem. *)
(*     now apply IHck. *)
(*   Qed. *)

(*   Lemma present_not_absent_list: *)
(*     forall xs (vs: list val), *)
(*       instant_same_clock xs -> *)
(*       ~ absent_list xs -> *)
(*       present_list xs. *)
(*   Proof. *)
(*     intros ** Hsamexs Hnabs. *)
(*     now destruct Hsamexs. *)
(*   Qed. *)

(*   Lemma sem_vars_gt0: *)
(*     forall H (xs: list (ident * type)) ls, *)
(*       0 < length xs -> *)
(*       sem_vars H (map fst xs) ls -> *)
(*       forall n, 0 < length (ls n). *)
(*   Proof. *)
(*     intros ** Hgt0 Hsem n. *)
(*     specialize (Hsem n). *)
(*     apply Forall2_length in Hsem. *)
(*     rewrite map_length in Hsem. *)
(*     now rewrite Hsem in Hgt0. *)
(*   Qed. *)

(*   Ltac assert_const_length xss := *)
(*     match goal with *)
(*       H: sem_vars _ _ xss |- _ => *)
(*       let H' := fresh in *)
(*       let k := fresh in *)
(*       let k' := fresh in *)
(*       assert (wf_streams xss) *)
(*         by (intros k k'; pose proof H as H'; *)
(*             unfold sem_vars, lift in *; *)
(*             specialize (H k); specialize (H' k'); *)
(*             apply Forall2_length in H; apply Forall2_length in H'; *)
(*             now rewrite H in H') *)
(*     end. *)

(*   (** ** Determinism of the semantics *) *)

(*   (** *** Instantaneous semantics *) *)

(*   Section InstantDeterminism. *)

(*     Variable base: bool. *)
(*     Variable R: env. *)
(*     Variable S: state. *)

(*     Lemma sem_var_var_instant_det: *)
(*       forall x v1 v2, *)
(*         sem_var_var_instant R x v1 *)
(*         -> sem_var_var_instant R x v2 *)
(*         -> v1 = v2. *)
(*     Proof. *)
(*       intros x v1 v2 H1 H2. *)
(*       inversion_clear H1 as [Hf1]; *)
(*         inversion_clear H2 as [Hf2]; *)
(*         congruence. *)
(*     Qed. *)
(*     Hint Resolve sem_var_var_instant_det. *)

(*     Lemma sem_clock_state_var_var_instant_det: *)
(*       (forall ck v1, *)
(*           sem_clock_instant base R S ck v1 -> *)
(*           forall v2, *)
(*             sem_clock_instant base R S ck v2 -> *)
(*             v1 = v2) *)
(*       /\ *)
(*       (forall ck x v1, *)
(*           sem_state_var_instant base R S ck x v1 -> *)
(*           forall v2, *)
(*             sem_state_var_instant base R S ck x v2 -> *)
(*             v1 = v2) *)
(*       /\ *)
(*       (forall ck x v1, *)
(*           sem_var_instant base R S ck x v1 -> *)
(*           forall v2, *)
(*             sem_var_instant base R S ck x v2 -> *)
(*             v1 = v2). *)
(*     Proof. *)
(*       apply sem_clock_state_var_var_mut. *)
(*       - intro; now inversion 1. *)
(*       - intros ** VarDet ?? Sem. *)
(*         inversion Sem as [ | | |??? b' ? SVar]; subst; auto. *)
(*         apply VarDet in SVar; inv SVar. *)
(*         destruct b'; simpl in *; congruence. *)
(*       - intros ** Sem; inv Sem; auto. *)
(*       - intros ** VarDet ?? Sem. *)
(*         inversion Sem as [ |????? SVar| |]; subst; auto. *)
(*         apply VarDet in SVar; inv SVar. *)
(*         destruct b; simpl in *; congruence. *)
(*       - intros ** ClockDet ? Sem. *)
(*         inversion_clear Sem as [|??? SClock]; try congruence. *)
(*         apply ClockDet in SClock; discriminate. *)
(*       - intros ** ClockDet ? Sem. *)
(*         inversion_clear Sem as [???? SClock|]; auto. *)
(*         apply ClockDet in SClock; discriminate. *)
(*       - intros ** Sem; inv Sem; eauto. *)
(*       - intros ** Sem; inv Sem; auto. *)
(*     Qed. *)

(*     Corollary sem_clock_instant_det: *)
(*       forall ck v1 v2, *)
(*         sem_clock_instant base R S ck v1 *)
(*         -> sem_clock_instant base R S ck v2 *)
(*         -> v1 = v2. *)
(*     Proof. *)
(*       intros; eapply sem_clock_state_var_var_instant_det; eauto. *)
(*     Qed. *)
(*     Hint Resolve sem_clock_instant_det. *)

(*     Corollary sem_state_var_instant_det: *)
(*       forall x ck v1 v2, *)
(*         sem_state_var_instant base R S ck x v1 *)
(*         -> sem_state_var_instant base R S ck x v2 *)
(*         -> v1 = v2. *)
(*     Proof. *)
(*       intros; eapply (proj1 (proj2 sem_clock_state_var_var_instant_det)); eauto. *)
(*     Qed. *)
(*     Hint Resolve sem_state_var_instant_det. *)

(*     Corollary sem_var_instant_det: *)
(*       forall x ck v1 v2, *)
(*         sem_var_instant base R S ck x v1 *)
(*         -> sem_var_instant base R S ck x v2 *)
(*         -> v1 = v2. *)
(*     Proof. *)
(*       intros; eapply sem_clock_state_var_var_instant_det; eauto. *)
(*     Qed. *)
(*     Hint Resolve sem_var_instant_det. *)

(*     Lemma sem_lexp_instant_det: *)
(*       forall e ck v1 v2, *)
(*         sem_lexp_instant base R S ck e v1 *)
(*         -> sem_lexp_instant base R S ck e v2 *)
(*         -> v1 = v2. *)
(*     Proof. *)
(*       induction e (* using lexp_ind2 *). *)
(*       - (* Econst *) *)
(*         do 2 inversion_clear 1; destruct base; congruence. *)
(*       - (* Evar *) *)
(*         intros ** S1 S2; inv S1; inv S2; eauto. *)
(*       - (* Ewhen *) *)
(*         intros ** S1 S2; inv S1; inv S2; eauto; *)
(*           repeat progress match goal with *)
(*                           | H1:sem_lexp_instant ?b ?R ?S ?ck ?e ?v1, *)
(*                                H2:sem_lexp_instant ?b ?R ?S ?ck ?e ?v2 |- _ => *)
(*                             apply IHe with (1:=H1) in H2 *)
(*                           | H1:sem_var_instant ?b ?R ?S ?ck ?i ?v1, *)
(*                                H2:sem_var_instant ?b ?R ?S ?ck ?i ?v2 |- _ => *)
(*                             apply sem_var_instant_det with (1:=H1) in H2 *)
(*                           | Hp:present _ = present _ |- _ => *)
(*                             injection Hp; intro; subst *)
(*                           | H1:val_to_bool _ = Some _, *)
(*                                H2:val_to_bool _ = Some (negb _) |- _ => *)
(*                             rewrite H2 in H1; exfalso; injection H1; *)
(*                               now apply Bool.no_fixpoint_negb *)
(*                           end; subst; auto. *)
(*       - (* Eunop *) *)
(*         intros ** S1 S2; inv S1; inv S2; *)
(*           repeat progress match goal with *)
(*                           | H1:sem_lexp_instant _ _ _ _ e _, H2:sem_lexp_instant _ _ _ _ e _ |- _ => *)
(*                             apply IHe with (1:=H1) in H2; inversion H2; subst *)
(*                           | H1:sem_unop _ _ _ = _, H2:sem_unop _ _ _ = _ |- _ => *)
(*                             rewrite H1 in H2; injection H2; intro; subst *)
(*                           | H1:sem_lexp_instant _ _ _ _ _ (present _), *)
(*                                H2:sem_lexp_instant _ _ _ _ _ absent |- _ => *)
(*                             apply IHe with (1:=H1) in H2 *)
(*                           end; try auto. *)
(*       - (* Ebinop *) *)
(*         intros ** S1 S2; inv S1; inv S2; *)
(*           repeat progress match goal with *)
(*                           | H1:sem_lexp_instant _ _ _ _ e1 _, H2:sem_lexp_instant _ _ _ _ e1 _ |- _ => *)
(*                             apply IHe1 with (1:=H1) in H2 *)
(*                           | H1:sem_lexp_instant _ _ _ _ e2 _, H2:sem_lexp_instant _ _ _ _ e2 _ |- _ => *)
(*                             apply IHe2 with (1:=H1) in H2 *)
(*                           | H1:sem_binop _ _ _ _ _ = Some ?v1, *)
(*                                H2:sem_binop _ _ _ _ _ = Some ?v2 |- _ => *)
(*                             rewrite H1 in H2; injection H2; intro; subst *)
(*                           | H:present _ = present _ |- _ => injection H; intro; subst *)
(*                           end; subst; auto; discriminate. *)
(*     Qed. *)
(*     Hint Resolve sem_lexp_instant_det. *)

(*     Lemma sem_laexp_instant_det: *)
(*       forall ck e v1 v2, *)
(*         sem_laexp_instant base R S ck e v1 *)
(*         -> sem_laexp_instant base R S ck e v2 *)
(*         -> v1 = v2. *)
(*     Proof. *)
(*       do 2 inversion_clear 1; eauto. *)
(*     Qed. *)

(*     Lemma sem_lexps_instant_det: *)
(*       forall les ck cs1 cs2, *)
(*         sem_lexps_instant base R S ck les cs1 -> *)
(*         sem_lexps_instant base R S ck les cs2 -> *)
(*         cs1 = cs2. *)
(*     Proof. *)
(*       intros ???; eapply Forall2_det; eauto. *)
(*     Qed. *)
(*     Hint Resolve sem_lexps_instant_det. *)

(*     Lemma sem_laexps_instant_det: *)
(*       forall ck e v1 v2, *)
(*         sem_laexps_instant base R S ck e v1 *)
(*         -> sem_laexps_instant base R S ck e v2 *)
(*         -> v1 = v2. *)
(*     Proof. *)
(*       do 2 inversion_clear 1; eauto. *)
(*     Qed. *)

(*     Lemma sem_cexp_instant_det: *)
(*       forall e ck v1 v2, *)
(*         sem_cexp_instant base R S ck e v1 *)
(*         -> sem_cexp_instant base R S ck e v2 *)
(*         -> v1 = v2. *)
(*     Proof. *)
(*       induction e; *)
(*         do 2 inversion_clear 1; *)
(*         try repeat progress match goal with *)
(*                             | H1: sem_cexp_instant ?bk ?R ?S ?ck ?e ?l, *)
(*                                   H2: sem_cexp_instant ?bk ?R ?S ?ck ?e ?r |- _ => *)
(*                               apply IHe1 with (1:=H1) in H2 *)
(*                                                          || apply IHe2 with (1:=H1) in H2; *)
(*                                 injection H2; intro; subst *)
(*                             | H1: sem_var_instant ?b ?R ?S ?ck ?i (present true_val), *)
(*                                   H2: sem_var_instant ?b ?R ?S ?ck ?i (present false_val) |- _ => *)
(*                               apply sem_var_instant_det with (1:=H1) in H2; *)
(*                                 exfalso; injection H2; now apply true_not_false_val *)
(*                             | H1: sem_lexp_instant ?bk ?R ?S ?ck ?l ?v1, *)
(*                                   H2: sem_lexp_instant ?bk ?R ?S ?ck ?l ?v2 |- _ => *)
(*                               apply sem_lexp_instant_det with (1:=H1) in H2; *)
(*                                 discriminate || injection H2; intro; subst *)
(*                             | H1: sem_var_instant ?bk ?R ?S ?ck ?i (present _), *)
(*                                   H2: sem_var_instant ?bk ?R ?S ?ck ?i absent |- _ => *)
(*                               apply sem_var_instant_det with (1:=H1) in H2; discriminate *)
(*                             | H1: val_to_bool _ = Some _, *)
(*                                   H2:val_to_bool _ = Some _ |- _ => *)
(*                               rewrite H1 in H2; injection H2; intro; subst *)
(*                             end; eauto. *)
(*     Qed. *)
(*     Hint Resolve sem_cexp_instant_det. *)

(*     Lemma sem_caexp_instant_det: *)
(*       forall ck e v1 v2, *)
(*         sem_caexp_instant base R S ck e v1 *)
(*         -> sem_caexp_instant base R S ck e v2 *)
(*         -> v1 = v2. *)
(*     Proof. *)
(*       intros until v2. *)
(*       do 2 inversion_clear 1; eauto. *)
(*     Qed. *)

(*   End InstantDeterminism. *)

(*   (** *** Lifted semantics *) *)

(*   (* Section LiftDeterminism. *) *)

(* (*     Variable bk : stream bool. *) *)
(* (*     Variable H : history. *) *)

(* (*     Require Import Logic.FunctionalExtensionality. *) *)

(* (*     Lemma lift_det: *) *)
(* (*       forall {A B} (P: bool -> env -> A -> B -> Prop) (bk: stream bool) *) *)
(* (*         x (xs1 xs2 : stream B), *) *)
(* (*         (forall b R v1 v2, P b R x v1 -> P b R x v2 -> v1 = v2) -> *) *)
(* (*         lift bk H P x xs1 -> lift bk H P x xs2 -> xs1 = xs2. *) *)
(* (*     Proof. *) *)
(* (*       intros ** Hpoint H1 H2. *) *)
(* (*       extensionality n. specialize (H1 n). specialize (H2 n). *) *)
(* (*       eapply Hpoint; eassumption. *) *)
(* (*     Qed. *) *)

(* (*     Lemma lift'_det: *) *)
(* (*       forall {A B} (P: env -> A -> B -> Prop) *) *)
(* (*         x (xs1 xs2 : stream B), *) *)
(* (*         (forall R v1 v2, P R x v1 -> P R x v2 -> v1 = v2) -> *) *)
(* (*         lift' H P x xs1 -> lift' H P x xs2 -> xs1 = xs2. *) *)
(* (*     Proof. *) *)
(* (*       intros ** Hpoint H1 H2. *) *)
(* (*       extensionality n. specialize (H1 n). specialize (H2 n). *) *)
(* (*       eapply Hpoint; eassumption. *) *)
(* (*     Qed. *) *)

(* (*     Ltac apply_lift sem_det := *) *)
(* (*       intros; eapply lift_det; try eassumption; *) *)
(* (*       compute; intros; eapply sem_det; eauto. *) *)

(* (*     Ltac apply_lift' sem_det := *) *)
(* (*       intros; eapply lift'_det; try eassumption; *) *)
(* (*       compute; intros; eapply sem_det; eauto. *) *)

(* (*     Lemma sem_var_det: *) *)
(* (*       forall x xs1 xs2, *) *)
(* (*         sem_var H x xs1 -> sem_var H x xs2 -> xs1 = xs2. *) *)
(* (*     Proof. *) *)
(* (*       apply_lift' sem_var_instant_det. *) *)
(* (*     Qed. *) *)

(* (*     Lemma sem_clock_det: *) *)
(* (*       forall ck bs1 bs2, *) *)
(* (*         sem_clock bk H ck bs1 -> sem_clock bk H ck bs2 -> bs1 = bs2. *) *)
(* (*     Proof. *) *)
(* (*       apply_lift sem_clock_instant_det. *) *)
(* (*     Qed. *) *)

(* (*     Lemma sem_lexp_det: *) *)
(* (*       forall e xs1 xs2, *) *)
(* (*         sem_lexp bk H e xs1 -> sem_lexp bk H e xs2 -> xs1 = xs2. *) *)
(* (*     Proof. *) *)
(* (*       apply_lift sem_lexp_instant_det. *) *)
(* (*     Qed. *) *)

(* (*     Lemma sem_lexps_det: *) *)
(* (*       forall les cs1 cs2, *) *)
(* (*         sem_lexps bk H les cs1 -> *) *)
(* (*         sem_lexps bk H les cs2 -> *) *)
(* (*         cs1 = cs2. *) *)
(* (*     Proof. *) *)
(* (*       apply_lift sem_lexps_instant_det. *) *)
(* (*     Qed. *) *)

(* (*     Lemma sem_laexp_det: *) *)
(* (*       forall ck e xs1 xs2, *) *)
(* (*         sem_laexp bk H ck e xs1 -> sem_laexp bk H ck e xs2 -> xs1 = xs2. *) *)
(* (*     Proof. *) *)
(* (*       apply_lift sem_laexp_instant_det. *) *)
(* (*     Qed. *) *)

(* (*     Lemma sem_laexps_det: *) *)
(* (*       forall ck e xs1 xs2, *) *)
(* (*         sem_laexps bk H ck e xs1 -> sem_laexps bk H ck e xs2 -> xs1 = xs2. *) *)
(* (*     Proof. *) *)
(* (*       apply_lift sem_laexps_instant_det. *) *)
(* (*     Qed. *) *)

(* (*     Lemma sem_cexp_det: *) *)
(* (*       forall c xs1 xs2, *) *)
(* (*         sem_cexp bk H c xs1 -> sem_cexp bk H c xs2 -> xs1 = xs2. *) *)
(* (*     Proof. *) *)
(* (*       apply_lift sem_cexp_instant_det. *) *)
(* (*     Qed. *) *)

(* (*     Lemma sem_caexp_det: *) *)
(* (*       forall ck c xs1 xs2, *) *)
(* (*         sem_caexp bk H ck c xs1 -> sem_caexp bk H ck c xs2 -> xs1 = xs2. *) *)
(* (*     Proof. *) *)
(* (*       apply_lift sem_caexp_instant_det. *) *)
(* (*     Qed. *) *)

(* (*   (* XXX: every semantics definition, including [sem_var] which doesn't *) *)
(* (* need it, takes a base clock value or base clock stream, except *) *)
(* (* [sem_var_instant]. For uniformity, we may want to pass a (useless) *) *)
(* (* clock to [sem_var_instant] too. *) *) *)

(* (*   End LiftDeterminism. *) *)

(*   (* Ltac sem_det := *) *)
(*   (*   match goal with *) *)
(*   (*   | H1: sem_clock_instant ?bk ?H ?C ?X, *) *)
(*   (*         H2: sem_clock_instant ?bk ?H ?C ?Y |- ?X = ?Y => *) *)
(*   (*     eapply sem_clock_instant_det; eexact H1 || eexact H2 *) *)
(*   (*   | H1: sem_clock ?bk ?H ?C ?X, *) *)
(*   (*         H2: sem_clock ?bk ?H ?C ?Y |- ?X = ?Y => *) *)
(*   (*     eapply sem_clock_det; eexact H1 || eexact H2 *) *)
(*   (*   | H1: sem_cexp_instant ?bk ?H ?C ?X, *) *)
(*   (*         H2: sem_cexp_instant ?bk ?H ?C ?Y |- ?X = ?Y => *) *)
(*   (*     eapply sem_cexp_instant_det; eexact H1 || eexact H2 *) *)
(*   (*   | H1: sem_cexp ?bk ?H ?C ?X, *) *)
(*   (*         H2: sem_cexp ?bk ?H ?C ?Y |- ?X = ?Y => *) *)
(*   (*     eapply sem_cexp_det; eexact H1 || eexact H2 *) *)
(*   (*   | H1: sem_lexps_instant ?bk ?H ?C ?X, *) *)
(*   (*         H2: sem_lexps_instant ?bk ?H ?C ?Y |- ?X = ?Y => *) *)
(*   (*     eapply sem_lexps_instant_det; eexact H1 || eexact H2 *) *)
(*   (*   | H1: sem_lexps ?bk ?H ?C ?X, *) *)
(*   (*         H2: sem_lexps ?bk ?H ?C ?Y |- ?X = ?Y => *) *)
(*   (*     eapply sem_lexps_det; eexact H1 || eexact H2 *) *)
(*   (*   | H1: sem_laexps_instant ?bk ?H ?ck ?C ?X, *) *)
(*   (*         H2: sem_laexps_instant ?bk ?H ?ck ?C ?Y |- ?X = ?Y => *) *)
(*   (*     eapply sem_laexps_instant_det; eexact H1 || eexact H2 *) *)
(*   (*   | H1: sem_laexps ?bk ?H ?ck ?C ?X, *) *)
(*   (*         H2: sem_laexps ?bk ?H ?ck ?C ?Y |- ?X = ?Y => *) *)
(*   (*     eapply sem_laexps_det; eexact H1 || eexact H2 *) *)
(*   (*   | H1: sem_lexp_instant ?bk ?H ?C ?X, *) *)
(*   (*         H2: sem_lexp_instant ?bk ?H ?C ?Y |- ?X = ?Y => *) *)
(*   (*     eapply sem_lexp_instant_det; eexact H1 || eexact H2 *) *)
(*   (*   | H1: sem_lexp ?bk ?H ?C ?X, *) *)
(*   (*         H2: sem_lexp ?bk ?H ?C ?Y |- ?X = ?Y => *) *)
(*   (*     eapply sem_lexp_det; eexact H1 || eexact H2 *) *)
(*   (*   | H1: sem_laexp_instant ?bk ?H ?CK ?C ?X, *) *)
(*   (*         H2: sem_laexp_instant ?bk ?H ?CK ?C ?Y |- ?X = ?Y => *) *)
(*   (*     eapply sem_laexp_instant_det; eexact H1 || eexact H2 *) *)
(*   (*   | H1: sem_laexp ?bk ?H ?CK ?C ?X, *) *)
(*   (*         H2: sem_laexp ?bk ?H ?CK ?C ?Y |- ?X = ?Y => *) *)
(*   (*     eapply sem_laexp_det; eexact H1 || eexact H2 *) *)
(*   (*   | H1: sem_var_instant ?H ?C ?X, *) *)
(*   (*         H2: sem_var_instant ?H ?C ?Y |- ?X = ?Y => *) *)
(*   (*     eapply sem_var_instant_det; eexact H1 || eexact H2 *) *)
(*   (*   | H1: sem_var ?H ?C ?X, *) *)
(*   (*         H2: sem_var ?H ?C ?Y |- ?X = ?Y => *) *)
(*   (*     eapply sem_var_det; eexact H1 || eexact H2 *) *)
(*   (*   end. *) *)
(*   (* Record mvalue := *) *)
(*   (*   Mvalue { content_i: val; *) *)
(*   (*            reset_i: bool *) *)
(*   (*          }. *) *)


(*   (** Morphisms properties *) *)

(*   Add Parametric Morphism P b E E': (fun xss yss => sem_block P b E xss yss E') *)
(*       with signature eq_str ==> eq_str ==> Basics.impl *)
(*         as sem_node_eq_str. *)
(*   Proof. *)
(*     intros ** E1 ? ? E2 Block. *)
(*     inv Block. *)
(*     econstructor; eauto; intro; try rewrite <-E1; try rewrite <-E2; auto. *)
(*   Qed. *)

(*   Lemma sem_block_wf: *)
(*     forall P f E E' xss yss, *)
(*       sem_block P f E xss yss E' -> *)
(*       wf_streams xss /\ wf_streams yss. *)
(*   Proof. *)
(*     intros ** Sem; split; inv Sem; *)
(*       assert_const_length xss; assert_const_length yss; auto. *)
(*   Qed. *)

(*   (* Lemma sem_EqCall_gt0: *) *)
(*   (*   forall P bk H M xs ck b i es, *) *)
(*   (*     sem_equation P bk H M (EqCall xs ck b i es) -> *) *)
(*   (*     0 < length xs. *) *)
(*   (* Proof. *) *)
(*   (*   inversion_clear 1 as [| | |????????????? Block' Vars]. *) *)
(*   (*   inversion_clear Block' as [??????????? Out]. *) *)
(*   (*   specialize (Out 0); specialize (Vars 0); simpl in *; *) *)
(*   (*     apply Forall2_length in Out; apply Forall2_length in Vars. *) *)
(*   (*   rewrite <-Out in Vars; rewrite Vars, map_length; apply b_outgt0. *) *)
(*   (* Qed. *) *)

(*   (* Lemma In_fold_left_fby_eq: *) *)
(*   (*   forall x eqs m, *) *)
(*   (*     PS.In x (fold_left fby_eq eqs m) *) *)
(*   (*     <-> PS.In x (fbys eqs) \/ PS.In x m. *) *)
(*   (* Proof. *) *)
(*   (*   unfold fbys. *) *)
(*   (*   induction eqs as [|eq]. *) *)
(*   (*   - split; auto. *) *)
(*   (*     destruct 1 as [H|]. *) *)
(*   (*     apply not_In_empty in H; contradiction. *) *)
(*   (*     auto. *) *)
(*   (*   - split. *) *)
(*   (*     + intro H. *) *)
(*   (*       simpl; rewrite IHeqs. *) *)
(*   (*       simpl in H; apply IHeqs in H; destruct H; auto. *) *)
(*   (*       destruct eq; auto. *) *)
(*   (*       apply PS.add_spec in H. *) *)
(*   (*       destruct H. *) *)
(*   (*       rewrite H; left; right; apply PS.add_spec; intuition. *) *)
(*   (*       intuition. *) *)
(*   (*     + destruct 1 as [H|H]. *) *)
(*   (*       * simpl in H; rewrite IHeqs in H; apply IHeqs; destruct H; auto. *) *)
(*   (*         right. *) *)
(*   (*         destruct eq; try (apply not_In_empty in H; contradiction). *) *)
(*   (*         simpl; apply PS.add_spec. *) *)
(*   (*         apply PS.add_spec in H; destruct H; *) *)
(*   (*           try apply not_In_empty in H; intuition. *) *)
(*   (*       * apply IHeqs; right; destruct eq; auto. *) *)
(*   (*         apply PS.add_spec; auto. *) *)
(*   (* Qed. *) *)

(*   (* Lemma In_fold_left_inst_eq: *) *)
(*   (*   forall x eqs m, *) *)
(*   (*     PS.In x (fold_left inst_eq eqs m) *) *)
(*   (*     <-> PS.In x (insts eqs) \/ PS.In x m. *) *)
(*   (* Proof. *) *)
(*   (*   unfold insts. *) *)
(*   (*   induction eqs as [|eq]. *) *)
(*   (*   - split; auto. *) *)
(*   (*     destruct 1 as [H|]. *) *)
(*   (*     apply not_In_empty in H; contradiction. *) *)
(*   (*     auto. *) *)
(*   (*   - split. *) *)
(*   (*     + intro H. *) *)
(*   (*       simpl; rewrite IHeqs. *) *)
(*   (*       simpl in H; apply IHeqs in H; destruct H; auto. *) *)
(*   (*       destruct eq; auto; apply PS.add_spec in H; destruct H; auto; *) *)
(*   (*         rewrite H; left; right; apply PS.add_spec; auto. *) *)
(*   (*     + destruct 1 as [H|H]. *) *)
(*   (*       * simpl in H; rewrite IHeqs in H; apply IHeqs; destruct H; auto. *) *)
(*   (*         right. *) *)
(*   (*         destruct eq; try (apply not_In_empty in H; contradiction); *) *)
(*   (*           simpl; apply PS.add_spec; *) *)
(*   (*             apply PS.add_spec in H; destruct H; auto; *) *)
(*   (*               apply not_In_empty in H; contradiction. *) *)
(*   (*       * apply IHeqs; right; destruct eq; auto; *) *)
(*   (*           apply PS.add_spec; auto. *) *)
(*   (* Qed. *) *)

(*   (* Lemma well_structured_def: *) *)
(*   (*   forall M x ck e eqs, *) *)
(*   (*     well_structured_memories (EqDef x ck e :: eqs) M <-> *) *)
(*   (*     well_structured_memories eqs M. *) *)
(*   (* Proof. *) *)
(*   (*   split; eauto. *) *)
(*   (* Qed. *) *)

(*   (* Lemma well_structured_add_inst_call: *) *)
(*   (*   forall M M' xs ck f i es eqs, *) *)
(*   (*     well_structured_memories eqs M -> *) *)
(*   (*     well_structured_memories (EqCall xs ck f i es :: eqs) (add_inst i M' M). *) *)
(*   (* Proof. *) *)
(*   (*   intros ** WS. *) *)
(*   (*   constructor; unfold fbys, insts; simpl; split; intro H. *) *)
(*   (*   - rewrite find_val_add_inst in H; apply WS in H; auto. *) *)
(*   (*   - rewrite find_val_add_inst; apply WS in H; auto. *) *)
(*   (*   - rewrite In_fold_left_inst_eq. *) *)
(*   (*     destruct (ident_eqb x i) eqn: E; *) *)
(*   (*       [apply ident_eqb_eq in E; subst|apply ident_eqb_neq in E]. *) *)
(*   (*     + right; apply PSE.MP.Dec.F.add_1; auto. *) *)
(*   (*     + rewrite find_inst_gso in H; auto. *) *)
(*   (*       apply WS in H; auto. *) *)
(*   (*   - destruct (ident_eqb x i) eqn: E; *) *)
(*   (*       [apply ident_eqb_eq in E; subst|apply ident_eqb_neq in E]. *) *)
(*   (*     + rewrite find_inst_gss; intro; discriminate. *) *)
(*   (*     + rewrite find_inst_gso; auto. *) *)
(*   (*       apply WS. *) *)
(*   (*       apply In_fold_left_inst_eq in H as [|H]; auto. *) *)
(*   (*       apply PSE.MP.Dec.F.add_3 in H; auto. *) *)
(*   (*       contradict H; apply not_In_empty. *) *)
(*   (* Qed. *) *)

(*   (* Lemma well_structured_reset_call: *) *)
(*   (*   forall M xs ck f i es ck_r r eqs, *) *)
(*   (*     well_structured_memories (EqCall xs ck f i es :: eqs) M -> *) *)
(*   (*     well_structured_memories (EqReset ck_r f i r :: EqCall xs ck f i es :: eqs) M. *) *)
(*   (* Proof. *) *)
(*   (*   inversion_clear 1 as [Vals Insts]. *) *)
(*   (*   constructor; unfold fbys, insts in *; simpl in *. *) *)
(*   (*   - intro; rewrite Vals; reflexivity. *) *)
(*   (*   - intro; rewrite Insts. *) *)
(*   (*     rewrite 2 In_fold_left_inst_eq. *) *)
(*   (*     split; intros [H|H']; auto. *) *)
(*   (*     + rewrite PSE.MP.Dec.F.add_iff; auto. *) *)
(*   (*     + apply PSE.MP.Dec.F.add_iff in H' as []; auto. *) *)
(*   (*       rewrite PSE.MP.Dec.F.add_iff; auto. *) *)
(*   (* Qed. *) *)

(*   (* Corollary well_structured_add_inst_reset_call: *) *)
(*   (*   forall M M' xs ck f i es ck_r r eqs, *) *)
(*   (*     well_structured_memories eqs M -> *) *)
(*   (*     well_structured_memories (EqReset ck_r f i r :: EqCall xs ck f i es :: eqs) (add_inst i M' M). *) *)
(*   (* Proof. *) *)
(*   (*   intros; apply well_structured_reset_call, well_structured_add_inst_call; auto. *) *)
(*   (* Qed. *) *)

(*   (* Lemma well_structured_add_val_fby: *) *)
(*   (*   forall M mvs x ck v0 e eqs, *) *)
(*   (*     well_structured_memories eqs M -> *) *)
(*   (*     well_structured_memories (EqFby x ck v0 e :: eqs) (add_val x mvs M). *) *)
(*   (* Proof. *) *)
(*   (*   intros ** WS. *) *)
(*   (*   constructor; unfold fbys, insts; simpl; split; intro H. *) *)
(*   (*   - rewrite In_fold_left_fby_eq. *) *)
(*   (*     destruct (ident_eqb x x0) eqn: E; *) *)
(*   (*       [apply ident_eqb_eq in E; subst|apply ident_eqb_neq in E]. *) *)
(*   (*     + right; apply PSE.MP.Dec.F.add_1; auto. *) *)
(*   (*     + rewrite find_val_gso in H; auto. *) *)
(*   (*       apply WS in H; auto. *) *)
(*   (*   - destruct (ident_eqb x x0) eqn: E; *) *)
(*   (*       [apply ident_eqb_eq in E; subst|apply ident_eqb_neq in E]. *) *)
(*   (*     + rewrite find_val_gss; intro; discriminate. *) *)
(*   (*     + rewrite find_val_gso; auto. *) *)
(*   (*       apply WS. *) *)
(*   (*       apply In_fold_left_fby_eq in H as [|H]; auto. *) *)
(*   (*       apply PSE.MP.Dec.F.add_3 in H; auto. *) *)
(*   (*       contradict H; apply not_In_empty. *) *)
(*   (*   - rewrite find_inst_add_val in H; apply WS in H; auto. *) *)
(*   (*   - rewrite find_inst_add_val; apply WS in H; auto. *) *)
(*   (* Qed. *) *)

End SBSEMANTICS.
