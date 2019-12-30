(* *********************************************************************)
(*                                                                     *)
(*                 The Vélus verified Lustre compiler                  *)
(*                                                                     *)
(*             (c) 2019 Inria Paris (see the AUTHORS file)             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Permutation.
From Coq Require Import Setoid.
From Coq Require Import Morphisms.

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import VelusMemory.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Stc.StcIsSystem.
From Velus Require Import Stc.StcOrdered.
From Velus Require Import IndexedStreams.
From Velus Require Import CoreExpr.CESemantics.

Module Type STCSEMANTICS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Op)
       (Import CESyn : CESYNTAX        Op)
       (Import Syn   : STCSYNTAX   Ids Op       CESyn)
       (Import Syst  : STCISSYSTEM Ids Op       CESyn Syn)
       (Import Ord   : STCORDERED  Ids Op       CESyn Syn Syst)
       (Import Str   : INDEXEDSTREAMS  Op OpAux)
       (Import CESem : CESEMANTICS Ids Op OpAux CESyn Str).

  Definition state := memory val.

  Definition state_closed_inits (inits: list ident) (S: state) : Prop :=
    forall x, find_val x S <> None -> In x inits.

  Inductive state_closed: program -> ident -> state -> Prop :=
    state_closed_intro:
      forall P f S s P',
        find_system f P = Some (s, P') ->
        state_closed_inits (map fst s.(s_inits)) S ->
        (forall i S',
            find_inst i S = Some S' ->
            exists g,
              In (i, g) (s_subs s)
              /\ state_closed P' g S') ->
        state_closed P f S.

  Definition state_closed_insts (P: program) (subs: list (ident * ident)) (S: state) : Prop :=
    forall i Si,
      find_inst i S = Some Si ->
      exists g, In (i, g) subs
           /\ state_closed P g Si.

  Definition reset_inits (s: system) (S0: state) : Prop :=
    forall x c ck,
      In (x, (c, ck)) s.(s_inits) ->
      find_val x S0 = Some (sem_const c).

  Inductive initial_state: program -> ident -> state -> Prop :=
    initial_state_intro:
      forall P f S0 s P',
        find_system f P = Some (s, P') ->
        reset_inits s S0 ->
        (forall i g,
            In (i, g) s.(s_subs) ->
            exists Si0,
              find_inst i S0 = Some Si0
              /\ initial_state P' g Si0) ->
        initial_state P f S0.

  Section Semantics.

    Variable P: program.

    Inductive sem_trconstr: bool -> env -> state -> state -> state -> trconstr -> Prop :=
    | STcDef:
        forall base R S I S' x v ck ce,
          sem_caexp_instant base R ck ce v ->
          sem_var_instant R x v ->
          sem_trconstr base R S I S' (TcDef x ck ce)
    | STcNext:
        forall base R S I S' x ck e c v',
          find_val x S = Some c ->
          sem_var_instant R x (match v' with present _ => present c | absent => absent end) ->
          sem_aexp_instant base R ck e v' ->
          find_val x S' = Some (match v' with present c' => c' | absent => c end) ->
          sem_trconstr base R S I S' (TcNext x ck e)
    | STcReset:
        forall base R S I S' ck f i r Ii,
          sem_clock_instant base R ck r ->
          find_inst i I = Some Ii ->
          (if r
           then initial_state P f Ii
           else find_inst i S ⌈≋⌉ Some Ii) ->
          sem_trconstr base R S I S' (TcReset i ck f)
    | STcCall:
        forall base R S I S' ys rst ck f i es xs Ii os Si',
          sem_exps_instant base R es xs ->
          sem_clock_instant base R ck (clock_of_instant xs) ->
          (rst = false -> find_inst i S ⌈≋⌉ Some Ii) ->
          find_inst i I = Some Ii ->
          sem_system f Ii xs os Si' ->
          sem_vars_instant R ys os ->
          find_inst i S' = Some Si' ->
          sem_trconstr base R S I S' (TcCall i ys ck rst f es)

    with sem_system: ident -> state -> list value -> list value -> state -> Prop :=
           SSystem:
             forall f s P' S I S' R xs ys,
               find_system f P = Some (s, P') ->
               sem_vars_instant R (map fst s.(s_in)) xs ->
               sem_vars_instant R (map fst s.(s_out)) ys ->
               sem_clocked_vars_instant (clock_of_instant xs) R (idck s.(s_in)) ->
               Forall (sem_trconstr (clock_of_instant xs) R S I S') s.(s_tcs) ->
               state_closed P f S ->
               state_closed P f I ->
               state_closed P f S' ->
               sem_system f S xs ys S'.

  End Semantics.

  Section sem_system_mult.
    Variable P: program.

    Variable P_trconstr: bool -> env -> state -> state -> state -> trconstr -> Prop.
    Variable P_system: ident -> state -> list value -> list value -> state -> Prop.

    Hypothesis TcDefCase:
      forall base R S I S' x v ck ce,
        sem_caexp_instant base R ck ce v ->
        sem_var_instant R x v ->
        P_trconstr base R S I S' (TcDef x ck ce).

    Hypothesis TcNextCase:
      forall base R S I S' x ck e c v',
        find_val x S = Some c ->
        sem_var_instant R x (match v' with present _ => present c | absent => absent end) ->
        sem_aexp_instant base R ck e v' ->
        find_val x S' = Some (match v' with present c' => c' | absent => c end) ->
        P_trconstr base R S I S' (TcNext x ck e).

    Hypothesis TcResetCase:
      forall base R S I S' ck f i r Ii,
        sem_clock_instant base R ck r ->
        find_inst i I = Some Ii ->
        (if r
         then initial_state P f Ii
         else find_inst i S ⌈≋⌉ Some Ii) ->
        P_trconstr base R S I S' (TcReset i ck f).

    Hypothesis TcCallCase:
      forall base R S I S' i ys ck rst f es xs Ii os Si',
        sem_exps_instant base R es xs ->
        sem_clock_instant base R ck (clock_of_instant xs) ->
        (rst = false -> find_inst i S ⌈≋⌉ Some Ii) ->
        find_inst i I = Some Ii ->
        sem_system P f Ii xs os Si' ->
        sem_vars_instant R ys os ->
        find_inst i S' = Some Si' ->
        P_system f Ii xs os Si' ->
        P_trconstr base R S I S' (TcCall i ys ck rst f es).

    Hypothesis SystemCase:
      forall f s P' R S I S' xs ys,
        find_system f P = Some (s, P') ->
        sem_vars_instant R (map fst s.(s_in)) xs ->
        sem_vars_instant R (map fst s.(s_out)) ys ->
        sem_clocked_vars_instant (clock_of_instant xs) R (idck s.(s_in)) ->
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
           (f: ident) (S: state) (xs ys: list value) (S': state)
           (Sem: sem_system P f S xs ys S') {struct Sem}
         : P_system f S xs ys S'.
    Proof.
      - destruct Sem; eauto.
      - destruct Sem.
        eapply SystemCase; eauto.
        match goal with H: Forall _ _ |- _ => induction H; auto end.
    Qed.

    Combined Scheme sem_trconstr_system_ind from
             sem_trconstr_mult, sem_system_mult.

  End sem_system_mult.

  CoInductive loop: program -> ident -> stream (list value) -> stream (list value) -> state -> nat -> Prop :=
    loop_intro:
      forall P f xss yss Sn Sn' n,
        sem_system P f Sn (xss n) (yss n) Sn' ->
        loop P f xss yss Sn' (S n) ->
        loop P f xss yss Sn n.

  Section LoopCoind.

    Variable R: program -> ident -> stream (list value) -> stream (list value) -> state -> nat -> Prop.

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

  Add Parametric Morphism system : (reset_inits system)
      with signature equal_memory ==> Basics.impl
        as reset_inits_equal_memory.
  Proof.
    intros * E Rst ??? Hin.
    rewrite <-E; apply Rst in Hin; auto.
  Qed.

  Add Parametric Morphism P f : (initial_state P f)
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
      setoid_rewrite (@eq_subrelation _ equal_memory) in Sub'; auto.
      setoid_rewrite E in Sub'.
      apply orel_find_inst_Some in Sub' as (v' & Hv' & ->).
      symmetry in Hv'. eauto.
  Qed.

  Add Parametric Morphism inits : (state_closed_inits inits)
      with signature equal_memory ==> Basics.impl
        as state_closed_inits_equal_memory.
  Proof.
    unfold state_closed_inits.
    intros * E Closed ? Find.
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
    - intros * Sub.
      apply orel_eq in Sub.
      setoid_rewrite (@eq_subrelation _ equal_memory) in Sub; auto.
      setoid_rewrite <-E in Sub.
      apply orel_find_inst_Some in Sub as (S & HS & Sub').
      specialize (Insts _ _ Sub') as (b' & ? & ?). eauto.
  Qed.

  Add Parametric Morphism P : (state_closed_insts P)
      with signature @Permutation (ident * ident) ==> eq ==> Basics.impl
        as state_closed_insts_Permutation.
  Proof.
    intros * E ? Closed ?? Find; apply Closed in Find as (g&?&?).
    exists g; split; auto.
    now rewrite <-E.
  Qed.

  Add Parametric Morphism P f: (sem_system P f)
      with signature equal_memory ==> eq ==> eq ==> equal_memory ==> Basics.impl
        as sem_system_equal_memory.
  Proof.
    intros S1 S2 ??? S1' S2' ** Sem.
    revert dependent S2; revert dependent S2'.
    induction Sem as [| |??????????? Find Init|
                      ????????????????? Spec Find ?? Sub|] using sem_system_mult with
                   (P_trconstr := fun base R S1 I1 S1' tc =>
                                    forall S2 S2' I2,
                                      S1 ≋ S2 ->
                                      I1 ≋ I2 ->
                                      S1' ≋ S2' ->
                                      sem_trconstr P base R S2 I2 S2' tc);
      eauto using sem_trconstr.
    - intros * E EI E'.
      econstructor; eauto.
      + now rewrite <-E.
      + now rewrite <-E'.
    - intros * E EI E'.
      apply orel_eq in Find;
        setoid_rewrite (@eq_subrelation _ equal_memory) in Find; auto.
      rewrite EI in Find.
      apply Env.orel_find_Some in Find as (Is' & Eq & Find').
      destruct r.
      + econstructor; eauto; simpl. now rewrite Eq.
      + econstructor; eauto; simpl.
        now rewrite <-E, Eq.
    - intros * E EI E'.
      apply orel_eq in Find;
        setoid_rewrite (@eq_subrelation _ equal_memory) in Find; auto.
      rewrite EI in Find.
      apply Env.orel_find_Some in Find as (? & Eq & ?).
      apply orel_eq in Sub;
        setoid_rewrite (@eq_subrelation _ equal_memory) in Sub; auto.
      rewrite E' in Sub.
      apply orel_find_inst_Some in Sub as (? & Eq' & ?).
      symmetry in Eq, Eq'.
      destruct rst.
      + econstructor; eauto. discriminate.
      + specialize (Spec eq_refl).
        eapply STcCall; eauto.
        now rewrite <-Eq, <-E.
    - intros ? E ? E'.
      eapply SSystem with (I := I); eauto.
      + induction (s_tcs s); auto;
          repeat match goal with H: Forall ?P (_ :: _) |- _ => inv H end.
        constructor; auto.
        assert (I ≋ I) by reflexivity;
          auto.
      + now rewrite <-E'.
      + now rewrite <-E.
  Qed.

  Add Parametric Morphism : (state_closed_inits)
      with signature (@Permutation ident) ==> eq ==> Basics.impl
        as state_closed_inits_permutation.
  Proof.
    unfold state_closed_inits.
    intros * E ? Closed ? Find.
    rewrite <-E; auto.
  Qed.

  Add Parametric Morphism P b xss yss : (loop P b xss yss)
      with signature equal_memory ==> eq ==> Basics.impl
        as loop_equal_memory.
  Proof.
    cofix COFIX.
    intros * E n Loop.
    inv Loop.
    econstructor; eauto.
    intros; rewrite <-E; auto.
  Qed.

  Lemma initial_state_other:
    forall S0 s P f,
      s_name s <> f ->
      (initial_state P f S0 <->
      initial_state (s :: P) f S0).
  Proof.
    split; inversion_clear 1 as [????? Find]; econstructor; eauto.
    - rewrite find_system_other; eauto.
    - rewrite find_system_other in Find; eauto.
  Qed.

  Fact reset_inits_add_inst:
    forall s S0 i Si0,
      reset_inits s S0 ->
      reset_inits s (add_inst i Si0 S0).
  Proof.
    unfold reset_inits;
      setoid_rewrite find_val_add_inst; auto.
  Qed.

  Fact state_closed_inits_add_inst:
    forall inits S i Si,
      state_closed_inits inits S ->
      state_closed_inits inits (add_inst i Si S).
  Proof.
    unfold state_closed_inits;
      setoid_rewrite find_val_add_inst; auto.
  Qed.

  Lemma state_closed_other:
    forall S s P f,
      s_name s <> f ->
      (state_closed P f S <->
      state_closed (s :: P) f S).
  Proof.
    split; inversion_clear 1 as [????? Find]; econstructor; eauto.
    - rewrite find_system_other; eauto.
    - rewrite find_system_other in Find; eauto.
  Qed.

  Lemma state_closed_find_system_other:
    forall S i P P' f s g,
      Ordered_systems P ->
      find_system f P = Some (s, P') ->
      In (i, g) s.(s_subs) ->
      state_closed P g S ->
      state_closed P' g S.
  Proof.
    intros * Ord Find Hin Closed; inversion_clear Closed as [????? Find'].
    econstructor; eauto.
    apply find_system_app in Find as (?&?&?); subst.
    apply Ordered_systems_split in Ord.
    eapply Forall_forall in Ord as (FindNone & Neq &?&?&?); eauto; simpl in *.
    rewrite find_system_app', FindNone in Find'.
    simpl in Find'; destruct (ident_eqb (s_name s) g) eqn:Eq; auto.
    apply ident_eqb_eq in Eq; congruence.
  Qed.

  Lemma state_closed_insts_find_system_other:
    forall I s P P' f,
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

  Lemma state_closed_insts_cons:
    forall I s P,
      Ordered_systems (s :: P) ->
      state_closed_insts P s.(s_subs) I ->
      state_closed_insts (s :: P) s.(s_subs) I.
  Proof.
    intros * Ord Closed; inversion_clear Ord as [|??? Systems].
    intros ?? Find; apply Closed in Find as (g &?&?).
    exists g; split; auto.
    apply state_closed_other; auto.
    eapply Forall_forall in Systems as (?&?); eauto; auto.
  Qed.

  Lemma sem_system_cons:
    forall P s f xs S S' ys,
      Ordered_systems (s :: P) ->
      sem_system (s :: P) f xs S S' ys ->
      s.(s_name) <> f ->
      sem_system P f xs S S' ys.
  Proof.
    intros * Hord Hsem Hnf.
    revert Hnf.
    induction Hsem as [| | |?????????????????????? IH|
                       ????????? Hf ???? Closed ClosedI Closed' IH]
                        using sem_system_mult
      with (P_trconstr := fun bk H S I S' tc =>
                            ~Is_system_in_tc s.(s_name) tc ->
                            sem_trconstr P bk H S I S' tc);
      eauto using sem_trconstr.
    - intro Hnin; econstructor; eauto.
      destruct r; eauto.
      rewrite initial_state_other; eauto.
      intro E; apply Hnin; rewrite E; constructor.
    - intro Hnin; econstructor; eauto.
      apply IH; intro E; apply Hnin; rewrite E; constructor.
    - intros.
      pose proof Hf.
      rewrite find_system_other in Hf; auto.
      rewrite <-state_closed_other in Closed, ClosedI, Closed'; auto.
      eapply SSystem with (I := I); eauto.
      eapply find_system_later_not_Is_system_in in Hord; eauto.
      apply Forall_forall; intros.
      eapply Forall_forall in IH; eauto.
      apply IH.
      intro; apply Hord.
      apply Exists_exists; eauto.
  Qed.

  Lemma sem_system_cons2:
    forall s P f xs S S' ys,
      Ordered_systems (s :: P) ->
      sem_system P f xs S S' ys ->
      sem_system (s :: P) f xs S S' ys.
  Proof.
    intros * Hord Hsem.
    induction Hsem as [| | | |
                       ????????? Hfind ???? Closed ClosedI Closed' IHtcs] using sem_system_mult
      with (P_trconstr := fun bk H S I S' tc =>
                            ~Is_system_in_tc s.(s_name) tc ->
                            sem_trconstr (s :: P) bk H S I S' tc);
      eauto using sem_trconstr.
    - intros Notin; econstructor; eauto.
      destruct r; eauto.
      apply initial_state_other; auto.
      intro E; apply Notin; rewrite E; constructor.
    - pose proof Hfind as Hfind'; apply find_system_app in Hfind' as (?& E & FindNone).
      pose proof Hord as Hord'; rewrite E, app_comm_cons in Hord';
        apply Ordered_systems_split in Hord'.
      inversion_clear Hord as [|???? Hnin].
      assert (s.(s_name) <> f) as Hnf.
      { intro Hnf.
        rewrite Hnf in *.
        pose proof (find_system_name _ _ _ _ Hfind).
        apply find_system_app in Hfind as (?& Hp &?); subst.
        apply Forall_app in Hnin.
        destruct Hnin as [H' Hfg]; clear H'.
        inv Hfg; congruence.
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
        eapply find_system_later_not_Is_system_in; eauto using Ordered_systems.
        apply Exists_exists; eauto.
  Qed.

  Lemma sem_trconstrs_cons:
    forall P bk H S I S' tcs s,
      Ordered_systems (s :: P) ->
      ~ Is_system_in s.(s_name) tcs ->
      (Forall (sem_trconstr P bk H S I S') tcs <->
       Forall (sem_trconstr (s :: P) bk H S I S') tcs).
  Proof.
    intros * Hord Hnini.
    induction tcs as [|tc tcs IH]; [now constructor|].
    apply not_Is_system_in_cons in Hnini as [Hnini Hninis].
    split; intros Hsem; apply Forall_cons2 in Hsem as [Htc Htcs];
      apply IH in Htcs; auto; constructor; auto.
    - destruct Htc; eauto using sem_trconstr.
      + econstructor; eauto.
        destruct r; eauto.
        apply initial_state_other; auto.
        intro E; apply Hnini; rewrite E; constructor.
      + eauto using sem_trconstr, sem_system_cons2.
    - destruct Htc; eauto using sem_trconstr.
      + econstructor; eauto.
        destruct r; auto.
        rewrite initial_state_other; eauto.
        intro E; apply Hnini; rewrite E; constructor.
      + econstructor; eauto.
        eapply sem_system_cons; eauto.
        intro E; apply Hnini; rewrite E; constructor.
  Qed.

  Lemma reset_inits_det:
    forall P f S S' s P',
      state_closed P f S ->
      state_closed P f S' ->
      find_system f P = Some (s, P') ->
      reset_inits s S ->
      reset_inits s S' ->
      Env.Equal (values S) (values S').
  Proof.
    intros * Closed Closed' Find Rst Rst' x.
    inversion_clear Closed as [????? Find' Spec];
      rewrite Find' in Find; inv Find.
    inversion_clear Closed' as [????? Find Spec'];
      rewrite Find' in Find; inv Find.
    unfold state_closed_inits, reset_inits, find_val in *.
    destruct (Env.find x (values S)) eqn: E, (Env.find x (values S')) eqn: E'; auto.
    - assert (Env.find x (values S) <> None) as E1 by (apply not_None_is_Some; eauto).
      apply Spec, fst_InMembers, InMembers_In in E1 as ((? & ?) & Hin).
      pose proof Hin as Hin'.
      apply Rst in Hin; apply Rst' in Hin'.
      congruence.
    - assert (Env.find x (values S) <> None) as E1 by (apply not_None_is_Some; eauto).
      apply Spec, fst_InMembers, InMembers_In in E1 as ((? & ?)& Hin).
      apply Rst' in Hin.
      congruence.
    - assert (Env.find x (values S') <> None) as E1 by (apply not_None_is_Some; eauto).
      apply Spec', fst_InMembers, InMembers_In in E1 as ((? & ?)& Hin).
      apply Rst in Hin.
      congruence.
  Qed.

  Lemma initial_state_det:
    forall S S' P f,
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
    - eapply reset_inits_det; eauto using state_closed.
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

  Lemma sem_trconstrs_absent_states:
    forall S I S' P tcs R,
    (forall f xs S ys S',
        sem_system P f S xs ys S' ->
        absent_list xs ->
        S' ≋ S) ->
    state_closed_inits (inits_of tcs) S ->
    state_closed_inits (inits_of tcs) S' ->
    state_closed_insts P (calls_of tcs) S ->
    state_closed_insts P (calls_of tcs) S' ->
    (forall s rst, Step_with_reset_in s rst tcs ->
              if rst then Reset_in s tcs else ~ Reset_in s tcs) ->
    Forall (sem_trconstr P false R S I S') tcs ->
    S' ≋ S.
  Proof.
    intros * IH Inits Inits' Insts Insts' Spec Htcs.
    constructor.

    - clear Insts Insts' Spec.
      intros x.
      unfold state_closed_inits, find_val in *.
      specialize (Inits x); specialize (Inits' x).
      destruct (Env.find x (values S)) eqn: Find;
        destruct (Env.find x (values S')) eqn: Find'; auto.
      + assert (In x (inits_of tcs)) as Hin by (apply Inits; congruence).
        clear Inits Inits'.
        induction tcs as [|[]]; simpl in Hin; try contradiction;
          inversion_clear Htcs as [|?? Htc]; auto.
        destruct Hin; auto; subst.
        inversion_clear Htc as [|?????????? Find1 ? Exp Find1'| |]; unfold find_val in *.
        rewrite Find1 in Find; inv Find.
        inversion Exp as [???? Clock|];
          [contradict Clock; apply not_subrate_clock|]; subst.
        congruence.
      + assert (In x (inits_of tcs)) as Hin by (apply Inits; congruence).
        clear Inits Inits'.
        induction tcs as [|[]]; simpl in Hin; try contradiction;
          inversion_clear Htcs as [|?? Htc]; auto.
        destruct Hin; auto; subst.
        inversion_clear Htc as [|?????????? Find1 ? Exp Find1'| |]; unfold find_val in *.
        rewrite Find1 in Find; inv Find.
        inversion Exp as [???? Clock|];
          [contradict Clock; apply not_subrate_clock|]; subst.
        congruence.
      + assert (In x (inits_of tcs)) as Hin by (apply Inits'; congruence).
        clear Inits Inits'.
        induction tcs as [|[]]; simpl in Hin; try contradiction;
          inversion_clear Htcs as [|?? Htc]; auto.
        destruct Hin; auto; subst.
        inversion_clear Htc as [|?????????? Find1 ? Exp Find1'| |]; unfold find_val in *.
        congruence.

    - clear Inits Inits'.
      constructor.
      + setoid_rewrite Env.In_find.
        unfold state_closed_insts, find_inst in *.
        intro s; split; intros (?& Find).
        *{ apply Insts' in Find as (b & Hin &?).
           apply calls_of_In in Hin as (?&?& rst &?& Hin).
           pose proof Htcs as Htcs'.
           eapply Forall_forall in Htcs; eauto.
           assert (Step_with_reset_in s rst tcs) as Spec'
               by (apply Exists_exists; eexists; split; eauto; constructor).
           apply Spec in Spec'.
           destruct rst.
           - apply Exists_exists in Spec' as (?& Rst & E); inv E.
             eapply Forall_forall in Rst; eauto.
             inversion_clear Rst as [| |?????????? Clock FindI Init|].
             assert (r = false)
               by (rewrite <-Bool.not_true_iff_false;
                   intro E; subst; contradict Clock; apply not_subrate_clock); subst.
             apply orel_find_inst_Some in Init as (?&?&?); eauto.
           - inversion_clear Htcs as [| | |????????????????? Rst].
             apply orel_find_inst_Some in Rst as (?&?&?); eauto.
         }
        * apply Insts in Find as (b & Hin &?).
          apply calls_of_In in Hin as (?&?&?&?& Hin).
          eapply Forall_forall in Htcs; eauto.
          inv Htcs; eauto.
      + setoid_rewrite Env.Props.P.F.find_mapsto_iff.
        intros s e e' Find' Find.
        pose proof Find as Hin.
        apply Insts in Hin as (b & Hin &?).
        apply calls_of_In in Hin as (?&?& rst &?& Hin).
        pose proof Htcs as Htcs'.
        eapply Forall_forall in Htcs; eauto.
        assert (Step_with_reset_in s rst tcs) as Spec'
               by (apply Exists_exists; eexists; split; eauto; constructor).
        apply Spec in Spec'.
        inversion_clear Htcs as [| | |??????????????? Exps Clk Rst' FindI' SemSystem ? Find1'].
        unfold find_inst in *; rewrite Find1' in Find'; inv Find'.
        assert (absent_list xs) by (eapply clock_of_instant_false, not_subrate_clock_impl; eauto).
        apply IH in SemSystem; auto.
        rewrite SemSystem.
        destruct rst.
        * apply Exists_exists in Spec' as (?& Rst & E); inv E.
          eapply Forall_forall in Rst; eauto.
          inversion_clear Rst as [| |?????????? Clock FindI Init|];
            setoid_rewrite FindI' in FindI; inv FindI.
          assert (r = false)
            by (rewrite <-Bool.not_true_iff_false;
                intro E; subst; contradict Clock; apply not_subrate_clock); subst.
          unfold find_inst in Init; rewrite Find in Init; inv Init; symmetry; auto.
        * rewrite Find in Rst'; specialize (Rst' eq_refl); inv Rst'; symmetry; auto.
  Qed.

  Lemma sem_trconstrs_absent_vars:
    forall tcs S I S' P R x,
    (forall f xs S ys S',
        sem_system P f S xs ys S' ->
        absent_list xs ->
        absent_list ys) ->
    In x (variables tcs) ->
    Forall (sem_trconstr P false R S I S') tcs ->
    sem_var_instant R x absent.
  Proof.
    unfold variables.
    induction tcs as [|[]]; simpl; intros * IH Spec Htcs; try contradiction;
      inversion_clear Htcs as [|?? Htc];
      inversion_clear Htc as [????????? Exp| | |]; eauto.
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

  Lemma sem_system_absent:
    forall P f xs S ys S',
      Ordered_systems P ->
      sem_system P f S xs ys S' ->
      absent_list xs ->
      absent_list ys /\ S' ≋ S.
  Proof.
    intros * Ord Sem Abs.
    revert dependent xs; revert f S S' ys.
    induction P as [|system]; intros;
      inversion_clear Sem as [????????? Find Ins ?? Htcs Closed ClosedI Closed'];
      try now inv Find.
    pose proof Find; simpl in Find.
    destruct (ident_eqb (s_name system) f) eqn: Eq.
    - inv Find.
      assert ( ~ Is_system_in (s_name s) (s_tcs s))
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
        * intros; eapply IHP; eauto.
        * rewrite <-s_vars_out_in_tcs.
          apply in_app; auto.
      + inversion_clear Closed as [?????? Inits Insts];
          inversion_clear Closed' as [?????? Inits' Insts'].
        repeat match goal with
                 H: find_system ?b ?P = _, H': find_system ?b ?P = _ |- _ =>
                 rewrite H in H'; inv H'
               end.
        rewrite s_inits_in_tcs in Inits, Inits'.
        setoid_rewrite s_subs_calls_of in Insts;
          setoid_rewrite s_subs_calls_of in Insts'.
        eapply sem_trconstrs_absent_states; eauto.
        * intros; eapply IHP; eauto.
        * apply s_reset_consistency.
    - inv Ord; eapply IHP; eauto.
      apply ident_eqb_neq in Eq.
      rewrite <-state_closed_other in Closed, ClosedI, Closed'; eauto.
      eapply SSystem with (I := I); eauto.
      apply sem_trconstrs_cons in Htcs; eauto using Ordered_systems.
      eapply find_system_later_not_Is_system_in; eauto using Ordered_systems.
  Qed.

  Lemma state_closed_inits_empty:
    forall inits,
      state_closed_inits inits (empty_memory _).
  Proof.
    unfold state_closed_inits; setoid_rewrite find_val_gempty; intuition.
  Qed.

  Lemma state_closed_empty:
    forall P f s P',
      find_system f P = Some (s, P') ->
      state_closed P f (empty_memory _).
  Proof.
    intros * Find.
    econstructor; eauto.
    - apply state_closed_inits_empty.
    - setoid_rewrite find_inst_gempty; congruence.
  Qed.

  Lemma sem_system_find_val:
    forall P f S xs ys S' x s P',
      sem_system P f S xs ys S' ->
      find_system f P = Some (s, P') ->
      In x (map fst (s_inits s)) ->
      find_val x S <> None.
  Proof.
    inversion_clear 1 as [????????? Find ??? Htcs]; intros Find' Hin.
    rewrite Find in Find'; inv Find'.
    rewrite s_inits_in_tcs in Hin.
    induction Htcs as [|[] ? Htc]; simpl in *; try contradiction; auto.
    destruct Hin; subst; auto.
    inv Htc; congruence.
  Qed.

End STCSEMANTICS.

Module StcSemanticsFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Op)
       (CESyn : CESYNTAX        Op)
       (Syn   : STCSYNTAX   Ids Op       CESyn)
       (Syst  : STCISSYSTEM Ids Op       CESyn Syn)
       (Ord   : STCORDERED  Ids Op       CESyn Syn Syst)
       (Str   : INDEXEDSTREAMS  Op OpAux)
       (CESem : CESEMANTICS Ids Op OpAux CESyn Str)
<: STCSEMANTICS Ids Op OpAux CESyn Syn Syst Ord Str CESem.
  Include STCSEMANTICS Ids Op OpAux CESyn Syn Syst Ord Str CESem.
End StcSemanticsFun.
