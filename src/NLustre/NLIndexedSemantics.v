From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Setoid.
From Coq Require Import Morphisms.
From Coq Require Import Logic.FunctionalExtensionality.

From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import IndexedStreams.
From Velus Require Import CoreExpr.CESemantics.

(** * The NLustre semantics *)

(**

  We provide a "standard" dataflow semantics relating an environment
  of streams to a stream of outputs.

 *)

Module Type NLINDEXEDSEMANTICS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Ids Op)
       (Import Cks   : CLOCKS      Ids Op OpAux)
       (Import CESyn : CESYNTAX    Ids Op OpAux Cks)
       (Import Syn   : NLSYNTAX    Ids Op OpAux Cks CESyn)
       (Import Str   : INDEXEDSTREAMS  Ids Op OpAux Cks)
       (Import Ord   : NLORDERED   Ids Op OpAux Cks CESyn Syn)
       (Import CESem : CESEMANTICS Ids Op OpAux Cks CESyn      Str).

  Fixpoint hold (v0: value) (xs: stream svalue) (n: nat) : value :=
    match n with
    | 0   => v0
    | S m => match xs m with
            | absent     => hold v0 xs m
            | present hv => hv
            end
    end.

  Definition fby (v0: value) (xs: stream svalue) : stream svalue :=
    fun n =>
      match xs n with
      | absent => absent
      | _      => present (hold v0 xs n)
      end.

  Fixpoint doreset (xs: stream svalue) (rs: stream bool) (n : nat) : bool :=
    if rs n then true
    else match n with
         | 0 => false
         | S m => match xs m with
                 | absent => doreset xs rs m
                 | present _ => false
                 end
         end.

  Definition reset (v0: value) (xs: stream svalue) (rs: stream bool) : stream svalue :=
    fun n =>
      match xs n with
      | absent => absent
      | present x => if (doreset xs rs n) then present v0 else present x
      end.

  Lemma reset_spec : forall v0 xs rs v n,
      reset v0 xs rs n = v <->
      (xs n = absent /\ v = absent) \/
      (exists x, xs n = present x /\ doreset xs rs n = false /\ v = present x) \/
      (exists x, xs n = present x /\ doreset xs rs n = true /\ v = present v0).
  Proof.
    intros *. unfold reset.
    split.
    - intros Hres.
      destruct (xs n); simpl in *; auto.
      destruct (doreset xs rs n) eqn:Hres'; eauto 8.
    - intros [(Hxs&?)|[(?&Hxs&Hres&?)|(?&Hxs&Hres&?)]]; subst; rewrite Hxs; auto.
      1,2:rewrite Hres; auto.
  Qed.

  Fact lt_S_inv : forall n m,
      n < S m ->
      (n < m \/ n = m).
  Proof.
    intros * Hlt.
    apply Lt.le_lt_or_eq, Lt.lt_n_Sm_le; auto.
  Qed.

  Lemma doreset_spec : forall xs rs n,
      doreset xs rs n = true <->
      rs n = true \/
      (exists m, m < n /\ rs m = true /\
            forall k, m <= k -> k < n -> xs k = absent).
  Proof.
    induction n; (split; [intros Hrs|intros [Hrs|(?&Hmn&Hrs&Hk)]]); simpl in *.
    - destruct (rs 0); auto.
    - rewrite Hrs; auto.
    - inv Hmn.
    - destruct (rs (S n)); auto. right.
      destruct (xs n) eqn:Hxs. 2:inv Hrs.
      apply IHn in Hrs as [?|(?&?&?&?)].
      + exists n. repeat split; auto.
        intros ? Hle Hlt.
        apply lt_S_inv in Hlt as [?|?]; subst; auto.
        exfalso. eapply Lt.lt_irrefl, Lt.lt_le_trans; eauto.
      + exists x. repeat split; auto.
        intros ? Hle Hlt.
        apply lt_S_inv in Hlt as [?|?]; subst; auto.
    - rewrite Hrs; auto.
    - destruct (rs (S n)); auto.
      destruct (xs n) eqn:Hxs.
      + rewrite IHn.
        apply lt_S_inv in Hmn as [?|?]; subst; auto.
        right. exists x. repeat (split; auto).
      + exfalso. rewrite Hk in Hxs; auto. inv Hxs.
        apply Lt.lt_n_Sm_le; auto.
  Qed.

  Fact doreset_shift : forall xs rs xs' rs' ,
      (forall k, xs' (S k) = xs k) ->
      (forall k, rs' (S k) = rs k) ->
      ((exists x, xs' 0 = present x) \/ rs' 0 = false) ->
      forall n, doreset xs' rs' (S n) = doreset xs rs n.
  Proof.
    intros * Hxs Hrs Hxr0 n. induction n; simpl.
    - destruct (rs' 1) eqn:Hr; rewrite Hrs in Hr; rewrite Hr; auto.
      destruct Hxr0 as [(?&Hxr0)|Hxr0]; rewrite Hxr0; auto.
      destruct (xs' 0) eqn:Hx; auto.
    - destruct (rs' (S (S n))) eqn:Hr; rewrite Hrs in Hr; rewrite Hr; auto.
      destruct (xs' (S n)) eqn:Hx; rewrite Hxs in Hx; rewrite Hx; auto.
  Qed.

  Lemma reset_shift : forall v0 xs rs xs' rs' ,
      (forall k, xs' (S k) = xs k) ->
      (forall k, rs' (S k) = rs k) ->
      ((exists x, xs' 0 = present x) \/ rs' 0 = false) ->
      forall n, reset v0 xs' rs' (S n) = reset v0 xs rs n.
  Proof.
    intros * Hxs Hrs Hxr0 n.
    unfold reset.
    destruct (xs' (S n)) eqn:Hx; rewrite Hxs in Hx; rewrite Hx; auto.
    erewrite doreset_shift; eauto.
  Qed.

  Fact doreset_shift' : forall xs rs xs' rs' k x n,
      (forall k, xs' (S k) = xs k) ->
      (forall k, rs' (S k) = rs k) ->
      k < n -> xs k = present x ->
      doreset xs' rs' (S n) = doreset xs rs n.
  Proof.
    intros * Hxs Hrs Hkn Hxr0. induction n; simpl.
    - inv Hkn.
    - destruct (rs' (S (S n))) eqn:Hr; rewrite Hrs in Hr; rewrite Hr; auto.
      destruct (xs' (S n)) eqn:Hx; rewrite Hxs in Hx; rewrite Hx; auto.
      apply lt_S_inv in Hkn as [Hkn|?]; subst; try congruence.
      apply IHn; auto.
  Qed.

  Lemma reset_shift' : forall n v0 xs rs xs' rs' k x,
      (forall k, xs' (S k) = xs k) ->
      (forall k, rs' (S k) = rs k) ->
      k < n -> xs k = present x ->
      reset v0 xs' rs' (S n) = reset v0 xs rs n.
  Proof.
    intros * Hxs Hrs Hkn Hxr0.
    unfold reset.
    destruct (xs' (S n)) eqn:Hx; rewrite Hxs in Hx; rewrite Hx; auto.
    erewrite doreset_shift'; eauto.
  Qed.

  Definition bools_of (vs: stream svalue) (rs: stream bool) :=
    forall n, (vs n = absent /\ rs n = false) \/ (exists c', vs n = present (Venum c') /\ rs n = (c' ==b true_tag)).

  Lemma bools_of_det : forall vs rs rs',
      bools_of vs rs ->
      bools_of vs rs' ->
      rs' = rs.
  Proof.
    intros * Hb1 Hb2.
    extensionality n.
    specialize (Hb1 n) as [(?&?)|(?&?&?)]; specialize (Hb2 n) as [(?&?)|(?&?&?)]; congruence.
  Qed.

  Definition bools_ofs (vs : list vstream) (rs : cstream) :=
    exists rss, Forall2 bools_of vs rss /\
           (forall n, rs n = existsb (fun rs => rs n) rss).

  Global Instance bools_ofs_SameElements_Proper:
    Proper (SameElements eq ==> eq ==> Basics.impl)
           bools_ofs.
  Proof.
    intros xs xs' Eq bs bs' ? (rs&Bools&Disj); subst.
    eapply @Forall2_SameElements_1 with (eqB:=eq) in Bools as (rs'&Perm'&Bools'); eauto.
    1-3:eauto using eq_str_rel_Reflexive.
    econstructor; esplit. eauto.
    - intros. rewrite Disj. eapply existsb_SameElements_morph; eauto.
      intros ?? Heq; subst; eauto.
    - intros; subst; eauto.
    - intros. eapply bools_of_det; eauto.
  Qed.

  Lemma bools_ofs_det : forall vss rs rs',
      bools_ofs vss rs ->
      bools_ofs vss rs' ->
      rs' = rs.
  Proof.
    intros * (?&Hb1&Hd1) (?&Hb2&Hd2).
    extensionality n.
    rewrite Hd1, Hd2.
    assert (x0 = x); subst; auto.
    clear - Hb1 Hb2.
    rewrite Forall2_swap_args in Hb1. eapply Forall2_trans_ex in Hb2; eauto.
    clear - Hb2.
    induction Hb2 as [|???? (?&_&H1&H2)]; auto.
    eapply bools_of_det in H1; eauto with datatypes.
  Qed.

  Lemma bools_ofs_svalue_to_bool:
    forall ys rs n,
      bools_ofs ys rs ->
      Forall (fun y => exists r, svalue_to_bool (y n) = Some r) ys.
  Proof.
    intros * (rss&Bools&_).
    induction Bools; simpl in *; constructor; auto.
    specialize (H n) as [(?&?)|(?&?&?)]; subst; eauto.
    - erewrite H; simpl; eauto.
    - erewrite H; simpl; eauto.
  Qed.

  Lemma bools_ofs_svalue_to_bool_true:
    forall ys rs n,
    bools_ofs ys rs ->
    rs n = true <-> Exists (fun y => svalue_to_bool (y n) = Some true) ys.
  Proof.
    intros * (?&B1&B2).
    split; intros Rs.
    - rewrite B2 in Rs. clear B2.
      eapply Exists_existsb with (P:=fun x => x n = true) in Rs; intuition.
      induction B1; simpl in *; inv Rs; auto.
      left. specialize (H n) as [(?&?)|(?&?&Hy)]; try congruence.
      rewrite Hy in H1.
      rewrite H; simpl. congruence.
    - rewrite B2. clear B2.
      eapply Exists_existsb with (P:=fun x => x n = true); intuition.
      induction B1; simpl in *; inv Rs; auto.
      left. specialize (H n) as [(?&?)|(?&?&Hy)].
      1,2:rewrite H in H1; simpl in *; try congruence.
  Qed.

  Lemma bools_ofs_svalue_to_bool_false:
    forall ys rs n,
    bools_ofs ys rs ->
    rs n = false <-> Forall (fun y => svalue_to_bool (y n) = Some false) ys.
  Proof.
    intros * (?&B1&B2).
    split; intros Rs.
    - rewrite B2 in Rs. clear B2.
      apply existsb_Forall, forallb_Forall in Rs.
      induction B1; simpl in *; inv Rs; constructor; auto.
      specialize (H n) as [(?&?)|(?&?&Hy)]; try congruence.
      1,2:rewrite H; simpl; auto.
      rewrite Bool.negb_true_iff in H2.
      congruence.
    - rewrite B2. clear B2.
      eapply existsb_Forall, forallb_Forall.
      induction B1; simpl in *; inv Rs; auto.
      econstructor; eauto.
      specialize (H n) as [(?&Hy)|(?&?&Hy)].
      1,2:rewrite Hy; simpl in *; auto.
      rewrite H in H2; simpl in *. inv H2.
      rewrite H1; auto.
  Qed.

  (** ** Another formulation for the resetable fby.
         For the sem -> msem proof, it is simpler to have the fby and reset integrated *)

  Fixpoint holdreset (v0 : value) (xs : stream svalue) (rs : stream bool) (n : nat) :=
    match n with
    | 0   => v0
    | S m => match rs m, xs m with
            | true, absent => v0
            | false, absent => holdreset v0 xs rs m
            | _, present hv => hv
            end
      end.

  Definition fbyreset (v0: value) (xs: stream svalue) (rs : stream bool) : stream svalue :=
    fun n =>
      match rs n, xs n with
      | _, absent => absent
      | true, _   => present v0
      | false, _  => present (holdreset v0 xs rs n)
      end.

  Lemma reset_fby_fbyreset : forall v0 xs rs,
      reset v0 (fby v0 xs) rs ≈ fbyreset v0 xs rs.
  Proof.
    unfold reset, fby, fbyreset.
    intros * n.
    destruct (xs n), (rs n) eqn:Hrs; auto.
    - destruct n; simpl; rewrite Hrs; auto.
    - induction n; simpl. destruct (rs 0); auto.
      rewrite Hrs.
      destruct (xs n) eqn:Hxs, (rs n) eqn:Hrs'; simpl; auto.
      destruct n; simpl; rewrite Hrs'; auto.
  Qed.

  Section NodeSemantics.

    Variable G: global.

    Inductive sem_equation: stream bool -> history -> equation -> Prop :=
    | SEqDef:
        forall bk H x xs ck ce,
          sem_var H x xs ->
          sem_caexp bk H ck ce xs ->
          sem_equation bk H (EqDef x ck ce)
    | SEqApp:
        forall bk H x ck f arg xrs ys rs ls xs,
          sem_exps bk H arg ls ->
          sem_vars H x xs ->
          sem_clock bk H ck (clock_of ls) ->
          Forall2 (sem_var H) (map fst xrs) ys ->
          bools_ofs ys rs ->
          (forall k, sem_node f (mask k rs ls) (mask k rs xs)) ->
          sem_equation bk H (EqApp x ck f arg xrs)
    | SEqFby:
        forall bk H x ls xs c0 ck le xrs ys rs,
          sem_aexp bk H ck le ls ->
          sem_var H x xs ->
          Forall2 (sem_var H) (map fst xrs) ys ->
          sem_clocked_vars bk H xrs ->
          bools_ofs ys rs ->
          xs = reset (sem_const c0) (fby (sem_const c0) ls) rs ->
          sem_equation bk H (EqFby x ck c0 le xrs)

    with sem_node: ident -> stream (list svalue) -> stream (list svalue) -> Prop :=
         | SNode:
             forall bk H f xss yss n,
               bk = clock_of xss ->
               find_node f G = Some n ->
               sem_vars H (map fst n.(n_in)) xss ->
               sem_vars H (map fst n.(n_out)) yss ->
               sem_clocked_vars bk H (idck n.(n_in)) ->
               Forall (sem_equation bk H) n.(n_eqs) ->
               sem_node f xss yss.

    (* Definition sem_nodes : Prop := *)
    (*   Forall (fun no => exists xs ys, sem_node no.(n_name) xs ys) G. *)

  End NodeSemantics.

  Global Hint Constructors sem_equation : nlsem.

  (* The integration of (static) clocks into the (dynamic) semantics:

     1. Without a clocking constraint on [x = c fby e] (sem_aexp =
        sem_exp with clocking constraint) the semantics is
        non-deterministic.

        e.g., [x = true fby x] is satisfied by very many streams:
        present true, present true, present true, present true, ...
        absent, absent, absent, absent, absent, ...
        absent, present true, absent, present true, absent, ...
        etc.

        The additional constraint interprets the clock [ck] in the
        context [H] and only accepts those streams that are present
        iff the clock is true. This is the semantics that would anyway
        be "chosen" by the generated code, which respects the syntactic
        clocks.

     2. The clocking constraint on [x = e] is used in the proofs of
        [subrate_property_eqn(s)] and [sem_node_absent_absent], and
        later in the corresponding proofs of the MemSemantics. It
        essentially allows showing that all the outputs of a node
        are absent when the node's clock is false, and thus justifying
        that the compiled step function is not executed at such
        instants.

        The [clockof] clause in [xs = f(es)] is sufficient to give
        this property. In other words, a constraint explicitly linking
        stream svalues to clock svalues is not needed in this case.

     3. The [sem_clocked_vars] clause in [sem_node] requires that the
        streams passed as node arguments align with the instantiated
        clocks of the node interface.

        This is done to make possible the assertion, critical in
        [is_step_correct], that all arguments on the base clock of an
        application are present when that clock is true (and thus that
        the compiled expressions calculate the correct svalue). I.e., to
        link the static clocks to dynamic facts.

        NB: Every in-built 'assumption' like this is a risk since it does
            not have to be justified and may thus be forgotten or
            violated. The clause
                [sem_clocked_vars bk H (idck n.(n_in))]
            requires that, for a semantics to exist, the input streams
            of the top-level program must correspond with the clocks of
            the interface to the top-level program (with the base clock
            always equal to true). This oligation, however, will only
            appear in the development when a lemma that asserts the
            existence of a semantics is added.
        TODO: add a note to this effect near the final theorem.

        Alternative approaches:

        a. Proof of clock alignment

           Show that the clock true/false svalues and stream present/absent
           svalues align as a consequence of the definitions without
           adding additional constraints.

           The required reasoning seems to be related to, and may be as
           tricky as, the proof of the existence of a semantics. By
           assuming the required properties in the model, we simply push
           the obligation into the semantic existence proof, likely
           in the Lustre rather than NLustre model.

        b. Restrict node arguments to variables and constants

           Requiring normalization of node arguments eliminates the need
           to reason about evaluation correctness and thus the extra
           constraint. This is the simplest approach, but the code
           generated in the common case (all arguments on the base clock)
           is somehow less satisfying.

           In any case, normalization ends up imposing the clocking
           constraint from [x = e] for each normalized argument.

        c. Incorporate a stronger invariant into [is_step_correct]

           It may be possible to strengthen the invariant used in
           [is_step_correct], but this lemma is already quite involved,
           and this approach seems a bit ad hoc.
   *)

  (** ** Induction principle for [sem_node] and [sem_equation] *)

  (** The automagically-generated induction principle is not strong
enough: it does not support the internal fixpoint introduced by
[Forall] *)

  Section sem_node_mult.
    Variable G: global.

    Variable P_equation: stream bool -> history -> equation -> Prop.
    Variable P_node: ident -> stream (list svalue) -> stream (list svalue) -> Prop.

    Hypothesis EqDefCase:
      forall bk H x xs ck ce,
        sem_var H x xs ->
        sem_caexp bk H ck ce xs ->
        P_equation bk H (EqDef x ck ce).

    Hypothesis EqAppCase:
      forall bk H x ck f arg xrs ys rs ls xs,
        sem_exps bk H arg ls ->
        sem_vars H x xs ->
        sem_clock bk H ck (clock_of ls) ->
        Forall2 (sem_var H) (map fst xrs) ys ->
        bools_ofs ys rs ->
        (forall k, sem_node G f (mask k rs ls) (mask k rs xs)
              /\ P_node f (mask k rs ls) (mask k rs xs)) ->
        P_equation bk H (EqApp x ck f arg xrs).

    Hypothesis EqFbyCase:
      forall bk H x ls xs c0 ck le xrs ys rs,
        sem_aexp bk H ck le ls ->
        sem_var H x xs ->
        Forall2 (sem_var H) (map fst xrs) ys ->
        sem_clocked_vars bk H xrs ->
        bools_ofs ys rs ->
        xs = reset (sem_const c0) (fby (sem_const c0) ls) rs ->
        P_equation bk H (EqFby x ck c0 le xrs).

    Hypothesis NodeCase:
      forall bk H f xss yss n,
        bk = clock_of xss ->
        find_node f G = Some n ->
        sem_vars H (map fst n.(n_in)) xss ->
        sem_vars H (map fst n.(n_out)) yss ->
        sem_clocked_vars bk H (idck n.(n_in)) ->
        Forall (sem_equation G bk H) n.(n_eqs) ->
        Forall (P_equation bk H) n.(n_eqs) ->
        P_node f xss yss.

    Fixpoint sem_equation_mult
            (b: stream bool) (H: history) (e: equation)
            (Sem: sem_equation G b H e) {struct Sem}
      : P_equation b H e
    with sem_node_mult
           (f: ident) (xss oss: stream (list svalue))
           (Sem: sem_node G f xss oss) {struct Sem}
         : P_node f xss oss.
    Proof.
      - destruct Sem; eauto.
      - destruct Sem; eauto.
        eapply NodeCase; eauto.
        match goal with H: Forall _ (n_eqs _) |- _ => induction H; auto end.
    Qed.

    Combined Scheme sem_node_equation_reset_ind from
             sem_node_mult, sem_equation_mult.

  End sem_node_mult.

  Lemma hold_abs:
    forall n c xs,
      xs n = absent ->
      hold c xs n = hold c xs (S n).
  Proof.
    destruct n; intros * E; simpl; now rewrite E.
  Qed.

  Lemma hold_pres:
    forall v n c xs,
      xs n = present v ->
      v = hold c xs (S n).
  Proof.
    destruct n; intros * E; simpl; now rewrite E.
  Qed.

  Lemma sem_node_wf:
    forall G f xss yss,
      sem_node G f xss yss ->
      wf_streams xss /\ wf_streams yss.
  Proof.
    intros * Sem; split; inv Sem;
      assert_const_length xss; assert_const_length yss; auto.
  Qed.

  (** ** Properties of the [global] environment *)

  Lemma sem_node_cons:
    forall node G enums f xs ys,
      Ordered_nodes (Global enums (node::G))
      -> sem_node (Global enums (node::G)) f xs ys
      -> node.(n_name) <> f
      -> sem_node (Global enums G) f xs ys.
  Proof.
    intros node G enums f xs ys Hord Hsem Hnf.
    revert Hnf.
    induction Hsem as [
                     | bk H x ck f le y ys rs ls xs Hles Hvars Hck Hvar ? Hnodes
                     |
                     | bk H f xs ys n Hbk Hf ??? Heqs IH]
                        using sem_node_mult
      with (P_equation := fun bk H eq => ~Is_node_in_eq node.(n_name) eq
                                      -> sem_equation (Global enums G) bk H eq).
    - econstructor; eassumption.
    - intro Hnin.
      eapply SEqApp; eauto.
      intro k; specialize (Hnodes k); destruct Hnodes as (?&IH).
      apply IH. intro Hnf. apply Hnin. rewrite Hnf. constructor.
    - intro; eapply SEqFby; eassumption.
    - intro.
      rewrite find_node_other with (1:=Hnf) in Hf.
      eapply SNode; eauto.
      assert (Forall (fun eq => ~ Is_node_in_eq (n_name node) eq) (n_eqs n)) as IHeqs
        by (eapply Is_node_in_Forall; try eassumption;
            eapply find_node_other_not_Is_node_in; try eassumption).
      clear Heqs; induction n.(n_eqs); inv IH; inv IHeqs; eauto.
  Qed.

  Lemma sem_node_cons':
    forall node G enums f xs ys,
      Ordered_nodes (Global enums (node::G))
      -> sem_node (Global enums G) f xs ys
      -> node.(n_name) <> f
      -> sem_node (Global enums (node::G)) f xs ys.
  Proof.
    intros node G enums f xs ys Hord Hsem Hnf.
    revert Hnf.
    induction Hsem as [
                     | bk H x ck f le y ys rs ls xs Hles Hvars Hck Hvar ? Hnodes
                     |
                     | bk H f xs ys n Hbk Hf ??? Heqs IH]
                        using sem_node_mult
      with (P_equation := fun bk H eq => ~Is_node_in_eq node.(n_name) eq
                                      -> sem_equation (Global enums (node::G)) bk H eq).
    - econstructor; eassumption.
    - intro Hnin.
      eapply SEqApp; eauto.
      intro k; specialize (Hnodes k); destruct Hnodes as (?&IH).
      apply IH. intro Hnf. apply Hnin. rewrite Hnf. constructor.
    - intro; eapply SEqFby; eassumption.
    - intro; subst.
      econstructor; auto.
      rewrite find_node_other; eauto.
      1-4:eauto.
      assert (Forall (fun eq => ~ Is_node_in_eq (n_name node) eq) (n_eqs n)) as IHeqs
        by (eapply Is_node_in_Forall; try eassumption;
            eapply find_node_other_not_Is_node_in; try eassumption).
      clear Heqs; induction n.(n_eqs); inv IH; inv IHeqs; eauto.
  Qed.

  Lemma sem_equation_global_tl:
    forall bk nd G H eq enums,
      Ordered_nodes (Global enums (nd::G)) ->
      ~ Is_node_in_eq nd.(n_name) eq ->
      sem_equation (Global enums (nd::G)) bk H eq ->
      sem_equation (Global enums G) bk H eq.
  Proof.
    intros bk nd G H eq enums Hord Hnini Hsem.
    destruct eq; inversion Hsem; subst; eauto using sem_equation.
    - econstructor; eauto.
      intro k; eapply sem_node_cons; eauto.
      intro HH; rewrite HH in *; auto using Is_node_in_eq.
  Qed.

  Lemma Forall_sem_equation_global_tl:
    forall bk nd G H eqs enums,
      Ordered_nodes (Global enums (nd::G))
      -> ~ Is_node_in nd.(n_name) eqs
      -> Forall (sem_equation (Global enums (nd::G)) bk H) eqs
      -> Forall (sem_equation (Global enums G) bk H) eqs.
  Proof.
    intros bk nd G H eqs enums Hord Hnini.
    apply Forall_impl_In.
    intros eq Hin Hsem.
    eapply sem_equation_global_tl; eauto.
    apply Is_node_in_Forall in Hnini.
    apply Forall_forall with (1:=Hnini) (2:=Hin).
  Qed.

  Lemma sem_equation_global_tl':
    forall bk nd G H eq enums,
      Ordered_nodes (Global enums (nd::G)) ->
      ~ Is_node_in_eq nd.(n_name) eq ->
      sem_equation (Global enums G) bk H eq ->
      sem_equation (Global enums (nd::G)) bk H eq.
  Proof.
    intros bk nd G H eq enums Hord Hnini Hsem.
    destruct eq; inversion Hsem; subst; eauto using sem_equation.
    - econstructor; eauto.
      intro k; eapply sem_node_cons'; eauto.
      intro HH; rewrite HH in *; auto using Is_node_in_eq.
  Qed.

  Lemma Forall_sem_equation_global_tl':
    forall bk nd G H eqs enums,
      Ordered_nodes (Global enums (nd::G))
      -> ~ Is_node_in nd.(n_name) eqs
      -> Forall (sem_equation (Global enums G) bk H) eqs
      -> Forall (sem_equation (Global enums (nd::G)) bk H) eqs.
  Proof.
    intros bk nd G H eqs enums Hord Hnini.
    apply Forall_impl_In.
    intros eq Hin Hsem.
    eapply sem_equation_global_tl'; eauto.
    apply Is_node_in_Forall in Hnini.
    apply Forall_forall with (1:=Hnini) (2:=Hin).
  Qed.

  Lemma sem_equations_permutation:
    forall eqs eqs' G bk H,
      Forall (sem_equation G bk H) eqs ->
      Permutation eqs eqs' ->
      Forall (sem_equation G bk H) eqs'.
  Proof.
    intros eqs eqs' G bk H Hsem Hperm.
    induction Hperm as [|eq eqs eqs' Hperm IH|eq0 eq1 eqs|]; auto.
    - inv Hsem; auto.
    - inversion_clear Hsem as [|? ? ? Heqs'].
      inv Heqs'; auto.
  Qed.

(** Morphisms properties *)

  Add Parametric Morphism G: (sem_equation G)
      with signature eq_str ==> eq ==> eq ==> Basics.impl
        as sem_equation_eq_str.
  Proof.
    intros * E ?? Sem.
    induction Sem; econstructor; eauto;
      try eapply lift_eq_str; eauto; try reflexivity.
    rewrite <-E. eauto.
  Qed.

  Add Parametric Morphism G f: (sem_node G f)
      with signature eq_str ==> eq_str ==> Basics.impl
        as sem_node_eq_str.
  Proof.
    intros * E1 ? ? E2 Node.
    inversion_clear Node as [??????????? Heqs]; subst.
    econstructor; eauto; try intro n; try rewrite <-E1; try rewrite <-E2; eauto.
    induction Heqs; constructor; auto.
    rewrite <-E1; auto.
  Qed.

End NLINDEXEDSEMANTICS.

Module NLIndexedSemanticsFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Ids Op)
       (Cks   : CLOCKS      Ids Op OpAux)
       (CESyn : CESYNTAX    Ids Op OpAux Cks)
       (Syn   : NLSYNTAX    Ids Op OpAux Cks CESyn)
       (Str   : INDEXEDSTREAMS  Ids Op OpAux Cks)
       (Ord   : NLORDERED   Ids Op OpAux Cks CESyn Syn)
       (CESem : CESEMANTICS Ids Op OpAux Cks CESyn      Str)
<: NLINDEXEDSEMANTICS Ids Op OpAux Cks CESyn Syn Str Ord CESem.
  Include NLINDEXEDSEMANTICS Ids Op OpAux Cks CESyn Syn Str Ord CESem.
End NLIndexedSemanticsFun.
