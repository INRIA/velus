From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Setoid.
From Coq Require Import Morphisms.

From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import CoreExpr.Stream.
From Velus Require Import CoreExpr.CESemantics.

(** * The NLustre semantics *)

(**

  We provide a "standard" dataflow semantics relating an environment
  of streams to a stream of outputs.

 *)

Module Type NLSEMANTICS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Op)
       (Import CESyn : CESYNTAX        Op)
       (Import Syn   : NLSYNTAX    Ids Op       CESyn)
       (Import Str   : STREAM          Op OpAux)
       (Import Ord   : NLORDERED   Ids Op       CESyn Syn)
       (Import CESem : CESEMANTICS Ids Op OpAux CESyn      Str).

  Fixpoint hold (v0: val) (xs: stream value) (n: nat) : val :=
    match n with
    | 0   => v0
    | S m => match xs m with
            | absent     => hold v0 xs m
            | present hv => hv
            end
    end.

  Definition fby (v0: val) (xs: stream value) : stream value :=
    fun n =>
      match xs n with
      | absent => absent
      | _      => present (hold v0 xs n)
      end.

  Section NodeSemantics.

    Variable G: global.

    Inductive sem_equation: stream bool -> history -> equation -> Prop :=
    | SEqDef:
        forall bk H x xs ck ce,
          sem_var H x xs ->
          sem_caexp bk H ck ce xs ->
          sem_equation bk H (EqDef x ck ce)
    | SEqApp:
        forall bk H x ck f arg ls xs,
          sem_exps bk H arg ls ->
          sem_vars H x xs ->
          sem_clock bk H ck (clock_of ls) ->
          sem_node f ls xs ->
          sem_equation bk H (EqApp x ck f arg None)
    | SEqReset:
        forall bk H x ck f arg y ys rs ls xs,
          sem_exps bk H arg ls ->
          sem_vars H x xs ->
          sem_clock bk H ck (clock_of ls) ->
          sem_var H y ys ->
          bools_of ys rs ->
          (forall k, sem_node f (mask k rs ls) (mask k rs xs)) ->
          sem_equation bk H (EqApp x ck f arg (Some y))
    | SEqFby:
        forall bk H x ls xs c0 ck le,
          sem_aexp bk H ck le ls ->
          sem_var H x xs ->
          xs = fby (sem_const c0) ls ->
          sem_equation bk H (EqFby x ck c0 le)

    with sem_node: ident -> stream (list value) -> stream (list value) -> Prop :=
         | SNode:
             forall bk H f xss yss n,
               bk = clock_of xss ->
               find_node f G = Some n ->
               sem_vars H (map fst n.(n_in)) xss ->
               sem_vars H (map fst n.(n_out)) yss ->
               sem_clocked_vars bk H (idck n.(n_in)) ->
               Forall (sem_equation bk H) n.(n_eqs) ->
               sem_node f xss yss.

    Definition sem_nodes : Prop :=
      Forall (fun no => exists xs ys, sem_node no.(n_name) xs ys) G.

  End NodeSemantics.

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
        stream values to clock values is not needed in this case.

     3. The [sem_clocked_vars] clause in [sem_node] requires that the
        streams passed as node arguments align with the instantiated
        clocks of the node interface.

        This is done to make possible the assertion, critical in
        [is_step_correct], that all arguments on the base clock of an
        application are present when that clock is true (and thus that
        the compiled expressions calculate the correct value). I.e., to
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

           Show that the clock true/false values and stream present/absent
           values align as a consequence of the definitions without
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
    Variable P_node: ident -> stream (list value) -> stream (list value) -> Prop.

    Hypothesis EqDefCase:
      forall bk H x xs ck ce,
        sem_var H x xs ->
        sem_caexp bk H ck ce xs ->
        P_equation bk H (EqDef x ck ce).

    Hypothesis EqAppCase:
      forall bk H x ck f arg ls xs,
        sem_exps bk H arg ls ->
        sem_vars H x xs ->
        sem_clock bk H ck (clock_of ls) ->
        sem_node G f ls xs ->
        P_node f ls xs ->
        P_equation bk H (EqApp x ck f arg None).

    Hypothesis EqResetCase:
      forall bk H x ck f arg y ys rs ls xs,
        sem_exps bk H arg ls ->
        sem_vars H x xs ->
        sem_clock bk H ck (clock_of ls) ->
        sem_var H y ys ->
        bools_of ys rs ->
        (forall k, sem_node G f (mask k rs ls) (mask k rs xs)
              /\ P_node f (mask k rs ls) (mask k rs xs)) ->
        P_equation bk H (EqApp x ck f arg (Some y)).

    Hypothesis EqFbyCase:
      forall bk H x ls xs c0 ck le,
        sem_aexp bk H ck le ls ->
        sem_var H x xs ->
        xs = fby (sem_const c0) ls ->
        P_equation bk H (EqFby x ck c0 le).

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
           (f: ident) (xss oss: stream (list value))
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
    forall node G f xs ys,
      Ordered_nodes (node::G)
      -> sem_node (node::G) f xs ys
      -> node.(n_name) <> f
      -> sem_node G f xs ys.
  Proof.
    intros node G f xs ys Hord Hsem Hnf.
    revert Hnf.
    induction Hsem as [
                     | bk H x ck f le ls xs Hles Hvars Hck Hnode IH
                     | bk H x ck f le y ys rs ls xs Hles Hvars Hck Hvar ? Hnodes
                     |
                     | bk H f xs ys n Hbk Hf ??? Heqs IH]
                        using sem_node_mult
      with (P_equation := fun bk H eq => ~Is_node_in_eq node.(n_name) eq
                                      -> sem_equation G bk H eq).
    - econstructor; eassumption.
    - intro Hnin.
      econstructor; eauto.
      apply IH. intro Hnf. apply Hnin. rewrite Hnf. constructor.
    - intro Hnin.
      eapply SEqReset; eauto.
      intro k; specialize (Hnodes k); destruct Hnodes as (?&IH).
      apply IH. intro Hnf. apply Hnin. rewrite Hnf. constructor.
    - intro; eapply SEqFby; eassumption.
    - intro.
      rewrite find_node_tl with (1:=Hnf) in Hf.
      eapply SNode; eauto.
      assert (Forall (fun eq => ~ Is_node_in_eq (n_name node) eq) (n_eqs n)) as IHeqs
        by (eapply Is_node_in_Forall; try eassumption;
            eapply find_node_later_not_Is_node_in; try eassumption).
      clear Heqs; induction n.(n_eqs); inv IH; inv IHeqs; eauto.
  Qed.

  Lemma find_node_find_again:
    forall G f n g,
      Ordered_nodes G
      -> find_node f G = Some n
      -> Is_node_in g n.(n_eqs)
      -> Exists (fun nd => g = nd.(n_name)) G.
  Proof.
    intros G f n g Hord Hfind Hini.
    apply find_node_split in Hfind.
    destruct Hfind as [bG [aG Hfind]].
    rewrite Hfind in *.
    clear Hfind.
    apply Ordered_nodes_append in Hord.
    apply Exists_app.
    constructor 2.
    inversion_clear Hord as [|? ? ? HH H0]; clear H0.
    apply HH in Hini; clear HH.
    intuition.
  Qed.

  Lemma sem_equation_global_tl:
    forall bk nd G H eq,
      Ordered_nodes (nd::G) ->
      ~ Is_node_in_eq nd.(n_name) eq ->
      sem_equation (nd::G) bk H eq ->
      sem_equation G bk H eq.
  Proof.
    intros bk nd G H eq Hord Hnini Hsem.
    destruct eq; inversion Hsem; subst; eauto using sem_equation.
    - econstructor; eauto.
      eapply sem_node_cons; eauto.
      intro HH; rewrite HH in *; auto using Is_node_in_eq.
    - econstructor; eauto.
      intro k; eapply sem_node_cons; eauto.
      intro HH; rewrite HH in *; auto using Is_node_in_eq.
  Qed.

  Lemma Forall_sem_equation_global_tl:
    forall bk nd G H eqs,
      Ordered_nodes (nd::G)
      -> ~ Is_node_in nd.(n_name) eqs
      -> Forall (sem_equation (nd::G) bk H) eqs
      -> Forall (sem_equation G bk H) eqs.
  Proof.
    intros bk nd G H eqs Hord Hnini.
    apply Forall_impl_In.
    intros eq Hin Hsem.
    eapply sem_equation_global_tl; eauto.
    apply Is_node_in_Forall in Hnini.
    apply Forall_forall with (1:=Hnini) (2:=Hin).
  Qed.

  Lemma sem_node_cons2:
    forall nd G f xs ys,
      Ordered_nodes G
      -> sem_node G f xs ys
      -> Forall (fun nd' : node => n_name nd <> n_name nd') G
      -> sem_node (nd::G) f xs ys.
  Proof.
    Hint Constructors sem_equation.
    intros nd G f xs ys Hord Hsem Hnin.
    assert (Hnin':=Hnin).
    revert Hnin'.
    induction Hsem as [
                     | bk H x ck f le ls xs Hles Hvars Hck Hnode IH
                     | bk H x ck f le y ys rs ls xs Hles Hvars Hck Hvar ? Hnodes
                     |
                     | bk H f xs ys n Hbk Hfind Hxs Hys ? Heqs IH]
                        using sem_node_mult
      with (P_equation := fun bk H eq =>
                            ~Is_node_in_eq nd.(n_name) eq
                            -> sem_equation (nd::G) bk H eq);
      try eauto; try intro HH.
    - econstructor; eauto.
      intro k; specialize (Hnodes k); destruct Hnodes; auto.
    - clear HH.
      assert (nd.(n_name) <> f) as Hnf.
      { intro Hnf.
        rewrite Hnf in *.
        pose proof Hfind as Hfind'.
        apply find_node_split in Hfind.
        destruct Hfind as [bG [aG Hge]].
        rewrite Hge in Hnin.
        apply Forall_app in Hnin.
        destruct Hnin as [? Hfg].
        inversion_clear Hfg.
        match goal with H:f<>_ |- False => apply H end.
        erewrite find_node_name; eauto.
      }
      apply find_node_other with (2:=Hfind) in Hnf.
      econstructor; eauto.
      clear Heqs Hxs Hys.
      rename IH into Heqs.
      assert (forall g, Is_node_in g n.(n_eqs)
                   -> Exists (fun nd=> g = nd.(n_name)) G)
        as Hniex by
            (intros g Hini;
             eapply find_node_find_again with (1:=Hord) (2:=Hfind) in Hini; eauto).
      assert (Forall
                (fun eq=> forall g,
                     Is_node_in_eq g eq
                     -> Exists (fun nd=> g = nd.(n_name)) G) n.(n_eqs)) as HH.
      {
        clear Hfind Heqs Hnf.
        induction n.(n_eqs) as [|eq eqs IH]; [now constructor|].
        constructor.
        - intros g Hini.
          apply Hniex.
          constructor 1; apply Hini.
        - apply IH.
          intros g Hini; apply Hniex.
          constructor 2; apply Hini.
      }
      apply Forall_Forall with (1:=HH) in Heqs.
      apply Forall_impl with (2:=Heqs).
      intros eq IH.
      destruct IH as [Hsem IH1].
      apply IH1.
      intro Hini.
      apply Hsem in Hini.
      apply Forall_Exists with (1:=Hnin) in Hini.
      apply Exists_exists in Hini.
      destruct Hini as [nd' [Hin [Hneq Heq]]].
      intuition.
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
      eapply lift_eq_str; eauto; reflexivity.
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

End NLSEMANTICS.

Module NLSemanticsFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Op)
       (CESyn : CESYNTAX        Op)
       (Syn   : NLSYNTAX    Ids Op       CESyn)
       (Str   : STREAM          Op OpAux)
       (Ord   : NLORDERED   Ids Op       CESyn Syn)
       (CESem : CESEMANTICS Ids Op OpAux CESyn      Str)
<: NLSEMANTICS Ids Op OpAux CESyn Syn Str Ord CESem.
  Include NLSEMANTICS Ids Op OpAux CESyn Syn Str Ord CESem.
End NLSemanticsFun.
