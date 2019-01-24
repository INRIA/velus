Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Arith.Compare_dec.

Require Import Coq.FSets.FMapPositive.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.RMemory.
Require Import Velus.NLustre.Stream.
Require Import Velus.NLustre.NLExprSyntax.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.IsVariable.
Require Import Velus.NLustre.IsDefined.
Require Import Velus.NLustre.NLExprSemantics.
Require Import Velus.NLustre.NLSemantics.
Require Import Velus.NLustre.Ordered.
Require Import Velus.NLustre.WellFormed.
Require Import Velus.NLustre.Memories.
Require Import Velus.NLustre.IsFree.
Require Import Velus.NLustre.NoDup.

Set Implicit Arguments.

(** * The NLustre+Memory semantics *)

(**

  We provide a "non-standard" dataflow semantics where the state
  introduced by an [fby] is kept in a separate [memory] of
  streams. The only difference is therefore in the treatment of the
  [fby].

 *)


(* XXX: Is this comment still relevant?

   NB: The history H is not really necessary here. We could just as well
       replay all the semantic definitions using a valueEnv N ('N' for now),
       since all the historical information is in ms. This approach would
       have two advantages:

       1. Conceptually cleanliness: N corresponds more or less to the
          temporary variables in the Obc implementation (except that it
          would also contain values for variables defined by EqFby).

       2. No index needed to access values in when reasoning about
          translation correctness.

       But this approach requires more uninteresting definitions and
       and associated proofs of properties, and a longer proof of equivalence
       with sem_node: too much work for too little gain.
 *)

Module Type MEMSEMANTICS
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import OpAux   : OPERATORS_AUX   Op)
       (Import Clks    : CLOCKS          Ids)
       (Import ExprSyn : NLEXPRSYNTAX        Op)
       (Import Syn     : NLSYNTAX        Ids Op       Clks ExprSyn)
       (Import Str     : STREAM              Op OpAux)
       (Import Ord     : ORDERED         Ids Op       Clks ExprSyn Syn)
       (Import ExprSem : NLEXPRSEMANTICS Ids Op OpAux Clks ExprSyn     Str)
       (Import Sem     : NLSEMANTICS     Ids Op OpAux Clks ExprSyn Syn Str Ord ExprSem)
       (Import Mem     : MEMORIES        Ids Op       Clks ExprSyn Syn)
       (Import IsD     : ISDEFINED       Ids Op       Clks ExprSyn Syn                 Mem)
       (Import IsV     : ISVARIABLE      Ids Op       Clks ExprSyn Syn                 Mem IsD)
       (Import IsF     : ISFREE          Ids Op       Clks ExprSyn Syn)
       (Import NoD     : NODUP           Ids Op       Clks ExprSyn Syn                 Mem IsD IsV)
       (Import WeF     : WELLFORMED      Ids Op       Clks ExprSyn Syn             Ord Mem IsD IsV IsF NoD).

  Definition memories := stream (memory val).

  Definition memory_masked (k: nat) (rs: cstream) (M M': memories) :=
    forall n, count rs n = k -> M' n = M n.

  Definition mfby (x: ident) (c0: val) (xs: stream value) (M M': memories) (ys: stream value) : Prop :=
    find_val x (M 0) = Some c0
    /\ (forall n, find_val x (M (S n)) = find_val x (M' n))
    /\ forall n, match find_val x (M n) with
           | Some mv =>
             match xs n with
             | absent =>
               find_val x (M' n) = Some mv
               /\ ys n = absent
             | present v =>
               find_val x (M' n) = Some v
               /\ ys n = present mv
             end
           | None => False
           end.

  Section NodeSemantics.

    Definition sub_inst_n (x: ident) (M M': memories) : Prop :=
      forall n, sub_inst x (M n) (M' n).

    Variable G: global.

    (* Inductive well_formed_memory: memory val -> ident -> Prop := *)
    (*   well_formed_memory_intro: *)
    (*     forall M f n, *)
    (*       find_node f G = Some n -> *)
    (*       (forall i M', sub_inst i M M' -> *)
    (*                exists f', In (i, f') (gather_insts n.(n_eqs)) *)
    (*                      /\ well_formed_memory M' f') -> *)
    (*       (forall i f', In (i, f') (gather_insts n.(n_eqs)) -> *)
    (*                exists M', sub_inst i M M' *)
    (*                      /\ well_formed_memory M' f') -> *)
    (*       (forall x, (exists v, find_val x M = Some v) <-> In x (gather_mem n.(n_eqs))) -> *)
    (*       well_formed_memory M f. *)

    (* Definition well_formed_memory_n (M: memories) (f: ident) : Prop := *)
    (*   forall n, well_formed_memory (M n) f. *)

    Definition memory_closed (M: memory val) (eqs: list equation) : Prop :=
      (forall i, find_inst i M <> None -> InMembers i (gather_insts eqs))
      /\ forall x, find_val x M <> None -> In x (gather_mem eqs).

    Definition memory_closed_n (M: memories) (eqs: list equation) : Prop :=
      forall n, memory_closed (M n) eqs.

    (* Inductive well_formed_memory: memory val -> list equation -> Prop := *)
    (*   well_formed_memory_intro: *)
    (*     forall M eqs, *)
    (*       (forall i, (exists M', sub_inst i M M') <-> InMembers i (gather_insts eqs)) -> *)
    (*       (forall x, (exists v, find_val x M = Some v) <-> In x (gather_mem eqs)) -> *)
    (*       well_formed_memory M eqs. *)

    Inductive msem_equation: stream bool -> history -> memories -> memories -> equation -> Prop :=
    | SEqDef:
        forall bk H M M' x ck xs ce,
          sem_var H x xs ->
          sem_caexp bk H ck ce xs ->
          msem_equation bk H M M' (EqDef x ck ce)
    | SEqApp:
        forall bk H M M' x xs ck f Mx Mx' arg ls xss,
          Some x = hd_error xs ->
          sub_inst_n x M Mx ->
          sub_inst_n x M' Mx' ->
          sem_laexps bk H ck arg ls ->
          sem_vars H xs xss ->
          msem_node f ls Mx Mx' xss ->
          msem_equation bk H M M' (EqApp xs ck f arg None)
    | SEqReset:
        forall bk H M M' x xs ck f Mx Mx' arg r ck_r ys rs ls xss,
          Some x = hd_error xs ->
          sub_inst_n x M Mx ->
          sub_inst_n x M' Mx' ->
          sem_laexps bk H ck arg ls ->
          sem_vars H xs xss ->
          (* sem_avar bk H ck_r r ys -> *)
          sem_var H r ys ->
          reset_of ys rs ->
          msem_reset f rs ls Mx Mx' xss ->
          msem_equation bk H M M' (EqApp xs ck f arg (Some (r, ck_r)))
    | SEqFby:
        forall bk H M M' x ck ls xs c0 le,
          sem_laexp bk H ck le ls ->
          sem_var H x xs ->
          mfby x (sem_const c0) ls M M' xs ->
          msem_equation bk H M M' (EqFby x ck c0 le)

    with msem_reset:
           ident -> stream bool -> stream (list value) -> memories -> memories -> stream (list value) -> Prop :=
         | SReset:
             forall f r xss M M' yss,
               (forall k, exists Mk Mk',
                     msem_node f (mask (all_absent (xss 0)) k r xss)
                               Mk Mk'
                               (mask (all_absent (yss 0)) k r yss)
                     /\ memory_masked k r M Mk
                     /\ memory_masked k r M' Mk') ->
               msem_reset f r xss M M' yss

    with msem_node:
           ident -> stream (list value) -> memories -> memories -> stream (list value) -> Prop :=
         | SNode:
             forall bk H f xss M M' yss n,
               clock_of xss bk ->
               find_node f G = Some n ->
               sem_vars H (map fst n.(n_in)) xss ->
               sem_vars H (map fst n.(n_out)) yss ->
               same_clock xss ->
               same_clock yss ->
               (forall n, absent_list (xss n) <-> absent_list (yss n)) ->
               Forall (msem_equation bk H M M') n.(n_eqs) ->
               (* well_formed_memory_n M f -> *)
               memory_closed_n M n.(n_eqs) ->
               msem_node f xss M M' yss.

    Definition msem_equations bk H M M' eqs := Forall (msem_equation bk H M M') eqs.

  End NodeSemantics.

  (** ** Induction principle for [msem_equation] and [msem_node] *)

  (** The automagically-generated induction principle is not strong
enough: it does not support the internal fixpoint introduced by
[Forall] *)

  Section msem_node_mult.

    Variable G: global.

    Variable P_equation: stream bool -> history -> memories -> memories -> equation -> Prop.
    Variable P_reset: ident -> stream bool -> stream (list value) -> memories -> memories -> stream (list value) -> Prop.
    Variable P_node: ident -> stream (list value) -> memories -> memories -> stream (list value) -> Prop.

    Hypothesis EqDefCase:
      forall bk H M M' x ck xs ce,
        sem_var H x xs ->
        sem_caexp bk H ck ce xs ->
        P_equation bk H M M' (EqDef x ck ce).

    Hypothesis EqAppCase:
      forall bk H M M' x xs ck f Mx Mx' arg ls xss,
        Some x = hd_error xs ->
        sub_inst_n x M Mx ->
        sub_inst_n x M' Mx' ->
        sem_laexps bk H ck arg ls ->
        sem_vars H xs xss ->
        msem_node G f ls Mx Mx' xss ->
        P_node f ls Mx Mx' xss ->
        P_equation bk H M M' (EqApp xs ck f arg None).

    Hypothesis EqResetCase:
      forall bk H M M' x xs ck f Mx Mx' arg r ck_r ys rs ls xss,
        Some x = hd_error xs ->
        sub_inst_n x M Mx ->
        sub_inst_n x M' Mx' ->
        sem_laexps bk H ck arg ls ->
        sem_vars H xs xss ->
        (* sem_avar bk H ck_r r ys -> *)
        sem_var H r ys ->
        reset_of ys rs ->
        msem_reset G f rs ls Mx Mx' xss ->
        P_reset f rs ls Mx Mx' xss ->
        P_equation bk H M M' (EqApp xs ck f arg (Some (r, ck_r))).

    Hypothesis EqFbyCase:
      forall bk H M M' x ck ls xs c0 le,
        sem_laexp bk H ck le ls ->
        sem_var H x xs ->
        mfby x (sem_const c0) ls M M' xs ->
        P_equation bk H M M' (EqFby x ck c0 le).

    Hypothesis ResetCase:
      forall f r xss M M' yss,
        (forall k, exists Mk Mk',
              msem_node G f (mask (all_absent (xss 0)) k r xss)
                        Mk Mk'
                        (mask (all_absent (yss 0)) k r yss)
              /\ memory_masked k r M Mk
              /\ memory_masked k r M' Mk'
              /\ P_node f (mask (all_absent (xss 0)) k r xss)
                       Mk Mk'
                       (mask (all_absent (yss 0)) k r yss)) ->
        P_reset f r xss M M' yss.

    Hypothesis NodeCase:
      forall bk H f xss M M' yss n,
        clock_of xss bk ->
        find_node f G = Some n ->
        sem_vars H (map fst n.(n_in)) xss ->
        sem_vars H (map fst n.(n_out)) yss ->
        same_clock xss ->
        same_clock yss ->
        (forall n, absent_list (xss n) <-> absent_list (yss n)) ->
        Forall (msem_equation G bk H M M') n.(n_eqs) ->
        (* well_formed_memory_n G M f -> *)
        memory_closed_n M n.(n_eqs) ->
        Forall (P_equation bk H M M') n.(n_eqs) ->
        P_node f xss M M' yss.

    Fixpoint msem_equation_mult
             (b: stream bool) (H: history) (M M': memories) (e: equation)
             (Sem: msem_equation G b H M M' e) {struct Sem}
      : P_equation b H M M' e
    with msem_reset_mult
           (f: ident) (r: stream bool)
           (xss: stream (list value))
           (M M': memories)
           (oss: stream (list value))
           (Sem: msem_reset G f r xss M M' oss) {struct Sem}
         : P_reset f r xss M M' oss
    with msem_node_mult
           (f: ident)
           (xss: stream (list value))
           (M M': memories)
           (oss: stream (list value))
           (Sem: msem_node G f xss M M' oss) {struct Sem}
         : P_node f xss M M' oss.
    Proof.
      - destruct Sem; eauto.
      - destruct Sem; eauto.
        apply ResetCase; auto.
        intro k; destruct (H k) as (?&?&?&?&?); eauto 7.
      - destruct Sem; eauto.
        eapply NodeCase; eauto.
        clear H8.
        induction H7; auto.
    Qed.

    Combined Scheme msem_equation_node_reset_ind from
             msem_equation_mult, msem_node_mult, msem_reset_mult.

  End msem_node_mult.

  Definition msem_nodes (G: global) : Prop :=
    Forall (fun no => exists xs M M' ys, msem_node G no.(n_name) xs M M' ys) G.

(*   (** Morphisms properties *) *)

(* Require Import Morphisms. *)
(*   Add Parametric Morphism G f xs ys: (fun M M' => msem_node G f xs M M' ys) *)
(*       with signature equal_memory ==> equal_memory ==> Basics.impl *)
(*         as msem_node_equal_memory. *)
(*   Proof. *)
(*     intros ** E1 ? ? E2 Node. *)
(*     inv Node. *)
(*     econstructor; eauto; intro; try rewrite <-E1; try rewrite <-E2; auto. *)
(*   Qed. *)

  (** ** Properties *)

  (** *** Equation non-activation *)

  (* Lemma subrate_property_eqn: *)
  (*   forall G H M bk xss eqn n, *)
  (*     clock_of xss bk -> *)
  (*     msem_equation G bk H M eqn -> *)
  (*     0 < length (xss n) -> *)
  (*     absent_list (xss n) -> *)
  (*     rhs_absent_instant (bk n) (restr H n) eqn. *)
  (* Proof. *)
  (*   intros * Hck Hsem Hlen Habs. *)
  (*   assert (Hbk: bk n = false). *)
  (*   { *)
  (*     destruct (Bool.bool_dec (bk n) false) as [Hbk | Hbk]; eauto. *)
  (*     exfalso. *)
  (*     apply Bool.not_false_is_true in Hbk. *)
  (*     eapply Hck in Hbk. *)
  (*     eapply not_absent_present_list in Hbk; auto. *)
  (*   } *)
  (*   induction Hsem as [???????? Hsem | *)
  (*                      ????????????? Hsem | *)
  (*                      ???????????????? Hsem ? Hvar | *)
  (*                      ????????? Hsem]; *)
  (*     unfold sem_caexp, lift in Hsem; specialize (Hsem n); inv Hsem; *)
  (*       try (exfalso; rewrite Hbk in *; now eapply not_subrate_clock; eauto). *)
  (*   - eauto using rhs_absent_instant, sem_caexp_instant. *)
  (*   - econstructor. *)
  (*     + apply SLabss; eauto. *)
  (*     + match goal with H: ls n = _ |- _ => rewrite H end; apply all_absent_spec. *)
  (*   - unfold sem_var, lift in Hvar; specialize (Hvar n); inv Hvar; *)
  (*       try (exfalso; rewrite Hbk in *; now eapply not_subrate_clock; eauto). *)
  (*     econstructor. *)
  (*     + apply SLabss; eauto. *)
  (*     + match goal with H: ls n = _ |- _ => rewrite H end; apply all_absent_spec. *)
  (*     (* + eauto using sem_avar_instant. *) *)
  (*   - eauto using rhs_absent_instant, sem_laexp_instant. *)
  (* Qed. *)

  (* Lemma subrate_property_eqns: *)
  (*   forall G H M bk xss eqns n, *)
  (*     clock_of xss bk -> *)
  (*     msem_equations G bk H M eqns -> *)
  (*     0 < length (xss n) -> *)
  (*     absent_list (xss n) -> *)
  (*     Forall (rhs_absent_instant (bk n) (restr H n)) eqns. *)
  (* Proof. *)
  (*   intros * Hck Hsem Habs. *)
  (*   induction eqns as [|eqn eqns]; auto. *)
  (*   inversion_clear Hsem. *)
  (*   constructor. *)
  (*   eapply subrate_property_eqn; eauto. *)
  (*   eapply IHeqns; eauto. *)
  (* Qed. *)

  (** *** Environment cons-ing lemmas *)

  (* Instead of repeating all these cons lemmas (i.e., copying and pasting them),
   and dealing with similar obligations multiple times in translation_correct,
   maybe it would be better to bake Ordered_nodes into msem_node and to make
   it like Miniimp, i.e.,
      find_node f G = Some (nd, G') and msem_node G' nd xs ys ?
   TODO: try this when the other elements are stabilised. *)

  Definition valid_app_eq (eq: equation) :=
    match eq with
    | EqApp xs _ _ _ _ => 0 < length xs
    | _ => True
    end.

  Definition valid_app_eqs (eqs: list equation) : Prop :=
    Forall valid_app_eq eqs.

  Lemma Is_node_in_gather_insts:
    forall eqs f,
      valid_app_eqs eqs ->
      ((exists i, In (i, f) (gather_insts eqs)) <-> Is_node_in f eqs).
  Proof.
    unfold Is_node_in.
    induction eqs as [|[]]; simpl; inversion_clear 1.
    - split; inversion 1; contradiction.
    - split; [intros ** (?&Hin)|inversion_clear 1 as [?? Hin|?? Hin]].
      + right; rewrite <-IHeqs; eauto.
      + inv Hin.
      + apply IHeqs in Hin; auto.
    - split; [intros ** (?&Hin)|inversion_clear 1 as [?? Hin|?? Hin]].
      + unfold gather_insts, concatMap in *; simpl in Hin.
        destruct i; simpl in Hin.
        * right; rewrite <-IHeqs; eauto.
        *{ destruct Hin as [E|].
           - inv E; subst; left; constructor.
           - right; rewrite <-IHeqs; eauto.
         }
      + unfold gather_insts, concatMap; simpl.
        destruct i; simpl.
        * simpl in *; omega.
        * inv Hin; eauto.
      + apply IHeqs in Hin as (?&?); auto.
        eexists. unfold gather_insts, concatMap in *.
        apply in_app; right; eauto.
    - split; [intros ** (?&Hin)|inversion_clear 1 as [?? Hin|?? Hin]].
      + right; rewrite <-IHeqs; eauto.
      + inv Hin.
      + apply IHeqs in Hin; auto.
  Qed.

  Lemma Is_node_in_gather_insts':
    forall eqs i f,
      In (i, f) (gather_insts eqs) -> Is_node_in f eqs.
  Proof.
    unfold Is_node_in, gather_insts, concatMap.
    induction eqs as [|[]]; simpl; eauto.
    - contradiction.
    - intros ** Hin; destruct i; simpl; eauto.
      apply in_app in Hin as [Hin|]; eauto.
      destruct Hin as [Hin|]; try contradiction.
      inv Hin; auto using Is_node_in_eq.
  Qed.

  Inductive valid_app_node: global -> ident -> Prop :=
    valid_app_node_intro:
      forall G f n,
        find_node f G = Some n ->
        (forall xs ck f es r, In (EqApp xs ck f es r) n.(n_eqs) ->
                         0 < length xs /\ valid_app_node G f) ->
        valid_app_node G f.

  Lemma valid_app_node_eqs:
    forall G f n,
      valid_app_node G f ->
      find_node f G = Some n ->
      valid_app_eqs n.(n_eqs).
  Proof.
    inversion_clear 1 as [??? Find Spec]; intros Find'.
    rewrite Find in Find'; inv Find'.
    apply Forall_forall; intros []; simpl; auto.
    intros; edestruct Spec; eauto.
  Qed.

  (* Lemma well_formed_memory_cons: *)
  (*   forall M n G f, *)
  (*     Ordered_nodes (n :: G) -> *)
  (*     valid_app_node G f -> *)
  (*     well_formed_memory (n :: G) M f -> *)
  (*     n.(n_name) <> f -> *)
  (*     well_formed_memory G M f. *)
  (* Proof. *)
  (*   induction M as [? IH] using memory_ind'; *)
  (*     inversion_clear 2 as [??? Find' AppIn]; *)
  (*     inversion_clear 1 as [??? Find Insts Insts']; intros. *)
  (*   rewrite find_node_tl in Find; auto. *)
  (*   rewrite Find in Find'; inv Find'. *)
  (*   econstructor; eauto. *)
  (*   - intros ** Sub. *)
  (*     edestruct Insts as (f' &?&?); eauto. *)
  (*     exists f'; split; auto. *)
  (*     assert (valid_app_eqs (n_eqs n0)) as Valid *)
  (*         by (eapply valid_app_node_eqs; eauto using valid_app_node). *)
  (*     assert (Is_node_in f' (n_eqs n0)) as Hin *)
  (*         by (apply Is_node_in_gather_insts; eauto). *)
  (*     apply Exists_exists in Hin as (?&?& Hin). *)
  (*     inv Hin. *)
  (*     eapply IH; eauto. *)
  (*     + edestruct AppIn; eauto. *)
  (*     + eapply find_node_later_not_Is_node_in in Find; eauto. *)
  (*       rewrite <-Is_node_in_gather_insts in Find; eauto. *)
  (*       intro E; apply Find; rewrite E; eauto. *)
  (*   - intros ** Hin. *)
  (*     edestruct Insts' as (M' &?&?); eauto. *)
  (*     exists M'; split; auto. *)
  (*     assert (valid_app_eqs (n_eqs n0)) as Valid *)
  (*         by (eapply valid_app_node_eqs; eauto using valid_app_node). *)
  (*     assert (Is_node_in f' (n_eqs n0)) as Hin' *)
  (*         by (apply Is_node_in_gather_insts; eauto). *)
  (*     apply Exists_exists in Hin' as (?&?& Hin'). *)
  (*     inv Hin'. *)
  (*     eapply IH; eauto. *)
  (*     + edestruct AppIn; eauto. *)
  (*     + eapply find_node_later_not_Is_node_in in Find; eauto. *)
  (*       rewrite <-Is_node_in_gather_insts in Find; eauto. *)
  (*       intro E; apply Find; rewrite E; eauto. *)
  (* Qed. *)

  Lemma msem_node_valid_app_cons:
    forall n G f xs M' M ys,
      Ordered_nodes (n :: G) ->
      msem_node (n :: G) f xs M M' ys ->
      n.(n_name) <> f ->
      valid_app_node G f.
  Proof.
    intros ** Hord Hsem Hnf; revert Hnf.
    induction Hsem as [| | | |?????? Reset|????????? Find ??????? Heqs] using msem_node_mult
      with (P_equation := fun bk H M M' eq =>
                            valid_app_eq eq
                            /\ forall f, n.(n_name) <> f ->
                                   Is_node_in_eq f eq ->
                                   valid_app_node G f)
           (P_reset := fun f r xss M M' yss =>
                         n.(n_name) <> f -> valid_app_node G f);
      simpl; auto.
    - split; auto; inversion 2.
    - split.
      + destruct xs; simpl in *; try omega; discriminate.
      + inversion 2; subst; auto.
    - split.
      + destruct xs; simpl in *; try omega; discriminate.
      + inversion 2; subst; auto.
    - split; auto; inversion 2.
    - destruct (Reset 0) as (?&?&?&?&?&?); auto.
    - intros; rewrite find_node_tl in Find; auto.
      rewrite Forall_forall in Heqs.
      econstructor; eauto.
      intros; edestruct Heqs as (?& ValidNode);
        simpl in *; eauto; split; auto.
      apply ValidNode; auto using Is_node_in_eq.
      eapply find_node_later_not_Is_node_in in Hord; eauto.
      intro E; apply Hord; rewrite E.
      apply Exists_exists.
      eexists; split; eauto using Is_node_in_eq.
  Qed.

  Lemma msem_node_cons:
    forall n G f xs M M' ys,
      Ordered_nodes (n :: G) ->
      msem_node (n :: G) f xs M M' ys ->
      n.(n_name) <> f ->
      msem_node G f xs M M' ys.
  Proof.
    Hint Constructors msem_node msem_equation msem_reset.
    intros ** Hord Hsem Hnf.
    revert Hnf.
    induction Hsem as [| | | |?????? IH |????????? Hf ??????? IH]
        using msem_node_mult
      with (P_equation := fun bk H M M' eq =>
                            ~Is_node_in_eq n.(n_name) eq ->
                            msem_equation G bk H M M' eq)
           (P_reset := fun f r xss M M' yss =>
                         n_name n <> f ->
                         msem_reset G f r xss M M' yss); eauto.
    - intro Hnin.
      econstructor; eauto.
      apply IHHsem. intro Hnf; apply Hnin; rewrite Hnf. constructor.
    - intro Hnin.
      econstructor; eauto.
      apply IHHsem. intro Hnf; apply Hnin; rewrite Hnf. constructor.
    - intro. econstructor. intro k; destruct (IH k) as (?&?&?&?&?&?); eauto 6.
    - intro.
      pose proof Hf.
      rewrite find_node_tl with (1:=Hnf) in Hf.
      econstructor; eauto.
      + apply find_node_later_not_Is_node_in with (2:=Hf) in Hord.
        apply Is_node_in_Forall in Hord.
        apply Forall_Forall with (1:=Hord) in IH.
        apply Forall_impl with (2:=IH).
        intuition.
      (* + intro; eapply well_formed_memory_cons; eauto. *)
      (*   eapply msem_node_valid_app_cons; eauto. *)
  Qed.

  Corollary msem_reset_cons:
    forall n G f r xs M M' ys,
      Ordered_nodes (n :: G) ->
      msem_reset (n :: G) f r xs M M' ys ->
      n.(n_name) <> f ->
      msem_reset G f r xs M M' ys.
  Proof.
    intros ** Sem ?.
    inversion_clear Sem as [?????? SemN].
    constructor.
    intro k; destruct (SemN k) as (?&?&?&?); eauto using msem_node_cons.
  Qed.

  (* Lemma well_formed_memory_cons2: *)
  (*   forall M n G f, *)
  (*     valid_app_node G f -> *)
  (*     well_formed_memory G M f -> *)
  (*     Forall (fun n' => n_name n <> n_name n') G -> *)
  (*     well_formed_memory (n :: G) M f. *)
  (* Proof. *)
  (*   induction M as [? IH] using memory_ind'; *)
  (*     inversion_clear 1 as [??? Find' AppIn]; *)
  (*     inversion_clear 1 as [??? Find Insts Insts']; intros ** Hnin. *)
  (*   rewrite Find in Find'; inv Find'. *)
  (*   assert (n.(n_name) <> f) as Hnf. *)
  (*   { intro Hnf. *)
  (*     rewrite Hnf in *. *)
  (*     pose proof (find_node_name _ _ _ Find). *)
  (*     apply find_node_split in Find. *)
  (*     destruct Find as [bG [aG Hge]]. *)
  (*     rewrite Hge in Hnin. *)
  (*     apply Forall_app in Hnin. *)
  (*     destruct Hnin as [H' Hfg]; clear H'. *)
  (*     inversion_clear Hfg. *)
  (*     match goal with H:f<>_ |- False => now apply H end. *)
  (*   } *)
  (*   pose proof Find as Find'. *)
  (*   rewrite <-find_node_other in Find; eauto. *)
  (*   econstructor; eauto. *)
  (*   - intros ** Sub. *)
  (*     edestruct Insts as (f' &?&?); eauto. *)
  (*     exists f'; split; auto. *)
  (*     assert (valid_app_eqs (n_eqs n0)) as Valid *)
  (*         by (eapply valid_app_node_eqs with (2 := Find'); eauto using valid_app_node). *)
  (*     assert (Is_node_in f' (n_eqs n0)) as Hin *)
  (*         by (apply Is_node_in_gather_insts; eauto). *)
  (*     apply Exists_exists in Hin as (?&?& Hin). *)
  (*     inv Hin. *)
  (*     eapply IH; eauto. *)
  (*     edestruct AppIn; eauto. *)
  (*   - intros ** Hin. *)
  (*     edestruct Insts' as (M' &?&?); eauto. *)
  (*     exists M'; split; auto. *)
  (*     assert (valid_app_eqs (n_eqs n0)) as Valid *)
  (*         by (eapply valid_app_node_eqs; eauto using valid_app_node). *)
  (*     assert (Is_node_in f' (n_eqs n0)) as Hin' *)
  (*         by (apply Is_node_in_gather_insts; eauto). *)
  (*     apply Exists_exists in Hin' as (?&?& Hin'). *)
  (*     inv Hin'. *)
  (*     eapply IH; eauto. *)
  (*     edestruct AppIn; eauto. *)
  (* Qed. *)

  Lemma msem_node_valid_app:
    forall G f xs M' M ys,
      msem_node G f xs M M' ys ->
      valid_app_node G f.
  Proof.
    intro G.
    induction 1 as [| | | |?????? Reset|????????????????? Heqs] using msem_node_mult
      with (P_equation := fun bk H M M' eq =>
                            valid_app_eq eq
                            /\ forall f, Is_node_in_eq f eq -> valid_app_node G f)
           (P_reset := fun f r xss M M' yss =>
                         valid_app_node G f); simpl; auto.
    - split; auto; inversion 1.
    - split.
      + destruct xs; simpl in *; try omega; discriminate.
      + now inversion_clear 1.
    - split.
      + destruct xs; simpl in *; try omega; discriminate.
      + now inversion_clear 1.
    - split; auto; inversion 1.
    - destruct (Reset 0) as (?&?&?&?&?&?); auto.
    - rewrite Forall_forall in Heqs.
      econstructor; eauto.
      intros; edestruct Heqs as (?& ValidNode);
        simpl in *; eauto; split; auto.
      auto using Is_node_in_eq.
  Qed.

  Lemma msem_node_cons2:
    forall n G f xs M M' ys,
      Ordered_nodes G ->
      msem_node G f xs M M' ys ->
      Forall (fun n' => n_name n <> n_name n') G ->
      msem_node (n :: G) f xs M M' ys.
  Proof.
    Hint Constructors msem_equation.
    intros ** Hord Hsem Hnin.
    assert (Hnin':=Hnin).
    revert Hnin'.
    induction Hsem as [| | | |?????? IH|??????? n' ? Hfind ????? Heqs WF IH]
        using msem_node_mult
      with (P_equation := fun bk H M M' eq =>
                            ~Is_node_in_eq n.(n_name) eq ->
                            msem_equation (n :: G) bk H M M' eq)
           (P_reset := fun f r xss M M' yss =>
                         Forall (fun n' : node => n_name n <> n_name n') G ->
                         msem_reset (n :: G) f r xss M M' yss); eauto.
    - intro. constructor; intro k; destruct (IH k) as (?&?&?&?&?&?); eauto 6.
    - intro HH; clear HH.
      assert (n.(n_name) <> f) as Hnf.
      { intro Hnf.
        rewrite Hnf in *.
        pose proof (find_node_name _ _ _ Hfind).
        apply find_node_split in Hfind.
        destruct Hfind as [bG [aG Hge]].
        rewrite Hge in Hnin.
        apply Forall_app in Hnin.
        destruct Hnin as [H' Hfg]; clear H'.
        inversion_clear Hfg.
        match goal with H:f<>_ |- False => now apply H end.
      }
      apply find_node_other with (2:=Hfind) in Hnf.
      econstructor; eauto.
      + assert (forall g, Is_node_in g n'.(n_eqs) -> Exists (fun nd=> g = nd.(n_name)) G)
          as Hniex by (intros g Hini;
                       apply find_node_find_again with (1:=Hord) (2:=Hfind) in Hini;
                       exact Hini).
        assert (Forall (fun eq => forall g,
                            Is_node_in_eq g eq -> Exists (fun nd=> g = nd.(n_name)) G)
                       n'.(n_eqs)) as HH.
        {
          clear Heqs IH WF.
          induction n'.(n_eqs) as [|eq eqs]; [now constructor|].
          constructor.
          - intros g Hini.
            apply Hniex.
            constructor 1; apply Hini.
          - apply IHeqs.
            intros g Hini; apply Hniex.
            constructor 2; apply Hini.
        }
        apply Forall_Forall with (1:=HH) in IH.
        apply Forall_impl with (2:=IH).
        intros eq (Hsem & IH1).
        apply IH1.
        intro Hini.
        apply Hsem in Hini.
        apply Forall_Exists with (1:=Hnin) in Hini.
        apply Exists_exists in Hini.
        destruct Hini as [nd' [Hin [Hneq Heq]]].
        intuition.
      (* + intro; eapply well_formed_memory_cons2; eauto. *)
      (*   eapply msem_node_valid_app; eauto. *)
  Qed.

  Lemma msem_reset_cons2:
    forall n G f r xs M M' ys,
      Ordered_nodes G ->
      msem_reset G f r xs M M' ys ->
      Forall (fun n' => n_name n <> n_name n') G ->
      msem_reset (n :: G) f r xs M M' ys.
  Proof.
    intros ** Sem ?.
    inversion_clear Sem as [?????? SemN].
    constructor.
    intro k; destruct (SemN k) as (?&?&?&?); eauto using msem_node_cons2.
  Qed.

  Lemma msem_equation_cons2:
    forall G bk H M M' eqs n,
      Ordered_nodes (n :: G) ->
      Forall (msem_equation G bk H M M') eqs ->
      ~Is_node_in n.(n_name) eqs ->
      Forall (msem_equation (n :: G) bk H M M') eqs.
  Proof.
    Hint Constructors msem_equation.
    intros ** Hord Hsem Hnini.
    induction eqs as [|eq eqs IH]; [now constructor|].
    apply Forall_cons2 in Hsem.
    destruct Hsem as [Heq Heqs].
    apply not_Is_node_in_cons in Hnini.
    destruct Hnini as [Hnini Hninis].
    apply IH with (2:=Hninis) in Heqs.
    constructor; [|now apply Heqs].
    inv Hord.
    destruct Heq; eauto.
    - eauto using msem_node_cons2.
    - eauto using msem_reset_cons2.
  Qed.

  Lemma find_node_msem_node:
    forall G f,
      msem_nodes G ->
      find_node f G <> None ->
      exists xs M M' ys,
        msem_node G f xs M M' ys.
  Proof.
    intros G f Hnds Hfind.
    apply find_node_Exists in Hfind.
    apply Exists_exists in Hfind.
    destruct Hfind as [nd [Hin Hf]].
    unfold msem_nodes in Hnds.
    rewrite Forall_forall in Hnds.
    apply Hnds in Hin.
    destruct Hin as [xs [M [M' [ys Hmsem]]]].
    exists xs, M, M', ys.
    rewrite Hf in *.
    exact Hmsem.
  Qed.

  (* TODO: Tidy this up... *)
  Lemma Forall_msem_equation_global_tl:
    forall n G bk H M M' eqs,
      Ordered_nodes (n :: G) ->
      ~ Is_node_in n.(n_name) eqs ->
      Forall (msem_equation (n :: G) bk H M M') eqs ->
      Forall (msem_equation G bk H M M') eqs.
  Proof.
    intros ??????? Hord.
    induction eqs as [|eq eqs IH]; trivial; [].
    intros Hnini Hmsem.
    apply Forall_cons2 in Hmsem; destruct Hmsem as [Hseq Hseqs].
    apply IH in Hseqs.
    - apply Forall_cons; trivial.
      apply not_Is_node_in_cons in Hnini.
      destruct Hnini.
      inv Hseq; eauto;
        assert (n.(n_name) <> f)
        by (intro HH; apply H0; rewrite HH; constructor).
      + eauto using msem_node_cons.
      + eauto using msem_reset_cons.
    - apply not_Is_node_in_cons in Hnini.
      now destruct Hnini.
  Qed.

  (** *** Memory management *)

  Definition add_val_n (y: ident) (ms: stream val) (M: memories): memories :=
    fun n => add_val y (ms n) (M n).

  Lemma mfby_add_val_n:
    forall x v0 ls M M' xs y ms ms',
      x <> y ->
      mfby x v0 ls M M' xs ->
      mfby x v0 ls (add_val_n y ms M) (add_val_n y ms' M') xs.
  Proof.
    unfold add_val_n.
    intros ** Fby; destruct Fby as (?&?& Spec).
    split; [|split].
    - rewrite find_val_gso; auto.
    - intro; rewrite 2 find_val_gso; auto.
    - intro n; rewrite 2 find_val_gso; auto; apply Spec.
  Qed.

  Definition add_inst_n (y: ident) (M' M: memories): memories :=
    fun n => add_inst y (M' n) (M n).

  Lemma mfby_add_inst_n:
    forall x v0 ls M M' xs y My My',
      mfby x v0 ls M M' xs ->
      mfby x v0 ls (add_inst_n y My M) (add_inst_n y My' M') xs.
  Proof.
    inversion 1; econstructor; eauto.
  Qed.

  Hint Resolve mfby_add_val_n mfby_add_inst_n.

  Lemma msem_equation_madd_val:
    forall G bk H M M' x ms ms' eqs,
      ~Is_defined_in_eqs x eqs ->
      Forall (msem_equation G bk H M M') eqs ->
      Forall (msem_equation G bk H (add_val_n x ms M) (add_val_n x ms' M')) eqs.
  Proof.
    Hint Constructors msem_equation.
    intros ** Hnd Hsem.
    induction eqs as [|eq eqs IH]; [now constructor|].
    apply not_Is_defined_in_cons in Hnd.
    destruct Hnd as [Hnd Hnds].
    apply Forall_cons2 in Hsem.
    destruct Hsem as [Hsem Hsems].
    constructor; [|now apply IH with (1:=Hnds) (2:=Hsems)].
    destruct Hsem; eauto.
    apply not_Is_defined_in_eq_EqFby in Hnd.
    eapply SEqFby; eauto.
  Qed.

  Lemma msem_equation_madd_inst:
    forall G bk H M M' Mx Mx' x eqs,
      ~Is_defined_in_eqs x eqs ->
      Forall (msem_equation G bk H M M') eqs ->
      Forall (msem_equation G bk H (add_inst_n x Mx M) (add_inst_n x Mx' M')) eqs.
  Proof.
    Hint Constructors msem_equation.
    intros * Hnd Hsem.
    induction eqs as [|eq eqs IH]; [now constructor|].
    apply not_Is_defined_in_cons in Hnd.
    destruct Hnd as [Hnd Hnds].
    apply Forall_cons2 in Hsem.
    destruct Hsem as [Hsem Hsems].
    constructor; [|now apply IH with (1:=Hnds) (2:=Hsems)].
    destruct Hsem as [|???? x' ???????? Hsome
                         |???? x' ???????????? Hsome|];
      eauto;
      assert (sub_inst_n x' (add_inst_n x Mx M) Mx0)
        by (apply not_Is_defined_in_eq_EqApp in Hnd;
            unfold sub_inst_n, sub_inst, add_inst_n in *; intro;
            rewrite find_inst_gso; auto; intro; subst x; destruct xs;
            inv Hsome; apply Hnd; now constructor);
      assert (sub_inst_n x' (add_inst_n x Mx' M') Mx'0)
        by (apply not_Is_defined_in_eq_EqApp in Hnd;
            unfold sub_inst_n, sub_inst, add_inst_n in *; intro;
            rewrite find_inst_gso; auto; intro; subst x; destruct xs;
            inv Hsome; apply Hnd; now constructor);
      eauto.
  Qed.

  (* Inductive memory_eq {A} : memory A -> memory A -> Prop := *)
  (*   memory_eq_intro: *)
  (*     forall M M', *)
  (*       (forall x, find_val x M = find_val x M') -> *)
  (*       (forall x Mx, sub_inst x M Mx -> (exists Mx', sub_inst x M' Mx' /\ memory_eq Mx Mx')) -> *)
  (*       (forall x Mx', sub_inst x M' Mx' -> (exists Mx, sub_inst x M Mx /\ memory_eq Mx Mx')) -> *)
  (*       memory_eq M M'. *)

  (* Lemma well_formed_memory_eqdef: *)
  (*   forall M x ck e eqs, *)
  (*     well_formed_memory M (EqDef x ck e :: eqs) -> *)
  (*     well_formed_memory M eqs. *)
  (* Proof. *)
  (*   inversion_clear 1; auto using well_formed_memory. *)
  (* Qed. *)

  (* Lemma foo: *)
  (*   forall G n0 f xss M M' yss, *)
  (*     msem_node G f xss M M' yss -> *)
  (*     (forall n, n < n0 -> absent_list (xss n)) -> *)
  (*     forall n, n <= n0 -> memory_eq (M n) (M 0). *)
  (* Proof. *)
  (*   inversion_clear 1 as [??????????????? Heqs WF]. *)
  (*   induction Heqs as [|eq ? Heq]; intros Abs n' Spec. *)
  (*   - pose proof WF as WF0. *)
  (*     specialize (WF n'); *)
  (*       specialize (WF0 0). *)
  (*     inversion_clear WF as [?? Insts Vals]; *)
  (*       inversion_clear WF0 as [?? Insts0 Vals0]; simpl in *. *)
  (*     constructor. *)
  (*     + intro; specialize (Vals x); specialize (Vals0 x). *)
  (*       destruct (find_val x (M n')), (find_val x (M 0)); auto. *)
  (*       * exfalso; eapply Vals; eauto. *)
  (*       * exfalso; apply Vals; eauto. *)
  (*       * exfalso; apply Vals0; eauto. *)
  (*     + intros; exfalso; eapply Insts; eauto. *)
  (*     + intros; exfalso; eapply Insts0; eauto. *)
  (*   - destruct eq. *)
  (*     + apply IHHeqs; auto. *)
  (*       intro k; eapply well_formed_memory_eqdef; eauto. *)
  (*     + inversion_clear Heq as [|????????????? Hd| |]. *)
  (*       * specialize (WF n'). *)
  (*         inversion_clear WF as [?? Insts]. *)
  (*         specialize (Insts x). *)
  (*         destruct Insts as [Insts]. *)

  (*         ; unfold gather_insts, concatMap in *. *)
  (*         simpl in Insts. *)
  (*         destruct i; simpl in *; try discriminate; inv Hd. *)
  (*         specialize (Insts i). *)
  (*         destruct Insts as [Insts Insts']. *)
  (*         destruct Insts; eauto. *)
  (*     + *)


  (*       * *)
  (*       assert (not (not (M n' = @empty_memory val))). *)
  (*     intro. *)
  (*     eapply H. *)
  (*     SearchAbout (Env.empty). *)
  (*   induction G as [|node]. *)
  (*   inversion 2; *)
  (*     match goal with Hf: find_node _ [] = _ |- _ => inversion Hf end. *)
  (*   intros ** Hwdef Hsem Abs n Spec. *)
  (*   assert (Hsem' := Hsem). *)
  (*   inversion_clear Hsem' as [????????? Hfind ????? Heqs]. *)
  (*   pose proof (Welldef_global_Ordered_nodes _ Hwdef) as Hord. *)
  (*   pose proof (Welldef_global_cons _ _ Hwdef) as HwdefG. *)
  (*   pose proof (find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini. *)
  (*   simpl in Hfind. *)
  (*   destruct (ident_eqb node.(n_name) f) eqn:Hnf. *)
  (*   - assert (Hord':=Hord). *)
  (*     inversion_clear Hord as [|? ? Hord'' Hnneqs Hnn]. *)
  (*     injection Hfind; intro HR; rewrite HR in *; clear HR; simpl in *. *)
  (*     eapply Forall_msem_equation_global_tl in Heqs; eauto. *)
  (*     (* assert (forall f xs ys, *) *)
  (*     (*            sem_node G f xs ys -> *) *)
  (*     (*            exists M M', msem_node G f xs M M' ys) as IHG' *) *)
  (*     (*     by auto. *) *)
  (*     (* assert (forall f r xs ys, *) *)
  (*     (*            sem_reset G f r xs ys -> *) *)
  (*     (*            exists M M', msem_reset G f r xs M M' ys) as IHG'' *) *)
  (*     (*     by (intros; now apply sem_msem_reset). *) *)

  (*     inversion_clear Hwdef as [|??? neqs]. *)
  (*     simpl in neqs; unfold neqs in *. *)
  (*     assert (exists M1 M1', Forall (msem_equation G bk H M1 M1') n.(n_eqs)) *)
  (*       as (M1 & M1' & Hmsem) by now eapply sem_msem_eqs; eauto. *)
  (*     exists M1, M1'. *)
  (*     econstructor; eauto. *)
  (*     + simpl; now rewrite Hnf. *)
  (*     + eapply msem_equation_cons2; eauto. *)
  (*     + admit. *)
  (*   - apply ident_eqb_neq in Hnf. *)
  (*     apply sem_node_cons with (1:=Hord) (3:=Hnf) in Hsem. *)
  (*     inv Hord. *)
  (*     eapply IHG in Hsem as (M & M' &?); eauto. *)
  (*     exists M, M'. *)
  (*     now eapply msem_node_cons2; eauto. *)
  (*   inversion_clear 1 as [???????????????? WF Heqs]. *)
  (*   intros ** Abs n' Spec. *)
  (*   specialize (WF n'). *)
  (*   inv WF. *)
  (*   - specialize (WF n'). inversion WF. *)

  (* XXX: I believe that this comment is outdated ([no_dup_defs] is long gone)

   - The no_dup_defs hypothesis is essential for the EqApp case.

     If the set of equations contains two EqApp's to the same variable:
        eq::eqs = [ EqApp x f lae; ...; EqApp x g lae' ]

     Then it is possible to have a coherent H, namely if
        f(lae) = g(lae')

     But nothing forces the 'memory streams' (internal memories) of
     f(lae) and g(lae') to be the same. This is problematic since they are
     both 'stored' at M x...

   - The no_dup_defs hypothesis is not essential for the EqFby case.

     If the set of equations contains two EqFby's to for the same variable:
        eq::eqs = [ EqFby x v0 lae; ...; EqFby x v0' lae'; ... ]

     then the 'memory streams' associated with each, ms and ms', must be
     identical since if (Forall (sem_equation G H) (eq::eqs)) exists then
     then the H forces the coherence between 'both' x's, and necessarily also
     between v0 and v0', and lae and lae'.

     That said, proving this result is harder than just assuming something
     that should be true anyway: that there are no duplicate definitions in
     eqs.

   Note that the no_dup_defs hypothesis requires a stronger definition of
   either Is_well_sch or Welldef_global.
   *)

  (* Lemma well_formed_memory_add_inst: *)
  (*   forall G M g x Mx n, *)
  (*     find_node g G = Some n -> *)
  (*     not (InMembers x (gather_insts n.(n_eqs))) -> *)
  (*     well_formed_memory G M g -> *)
  (*     well_formed_memory G (add_inst x Mx M) g. *)
  (* Proof. *)
  (*   (* induction M as [? IH] using memory_ind'. *) *)
  (*   intros ** Find Notin WF. *)
  (*   inversion_clear WF as [??? Find' Insts Insts']; *)
  (*     rewrite Find' in Find; inv Find. *)
  (*   econstructor; eauto. *)
  (*   - intros y ** Sub. *)
  (*     unfold sub_inst in Sub. *)
  (*     destruct (ident_eq_dec x y). *)
  (*     + subst; rewrite find_inst_gss in Sub; inv Sub. *)

  (*       admit. *)
  (*     + rewrite find_inst_gso in Sub; auto. *)
  (*   - intros y ** Hin. *)
  (*     unfold sub_inst. *)
  (*     destruct (ident_eq_dec x y). *)
  (*     + subst; rewrite find_inst_gss. *)
  (*       exfalso; apply Notin. *)
  (*       eapply In_InMembers; eauto. *)
  (*     + rewrite find_inst_gso; auto. *)
  (*       now apply Insts'. *)
  (* Qed. *)



  (** ** Fundamental theorem *)

  (**

We show that the standard semantics implies the existence of a
dataflow memory for which the non-standard semantics holds true.

   *)

  Definition stutter (v0: val) (xs: stream value) (n: nat) : val := (* TODO: inline in proof *)
    match xs n with
    | present v => v
    | absent => hold v0 xs n
    end.

  (* Lemma stutter_hold_absent: *)
  (*   forall n v0 xs, *)
  (*     xs n = absent -> *)
  (*     stutter v0 xs n = hold v0 xs n. *)
  (* Proof. *)
  (*   induction n; simpl. ; intros ** ->; auto. *)
  (*   destruct (xs n) eqn: E'; auto. *)
  (*   destruct n; simpl; rewrite E'; auto. *)
  (* Qed. *)

  (* Lemma stutter_present: *)
  (*   forall n v0 xs c, *)
  (*     xs n = present c -> *)
  (*     stutter v0 xs n = c. *)
  (* Proof. *)
  (*   destruct n; simpl; intros ** ->; auto. *)
  (* Qed. *)

  Fact hd_error_Some_In:
    forall {A} (xs: list A) x,
      hd_error xs = Some x ->
      In x xs.
  Proof.
    induction xs; simpl; try discriminate.
    inversion 1; auto.
  Qed.

  Fact hd_error_Some_hd:
    forall {A} d (xs: list A) x,
      hd_error xs = Some x ->
      hd d xs = x.
  Proof.
    destruct xs; simpl; intros; try discriminate.
    now inv H.
  Qed.

  (* Lemma memory_closed_n_Def: *)
  (*   forall M eqs x ck ce, *)
  (*     memory_closed_n M eqs -> *)
  (*     memory_closed_n M (EqDef x ck ce :: eqs). *)
  (* Proof. *)
  (*   intros ** WF n; specialize (WF n); destruct WF; *)
  (*     split; auto. *)
  (* Qed. *)

  Lemma memory_closed_n_App:
    forall M eqs i Mx xs ck f es r,
      memory_closed_n M eqs ->
      hd_error xs = Some i ->
      memory_closed_n (add_inst_n i Mx M) (EqApp xs ck f es r :: eqs).
  Proof.
    intros ** WF Hd n; specialize (WF n); destruct WF as (Insts &?).
    split; auto.
    intro y; intros ** Hin.
    unfold sub_inst, add_inst_n in Hin; apply not_None_is_Some in Hin as (?& Find).
    destruct (ident_eq_dec y i).
    - subst.
      unfold gather_insts, concatMap; simpl.
      destruct xs; simpl in *; inv Hd; left; auto.
    - rewrite find_inst_gso in Find; auto.
      unfold gather_insts, concatMap; simpl.
      apply InMembers_app; right; auto.
      apply Insts; eauto.
      apply not_None_is_Some; eauto.
  Qed.

  Lemma memory_closed_n_Fby:
    forall M eqs x ck v0 e vs,
      memory_closed_n M eqs ->
      memory_closed_n (add_val_n x vs M) (EqFby x ck v0 e :: eqs).
  Proof.
    intros ** WF n; specialize (WF n); destruct WF as (?& Vals).
    split; auto.
    intro y; intros ** Hin.
    unfold add_val_n in Hin; apply not_None_is_Some in Hin as (?& Find).
    destruct (ident_eq_dec y x).
    - subst; simpl; auto.
    - rewrite find_val_gso in Find; auto.
      unfold gather_mem, concatMap; simpl.
      right; apply Vals; eauto.
      apply not_None_is_Some; eauto.
  Qed.

  Lemma sem_msem_eq:
    forall G bk H eqs M M' eq mems argIn,
      (forall f xs ys,
          sem_node G f xs ys ->
          exists M M', msem_node G f xs M M' ys) ->
      (forall f r xs ys,
          sem_reset G f r xs ys ->
          exists M M', msem_reset G f r xs M M' ys) ->
      sem_equation G bk H eq ->
      Is_well_sch mems argIn (eq :: eqs) -> (* TODO *)
      Forall (msem_equation G bk H M M') eqs ->
      memory_closed_n M eqs ->
      exists M1 M1', Forall (msem_equation G bk H M1 M1') (eq :: eqs)
                /\ memory_closed_n M1 (eq :: eqs).
  Proof.
    intros ** IH IH' Heq Hwsch Hmeqs WF.
    inversion Heq as [|???????? Hls Hxs Hsem
                         |???????????? Hls Hxs Hy Hr Hsem
                         |???????? Hle Hvar];
      match goal with H:_=eq |- _ => rewrite <-H in * end.

    - exists M, M'.
      econstructor; eauto.

    - apply IH in Hsem as (Mx & Mx' & Hmsem).
      exists (add_inst_n (hd Ids.default x) Mx M), (add_inst_n (hd Ids.default x) Mx' M').

      assert (exists i, hd_error x = Some i) as [i Hsome].
      { assert (Hlen: 0 < length x).
        { assert (length x = length (xs 0))
            by (specialize (Hxs 0); simpl in Hxs; eapply Forall2_length; eauto).

          assert (exists n, length (map fst n.(n_out)) = length (xs 0)
                       /\ 0 < length n.(n_out)) as (n & ? & ?).
          { inv Hmsem.
            exists n; split; auto.
            - eapply Forall2_length; eauto.
              specialize (H9 0); eauto.
            - exact n.(n_outgt0).
          }
          assert (length (map fst n.(n_out)) = length n.(n_out))
            by apply map_length.
          intuition.
        }
        now apply length_hd_error.
      }
      erewrite hd_error_Some_hd; eauto; split.
      + constructor.
        * econstructor; eauto;
            unfold sub_inst, add_inst_n; intro; now apply find_inst_gss.
          * inversion_clear Hwsch.
            assert (Is_defined_in_eq i (EqApp x ck f arg None))
              by (constructor; apply hd_error_Some_In; auto).
            apply msem_equation_madd_inst; auto.
      + apply memory_closed_n_App; auto.

    - pose proof Hsem as Hsem'.
      apply IH' in Hsem as (Mx & Mx' & Hmsem).
      exists (add_inst_n (hd Ids.default x) Mx M), (add_inst_n (hd Ids.default x) Mx' M').

      assert (exists i, hd_error x = Some i) as [i Hsome].
      { assert (Hlen: 0 < length x).
        { assert (length x = length (xs 0))
            by (specialize (Hxs 0); simpl in Hxs; eapply Forall2_length; eauto).

          assert (exists n, length (map fst n.(n_out)) = length (xs 0)
                       /\ 0 < length n.(n_out)) as (n & ? & ?).
          { inversion_clear Hmsem as [?????? Hmsem'].
            destruct (Hmsem' 0) as (?&?& Hmsem'' & ?);
              inversion_clear Hmsem'' as [??????????? Hout].
            exists n; split; auto.
            - unfold sem_vars, lift in Hout; specialize (Hout 0).
              apply Forall2_length in Hout; rewrite Hout.
              rewrite mask_length; auto.
              inversion_clear Hsem' as [???? Hsem].
              eapply wf_streams_mask.
              intro n'; specialize (Hsem n');
                apply sem_node_wf in Hsem as (? & ?); eauto.
            - exact n.(n_outgt0).
          }
          assert (length (map fst n.(n_out)) = length n.(n_out))
            by apply map_length.
          intuition.
        }
        now apply length_hd_error.
      }
      erewrite hd_error_Some_hd; eauto; split.
      + constructor.
        * econstructor; eauto;
            unfold sub_inst, add_inst_n; intro; now apply find_inst_gss.
        * inversion_clear Hwsch.
          assert (Is_defined_in_eq i (EqApp x ck f arg (Some (y, ck_r))))
            by (constructor; apply hd_error_Some_In; auto).
          apply msem_equation_madd_inst; auto.
      + apply memory_closed_n_App; auto.

    - exists (add_val_n x (hold (sem_const c0) ls) M), (add_val_n x (stutter (sem_const c0) ls) M').
      split.
      + constructor.
        * unfold add_val_n.
          econstructor; eauto; split; [|split];
            subst; unfold fby, stutter; simpl;
              intros; repeat rewrite find_val_gss; auto.
          destruct (ls n); auto.
        * inversion_clear Hwsch.
          apply msem_equation_madd_val; eauto.
      + now apply memory_closed_n_Fby.
  Qed.

  (* Lemma msem_equation_same_initial_state_cons: *)
  (*     forall G eq eqs bk1 H1 M1 M1' bk2 H2 M2 M2' Me1 Me1' Me2 Me2' mems argIn, *)
  (*       (forall f xss1 M1 M1' yss1 xss2 M2 M2' yss2, *)
  (*           msem_node G f xss1 M1 M1' yss1 -> *)
  (*           msem_node G f xss2 M2 M2' yss2 -> *)
  (*           exists M1 M2, *)
  (*             msem_node G f xss1 M1 M1' yss1  *)
  (*             /\ msem_node G f xss2 M2 M2' yss2  *)
  (*             /\ M1 0 = M2 0) -> *)
  (*       M1 0 = M2 0 -> *)
  (*       msem_equation G bk1 H1 Me1 Me1' eq -> *)
  (*       msem_equation G bk2 H2 Me2 Me2' eq -> *)
  (*       Is_well_sch mems argIn (eq :: eqs) -> *)
  (*       Forall (msem_equation G bk1 H1 M1 M1') eqs -> *)
  (*       Forall (msem_equation G bk2 H2 M2 M2') eqs -> *)
  (*       exists M1 M2, *)
  (*         Forall (msem_equation G bk1 H1 M1 M1') (eq :: eqs) *)
  (*         /\ Forall (msem_equation G bk2 H2 M2 M2') (eq :: eqs) *)
  (*         /\ M1 0 = M2 0. *)
  (*   Proof. *)
  (*     intros ** IHNode Spec Heq1 Heq2 Hwsch Hmeqs1 Hmeqs2. *)
  (*     inversion Heq1 as [| *)
  (*                       ????????????? Hd1 ???? Node1| *)
  (*                       ????????????????? Hd1 ?????? Reset1| *)
  (*                       ?????????? Exps1 ? Mfby1];  *)
  (*       inversion Heq2 as [| *)
  (*                          ????????????? Hd2 ???? Node2| *)
  (*                          ????????????????? Hd2 ?????? Reset2| *)
  (*                          ?????????? Exps2 ? Mfby2]; subst; try discriminate; *)
  (*         match goal with *)
  (*         | H: _ = _ |- _ => inv H *)
  (*         end;       *)
  (*         inv Hwsch. *)
  (*     - do 2 econstructor; split; eauto; split; eauto.  *)
  (*     - rewrite <-Hd1 in Hd2; inv Hd2. *)
  (*       edestruct IHNode as (Mx1 & Mx2 & ? & ? & ?); eauto.  *)
  (*       exists (add_inst_n x Mx1 M1), (add_inst_n x Mx2 M2); split; [|split]. *)
  (*       + constructor; auto. *)
  (*         * econstructor; eauto; *)
  (*             unfold sub_inst_n, sub_inst, add_inst_n. *)
  (*           intro. rewrite find_inst_gss. ; *)
  (*             setoid_rewrite find_inst_gss; auto. *)
  (*         * assert (Is_defined_in_eq x (EqApp xs ck f arg None)) *)
  (*             by (constructor; apply hd_error_Some_In; auto). *)
  (*           apply msem_equation_madd_inst; auto. *)
  (*       + constructor; auto. *)
  (*         * econstructor; eauto; *)
  (*             unfold sub_inst_n, sub_inst, add_inst_n; *)
  (*             setoid_rewrite find_inst_gss; auto. *)
  (*         * assert (Is_defined_in_eq x (EqApp xs ck f arg None)) *)
  (*             by (constructor; apply hd_error_Some_In; auto). *)
  (*           apply msem_equation_madd_inst; auto. *)
  (*       + unfold add_inst_n. *)
  (*         eapply IHNode in Node1; eauto. *)
  (*         now rewrite Node1, Spec.  *)
  (*     - rewrite <-Hd1 in Hd2; inv Hd2. *)
  (*       exists (add_inst_n x Mx M1), (add_inst_n x Mx' M1'), (add_inst_n x Mx0 M2), (add_inst_n x Mx'0 M2'); split; [|split]. *)
  (*       + constructor; auto. *)
  (*         * econstructor; eauto; *)
  (*             unfold sub_inst_n, sub_inst, add_inst_n; *)
  (*             setoid_rewrite find_inst_gss; auto. *)
  (*         * assert (Is_defined_in_eq x (EqApp xs ck f arg (Some (r, ck_r)))) *)
  (*             by (constructor; apply hd_error_Some_In; auto). *)
  (*           apply msem_equation_madd_inst; auto. *)
  (*       + constructor; auto. *)
  (*         * econstructor; eauto; *)
  (*             unfold sub_inst_n, sub_inst, add_inst_n; *)
  (*             setoid_rewrite find_inst_gss; auto. *)
  (*         * assert (Is_defined_in_eq x (EqApp xs ck f arg (Some (r, ck_r)))) *)
  (*             by (constructor; apply hd_error_Some_In; auto). *)
  (*           apply msem_equation_madd_inst; auto. *)
  (*       + unfold add_inst_n. *)
  (*         inversion_clear Reset1 as [?????? Nodes1]; *)
  (*           inversion_clear Reset2 as [?????? Nodes2]. *)
  (*         specialize (Nodes1 (count rs 0)); destruct Nodes1 as (Mk1 & Mk1' & Node1 & Mmask1 & Mmask1'); *)
  (*           specialize (Nodes2 (count rs0 0)); destruct Nodes2 as (Mk2 & Mk2' & Node2 & Mmask2 & Mmask2'). *)
  (*         eapply IHNode in Node1; eauto. *)
  (*         specialize (Mmask1 0); specialize (Mmask2 0). *)
  (*         rewrite <-Mmask1, <-Mmask2, Node1, Spec; auto.  *)
  (*     - exists (fun n => add_val x (match find_val x (Me1 n) with *)
  (*                           | Some v => v *)
  (*                           | None => false_val *)
  (*                           end) (M1 n)), *)
  (*       (fun n => add_val x (match find_val x (Me1' n) with *)
  (*                         | Some v => v *)
  (*                         | None => false_val *)
  (*                         end) (M1' n)), *)
  (*       (fun n => add_val x (match find_val x (Me2 n) with *)
  (*                         | Some v => v *)
  (*                         | None => false_val *)
  (*                         end) (M2 n)), *)
  (*       (fun n => add_val x (match find_val x (Me2' n) with *)
  (*                         | Some v => v *)
  (*                         | None => false_val *)
  (*                         end) (M2' n)). *)
  (*       inversion_clear Mfby1 as [?????? Init1 Spec1']; *)
  (*         inversion_clear Mfby2 as [?????? Init2 Spec2']. *)
  (*       split; [|split]. *)
  (*       + constructor; auto. *)
  (*         *{ do 2 (econstructor; eauto). *)
  (*            - rewrite Init1, find_val_gss; auto. *)
  (*            - intro n; specialize (Spec1' n); destruct (find_val x (Me1 n)) eqn: E; try contradiction. *)
  (*              repeat rewrite find_val_gss; auto. *)
  (*              destruct (ls n) eqn: E'; auto. *)
  (*              + destruct Spec1' as (-> & -> & ?); intuition. *)
  (*              + destruct Spec1' as (-> & -> & ?); intuition. *)
  (*          } *)
  (*         * apply msem_equation_madd_val; eauto. *)
  (*       + constructor; auto. *)
  (*         *{ do 2 (econstructor; eauto). *)
  (*            - rewrite Init2, find_val_gss; auto. *)
  (*            - intro n; specialize (Spec2' n); destruct (find_val x (Me2 n)) eqn: E; try contradiction. *)
  (*              repeat rewrite find_val_gss; auto. *)
  (*              destruct (ls0 n) eqn: E'; auto. *)
  (*              + destruct Spec2' as (-> & -> & ?); intuition. *)
  (*              + destruct Spec2' as (-> & -> & ?); intuition. *)
  (*          } *)
  (*         * apply msem_equation_madd_val; eauto. *)
  (*       + now rewrite Init1, Init2, Spec.  *)
  (* Qed. *)

  (*   Corollary msem_equation_same_initial_state: *)
  (*     forall G eqs bk1 H1 M1 M1' bk2 H2 M2 M2' mems argIn, *)
  (*       (forall f xss1 M1 M1' yss1 xss2 M2 M2' yss2, *)
  (*           msem_node G f xss1 M1 M1' yss1 -> *)
  (*           msem_node G f xss2 M2 M2' yss2 -> *)
  (*           M1 0 = M2 0) -> *)
  (*       Is_well_sch mems argIn eqs -> *)
  (*       Forall (msem_equation G bk1 H1 M1 M1') eqs -> *)
  (*       Forall (msem_equation G bk2 H2 M2 M2') eqs -> *)
  (*       exists M1 M1' M2 M2', *)
  (*         Forall (msem_equation G bk1 H1 M1 M1') eqs *)
  (*         /\ Forall (msem_equation G bk1 H1 M2 M2') eqs *)
  (*         /\ M1 0 = M2 0. *)
  (* Proof. *)
  (*   intros ** IH Hwsch Heqs1 Heqs2. *)
  (*   induction eqs as [|eq eqs IHeqs]; [do 4 exists (fun n => empty_memory _); constructor; auto|]. *)
  (*   apply Forall_cons2 in Heqs1 as [Heq1 Heqs1]; *)
  (*     apply Forall_cons2 in Heqs2 as [Heq2 Heqs2]. *)
  (*   eapply IHeqs with (1:=Is_well_sch_cons _ _ _ _ Hwsch) *)
  (*     in Heqs1 *)
  (*     as (?&?&?&?&?&?&?); eauto. *)
  (*   eapply msem_equation_same_initial_state_cons; eauto. *)
  (* Qed. *)

  (* Lemma same_initial_memory: *)
  (*   forall G f xss1 xss2 M1 M2 M1' M2' yss1 yss2, *)
  (*     Welldef_global G -> *)
  (*     msem_node G f xss1 M1 M1' yss1 -> *)
  (*     msem_node G f xss2 M2 M2' yss2 -> *)
  (*     exists M1 M1' M2 M2', *)
  (*       msem_node G f xss1 M1 M1' yss1  *)
  (*       /\ msem_node G f xss2 M2 M2' yss2  *)
  (*       /\ M1 0 = M2 0. *)
  (* Proof. *)
  (*   induction G as [|node]. *)
  (*   inversion 2; *)
  (*     match goal with Hf: find_node _ [] = _ |- _ => inversion Hf end. *)
  (*   intros ** Hwdef Hsem1 Hsem2. *)
  (*   (* assert (Hsem' := Hsem). *) *)
  (*   inversion_clear Hsem1 as [????????? Hfind1 ????? Heqs1]; *)
  (*     inversion_clear Hsem2 as [????????? Hfind2 ????? Heqs2]. *)
  (*   rewrite Hfind1 in Hfind2; inv Hfind2.  *)
  (*   pose proof (Welldef_global_Ordered_nodes _ Hwdef) as Hord. *)
  (*   pose proof (Welldef_global_cons _ _ Hwdef) as HwdefG. *)
  (*   pose proof (find_node_not_Is_node_in _ _ _ Hord Hfind1) as Hnini. *)
  (*   simpl in Hfind1. *)
  (*   destruct (ident_eqb node.(n_name) f) eqn:Hnf. *)
  (*   - assert (Hord':=Hord). *)
  (*     inversion_clear Hord as [|? ? Hord'' Hnneqs Hnn]. *)
  (*     inv Hfind1. *)
  (*     (* injection Hfind; intro HR; rewrite HR in *; clear HR; simpl in *. *) *)
  (*     eapply Forall_msem_equation_global_tl in Heqs1; eauto. *)
  (*     eapply Forall_msem_equation_global_tl in Heqs2; eauto. *)
  (*     (* assert (forall f xs ys, *) *)
  (*     (*            sem_node G f xs ys -> *) *)
  (*     (*            exists M M', msem_node G f xs M M' ys) as IHG' *) *)
  (*     (*     by auto. *) *)
  (*     (* assert (forall f r xs ys, *) *)
  (*     (*            sem_reset G f r xs ys -> *) *)
  (*     (*            exists M M', msem_reset G f r xs M M' ys) as IHG'' *) *)
  (*     (*     by (intros; now apply sem_msem_reset). *) *)

  (*     (* inversion_clear Hwdef as [|??? neqs]. *) *)
  (*     (* simpl in neqs; unfold neqs in *. *) *)
  (*     edestruct msem_equation_same_initial_state; eauto. *)
  (*     + intros; apply  *)
  (*     assert (exists M1 M1', Forall (msem_equation G bk H M1 M1') n.(n_eqs)) *)
  (*       as (M1 & M1' & Hmsem) by now eapply sem_msem_eqs; eauto. *)
  (*     exists M1, M1'. *)
  (*     econstructor; eauto. *)
  (*     + simpl; now rewrite Hnf. *)
  (*     + eapply msem_equation_cons2; eauto. *)
  (*   - apply ident_eqb_neq in Hnf. *)
  (*     apply sem_node_cons with (1:=Hord) (3:=Hnf) in Hsem. *)
  (*     inv Hord. *)
  (*     eapply IHG in Hsem as (M & M' &?); eauto. *)
  (*     exists M, M'. *)
  (*     now eapply msem_node_cons2; eauto. *)


  (*   inversion_clear 1 as [????????? Find1 ????? Heqs1]; *)
  (*     inversion_clear 1 as [????????? Find2 ????? Heqs2]. *)
  (*   rewrite Find2 in Find1; inv Find1. *)
  (*   pose proof (n_eqsgt0 n). *)
  (*   induction (n_eqs n); simpl in *; try omega. *)
  (*     inversion_clear 1 as [Find2]. *)


  Lemma mfby_absent_until:
    forall n0 x v0 ls M M' xs,
      mfby x v0 ls M M' xs ->
      (forall n, n < n0 -> ls n = absent) ->
      forall n, n <= n0 -> find_val x (M n) = Some v0.
  Proof.
    intros ** Mfby Abs n E; induction n;
      destruct Mfby as (Init & Spec & Spec'); auto.
    rewrite Spec.
    specialize (Spec' n).
    destruct (find_val x (M n)); try contradiction.
    rewrite Abs in Spec'; try omega.
    destruct Spec' as [->].
    apply IHn; omega.
  Qed.

  Lemma memory_closed_empty:
    forall M, memory_closed M [] ->
         M ≋ empty_memory _.
  Proof.
    intros ** (Insts & Vals); unfold find_val, find_inst in *.
    constructor; simpl in *.
    - intro x.
      assert (Env.find x (values M) = None) as ->.
      { apply not_Some_is_None; intros ** E.
        eapply Vals, not_None_is_Some; eauto.
      }
      now rewrite Env.gempty.
    - split.
      + setoid_rewrite Env.Props.P.F.empty_in_iff; setoid_rewrite Env.In_find; split; try contradiction.
        intros (?&?); eapply Insts, not_None_is_Some; eauto.
      + setoid_rewrite Env.Props.P.F.empty_mapsto_iff; contradiction.
  Qed.

  Require Import Setoid.

  Lemma msem_node_absent_until:
    forall n0 G f xss M M' yss,
      msem_node G f xss M M' yss ->
      (forall n, n < n0 -> absent_list (xss n)) ->
      forall n, n <= n0 -> M n ≋ M 0.
  Proof.
    inversion_clear 1 as [??????????????? Heqs Hmem].
    induction (n_eqs n) as [|[]]; intros ** Abs k Spec; inv Heqs; auto.
    - assert (forall n, M n ≋ empty_memory _) as E
          by (intro; apply memory_closed_empty; auto).
      rewrite 2 E; reflexivity.
    -

  Lemma msem_equation_absent_until_cons:
    forall n0 G eq eqs bk H M M' Me Me' mems argIn,
      (forall f xss M M' yss,
          msem_node G f xss M M' yss ->
          (forall n, n < n0 -> absent_list (xss n)) ->
          forall n, n <= n0 -> M n = M 0) ->
      (forall n, n < n0 -> bk n = false) ->
      (forall n, n <= n0 -> M n = M 0) ->
      msem_equation G bk H Me Me' eq ->
      Is_well_sch mems argIn (eq :: eqs) ->
      Forall (msem_equation G bk H M M') eqs ->
      exists M1 M1',
        Forall (msem_equation G bk H M1 M1') (eq :: eqs)
        /\ forall n, n <= n0 -> M1 n = M1 0.
  Proof.
    intros ** IHNode Abs Spec Heq Hwsch Hmeqs.
      inversion Heq as [|
                        ???????????????? Args ? Node|
                        ???????????????????? Args ??? Reset|
                        ?????????? Exps ? Mfby]; subst;
        inv Hwsch.
      - do 3 econstructor; eauto.
      - exists (add_inst_n x Mx M), (add_inst_n x Mx' M'); split.
        + constructor; auto.
          * econstructor; eauto;
              unfold sub_inst_n, sub_inst, add_inst_n;
              setoid_rewrite find_inst_gss; auto.
          * assert (Is_defined_in_eq x (EqApp xs ck f arg None))
              by (constructor; apply hd_error_Some_In; auto).
            apply msem_equation_madd_inst; auto.
        + intros.
          unfold add_inst_n.
          eapply IHNode in Node; eauto.
          * rewrite Node, Spec; auto.
          *{ intros n' ?.
             specialize (Args n');
               inversion_clear Args as [?????? Clock|??? E].
             - rewrite Abs in Clock; auto.
               contradict Clock; apply not_subrate_clock.
             - rewrite E; apply all_absent_spec.
           }
      - exists (add_inst_n x Mx M), (add_inst_n x Mx' M'); split.
        + constructor; auto.
          * econstructor; eauto;
              unfold sub_inst_n, sub_inst, add_inst_n;
              setoid_rewrite find_inst_gss; auto.
          * assert (Is_defined_in_eq x (EqApp xs ck f arg (Some (r, ck_r))))
              by (constructor; apply hd_error_Some_In; auto).
            apply msem_equation_madd_inst; auto.
        + intros.
          unfold add_inst_n.
          inversion_clear Reset as [?????? Nodes].
          destruct (Nodes (count rs 0)) as (Mk0 & Mk'0 & Node0 & Mmask0 & Mmask'0).
          specialize (Nodes (count rs n)).
          destruct Nodes as (Mk & Mk' & Node & Mmask & Mmask').
          eapply IHNode in Node; eauto.
          * specialize (Mmask n).
            rewrite <-Mmask, Node, Spec; auto.
            specialize (Mmask0 0).
            admit.
          *{ intros n' ?.
             apply absent_list_mask.
             - specialize (Args n');
                 inversion_clear Args as [?????? Clock|??? E].
               + rewrite Abs in Clock; auto.
                 contradict Clock; apply not_subrate_clock.
               + rewrite E; apply all_absent_spec.
             - apply all_absent_spec.
           }
      - exists (fun n => add_val x (match find_val x (Me n) with
                            | Some v => v
                            | None => false_val
                            end) (M n)),
        (fun n => add_val x (match find_val x (Me' n) with
                          | Some v => v
                          | None => false_val
                          end) (M' n)).
        split.
        + inversion_clear Mfby as [?????? Init Spec'].
          constructor; auto.
          *{ do 2 (econstructor; eauto).
             - rewrite Init, find_val_gss; auto.
             - intro n; specialize (Spec' n); destruct (find_val x (Me n)) eqn: E; try contradiction.
               repeat rewrite find_val_gss; auto.
               destruct (ls n) eqn: E'; auto.
               + destruct Spec' as (-> & -> & ?); intuition.
               + destruct Spec' as (-> & -> & ?); intuition.
           }
          * apply msem_equation_madd_val; eauto.
        + intros; unfold add_val_n.
          erewrite mfby_absent_until; eauto.
          * inversion_clear Mfby as [?????? Init].
            rewrite Init, Spec; auto.
          * intros n' ?.
            specialize (Exps n');
              inversion_clear Exps as [???? Clock|]; auto.
            rewrite Abs in Clock; auto.
            contradict Clock; apply not_subrate_clock.
    Qed.

    Corollary msem_equation_absent_until:
      forall n0 G eqs bk H M M' mems argIn,
        (forall f xss M M' yss,
            msem_node G f xss M M' yss ->
            (forall n, n < n0 -> absent_list (xss n)) ->
            forall n, n <= n0 -> M n = M 0) ->
        (forall n, n < n0 -> bk n = false) ->
        Is_well_sch mems argIn eqs ->
        Forall (msem_equation G bk H M M') eqs ->
        exists M1 M1',
          Forall (msem_equation G bk H M1 M1') eqs
          /\ forall n, n <= n0 -> M1 n = M1 0.
  Proof.
    intros ** IH Abs Hwsch Heqs.
    induction eqs as [|eq eqs IHeqs]; [do 2 exists (fun n => empty_memory _); now constructor|].
    apply Forall_cons2 in Heqs as [Heq Heqs].
    eapply IHeqs with (1:=Is_well_sch_cons _ _ _ _ Hwsch)
      in Heqs
      as (?&?&?&?); eauto.
    eapply msem_equation_absent_until_cons; eauto.
  Qed.

  Lemma well_formed_empty_eqs_n:
    memory_closed_n (fun _ : nat => empty_memory val) [].
  Proof.
    constructor; simpl.
    - split; intros ** Hin; try contradiction.
      destruct Hin as (?& Hin); unfold sub_inst, empty_memory, find_inst in Hin;
        simpl in Hin.
      rewrite Env.gempty in Hin; discriminate.
    - split; intros ** Hin; try contradiction.
      destruct Hin as (?& Hin); unfold empty_memory, find_val in Hin;
        simpl in Hin.
      rewrite Env.gempty in Hin; discriminate.
  Qed.


  (* XXX: for this lemma, and the ones before/after it, factorize 'G',
'bk' and possibly other variables in a Section *)
  Corollary sem_msem_eqs:
    forall G bk H eqs mems argIn,
      (forall f xs ys,
          sem_node G f xs ys ->
          exists M M', msem_node G f xs M M' ys) ->
      (forall f r xs ys,
          sem_reset G f r xs ys ->
          exists M M', msem_reset G f r xs M M' ys) ->
      Is_well_sch mems argIn eqs -> (* TODO *)
      Forall (sem_equation G bk H) eqs ->
      exists M1 M1', Forall (msem_equation G bk H M1 M1') eqs
                /\ memory_closed_n M1 eqs.
  Proof.
    intros ** IH Hwsch Heqs.
    induction eqs as [|eq eqs IHeqs].
    - exists (fun n => empty_memory _), (fun n => empty_memory _); split; auto.
      apply well_formed_empty_eqs_n.
    - apply Forall_cons2 in Heqs as [Heq Heqs].
      eapply IHeqs with (1:=Is_well_sch_cons _ _ _ _ Hwsch)
        in Heqs
        as (?&?&?&?); eauto.
      eapply sem_msem_eq; eauto.
  Qed.

  Require Import Coq.Logic.ClassicalChoice.
  Require Import Coq.Logic.ConstructiveEpsilon.
  Require Import Coq.Logic.Epsilon.
  Require Import Coq.Logic.IndefiniteDescription.

  (* Check functional_choice. *)

  (* Lemma functional_choice_sig: *)
  (*   forall A B (R: A -> B -> Prop), *)
  (*     (forall x, { y | R x y }) -> *)
  (*     exists f, forall x, R x (f x). *)
  (* Proof. *)
  (*   intros ** Ex. *)
  (*   exists (fun n => proj1_sig (Ex n)). *)
  (*   intro x; destruct (Ex x); auto. *)
  (* Qed. *)

  Theorem sem_msem_reset:
    forall G f r xs ys,
      (forall f xs ys,
          sem_node G f xs ys ->
          exists M M', msem_node G f xs M M' ys) ->
      sem_reset G f r xs ys ->
      exists M M', msem_reset G f r xs M M' ys.
  Proof.
    intros ** IH Sem.
    inversion_clear Sem as [???? Sem'].
    assert (forall k, exists Mk Mk', msem_node G f (mask (all_absent (xs 0)) k r xs)
                                     Mk Mk'
                                     (mask (all_absent (ys 0)) k r ys)) as Msem'
        by (intro; specialize (Sem' k); apply IH in Sem'; auto).
    assert (exists F F', forall k, msem_node G f (mask (all_absent (xs 0)) k r xs)
                                   (F k) (F' k)
                                   (mask (all_absent (ys 0)) k r ys))
      as (F & F' & Msem).
    {
      (** Infinite Description  *)
      do 2 apply functional_choice in Msem' as (?&Msem'); eauto.

      (** Epsilon  *)
      (* assert (inhabited memories) as I *)
      (*     by (constructor; exact (fun n => @empty_memory val)). *)
      (* exists (fun n => epsilon *)
      (*            I (fun M => msem_node G f (mask (all_absent (xs 0)) n r xs) M *)
      (*                               (mask (all_absent (ys 0)) n r ys))). *)
      (* intro; now apply epsilon_spec.  *)

      (** Constructive Epsilon  *)
      (* pose proof (constructive_ground_epsilon memories) as F. *)

      (** Classical Choice  *)
      (* now apply choice in Msem'.   *)
    }
    clear Msem'.

    exists (fun n => F (count r n) n), (fun n => F' (count r n) n).
    constructor.
    intro k; specialize (Msem k).
    do 2 eexists; intuition eauto;
      intros n Count; auto.
  Qed.

  (* Lemma sem_node_valid_app_cons: *)
  (*   forall n G f xs ys, *)
  (*     Ordered_nodes (n :: G) -> *)
  (*     sem_node (n :: G) f xs ys -> *)
  (*     n.(n_name) <> f -> *)
  (*     valid_app_node G f. *)
  (* Proof. *)
  (*   intros ** Hord Hsem Hnf; revert Hnf. *)
  (*   induction Hsem as [| | | |???? Reset|??????? Find ?????? Heqs] using sem_node_mult *)
  (*     with (P_equation := fun bk H eq => *)
  (*                           valid_app_eq eq *)
  (*                           /\ forall f, n.(n_name) <> f -> *)
  (*                                  Is_node_in_eq f eq -> *)
  (*                                  valid_app_node G f) *)
  (*          (P_reset := fun f r xss yss => *)
  (*                        n.(n_name) <> f -> valid_app_node G f); *)
  (*     simpl; auto. *)
  (*   - split; auto; inversion 2. *)
  (*   - split. *)
  (*     + eapply sem_EqApp_gt0; eauto. *)
  (*     + inversion 2; subst; auto. *)
  (*   - split. *)
  (*     + eapply sem_EqApp_gt0; eauto. *)
  (*     + inversion 2; subst; auto. *)
  (*   - split; auto; inversion 2. *)
  (*   - destruct (Reset 0) as (?&?); auto. *)
  (*   - intros; rewrite find_node_tl in Find; auto. *)
  (*     rewrite Forall_forall in Heqs. *)
  (*     econstructor; eauto. *)
  (*     intros; edestruct Heqs as (?& ValidNode); *)
  (*       simpl in *; eauto; split; auto. *)
  (*     apply ValidNode; auto using Is_node_in_eq. *)
  (*     eapply find_node_later_not_Is_node_in in Hord; eauto. *)
  (*     intro E; apply Hord; rewrite E. *)
  (*     apply Exists_exists. *)
  (*     eexists; split; eauto using Is_node_in_eq. *)
  (*     Grab Existential Variables. *)
  (*     exact ck. *)
  (* Qed. *)

  (* Lemma sem_node_valid_app_cons2: *)
  (*   forall G f xs ys, *)
  (*     sem_node G f xs ys -> *)
  (*     valid_app_node G f. *)
  (* Proof. *)
  (*   intro G. *)
  (*   induction 1 as [| | | |???? Reset|?????????????? Heqs] using sem_node_mult *)
  (*     with (P_equation := fun bk H eq => *)
  (*                           valid_app_eq eq *)
  (*                           /\ forall f, Is_node_in_eq f eq -> valid_app_node G f) *)
  (*          (P_reset := fun f r xss yss => *)
  (*                        valid_app_node G f); simpl; auto. *)
  (*   - split; auto; inversion 1. *)
  (*   - split. *)
  (*     + eapply sem_EqApp_gt0; eauto. *)
  (*     + now inversion_clear 1. *)
  (*   - split. *)
  (*     + eapply sem_EqApp_gt0; eauto. *)
  (*     + now inversion_clear 1. *)
  (*   - split; auto; inversion 1. *)
  (*   - destruct (Reset 0) as (?&?); auto. *)
  (*   - rewrite Forall_forall in Heqs. *)
  (*     econstructor; eauto. *)
  (*     intros; edestruct Heqs as (?& ValidNode); *)
  (*       simpl in *; eauto; split; auto using Is_node_in_eq. *)
  (*     Grab Existential Variables. *)
  (*     exact ck. *)
  (* Qed. *)

  Theorem sem_msem_node:
    forall G f xs ys,
      Welldef_global G ->
      sem_node G f xs ys ->
      exists M M', msem_node G f xs M M' ys.
  Proof.
    induction G as [|node].
    inversion 2;
      match goal with Hf: find_node _ [] = _ |- _ => inversion Hf end.
    intros ** Hwdef Hsem.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [??????? Hfind ????? Heqs].
    pose proof (Welldef_global_Ordered_nodes _ Hwdef) as Hord.
    pose proof (Welldef_global_cons _ _ Hwdef) as HwdefG.
    pose proof (find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    pose proof Hfind.
    simpl in Hfind.
    destruct (ident_eqb node.(n_name) f) eqn:Hnf.
    - assert (Hord':=Hord).
      inversion_clear Hord as [|? ? Hord'' Hnneqs Hnn].
      injection Hfind; intro HR; rewrite HR in *; clear HR; simpl in *.
      eapply Forall_sem_equation_global_tl in Heqs; eauto.
      assert (forall f xs ys,
                 sem_node G f xs ys ->
                 exists M M', msem_node G f xs M M' ys) as IHG'
          by auto.
      assert (forall f r xs ys,
                 sem_reset G f r xs ys ->
                 exists M M', msem_reset G f r xs M M' ys) as IHG''
          by (intros; now apply sem_msem_reset).

      inversion_clear Hwdef as [|??? neqs].
      simpl in neqs; unfold neqs in *.
      assert (exists M1 M1', Forall (msem_equation G bk H M1 M1') n.(n_eqs)
                        /\ memory_closed_n M1 n.(n_eqs))
        as (M1 & M1' & Hmsem & ?) by now eapply sem_msem_eqs; eauto.
      exists M1, M1'.
      econstructor; eauto.
      eapply msem_equation_cons2; eauto.
    - apply ident_eqb_neq in Hnf.
      apply sem_node_cons with (1:=Hord) (3:=Hnf) in Hsem.
      inv Hord.
      eapply IHG in Hsem as (M & M' &?); eauto.
      exists M, M'.
      now eapply msem_node_cons2; eauto.
  Qed.

  (* We use the mem-semantics to assert the absence of applications
  with no return arguments. This is a bit of a hack, if you ask me. So
  don't ask. *)
  Lemma non_trivial_EqApp:
    forall G bk H M M' eqs ,
      Forall (msem_equation G bk H M M') eqs ->
      forall ck f les y, ~ In (EqApp [] ck f les y) eqs.
  Proof.
  induction eqs; intros ** Hsem ? ? ? ? Hin.
  - match goal with
    | H: In _ [] |- _ => inv H
    end.
  - destruct Hin as [Hin_eq | Hin_eqs ]; subst.
    + inversion_clear Hsem as [ | ? ? Hsem_eq ];
      inv Hsem_eq; discriminate.
    + eapply IHeqs. inv Hsem; auto.
      repeat eexists. eauto.
  Qed.


End MEMSEMANTICS.

Module MemSemanticsFun
       (Ids     : IDS)
       (Op      : OPERATORS)
       (OpAux   : OPERATORS_AUX   Op)
       (Clks    : CLOCKS          Ids)
       (ExprSyn : NLEXPRSYNTAX        Op)
       (Syn     : NLSYNTAX        Ids Op       Clks ExprSyn)
       (Str     : STREAM              Op OpAux)
       (Ord     : ORDERED         Ids Op       Clks ExprSyn Syn)
       (ExprSem : NLEXPRSEMANTICS Ids Op OpAux Clks ExprSyn     Str)
       (Sem     : NLSEMANTICS     Ids Op OpAux Clks ExprSyn Syn Str Ord ExprSem)
       (Mem     : MEMORIES        Ids Op       Clks ExprSyn Syn)
       (IsD     : ISDEFINED       Ids Op       Clks ExprSyn Syn                 Mem)
       (IsV     : ISVARIABLE      Ids Op       Clks ExprSyn Syn                 Mem IsD)
       (IsF     : ISFREE          Ids Op       Clks ExprSyn Syn)
       (NoD     : NODUP           Ids Op       Clks ExprSyn Syn                 Mem IsD IsV)
       (WeF     : WELLFORMED      Ids Op       Clks ExprSyn Syn             Ord Mem IsD IsV IsF NoD)
       <: MEMSEMANTICS Ids Op OpAux Clks ExprSyn Syn Str Ord ExprSem Sem Mem IsD IsV IsF NoD WeF.
  Include MEMSEMANTICS Ids Op OpAux Clks ExprSyn Syn Str Ord ExprSem Sem Mem IsD IsV IsF NoD WeF.
End MemSemanticsFun.
