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

  Inductive mfby: ident -> val -> stream value -> memories -> memories -> stream value -> Prop :=
    mfby_intro:
      forall x v0 ls M M' xs,
        find_val x (M 0) = Some v0 ->
        (forall n, match find_val x (M n) with
              | Some mv =>
                match ls n with
                | absent =>
                  find_val x (M (S n)) = Some mv
                  /\ find_val x (M' n) = Some mv
                  /\ xs n = absent
                | present v =>
                  find_val x (M (S n)) = Some v
                  /\ find_val x (M' n) = Some v
                  /\ xs n = present mv
                end
              | None => False
              end) ->
        mfby x v0 ls M M' xs.

  Section NodeSemantics.

    Definition sub_inst_n (x: ident) (M M': memories) : Prop :=
      forall n, sub_inst x (M n) (M' n).

    Variable G: global.

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
        forall bk H M M' x xs ck f Mx Mx' arg r ck_r ys ls xss,
          Some x = hd_error xs ->
          sub_inst_n x M Mx ->
          sub_inst_n x M' Mx' ->
          sem_laexps bk H ck arg ls ->
          sem_vars H xs xss ->
          (* sem_avar bk H ck_r r ys -> *)
          sem_var H r ys ->
          msem_reset f (reset_of ys) ls Mx Mx' xss ->
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
      forall bk H M M' x xs ck f Mx Mx' arg r ck_r ys ls xss,
        Some x = hd_error xs ->
        sub_inst_n x M Mx ->
        sub_inst_n x M' Mx' ->
        sem_laexps bk H ck arg ls ->
        sem_vars H xs xss ->
        (* sem_avar bk H ck_r r ys -> *)
        sem_var H r ys ->
        msem_reset G f (reset_of ys) ls Mx Mx' xss ->
        P_reset f (reset_of ys) ls Mx Mx' xss ->
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
         induction H7; auto.
    Qed.

    Combined Scheme msem_equation_node_reset_ind from
             msem_equation_mult, msem_node_mult, msem_reset_mult.

  End msem_node_mult.

  Definition msem_nodes (G: global) : Prop :=
    Forall (fun no => exists xs M M' ys, msem_node G no.(n_name) xs M M' ys) G.

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

  Lemma msem_node_cons:
    forall n G f xs M M' ys,
      Ordered_nodes (n :: G) ->
      msem_node (n :: G) f xs M M' ys ->
      n.(n_name) <> f ->
      msem_node G f xs M M' ys.
  Proof.
    Hint Constructors msem_equation msem_reset.
    intros ** Hord Hsem Hnf.
    revert Hnf.
    induction Hsem as [| | | |?????? IH |????????? Hf ?????? IH]
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
      rewrite find_node_tl with (1:=Hnf) in Hf.
      econstructor; eauto.
      apply find_node_later_not_Is_node_in with (2:=Hf) in Hord.
      apply Is_node_in_Forall in Hord.
      apply Forall_Forall with (1:=Hord) in IH.
      apply Forall_impl with (2:=IH).
      intuition.
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
    induction Hsem as [| | | |?????? IH|??????? n' ? Hfind ????? Heqs IH]
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
      assert (forall g, Is_node_in g n'.(n_eqs) -> Exists (fun nd=> g = nd.(n_name)) G)
        as Hniex by (intros g Hini;
                     apply find_node_find_again with (1:=Hord) (2:=Hfind) in Hini;
                     exact Hini).
      assert (Forall (fun eq => forall g,
                          Is_node_in_eq g eq -> Exists (fun nd=> g = nd.(n_name)) G)
                     n'.(n_eqs)) as HH.
      {
        clear Heqs IH.
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
      (forall f, Is_node_in f eqs -> find_node f G <> None) ->
      ~ Is_node_in n.(n_name) eqs ->
      Forall (msem_equation (n :: G) bk H M M') eqs ->
      Forall (msem_equation G bk H M M') eqs.
  Proof.
    intros ??????? Hord.
    induction eqs as [|eq eqs IH]; trivial; [].
    intros Hfind Hnini Hmsem.
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
    - intros f Hini.
      apply (Exists_cons_tl eq) in Hini.
      now apply (Hfind _ Hini).
    - apply not_Is_node_in_cons in Hnini.
      now destruct Hnini.
  Qed.

  (** *** Memory management *)

  Definition add_vals (y: ident) (ms: stream val) (M: memories): memories :=
    fun n => add_val y (ms n) (M n).

  Lemma mfby_add_vals:
    forall x v0 ls M M' xs y ms ms',
      x <> y ->
      mfby x v0 ls M M' xs ->
      mfby x v0 ls (add_vals y ms M) (add_vals y ms' M') xs.
  Proof.
    unfold add_vals.
    intros ** Fby; inversion_clear Fby as [??????? Spec].
    constructor.
    - rewrite find_val_gso; auto.
    - intro n; rewrite 3 find_val_gso; auto.
      exact (Spec n).
  Qed.

  Definition add_insts (y: ident) (M' M: memories): memories :=
    fun n => add_inst y (M' n) (M n).

  Lemma mfby_add_insts:
    forall x v0 ls M M' xs y My My',
      mfby x v0 ls M M' xs ->
      mfby x v0 ls (add_insts y My M) (add_insts y My' M') xs.
  Proof.
    inversion 1; econstructor; eauto.
  Qed.

  Hint Resolve mfby_add_vals mfby_add_insts.

  Lemma msem_equation_madd_val:
    forall G bk H M M' x ms ms' eqs,
      ~Is_defined_in_eqs x eqs ->
      Forall (msem_equation G bk H M M') eqs ->
      Forall (msem_equation G bk H (add_vals x ms M) (add_vals x ms' M')) eqs.
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
      Forall (msem_equation G bk H (add_insts x Mx M) (add_insts x Mx' M')) eqs.
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
                         |???? x' ??????????? Hsome|];
      eauto;
      assert (sub_inst_n x' (add_insts x Mx M) Mx0)
        by (apply not_Is_defined_in_eq_EqApp in Hnd;
            unfold sub_inst_n, sub_inst, add_insts in *; intro;
            rewrite find_inst_gso; auto; intro; subst x; destruct xs;
            inv Hsome; apply Hnd; now constructor);
      assert (sub_inst_n x' (add_insts x Mx' M') Mx'0)
        by (apply not_Is_defined_in_eq_EqApp in Hnd;
            unfold sub_inst_n, sub_inst, add_insts in *; intro;
            rewrite find_inst_gso; auto; intro; subst x; destruct xs;
            inv Hsome; apply Hnd; now constructor);
      eauto.
  Qed.

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

  (** ** Fundamental theorem *)

  (**

We show that the standard semantics implies the existence of a
dataflow memory for which the non-standard semantics holds true.

   *)

  Fixpoint stutter (v0: val) (xs: stream value) (n: nat) : val :=
    match xs n with
    | present v => v
    | absent => match n with
               | 0 => v0
               | S n => stutter v0 xs n
               end
    end.

  Lemma sem_msem_eq:
    forall G bk H eqs M M' eq mems argIn,
      (forall f xs ys,
          sem_node G f xs ys ->
          exists M M', msem_node G f xs M M' ys) ->
      (forall f r xs ys,
          sem_reset G f r xs ys ->
          exists M M', msem_reset G f r xs M M' ys) ->
      sem_equation G bk H eq ->
      Is_well_sch mems argIn (eq :: eqs) ->
      Forall (msem_equation G bk H M M') eqs ->
      exists M1 M1', Forall (msem_equation G bk H M1 M1') (eq :: eqs).
  Proof.
    intros ** IH IH' Heq Hwsch Hmeqs.
    inversion Heq as [|???????? Hls Hxs Hsem
                         |??????????? Hls Hxs Hy Hsem
                         |???????? Hle Hvar];
      match goal with H:_=eq |- _ => rewrite <-H in * end.

    - exists M, M'.
      repeat (econstructor; eauto).

    - apply IH in Hsem as (Mx & Mx' & Hmsem).
      exists (add_insts (hd Ids.default x) Mx M), (add_insts (hd Ids.default x) Mx' M').

      assert (exists i, Some i = hd_error x) as [i Hsome].
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

        destruct x; try now inv Hlen.
        eexists; simpl; eauto.
      }

      assert (Hhd: hd Ids.default x = i).
      { destruct x; simpl in *; try discriminate.
        injection Hsome; congruence.
      }
      rewrite Hhd; clear Hhd.

      constructor.
      + econstructor; eauto;
          unfold sub_inst, add_insts; intro; now apply find_inst_gss.
      + inversion_clear Hwsch.
        assert (Is_defined_in_eq i (EqApp x ck f arg None)).
        { constructor. destruct x; try discriminate.
          injection Hsome. intro; subst i. constructor (auto).
        }
        now apply msem_equation_madd_inst; auto.

    - pose proof Hsem as Hsem'.
      apply IH' in Hsem as (Mx & Mx' & Hmsem).
      exists (add_insts (hd Ids.default x) Mx M), (add_insts (hd Ids.default x) Mx' M').

      assert (exists i, Some i = hd_error x) as [i Hsome].
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

        destruct x; try now inv Hlen.
        eexists; simpl; eauto.
      }

      assert (Hhd: hd Ids.default x = i).
      { destruct x; simpl in *; try discriminate.
        injection Hsome; congruence.
      }

      rewrite Hhd; clear Hhd.

      constructor.
      + econstructor; eauto;
          unfold sub_inst, add_insts; intro; now apply find_inst_gss.
      + inversion_clear Hwsch.
        assert (Is_defined_in_eq i (EqApp x ck f arg (Some (y, ck_r)))).
        { constructor. destruct x; try discriminate.
          injection Hsome. intro; subst i. constructor (auto).
        }
        apply msem_equation_madd_inst; auto.

    - exists (add_vals x (hold (sem_const c0) ls) M), (add_vals x (stutter (sem_const c0) ls) M').
      constructor.
      + unfold add_vals.
        do 2 (econstructor; eauto).
        * now apply find_val_gss.
        (* * reflexivity. *)
        *{ subst; unfold fby; simpl.
           intro n; destruct (ls n) eqn: E; auto;
            repeat rewrite find_val_gss; auto.
           - intuition; clear - E.
             induction n; simpl; rewrite E; auto.
             destruct (ls n) eqn: E'; auto.
             destruct n; simpl; rewrite E'; auto.
           - intuition; destruct n; simpl; now rewrite E.
         }
      + inversion_clear Hwsch.
        apply msem_equation_madd_val; eauto.
  Qed.

  (* Fixpoint interp_equation (G: global) (bk: cstream) (H: history) (eq: equation) (M: memories) {struct eq}: memories := *)
  (*   match eq with *)
  (*   | EqDef x ck ce => *)
  (*     M *)

  (*   | EqApp xs ck f arg None => *)
  (*     fun n => *)
  (*       match hd_error xs with *)
  (*       | Some x => *)
  (*         match mfind_inst x (M n) with *)
  (*         | Some M' => *)
  (*           let M' := interp_node G f M' in *)
  (*           madd_inst x M' (M n) *)
  (*         | None => *)
  (*           empty_memory _ *)
  (*         end *)
  (*     | None => *)
  (*       empty_memory _ *)
  (*     end *)

  (*   | EqApp xs ck f arg (Some (r, ck_r)) => *)
  (*     let rs := interp_annotated bk H (fun _ => interp_var_instant) ck_r r in *)
  (*     fun n => *)
  (*       match hd_error xs with *)
  (*       | Some x => *)
  (*         match mfind_inst x (M n) with *)
  (*         | Some M' => *)
  (*           let M' := interp_reset G f (reset_of rs n) M' in *)
  (*           madd_inst x M' (M n) *)
  (*         | None => *)
  (*           empty_memory _ *)
  (*         end *)
  (*     | None => *)
  (*       empty_memory _ *)
  (*     end *)

  (*   | EqFby x ck c0 le => *)
  (*     let ls := interp_annotated bk H interp_lexp_instant ck le in *)
  (*     add_vals x (hold (sem_const c0) ls) M *)
  (*   end *)

  (* with interp_node (G: global) (f: ident) (M: memory val): memory val := *)
  (*        match find_node f G with *)
  (*        | Some n => *)
  (*          List.fold_left (interp_equation G   *)
  (*          empty_memory _ *)
  (*        | None => *)
  (*          empty_memory _ *)
  (*        end *)

  (* with interp_reset (G: global) (f: ident) (r: bool) (M: memory val): memory val := *)
  (*        interp_node G f M *)
  (* . *)

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
      Is_well_sch mems argIn eqs ->
      Forall (sem_equation G bk H) eqs ->
      exists M1 M1', Forall (msem_equation G bk H M1 M1') eqs.
  Proof.
    intros ** IH Hwsch Heqs.
    induction eqs as [|eq eqs IHeqs]; [do 2 exists (fun n => empty_memory _); now constructor|].
    apply Forall_cons2 in Heqs as [Heq Heqs].
    eapply IHeqs with (1:=Is_well_sch_cons _ _ _ _ Hwsch)
      in Heqs
      as (?&?&?); eauto.
    eapply sem_msem_eq; eauto.
  Qed.

  Require Import Coq.Logic.ClassicalChoice.
  Require Import Coq.Logic.ConstructiveEpsilon.
  Require Import Coq.Logic.Epsilon.
  Require Import Coq.Logic.IndefiniteDescription.

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
      assert (exists M1 M1', Forall (msem_equation G bk H M1 M1') n.(n_eqs))
        as (M1 & M1' & Hmsem) by now eapply sem_msem_eqs; eauto.
      exists M1, M1'.
      econstructor; eauto.
      + simpl; now rewrite Hnf.
      + eapply msem_equation_cons2; eauto.
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
