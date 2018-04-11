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
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.IsVariable.
Require Import Velus.NLustre.IsDefined.
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
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Op)
       (Import Clks  : CLOCKS      Ids)
       (Import Syn   : NLSYNTAX    Ids Op       Clks)
       (Import Str   : STREAM             Op OpAux)
       (Import Ord   : ORDERED     Ids Op       Clks Syn)
       (Import Sem   : NLSEMANTICS Ids Op OpAux Clks Syn Str Ord)
       (Import Mem   : MEMORIES    Ids Op       Clks Syn)
       (Import IsD   : ISDEFINED   Ids Op       Clks Syn         Mem)
       (Import IsV   : ISVARIABLE  Ids Op       Clks Syn         Mem IsD)
       (Import IsF   : ISFREE      Ids Op       Clks Syn)
       (Import NoD   : NODUP       Ids Op       Clks Syn         Mem IsD IsV)
       (Import WeF   : WELLFORMED  Ids Op       Clks Syn     Ord Mem IsD IsV IsF NoD).

  Definition memories := stream (memory val).

  (* Definition mask'' {A} (k: nat) (rs: cstream) (xs ys: stream A) : Prop := *)
  (*   ys 0 = xs 0 *)
  (*   /\ forall n, ys n = match nat_compare (count rs n) k with *)
  (*                 | Lt => xs 0 *)
  (*                 | Eq => xs (if rs n then 0 else n) *)
  (*                 | Gt => if EqNat.beq_nat (count rs n) (S k) && rs n *)
  (*                        then xs n else ys (pred n) *)
  (*                 end. *)

  (* Fixpoint mask' {A} (k: nat) (rs: cstream) (xs: stream A) (n: nat) : A := *)
  (*   match n with *)
  (*   | 0 => xs 0 *)
  (*   | S n' => *)
  (*     match nat_compare (count rs n) k with *)
  (*     | Lt => xs 0 *)
  (*     | Eq => xs (if rs n then 0 else n) *)
  (*     | Gt => if EqNat.beq_nat (count rs n) (S k) && rs n *)
  (*            then xs n else mask' k rs xs n' *)
  (*     end *)
  (*   end. *)

  (* Lemma mask'_eq: *)
  (*   forall {A} n k rs (xs: stream A), *)
  (*     count rs n = k -> *)
  (*     mask' k rs xs n = xs (if rs n then 0 else n). *)
  (* Proof. *)
  (*   destruct n; intros ** Count; simpl in *. *)
  (*   - now destruct (rs 0). *)
  (*   - apply nat_compare_eq_iff in Count; now rewrite Count. *)
  (* Qed. *)

  (* Lemma mask'_lt: *)
  (*   forall {A} n k rs (xs: stream A), *)
  (*     count rs n < k -> *)
  (*     mask' k rs xs n = xs 0. *)
  (* Proof. *)
  (*   destruct n; intros ** Count; simpl in *; auto. *)
  (*   apply nat_compare_lt in Count; now rewrite Count. *)
  (* Qed. *)

  (* Lemma mask'_spec: *)
  (*   forall {A} k rs (xs: stream A), *)
  (*     mask'' k rs xs (mask' k rs xs). *)
  (* Proof. *)
  (*   split; auto. *)
  (*   induction n; simpl; auto. *)
  (*   destruct (nat_compare (if rs 0 then 1 else 0) k), (rs 0); simpl; auto. *)
  (*   destruct k; simpl; auto. *)
  (* Qed. *)

  Fixpoint mmask (k: nat) (rs: cstream) (M: memories) (n: nat) : memory val :=
    match n with
    | 0 => M 0
    | S n' => match nat_compare (count rs n) k with
             | Lt => M 0
             | Eq => M (if rs n then 0 else n)
             | Gt => if EqNat.beq_nat (count rs n) (S k) && rs n
                    then M n else mmask k rs M n'
             end
    end.

  Definition mmask' (k: nat) (rs: cstream) (M M': memories) : Prop :=
    M' 0 = M 0
    /\ forall n, M' n = match nat_compare (count rs n) k with
                  | Lt => M 0
                  | Eq => M (if rs n then 0 else n)
                  | Gt => if EqNat.beq_nat (count rs n) (S k) && rs n
                         then M n else M' (pred n)
                  end.

  Lemma mmask_spec:
    forall k rs M,
      mmask' k rs M (mmask k rs M).
  Proof.
    split; auto.
    induction n; simpl; auto.
    destruct (nat_compare (if rs 0 then 1 else 0) k), (rs 0); simpl; auto.
    destruct k; simpl; auto.
  Qed.

  (* Lemma mmask_mfind_mem: *)
  (*   forall x M n k rs, *)
  (*     mfind_mem x (M n) <> None -> *)
  (*     mfind_mem x (mmask k rs M n) <> None. *)
  (* Proof. *)
  (*   intros ** E E'; apply E; clear E. *)
  (*   induction n; simpl in *; auto. *)
  (*   destruct () *)
  (*   - contradiction. *)


  Lemma mmask_eq:
    forall n k rs M,
      count rs n = k ->
      mmask k rs M n = M (if rs n then 0 else n).
  Proof.
    destruct n; intros ** Count; simpl in *.
    - now destruct (rs 0).
    - apply nat_compare_eq_iff in Count; now rewrite Count.
  Qed.

  Lemma mmask_lt:
    forall n k rs M,
      count rs n < k ->
      mmask k rs M n = M 0.
  Proof.
    destruct n; intros ** Count; simpl in *; auto.
    apply nat_compare_lt in Count; now rewrite Count.
  Qed.

  Lemma mmask_gt:
    forall n k rs M,
      count rs n > k ->
      mmask k rs M n = if EqNat.beq_nat (count rs n) (S k) && rs n
                       then M n else mmask k rs M (pred n).
  Proof.
    destruct n; intros ** Count; simpl in *.
    - now destruct (EqNat.beq_nat (if rs 0 then 1 else 0) (S k) && rs 0).
    - apply nat_compare_gt in Count; now rewrite Count.
  Qed.

  (* Definition memory_reset (rs: cstream) (M: memory) : memory := *)
  (*   mmap (fun ms => fun n => ms (if rs n then 0 else n)) M. *)

  Inductive mfby: ident -> val -> stream value -> memories -> stream value -> Prop :=
    mfby_intro:
      forall x v0 ls M xs,
        mfind_mem x (M 0) = Some v0 ->
        (forall n, match mfind_mem x (M n) with
              | Some mv =>
                match ls n with
                | absent    => mfind_mem x (M (S n)) = Some mv /\ xs n = absent
                | present v => mfind_mem x (M (S n)) = Some v  /\ xs n = present mv
                end
              | None => False
              end) ->
        mfby x v0 ls M xs.

  Lemma mmask_mfby:
    forall M x v0 xs ls k rs n,
      mfby x v0 ls M xs ->
      mfind_mem x (mmask k rs M n) <> None.
  Proof.
    intros ** Fby Find'; inversion_clear Fby as [????? Find Spec].
    induction n; simpl in Find'.
    - rewrite Find in Find'; discriminate.
    - destruct (nat_compare (if rs (S n) then S (count rs n) else count rs n) k), (rs (S n));
        try (now rewrite Find in Find'; discriminate).
      + specialize (Spec (S n)); rewrite Find' in Spec; auto.
      + destruct (EqNat.beq_nat (S (count rs n)) (S k) && true); auto.
        specialize (Spec (S n)); rewrite Find' in Spec; auto.
      + destruct (EqNat.beq_nat (count rs n) (S k) && false); auto.
        specialize (Spec (S n)); rewrite Find' in Spec; auto.
  Qed.

  Lemma foo:
    forall x v0 ls M xs k rs,
      mfby x v0 ls M xs ->
      (forall n,
          rs n = true ->
          mfind_mem x (M n) = Some v0) ->
      mfby x v0 (mask absent k rs ls) (mmask k rs M) (mask absent k rs xs).
  Proof.
    intros ** Fby Rst.
    inversion_clear Fby as [????? Find Spec].
    econstructor; eauto.
    intro n(* ; specialize (Spec n); specialize (Rst n) *).
    unfold mask; simpl.
    destruct (nat_compare (count rs n) k) eqn: E.
    - specialize (Spec n); specialize (Rst n).
      assert (EqNat.beq_nat k (count rs n) = true) as ->
          by now rewrite NPeano.Nat.eqb_sym, EqNat.beq_nat_true_iff,
             <-nat_compare_eq_iff.
      rewrite mmask_eq by now apply nat_compare_eq_iff.
      destruct (rs (S n)).
      + assert (nat_compare (S (count rs n)) k = Gt) as ->
            by (rewrite <-nat_compare_gt; apply Gt.le_gt_S;
                apply nat_compare_eq_iff in E; omega).
        assert (EqNat.beq_nat (S (count rs n)) (S k) = true) as ->
            by now apply EqNat.beq_nat_true_iff, eq_sym,
               eq_S, EqNat.beq_nat_true_iff.
        destruct (ls n), (rs n); simpl; intuition;
          rewrite H2 in Spec; rewrite Find; intuition.
      + rewrite E.
        destruct (ls n), (rs n); intuition;
          rewrite H0 in Spec; rewrite Find; intuition.
    - assert (EqNat.beq_nat k (count rs n) = false) as ->
          by (apply nat_compare_lt in E; apply EqNat.beq_nat_false_iff;
              intro; subst; omega).
      rewrite mmask_lt by (now apply nat_compare_lt); rewrite Find.
      destruct (rs (S n)).
      + destruct (nat_compare (S (count rs n)) k) eqn: E'; intuition.
        apply nat_compare_lt in E; apply nat_compare_gt in E'; omega.
      + rewrite E; auto.
    - assert (EqNat.beq_nat k (count rs n) = false) as ->
          by (apply nat_compare_gt in E; apply EqNat.beq_nat_false_iff;
              intro; subst; omega).
      destruct (rs (S n)).
      + assert (nat_compare (S (count rs n)) k = Gt) as ->
            by (rewrite <-nat_compare_gt in *; omega).
        assert (EqNat.beq_nat (S (count rs n)) (S k) = false) as ->
            by (apply EqNat.beq_nat_false_iff, not_eq_S,
                not_eq_sym; apply nat_compare_gt in E; omega).
        simpl.
        destruct (mfind_mem x (mmask k rs M n)) eqn: Find'; auto.
        eapply mmask_mfby; eauto using mfby.
      + rewrite E, Bool.andb_false_r.
        destruct (mfind_mem x (mmask k rs M n)) eqn: Find'; auto.
        eapply mmask_mfby; eauto using mfby.
  Qed.

  (* Implicit Type M : memory. *)

  Section NodeSemantics.

    Definition sub_inst (x: ident) (M M': memories) : Prop :=
      forall n, mfind_inst x (M n) = Some (M' n).

    Variable G: global.

    Inductive msem_equation: stream bool -> history -> memories -> equation -> Prop :=
    | SEqDef:
        forall bk H M x ck xs ce,
          sem_var bk H x xs ->
          sem_caexp bk H ck ce xs ->
          msem_equation bk H M (EqDef x ck ce)
    | SEqApp:
        forall bk H M x xs ck f M' arg ls xss,
          Some x = hd_error xs ->
          sub_inst x M M' ->
          sem_laexps bk H ck arg ls ->
          sem_vars bk H xs xss ->
          msem_node f ls M' xss ->
          msem_equation bk H M (EqApp xs ck f arg None)
    | SEqReset:
        forall bk H M x xs ck f M' arg y ck_r ys ls xss,
          Some x = hd_error xs ->
          sub_inst x M M' ->
          sem_laexps bk H ck arg ls ->
          sem_vars bk H xs xss ->
          sem_var bk H y ys ->
          msem_reset f (reset_of ys) ls M' xss ->
          msem_equation bk H M (EqApp xs ck f arg (Some (y, ck_r)))
    | SEqFby:
        forall bk H M x ck ls xs c0 le,
          sem_laexp bk H ck le ls ->
          sem_var bk H x xs ->
          mfby x (sem_const c0) ls M xs ->
          msem_equation bk H M (EqFby x ck c0 le)

    with msem_reset:
           ident -> stream bool -> stream (list value) -> memories ->
           stream (list value) -> Prop :=
         | SReset:
             forall f r xss M yss,
               (forall k, msem_node f
                               (mask (all_absent (xss 0)) k r xss)
                               (mmask k r M)
                               (mask (all_absent (yss 0)) k r yss)) ->
               msem_reset f r xss M yss

    with msem_node:
           ident -> stream (list value) -> memories -> stream (list value) -> Prop :=
         | SNode:
             forall bk H f xss M yss n,
               clock_of xss bk ->
               find_node f G = Some n ->
               sem_vars bk H (map fst n.(n_in)) xss ->
               sem_vars bk H (map fst n.(n_out)) yss ->
               same_clock xss ->
               same_clock yss ->
               (forall n, absent_list (xss n) <-> absent_list (yss n)) ->
               Forall (msem_equation bk H M) n.(n_eqs) ->
               msem_node f xss M yss.

    Definition msem_equations bk H M eqs := Forall (msem_equation bk H M) eqs.

  End NodeSemantics.

  (** ** Induction principle for [msem_equation] and [msem_node] *)

  (** The automagically-generated induction principle is not strong
enough: it does not support the internal fixpoint introduced by
[Forall] *)

  Section msem_node_mult.

    Variable G: global.

    Variable P_equation: stream bool -> history -> memories -> equation -> Prop.
    Variable P_reset: ident -> stream bool -> stream (list value) -> memories -> stream (list value) -> Prop.
    Variable P_node: ident -> stream (list value) -> memories -> stream (list value) -> Prop.

    Hypothesis EqDefCase:
      forall bk H M x ck xs ce,
        sem_var bk H x xs ->
        sem_caexp bk H ck ce xs ->
        P_equation bk H M (EqDef x ck ce).

    Hypothesis EqAppCase:
      forall bk H M x xs ck f M' arg ls xss,
        Some x = hd_error xs ->
        sub_inst x M M' ->
        sem_laexps bk H ck arg ls ->
        sem_vars bk H xs xss ->
        msem_node G f ls M' xss ->
        P_node f ls M' xss ->
        P_equation bk H M (EqApp xs ck f arg None).

    Hypothesis EqResetCase:
      forall bk H M x xs ck f M' arg y ck_r ys ls xss,
        Some x = hd_error xs ->
        sub_inst x M M' ->
        sem_laexps bk H ck arg ls ->
        sem_vars bk H xs xss ->
        sem_var bk H y ys ->
        msem_reset G f (reset_of ys) ls M' xss ->
        P_reset f (reset_of ys) ls M' xss ->
        P_equation bk H M (EqApp xs ck f arg (Some (y, ck_r))).

    Hypothesis EqFbyCase:
      forall bk H M x ck ls xs c0 le,
        sem_laexp bk H ck le ls ->
        sem_var bk H x xs ->
        mfby x (sem_const c0) ls M xs ->
        P_equation bk H M (EqFby x ck c0 le).

    Hypothesis ResetCase:
      forall f r xss M yss,
        (forall n, msem_node G f
                        (mask (all_absent (xss 0)) n r xss)
                        (mmask n r M)
                        (mask (all_absent (yss 0)) n r yss)) ->
        (forall k, P_node f
                     (mask (all_absent (xss 0)) k r xss)
                     (mmask k r M)
                     (mask (all_absent (yss 0)) k r yss)) ->
        P_reset f r xss M yss.

    Hypothesis NodeCase:
      forall bk H f xss M yss n,
        clock_of xss bk ->
        find_node f G = Some n ->
        sem_vars bk H (map fst n.(n_in)) xss ->
        sem_vars bk H (map fst n.(n_out)) yss ->
        same_clock xss ->
        same_clock yss ->
        (forall n, absent_list (xss n) <-> absent_list (yss n)) ->
        Forall (msem_equation G bk H M) n.(n_eqs) ->
        Forall (P_equation bk H M) n.(n_eqs) ->
        P_node f xss M yss.

    Fixpoint msem_equation_mult
             (b: stream bool) (H: history) (M: memories) (e: equation)
             (Sem: msem_equation G b H M e) {struct Sem}
      : P_equation b H M e
    with msem_reset_mult
           (f: ident) (r: stream bool)
           (xss: stream (list value))
           (M: memories)
           (oss: stream (list value))
           (Sem: msem_reset G f r xss M oss) {struct Sem}
         : P_reset f r xss M oss
    with msem_node_mult
           (f: ident)
           (xss: stream (list value))
           (M: memories)
           (oss: stream (list value))
           (Sem: msem_node G f xss M oss) {struct Sem}
         : P_node f xss M oss.
    Proof.
      - destruct Sem; eauto.
      - destruct Sem; eauto.
      - destruct Sem; eauto.
        eapply NodeCase; eauto.
        (* clear H1 defd vout good. *)
         induction H7; auto.
    Qed.

    Combined Scheme msem_equation_node_ind from msem_equation_mult, msem_node_mult, msem_reset_mult.

  End msem_node_mult.

  Definition msem_nodes (G: global) : Prop :=
    Forall (fun no => exists xs M ys, msem_node G no.(n_name) xs M ys) G.

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
  (*   rewrite Hbk in *. *)
  (*   destruct eqn. *)
  (*   constructor. *)
  (*   apply SCabs; try apply subrate_clock. *)

  (*   ; *)
  (*     try repeat *)
  (*         match goal with *)
  (*         | |- rhs_absent_instant false _ (EqDef _ _ _) => *)
  (*           constructor *)
  (*         | |- rhs_absent_instant false _ (EqFby _ _ _ _) => *)
  (*           constructor *)
  (*         | |- sem_caexp_instant false _ ?ck ?ce absent => *)
  (*           apply SCabs *)
  (*         | |- sem_clock_instant false _ ?ck false => *)
  (*           apply subrate_clock *)
  (*         | |- sem_laexp_instant false _ ?ck ?le absent => *)
  (*           apply SLabs *)
  (*         | |- sem_laexps_instant false _ ?ck ?les _ => *)
  (*           apply SLabss; eauto *)
  (*         end. *)
  (*   clear Hsem Habs. *)
  (*   apply AEqApp with (vs:=map (fun _ =>absent) l). *)
  (*   apply SLabss; auto. apply subrate_clock. *)
  (*   induction l; [constructor|]. *)
  (*   apply Forall_cons; auto. *)
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
    forall n G f xs M ys,
      Ordered_nodes (n :: G) ->
      msem_node (n :: G) f xs M ys ->
      n.(n_name) <> f ->
      msem_node G f xs M ys.
  Proof.
    Hint Constructors msem_equation msem_reset.
    intros ** Hord Hsem Hnf.
    revert Hnf.
    induction Hsem as [| | | |?????? IH |???????? Hf ?????? IH ]
        using msem_node_mult
      with (P_equation := fun bk H M eq =>
                            ~Is_node_in_eq n.(n_name) eq ->
                            msem_equation G bk H M eq)
           (P_reset := fun f r xss M yss =>
                         n_name n <> f ->
                         msem_reset G f r xss M yss); eauto.
    - intro Hnin.
      econstructor; eauto.
      apply IHHsem. intro Hnf; apply Hnin; rewrite Hnf. constructor.
    - intro Hnin.
      econstructor; eauto.
      apply IHHsem. intro Hnf; apply Hnin; rewrite Hnf. constructor.
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
    forall n G f r xs M ys,
      Ordered_nodes (n :: G) ->
      msem_reset (n :: G) f r xs M ys ->
      n.(n_name) <> f ->
      msem_reset G f r xs M ys.
  Proof.
    intros ** Sem ?.
    inversion_clear Sem as [????? SemN].
    constructor; eauto using msem_node_cons.
  Qed.

  Lemma msem_node_cons2:
    forall n G f xs M ys,
      Ordered_nodes G ->
      msem_node G f xs M ys ->
      Forall (fun n' => n_name n <> n_name n') G ->
      msem_node (n :: G) f xs M ys.
  Proof.
    Hint Constructors msem_equation.
    intros ** Hord Hsem Hnin.
    assert (Hnin':=Hnin).
    revert Hnin'.
    induction Hsem as [| | | |?????? IH|?????? n' ? Hfind ????? Heqs IH]
        using msem_node_mult
      with (P_equation := fun bk H M eq =>
                            ~Is_node_in_eq n.(n_name) eq ->
                            msem_equation (n :: G) bk H M eq)
           (P_reset := fun f r xss M yss =>
                         Forall (fun n' : node => n_name n <> n_name n') G ->
                         msem_reset (n :: G) f r xss M yss); eauto.
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
    forall n G f r xs M ys,
      Ordered_nodes G ->
      msem_reset G f r xs M ys ->
      Forall (fun n' => n_name n <> n_name n') G ->
      msem_reset (n :: G) f r xs M ys.
  Proof.
    intros ** Sem ?.
    inversion_clear Sem as [????? SemN].
    constructor; eauto using msem_node_cons2.
  Qed.

  Lemma msem_equation_cons2:
    forall G bk H M eqs n,
      Ordered_nodes (n :: G) ->
      Forall (msem_equation G bk H M) eqs ->
      ~Is_node_in n.(n_name) eqs ->
      Forall (msem_equation (n :: G) bk H M) eqs.
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
    destruct Heq as [| |? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hmsem|];
      try now eauto.
    - eauto using msem_node_cons2.
    - eauto using msem_reset_cons2.
  Qed.

  Lemma find_node_msem_node:
    forall G f,
      msem_nodes G ->
      find_node f G <> None ->
      exists xs M ys,
        msem_node G f xs M ys.
  Proof.
    intros G f Hnds Hfind.
    apply find_node_Exists in Hfind.
    apply Exists_exists in Hfind.
    destruct Hfind as [nd [Hin Hf]].
    unfold msem_nodes in Hnds.
    rewrite Forall_forall in Hnds.
    apply Hnds in Hin.
    destruct Hin as [xs [M [ys Hmsem]]].
    exists xs; exists M; exists ys.
    rewrite Hf in *.
    exact Hmsem.
  Qed.

  (* TODO: Tidy this up... *)
  Lemma Forall_msem_equation_global_tl:
    forall n G bk H M eqs,
      Ordered_nodes (n :: G) ->
      (forall f, Is_node_in f eqs -> find_node f G <> None) ->
      ~ Is_node_in n.(n_name) eqs ->
      Forall (msem_equation (n :: G) bk H M) eqs ->
      Forall (msem_equation G bk H M) eqs.
  Proof.
    intros ? ? ? ? ? ? Hord.
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

  Definition add_mems (y: ident) (ms: stream val) (M: memories): memories :=
    fun n => madd_mem y (ms n) (M n).

  Lemma mfby_add_mems:
    forall x v0 ls M xs y ms,
      x <> y ->
      mfby x v0 ls M xs ->
      mfby x v0 ls (add_mems y ms M) xs.
  Proof.
    unfold add_mems.
    intros ** Fby; inversion_clear Fby as [?????? Spec].
    constructor.
    - rewrite mfind_mem_gso; auto.
    - intro n; rewrite 2 mfind_mem_gso; auto.
      exact (Spec n).
  Qed.

  Definition add_objs (y: ident) (M' M: memories): memories :=
    fun n => madd_obj y (M' n) (M n).

  Lemma mfby_add_objs:
    forall x v0 ls M xs y M',
      mfby x v0 ls M xs ->
      mfby x v0 ls (add_objs y M' M) xs.
  Proof.
    inversion 1; econstructor; eauto.
  Qed.

  Hint Resolve mfby_add_mems mfby_add_objs.

  Lemma msem_equation_madd_mem:
    forall G bk H M x ms eqs,
      ~Is_defined_in_eqs x eqs ->
      Forall (msem_equation G bk H M) eqs ->
      Forall (msem_equation G bk H (add_mems x ms M)) eqs.
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

  Lemma msem_equation_madd_obj:
    forall G bk H M M' x eqs,
      ~Is_defined_in_eqs x eqs ->
      Forall (msem_equation G bk H M) eqs ->
      Forall (msem_equation G bk H (add_objs x M' M)) eqs.
  Proof.
    Hint Constructors msem_equation.
    intros * Hnd Hsem.
    induction eqs as [|eq eqs IH]; [now constructor|].
    apply not_Is_defined_in_cons in Hnd.
    destruct Hnd as [Hnd Hnds].
    apply Forall_cons2 in Hsem.
    destruct Hsem as [Hsem Hsems].
    constructor; [|now apply IH with (1:=Hnds) (2:=Hsems)].
    destruct Hsem as [|? ? ? x' ? ? ? ? ? ? ? Hsome
                         |? ? ? x' ? ? ? ? ? ? ? ? ? ? Hsome|];
      eauto;
      assert (sub_inst x' (add_objs x M' M) M'0)
        by (apply not_Is_defined_in_eq_EqApp in Hnd;
            unfold sub_inst, add_objs; intro; rewrite mfind_inst_gso; auto;
            intro; subst x; destruct xs; inv Hsome; apply Hnd; now constructor);
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

  Lemma sem_msem_eq:
    forall G bk H eqs M eq mems argIn,
      (forall f xs ys,
          sem_node G f xs ys ->
          exists M, msem_node G f xs M ys) ->
      (forall f r xs ys,
          sem_reset G f r xs ys ->
          exists M, msem_reset G f r xs M ys) ->
      sem_equation G bk H eq ->
      Is_well_sch mems argIn (eq :: eqs) ->
      Forall (msem_equation G bk H M) eqs ->
      exists M', Forall (msem_equation G bk H M') (eq :: eqs).
  Proof.
    intros ** IH IH' Heq Hwsch Hmeqs.
    inversion Heq as [|? ? ? ? ? ? ? ? Hls Hxs Hsem
                         |? ? ? ? ? ? ? ? ? ? ? Hls Hxs Hy Hsem
                         |? ? ? ? ? ? ? ? Hle Hvar];
      match goal with H:_=eq |- _ => rewrite <-H in * end.
    - exists M.
      repeat (econstructor; eauto).
    - apply IH in Hsem as [M' Hmsem].
      exists (add_objs (hd Ids.default x) M' M).

      assert (exists i, Some i = hd_error x) as [i Hsome].
      {
        assert (Hlen: 0 < length x).
        {
          assert (length x = length (xs 0))
            by (specialize (Hxs 0); simpl in Hxs; eapply Forall2_length; eauto).

          assert (exists n, length (map fst n.(n_out)) = length (xs 0)
                       /\ 0 < length n.(n_out)) as (n & ? & ?).
          {
            inv Hmsem.
            exists n; split; auto.
            - eapply Forall2_length; eauto.
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
      {
        destruct x; simpl in *; try discriminate.
        injection Hsome; congruence.
      }
      rewrite Hhd; clear Hhd.

      constructor.
      + econstructor; eauto.
        unfold sub_inst, add_objs; intro; now apply mfind_inst_gss.
      + inversion_clear Hwsch.
        assert (Is_defined_in_eq i (EqApp x ck f arg None)).
        {
          constructor. destruct x; try discriminate.
          injection Hsome. intro; subst i. constructor (auto).
        }
        now apply msem_equation_madd_obj; auto.

    - pose proof Hsem as Hsem'.
      apply IH' in Hsem as [M' Hmsem].
      exists (add_objs (hd Ids.default x) M' M).

      assert (exists i, Some i = hd_error x) as [i Hsome].
      {
        assert (Hlen: 0 < length x).
        {
          assert (length x = length (xs 0))
            by (specialize (Hxs 0); simpl in Hxs; eapply Forall2_length; eauto).

          assert (exists n, length (map fst n.(n_out)) = length (xs 0)
                       /\ 0 < length n.(n_out)) as (n & ? & ?).
          {
            inversion_clear Hmsem as [? ? ? ? ? Hmsem'].
            specialize (Hmsem' 0); inv Hmsem'.
            exists n; split; auto.
            - unfold sem_vars, lift in H9; specialize (H9 0).
              apply Forall2_length in H9; rewrite H9.
              rewrite mask_length; auto.
              inversion_clear Hsem' as [? ? ? ? Hsem].
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
      {
        destruct x; simpl in *; try discriminate.
        injection Hsome; congruence.
      }

      rewrite Hhd; clear Hhd.

      constructor.
      + econstructor; eauto.
        unfold sub_inst, add_objs; intro. now apply mfind_inst_gss.
      + inversion_clear Hwsch.
        assert (Is_defined_in_eq i (EqApp x ck f arg (Some (y, ck_r)))).
        {
          constructor. destruct x; try discriminate.
          injection Hsome. intro; subst i. constructor (auto).
        }
        apply msem_equation_madd_obj; auto.

    - exists (add_mems x (hold (sem_const c0) ls) M).
      constructor.
      + unfold add_mems.
        do 2 (econstructor; eauto).
        * now apply mfind_mem_gss.
        (* * reflexivity. *)
        * rewrite H1; unfold fby; simpl.
          intro n; destruct (ls n); auto;
            repeat rewrite mfind_mem_gss; auto.
      + inversion_clear Hwsch.
        apply msem_equation_madd_mem; eauto.
  Qed.

  (* XXX: for this lemma, and the ones before/after it, factorize 'G',
'bk' and possibly other variables in a Section *)
  Corollary sem_msem_eqs:
    forall G bk H eqs mems argIn,
      (forall f xs ys,
          sem_node G f xs ys ->
          exists M, msem_node G f xs M ys) ->
      (forall f r xs ys,
          sem_reset G f r xs ys ->
          exists M, msem_reset G f r xs M ys) ->
      Is_well_sch mems argIn eqs ->
      Forall (sem_equation G bk H) eqs ->
      exists M', Forall (msem_equation G bk H M') eqs.
  Proof.
    intros ** IH Hwsch Heqs.
    induction eqs as [|eq eqs IHeqs]; [exists (fun n => empty_memory _); now constructor|].
    apply Forall_cons2 in Heqs as [Heq Heqs].
    eapply IHeqs with (1:=Is_well_sch_cons _ _ _ _ Hwsch)
      in Heqs
      as [M Heqs]; eauto.
    eapply sem_msem_eq; eauto.
  Qed.

  Require Import Coq.Logic.ClassicalChoice.

  Lemma bar:
    forall x F k M' r,
      (forall k k', F k 0 = F k' 0) ->
      sub_inst x (F k) M' ->
      sub_inst x (mmask k r (fun n => F (count r n) n)) M'.
  Proof.
    unfold sub_inst; intros ** Init Sub n.
    induction n; simpl.
    - specialize (Sub 0); erewrite Init; eauto.
    - destruct (nat_compare (count r n) k) eqn: E.
      + destruct (r (S n)) eqn: Rsn.
        * assert (nat_compare (S (count r n)) k = Gt) as ->
              by (rewrite <-nat_compare_gt; apply Gt.le_gt_S;
                  apply nat_compare_eq_iff in E; omega).
          assert (EqNat.beq_nat (S (count r n)) (S k) = true) as ->
              by now apply EqNat.beq_nat_true_iff, eq_S, nat_compare_eq.
          simpl.
          (* rewrite mmask_eq in IHn by now apply nat_compare_eq. *)
(*           destruct (r n) eqn: Rn. *)
(*           simpl in IHn. ; rewrite Rn in IHn. *)
(*           unfold count in IHn. *)
(* assert (EqNat.beq_nat k (count rs n) = true) as -> *)
(*           by now rewrite NPeano.Nat.eqb_sym, EqNat.beq_nat_true_iff, *)
(*              <-nat_compare_eq_iff. *)
(*       rewrite mmask_eq by now apply nat_compare_eq_iff. *)
(*       destruct (rs (S n)). *)
(*       + assert (nat_compare (S (count rs n)) k = Gt) as -> *)
(*             by (rewrite <-nat_compare_gt; apply Gt.le_gt_S; *)
(*                 apply nat_compare_eq_iff in E; omega). *)
(*         assert (EqNat.beq_nat (S (count rs n)) (S k) = true) as -> *)
(*             by now apply EqNat.beq_nat_true_iff, eq_sym, *)
(*                eq_S, EqNat.beq_nat_true_iff. *)
(*         destruct (ls n), (rs n); simpl; intuition; *)
(*           rewrite H2 in Spec; rewrite Find; intuition. *)
(*       + rewrite E. *)
(*         destruct (ls n), (rs n); intuition; *)
(*           rewrite H0 in Spec; rewrite Find; intuition. *)
(*     - assert (EqNat.beq_nat k (count rs n) = false) as -> *)
(*           by (apply nat_compare_lt in E; apply EqNat.beq_nat_false_iff; *)
(*               intro; subst; omega). *)
(*       rewrite mmask_lt by (now apply nat_compare_lt); rewrite Find. *)
(*       destruct (rs (S n)). *)
(*       + destruct (nat_compare (S (count rs n)) k) eqn: E'; intuition. *)
(*         apply nat_compare_lt in E; apply nat_compare_gt in E'; omega. *)
(*       + rewrite E; auto. *)
(*     - assert (EqNat.beq_nat k (count rs n) = false) as -> *)
(*           by (apply nat_compare_gt in E; apply EqNat.beq_nat_false_iff; *)
(*               intro; subst; omega). *)
(*       destruct (rs (S n)). *)
(*       + assert (nat_compare (S (count rs n)) k = Gt) as -> *)
(*             by (rewrite <-nat_compare_gt in *; omega). *)
(*         assert (EqNat.beq_nat (S (count rs n)) (S k) = false) as -> *)
(*             by (apply EqNat.beq_nat_false_iff, not_eq_S, *)
(*                 not_eq_sym; apply nat_compare_gt in E; omega). *)
(*         simpl. *)
(*         destruct (mfind_mem x (mmask k rs M n)) eqn: Find'; auto. *)
(*         eapply mmask_mfby; eauto using mfby. *)
(*       + rewrite E, Bool.andb_false_r. *)
(*         destruct (mfind_mem x (mmask k rs M n)) eqn: Find'; auto. *)
          (*         eapply mmask_mfby; eauto using mfby. *)
          Admitted.

  (* Require Import Morphisms. *)

  Require Import Setoid.

  Add Parametric Morphism k r : (mmask k r)
      with signature eq_str ==> eq_str
        as mmask_eq_str.
  Proof.
    intros ** E n.
    induction n; simpl; auto.
    rewrite IHn.
    destruct (nat_compare (if r (S n) then S (count r n) else count r n) k); auto.
    destruct (EqNat.beq_nat (if r (S n) then S (count r n) else count r n) (S k) && r (S n)); auto.
  Qed.

  Add Parametric Morphism x v0 ls : (mfby x v0 ls)
      with signature eq_str ==> eq ==> Basics.impl
        as mfby_eq_str.
  Proof.
    intros ** E ? Fby.
    inversion_clear Fby as [?????? Spec]; constructor.
    - now rewrite <-E.
    - intro n; specialize (Spec n).
      now repeat rewrite <-E.
  Qed.

  Add Parametric Morphism x : (sub_inst x)
      with signature eq_str ==> eq ==> Basics.impl
        as sub_inst_eq_str.
  Proof.
    intros ** E ? Sub n; specialize (Sub n).
    now rewrite <-E.
  Qed.

  Add Parametric Morphism G bk H: (msem_equation G bk H)
      with signature eq_str ==> eq ==> Basics.impl
        as msem_equation_eq_str.
  Proof.
    intros ** E ? Eq.
    induction Eq; eauto using (msem_equation); econstructor; eauto.
    - now rewrite <-E.
    - now rewrite <-E.
    - now rewrite <-E.
  Qed.

  Add Parametric Morphism G f: (msem_node G f)
      with signature eq ==> eq_str ==> eq ==> Basics.impl
        as msem_node_eq_str.
  Proof.
    intros ** E ? Node.
    inversion_clear Node as [?????????????? Heqs].
    econstructor; eauto.
    induction (n_eqs n); auto.
    inv Heqs.
    constructor; auto.
    now rewrite <-E.
  Qed.

  Add Parametric Morphism G f: (msem_reset G f)
      with signature eq ==> eq ==> eq_str ==> eq ==> Basics.impl
        as msem_reset_eq_str.
  Proof.
    intros ** E ? Res.
    inversion_clear Res as [????? Node].
    constructor; intro k.
    now rewrite <-E.
  Qed.


  (* Fixpoint depth {A} (m: memory A) : nat := *)
  (*   match m *)

  (* Program Fixpoint same_mem {A} (m m': memory A) {measure (depth m)}: Prop := *)
  (*   (forall x a, *)
  (*       mfind_mem x m = Some a -> *)
  (*       mfind_mem x m' = Some a) *)
  (*   /\ *)
  (*   (forall x m1 m1', *)
  (*       mfind_inst x m = Some m1 -> *)
  (*       mfind_inst x m' = Some m1' *)
  (*       /\ same_mem m1 m1'). *)

  (* Inductive same_mem: memories -> memories -> Prop := *)
  (*   same_mem_intro: *)
  (*     forall M M', *)
  (*       (forall x m m', sub_inst x M m -> *)
  (*                  sub_inst x M' m' -> *)
  (*                  same_mem m m') -> *)
  (*       (forall n x v, mfind_mem x (M n) = Some v -> *)
  (*                 mfind_mem x (M' n) = Some v) -> *)
  (*       same_mem M M'. *)

  (* Lemma same_mem_refl: *)
  (*   forall M, *)
  (*     same_mem M M. *)
  (* Proof. *)
  (*   constructor; intros. *)
  (*   - constructor. *)
  (*   intros ** n; reflexivity. *)
  (* Qed. *)

  (* Lemma eq_str_sym: *)
  (*   forall {A} (xs xs': stream A), *)
  (*     xs ≈ xs' -> xs' ≈ xs. *)
  (* Proof. *)
  (*   intros ** E n; auto. *)
  (* Qed. *)

  (* Lemma eq_str_trans: *)
  (*   forall {A} (xs ys zs: stream A), *)
  (*     xs ≈ ys -> ys ≈ zs -> xs ≈ zs. *)
  (* Proof. *)
  (*   intros ** E1 E2 n; auto. *)
  (*   rewrite E1; auto. *)
  (* Qed. *)

  (* Add Parametric Relation A : (stream A) (@eq_str A) *)
  (*     reflexivity proved by (@eq_str_refl A) *)
  (*     symmetry proved by (@eq_str_sym A) *)
  (*     transitivity proved by (@eq_str_trans A) *)
  (*       as eq_str_rel. *)


  (* Lemma msem_node_init: *)
  (*   forall G f xs M ys, *)
  (*     msem_node G f xs M ys ->  *)
  Theorem sem_msem_node:
    forall G f xs ys,
      Welldef_global G ->
      sem_node G f xs ys ->
      exists M, msem_node G f xs M ys.
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
                 exists M, msem_node G f xs M ys) as IHG'
          by auto.
      assert (forall f r xs ys,
                 sem_reset G f r xs ys ->
                 exists M, msem_reset G f r xs M ys) as IHG''.
      { clear - IHG'.
        intros ** Sem.
        inversion_clear Sem as [???? Sem'].
        assert (forall n, exists M, msem_node G f (mask (all_absent (xs 0)) n r xs) M
                                    (mask (all_absent (ys 0)) n r ys)) as Msem
            by (intro; specialize (Sem' n); apply IHG' in Sem'; auto).
        apply choice in Msem as (F & Msem).

        assert (forall k k', F k 0 = F k' 0) as Init.
        { intros k k'.
          pose proof (Msem k) as Semk; pose proof (Msem k') as Semk'.
          inversion_clear Semk as [???????? Find ????? Heqs Hnil];
            inversion_clear Semk' as [???????? Find' ????? Heqs' Hnil'].
          rewrite Find in Find'; inv Find'.
          induction (n_eqs n0) as [|e]; auto.
          - admit.
          - inv Heqs; inv Heqs'; auto.
        }

        assert (forall n k, r n = true -> F (count r n) n = F k 0) as Heq by admit.

        assert (forall n k k', count r n < k -> F k n = F k' 0) as Hlt by admit.

        (* assert (forall n k k', count r n > k -> *)
                          (* F k n = if EqNat.beq_nat (count r n) (S k) && rs n *)
                                  (* then  n else M' (pred n)F k' 0) as Hlt by admit. *)

        exists (fun n => F (count r n) n).
        constructor.
        intro k; specialize (Msem k).

        assert (mmask' k r (fun n' => F (count r n') n') (F k)) as Spec.
        { split; auto.
          intro.
          (* induction n. *)
          (* - admit. *)
          - destruct (nat_compare (count r n) k) eqn: E.
            + apply nat_compare_eq in E; subst.
              destruct (r n) eqn: Rn; auto.
            + apply nat_compare_lt in E; auto.
            + destruct (EqNat.beq_nat (count r n) (S k)) eqn: E'; simpl.
              * destruct (r n).
                admit.
                admit.
              * admit.

        }

        assert (mmask k r (fun n' => F (count r n') n') ≈ F k) as ->; auto.
        destruct Spec as (? & Spec).
        induction n.
        - simpl in *; auto.
        - rewrite Spec.
          destruct (nat_compare (count r (S n)) k) eqn: E.
          + apply nat_compare_eq in E; subst.
            rewrite mmask_eq; auto.
          + apply nat_compare_lt in E.
            rewrite mmask_lt; auto.
          + apply nat_compare_gt in E.
              rewrite mmask_gt; auto.
              simpl; rewrite IHn; auto.
        }

      inversion_clear Hwdef as [|??? neqs].
      simpl in neqs; unfold neqs in *.
      assert (exists M', Forall (msem_equation G bk H M') n.(n_eqs))
        as (M & Hmsem) by now eapply sem_msem_eqs; eauto.
      exists M.
      econstructor; eauto.
      + simpl; now rewrite Hnf.
      + eapply msem_equation_cons2; eauto.
    - apply ident_eqb_neq in Hnf.
      apply sem_node_cons with (1:=Hord) (3:=Hnf) in Hsem.
      inv Hord.
      eapply IHG in Hsem as [M]; eauto.
      exists M.
      now eapply msem_node_cons2; eauto.
  Qed.

  (* We use the mem-semantics to assert the absence of applications
  with no return arguments. This is a bit of a hack, if you ask me. So
  don't ask. *)
  Lemma non_trivial_EqApp:
    forall G bk H M eqs ,
      Forall (msem_equation G bk H M) eqs ->
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
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Op)
       (Clks  : CLOCKS      Ids)
       (Syn   : NLSYNTAX    Ids Op       Clks)
       (Str   : STREAM             Op OpAux)
       (Ord   : ORDERED     Ids Op       Clks Syn)
       (Sem   : NLSEMANTICS Ids Op OpAux Clks Syn Str Ord)
       (Mem   : MEMORIES    Ids Op       Clks Syn)
       (IsD   : ISDEFINED   Ids Op       Clks Syn         Mem)
       (IsV   : ISVARIABLE  Ids Op       Clks Syn         Mem IsD)
       (IsF   : ISFREE      Ids Op       Clks Syn)
       (NoD   : NODUP       Ids Op       Clks Syn         Mem IsD IsV)
       (WeF   : WELLFORMED  Ids Op       Clks Syn     Ord Mem IsD IsV IsF NoD)
       <: MEMSEMANTICS Ids Op OpAux Clks Syn Str Ord Sem Mem IsD IsV IsF NoD WeF.
  Include MEMSEMANTICS Ids Op OpAux Clks Syn Str Ord Sem Mem IsD IsV IsF NoD WeF.
End MemSemanticsFun.
