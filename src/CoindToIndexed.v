From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Setoid.
From Coq Require Import Morphisms.
From Coq Require Import Program.Tactics.

From Velus Require Import Common.
From Velus Require Import FunctionalEnvironment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import IndexedStreams.
From Velus Require Import CoindStreams.

Module Type COINDTOINDEXED
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS Ids Op OpAux)
       (Import CStr  : COINDSTREAMS Ids Op OpAux Cks)
       (Import IStr  : INDEXEDSTREAMS Ids Op OpAux Cks).

    (** * BASIC CORRESPONDENCES *)

    (** ** Definitions  *)

    (** Translate a coinductive Stream into an indexed stream.
        The result stream is the function which associates the [n]th element of
        the input Stream to each [n].
     *)
    Definition tr_Stream {A} (xs: Stream A) : stream A :=
      fun n => xs # n.

    (** Translate a list of Streams into a stream of list. *)
    Definition tr_Streams {A} (xss: list (Stream A)) : stream (list A) :=
      fun n => List.map (fun xs => tr_Stream xs n) xss.

    (** Translate an history from coinductive to indexed world.
        Every element of the history is translated.
     *)
    Definition tr_history {K} (H: @CStr.history K) : history :=
      fun n => FEnv.map (fun xs => tr_Stream xs n) H.
    Global Hint Unfold tr_history : fenv.

    (** ** Properties  *)

    (** Indexing a translated Stream at [0] is taking the head of the source
        Stream. *)
    Lemma tr_Stream_0:
      forall {A} (xs: Stream A) x,
        tr_Stream (x ⋅ xs) 0 = x.
    Proof. reflexivity. Qed.

    (** Another version of the previous lemma *)
    Lemma tr_Stream_hd:
      forall {A} (xs: Stream A),
        hd xs = tr_Stream xs 0.
    Proof. reflexivity. Qed.

    (** Indexing a translated Stream at [S n] is indexing the tail of the source
        Stream at [n]. *)
    Lemma tr_Stream_S:
      forall {A} (xs: Stream A) x n,
        tr_Stream (x ⋅ xs) (S n) = tr_Stream xs n.
    Proof. reflexivity. Qed.

    (** Another version of the previous lemma.  *)
    Lemma tr_Stream_tl:
      forall {A} (xs: Stream A) n,
        tr_Stream (tl xs) n = tr_Stream xs (S n).
    Proof. reflexivity. Qed.

    Lemma tr_Stream_nth {A}: forall (xs : Stream A) n,
        tr_Stream xs n = xs # n.
    Proof.
      intros xs n. revert xs.
      induction n; intros; unfold_St xs.
      rewrite tr_Stream_0, Str_nth_0. reflexivity.
      rewrite tr_Stream_S, Str_nth_S. eauto.
    Qed.

    Corollary tr_Stream_const:
      forall {A} (c: A) n,
        tr_Stream (Streams.const c) n = c.
    Proof.
      intros. rewrite tr_Stream_nth.
      apply const_nth.
    Qed.

    (** [tr_Stream] is compatible wrt to [EqSt]. *)
    Add Parametric Morphism A : (@tr_Stream A)
        with signature @EqSt A ==> eq ==> eq
          as tr_Stream_morph.
    Proof.
      intros xs ys Exs n.
      revert xs ys Exs; induction n; intros; destruct xs, ys; inv Exs.
      - rewrite 2 tr_Stream_0; auto.
      - rewrite 2 tr_Stream_S; auto.
    Qed.

    (** The counterpart of [tr_Stream_tl] for lists of Streams. *)
    Lemma tr_Streams_tl:
      forall A (xss: list (Stream A)) n,
        tr_Streams (List.map (tl (A:=A)) xss) n = tr_Streams xss (S n).
    Proof.
      intros; unfold tr_Streams; rewrite map_map; auto.
    Qed.

    Lemma tr_Streams_hd:
      forall A (xss: list (Stream A)),
        tr_Streams xss 0 = List.map (hd (A:=A)) xss.
    Proof.
      reflexivity.
    Qed.

    (** The counterpart of [tr_Stream_tl] for histories. *)
    Lemma tr_history_tl {K}:
      forall n (H: @CStr.history K),
        FEnv.Equiv eq (tr_history H (S n)) (tr_history (history_tl H) n).
    Proof.
      intros * x. simpl_fenv.
      destruct (H x); simpl; reflexivity.
    Qed.

    Fact tr_history_find_orel {K} : forall (H H': @CStr.history K) x x',
        orel (@EqSt _) (H x) (H' x') ->
        (forall n, orel (@eq _) ((tr_history H n) x) ((tr_history H' n) x')).
    Proof.
      intros * Horel n.
      simpl_fenv. unfold tr_Stream.
      inv Horel; simpl; auto with datatypes.
      rewrite H2; auto with datatypes.
    Qed.

    Fact tr_history_find_orel_mask {K} : forall (H H': @CStr.history K) rs k x x',
        orel (fun v1 v2 => EqSt (CStr.maskv k rs v1) v2) (H x) (H' x') ->
        (forall n, orel (fun v1 v2 => (if (CStr.count rs) # n =? k then v1 else absent) = v2) ((tr_history H n) x) ((tr_history H' n) x')).
    Proof.
      intros * Horel n.
      simpl_fenv. unfold tr_Stream.
      inv Horel; simpl; auto with datatypes.
      constructor; auto.
      rewrite <- H2, maskv_nth. reflexivity.
    Qed.

    Fact tr_history_find_orel_unmask {K} : forall (H H': @CStr.history K) rs k x x',
        orel (fun v1 v2 => EqSt v1 (CStr.maskv k rs v2)) (H x) (H' x') ->
        (forall n, orel (fun v1 v2 => (v1 = if (CStr.count rs) # n =? k then v2 else absent)) ((tr_history H n) x) ((tr_history H' n) x')).
    Proof.
      intros * Horel n.
      simpl_fenv. unfold tr_Stream.
      inv Horel; simpl; auto with datatypes.
      constructor; auto.
      rewrite H2, maskv_nth. reflexivity.
    Qed.

    Fact tr_Stream_ac {A} : forall xs n,
        tr_Stream (@abstract_clock A xs) n = match (xs # n) with absent => false | _ => true end.
    Proof.
      intros xs n.
      rewrite tr_Stream_nth. apply ac_nth.
    Qed.

    (** * SEMANTICS CORRESPONDENCE *)

    (** ** Variables *)

    Lemma sem_var_impl {K}:
      forall (H: @CStr.history K) x xs,
      CStr.sem_var H x xs ->
      sem_var (tr_history H) x (tr_Stream xs).
    Proof.
      intros * Find n.
      unfold sem_var_instant.
      inversion_clear Find as [???? Find' E].
      simpl_fenv.
      rewrite Find', E; simpl; auto.
    Qed.
    Global Hint Resolve sem_var_impl : coindstreams indexedstreams nlsem.

    (** ** Semantics of clocks *)

    (** We can then deduce the correspondence lemma for [sem_clock]. *)
    Lemma sem_clock_impl:
      forall H b ck bs,
        CStr.sem_clock H b ck bs ->
        IStr.sem_clock (tr_Stream b) (tr_history H) ck (tr_Stream bs).
    Proof.
      intros * Hsemck n. generalize dependent bs.
      induction ck; intros * Hsemck.
      - inv Hsemck. rewrite H1. constructor.
      - inv Hsemck. apply IHck in H6.
        apply sem_var_impl in H8. specialize (H8 n).
        repeat rewrite tr_Stream_nth in *.
        apply whenb_nth with (n:=n) in H9 as [(Hb&Hx&Hy)|[(?&Hb&Hx&?&Hy)|(Hb&Hx&Hy)]];
          rewrite Hb in *; rewrite Hx in *; rewrite Hy in *.
        1,3:constructor; auto.
        eapply Son_abs2; eauto.
    Qed.
    Global Hint Resolve sem_clock_impl : indexedstreams coindstreams nlsem.

End COINDTOINDEXED.

Module CoindToIndexedFun
       (Ids     : IDS)
       (Op      : OPERATORS)
       (OpAux   : OPERATORS_AUX          Ids Op)
       (Cks     : CLOCKS                 Ids Op OpAux)
       (CStr    : COINDSTREAMS           Ids Op OpAux Cks)
       (IStr    : INDEXEDSTREAMS         Ids Op OpAux Cks)
<: COINDTOINDEXED Ids Op OpAux Cks CStr IStr.
  Include COINDTOINDEXED Ids Op OpAux Cks CStr IStr.
End CoindToIndexedFun.
