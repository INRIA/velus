From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Setoid.
From Coq Require Import Morphisms.
From Coq Require Import NPeano.
From Coq Require Import Omega.
From Coq Require Import Program.Tactics.

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import IndexedStreams.
From Velus Require Import CoindStreams.

Module Type COINDTOINDEXED
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import CStr  : COINDSTREAMS Op OpAux)
       (Import IStr  : INDEXEDSTREAMS Op OpAux).

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
    Definition tr_history (H: CStr.history) : history :=
      fun n => Env.map (fun xs => tr_Stream xs n) H.

    (** ** Properties  *)

    (** Indexing a translated Stream at [0] is taking the head of the source
        Stream. *)
    Lemma tr_Stream_0:
      forall {A} (xs: Stream A) x,
        tr_Stream (x ⋅ xs) 0 = x.
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

    Lemma tr_Stream_const:
      forall {A} (c: A) n,
        tr_Stream (Streams.const c) n = c.
    Proof.
      induction n; rewrite unfold_Stream at 1; simpl.
      - now rewrite tr_Stream_0.
      - now rewrite tr_Stream_S.
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

    Fact tr_Streams_app:
      forall A (xss yss: list (Stream A)) n,
        tr_Streams (xss ++ yss) n = tr_Streams xss n ++ tr_Streams yss n.
    Proof.
      unfold tr_Streams; intros; rewrite map_app; auto.
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
    Lemma tr_history_tl:
      forall n H,
        tr_history H (S n) = tr_history (history_tl H) n.
    Proof.
      now repeat setoid_rewrite Env.map_map.
    Qed.

    (** * SEMANTICS CORRESPONDENCE *)

    (** ** Variables *)

    Lemma sem_var_impl:
      forall H x xs,
      CStr.sem_var H x xs ->
      sem_var (tr_history H) x (tr_Stream xs).
    Proof.
      intros * Find n.
      unfold sem_var_instant.
      inversion_clear Find as [???? Find' E].
      unfold tr_history, Env.map.
      rewrite Env.gmapi, Find', E; simpl; auto.
    Qed.
    Hint Resolve sem_var_impl.

    (** ** Semantics of clocks *)

    (** Give an indexed specification for [sem_clock] in the previous style,
        with added complexity as [sem_clock] depends on [H] and [b].
        We go by induction on the clock [ck] then by induction on [n] and
        inversion of the coinductive hypothesis as before. *)
    Hint Constructors sem_clock_instant.
    Lemma sem_clock_index:
      forall n H b ck bs,
        CStr.sem_clock H b ck bs ->
        (ck = Cbase
         /\ tr_Stream b n = tr_Stream bs n)
        \/
        (exists ck' x k c,
            ck = Con ck' x k
            /\ sem_clock_instant
                (tr_Stream b n) (tr_history H n) ck' true
            /\ sem_var_instant (tr_history H n) x
                                      (present c)
            /\ val_to_bool c = Some k
            /\ tr_Stream bs n = true)
        \/
        (exists ck' x k,
            ck = Con ck' x k
            /\ sem_clock_instant
                (tr_Stream b n) (tr_history H n) ck' false
            /\ sem_var_instant (tr_history H n) x absent
            /\ tr_Stream bs n = false)
        \/
        (exists ck' x k c,
            ck = Con ck' x (negb k)
            /\ sem_clock_instant
                (tr_Stream b n) (tr_history H n) ck' true
            /\ sem_var_instant (tr_history H n) x
                                      (present c)
            /\ val_to_bool c = Some k
            /\ tr_Stream bs n = false).
    Proof.
      Local Ltac rew_0 :=
        try match goal with
              H: tr_Stream _ _ = _ |- _ => now rewrite tr_Stream_0 in H
            end.
      intros n H b ck; revert n H b; induction ck as [|ck ? x k].
      - inversion_clear 1 as [? ? ? Eb| | |].
        left; intuition.
        now rewrite Eb.
      - intro n; revert x k; induction n; intros x k H bk bk' Indexed.
        + inversion_clear Indexed as [|? ? ? ? ? ? ? ? ? IndexedCk Hvar
                                     |? ? ? ? ? ? ? ? IndexedCk Hvar
                                     |? ? ? ? ? ? ? ? ? IndexedCk Hvar].
          * right; left.
            apply sem_var_impl in Hvar;
              unfold IStr.sem_var, IStr.lift in Hvar ; specialize (Hvar 0);
                rewrite tr_Stream_0 in Hvar.
            do 4 eexists; intuition; eauto.
            apply (IHck 0) in IndexedCk as [(? & E)|[|[]]]; destruct_conjs;
              subst; eauto; rew_0.
            rewrite E, tr_Stream_0; constructor.
          * right; right; left.
            apply sem_var_impl in Hvar;
              unfold IStr.sem_var, IStr.lift in Hvar ; specialize (Hvar 0);
                rewrite tr_Stream_0 in Hvar.
            do 3 eexists; intuition.
            apply (IHck 0) in IndexedCk as [(? & E)|[|[]]]; destruct_conjs;
              subst; eauto; rew_0.
            rewrite E, tr_Stream_0; constructor.
          * right; right; right.
            apply sem_var_impl in Hvar;
              unfold IStr.sem_var, IStr.lift in Hvar; specialize (Hvar 0);
                rewrite tr_Stream_0 in Hvar.
            do 4 eexists; intuition; eauto.
            apply (IHck 0) in IndexedCk as [(? & E)|[|[]]]; destruct_conjs;
              subst; eauto; rew_0.
            rewrite E, tr_Stream_0; constructor.
        + inversion_clear Indexed; rewrite <-tr_Stream_tl, tr_history_tl; eauto.
    Qed.

    (** We can then deduce the correspondence lemma for [sem_clock]. *)
    Corollary sem_clock_impl:
      forall H b ck bs,
        CStr.sem_clock H b ck bs ->
        sem_clock (tr_Stream b) (tr_history H) ck (tr_Stream bs).
    Proof.
      intros * Indexed n.
      apply (sem_clock_index n) in Indexed. destruct Indexed as [|[|[|]]];
                                              destruct_conjs;
        match goal with H: tr_Stream _ _ = _ |- _ => rewrite H end;
        subst; eauto.
    Qed.
    Hint Resolve sem_clock_impl.

End COINDTOINDEXED.

Module CoindToIndexedFun
       (Op      : OPERATORS)
       (OpAux   : OPERATORS_AUX          Op)
       (CStr    : COINDSTREAMS           Op OpAux)
       (IStr    : INDEXEDSTREAMS         Op OpAux)
<: COINDTOINDEXED Op OpAux CStr IStr.
  Include COINDTOINDEXED Op OpAux CStr IStr.
End CoindToIndexedFun.
