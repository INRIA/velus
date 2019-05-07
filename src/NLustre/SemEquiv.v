Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Coq.Sorting.Permutation.
Require Import Morphisms.

Require Import Coq.FSets.FMapPositive.
Require Import Velus.Common.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.NLOrdered.
Require Import Velus.CoreExpr.Stream.
Require Import Velus.NLustre.Streams.
Require Import Velus.NLustre.NLSemanticsCoInd.
Require Import Velus.NLustre.NLSemantics.
Require Import Velus.NLustre.CoIndToIndexed.
Require Import Velus.NLustre.IndexedToCoInd.
Require Import Velus.NLustre.NLInterpretor.

(* Require Import Setoid. *)
Module Type SEMEQUIV
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import OpAux   : OPERATORS_AUX    Op)
       (Import         : CLOCKS           Ids)
       (Import Syn     : NLSYNTAX         Ids Op      )
       (Import Str     : STREAM               Op OpAux)
       (Import Ord     : NLORDERED        Ids Op       Syn)
       (Indexed        : NLSEMANTICS      Ids Op OpAux Syn Str Ord)
       (CoInd          : NLSEMANTICSCOIND Ids Op OpAux Syn     Ord)
       (Import Interp  : NLINTERPRETOR    Ids Op OpAux Syn Str Ord Indexed)
       (Import C2I     : COINDTOINDEXED   Ids Op OpAux Syn Str Ord Indexed        CoInd)
       (Import I2C     : INDEXEDTOCOIND   Ids Op OpAux Syn Str Ord Indexed Interp CoInd).

Definition stream_equivalence {A} (xs: Stream A) (xs': stream A) :=
  forall n, Str_nth n xs = xs' n.

Definition streams_equivalence {A} (xss: list (Stream A)) (xss': stream (list A)) :=
  forall n, Forall2 (fun xs x => Str_nth n xs = x) xss (xss' n).

Definition history_equivalence (H: CoInd.History) (H': Indexed.history) :=
  forall x xs xs',
    (PM.MapsTo x xs H ->
     PM.MapsTo x xs' H' /\ stream_equivalence xs xs')
    /\
    (PM.MapsTo x xs' H' ->
     PM.MapsTo x xs H /\ stream_equivalence xs xs').

Record unified_stream A :=
  {
    coind: Stream A;
    indexed: stream A;
    equiv: stream_equivalence coind indexed
  }.
Arguments coind [A] _.
Arguments indexed [A] _ _.
Arguments equiv [A] _ _.

Record unified_streams A :=
  {
    coind_s: list (Stream A);
    indexed_s: stream (list A);
    equiv_s: streams_equivalence coind_s indexed_s
  }.
Arguments coind_s [A] _.
Arguments indexed_s [A] _ _.
Arguments equiv_s [A] _ _.

Record unified_history :=
  {
    coind_h: CoInd.History;
    indexed_h: Indexed.history;
    equiv_h: history_equivalence coind_h indexed_h
  }.

Record unified_stream_assert A :=
  {
    coind_assert: Stream A -> Prop;
    indexed_assert: stream A -> Prop;
    equiv_assert:
      forall xs,
        coind_assert (coind xs) <-> indexed_assert (indexed xs)
  }.

  Definition sem_var (H: unified_history) (x: ident) : unified_stream_assert value.
  Proof.
    eapply (Build_unified_stream_assert value
                                        (CoInd.sem_var (coind_h H) x)
                                        (Indexed.sem_var (fun _ => true) (indexed_h H) x)).
    split; intros Sem.
    - constructor.
      inv Sem.
      unfold Indexed.restr, tr_History.
      unfold PM.map.
      rewrite PM.gmapi.
      erewrite PM.find_1; eauto; simpl.
      + f_equal.
      + apply (proj1 (equiv_h H x xs' (indexed xs))); auto.
    - apply sem_var_inv in Sem as (? & ? & E).
      econstructor.
      + apply (proj2 (equiv_h H x (coind xs) x0)).
        now apply PM.find_2.
      + reflexivity.
  Qed.

  Lemma tr_stream_sound:
    forall {A} (xs: stream A),
     stream_equivalence (tr_stream xs) xs.
  Proof.
    unfold tr_stream, tr_stream_from, stream_equivalence.
    setoid_rewrite init_from_nth; auto.
  Qed.

  Lemma tr_Stream_sound:
    forall {A} (xs: Stream A),
      stream_equivalence xs (tr_Stream xs).
  Proof. now unfold stream_equivalence. Qed.

  Definition unified_from_indexed {A} (xs: stream A) : unified_stream A.
  Proof.
    eapply (Build_unified_stream _ _ xs), tr_stream_sound.
  Defined.

  Definition unified_from_coind {A} (xs: Stream A) : unified_stream A.
  Proof.
    eapply (Build_unified_stream _ xs), tr_Stream_sound.
  Defined.

End SEMEQUIV.
