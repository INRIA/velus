From Coq Require Import List.

From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.Ordered.
From Velus Require Import CoreExpr.Stream.
From Velus Require Import NLustre.Streams.
From Velus Require Import NLustre.NLSemanticsCoInd.
From Velus Require Import NLustre.NLSemantics.

Module Type UNIFIEDSTREAM
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import OpAux   : OPERATORS_AUX Op)
       (Import    : CLOCKS           Ids)
       (Import Syn     : NLSYNTAX         Ids Op      )
       (Import Str     : STREAM               Op OpAux)
       (Import Ord     : ORDERED          Ids Op       Syn)
       (Indexed        : NLSEMANTICS      Ids Op OpAux Syn Str Ord)
       (CoInd          : NLSEMANTICSCOIND Ids Op OpAux Syn     Ord).

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

Lemma unified_length:
  forall {A} n (xss: unified_streams A),
    length (coind_s xss) = length (indexed_s xss n).
Proof.
  intros; apply (Forall2_length _ _ _ (equiv_s xss n)).
Qed.

Definition length_s {A} (xss: unified_streams A) : nat :=
  length (coind_s xss).

(** If at instant [n], a property is true for all elements of the list
    obtained from the indexed stream, then it is true for the [n]th element
    of the Streams in the list of coinductive Streams. *)
Lemma Forall_In_unified_streams_nth:
  forall {A} n P (xss: unified_streams A) x,
    Forall P (indexed_s xss n) ->
    In x (coind_s xss) ->
    P (Str_nth n x).
Proof.
  intros ** Ps Hin.
  apply In_ex_nth with (d:=x) in Hin as (k & Len & Nth).
  pose proof (equiv_s xss n) as E.
  apply Forall2_forall2 in E as (? & E).
  erewrite E; eauto.
  instantiate (1:=hd x).
  eapply In_Forall; eauto.
  apply nth_In; now rewrite <-unified_length.
Qed.

(** This states the converse of the previous lemma. *)
Lemma Forall_In_unified_streams_nth':
  forall {A} n P (xss: unified_streams A) x,
    Forall (fun x => P (Str_nth n x)) (coind_s xss) ->
    In x (indexed_s xss n) ->
    P x.
Proof.
  intros ** Ps Hin.
  apply In_ex_nth with (d:=x) in Hin as (k & Len & Nth).
  rewrite <-unified_length in Len.
  pose proof (equiv_s xss n) as E.
  apply Forall2_forall2 in E as (? & E).
  erewrite <-E; eauto.
  instantiate (1:=Streams.const x).
  eapply In_Forall in Ps; eauto.
  now apply nth_In.
Qed.

Corollary Forall_unified_streams_nth:
  forall {A} (xss: unified_streams A) n P,
    Forall P (indexed_s xss n) <-> Forall (fun x => P (Str_nth n x)) (coind_s xss).
Proof.
  split; intros; apply Forall_forall; intros.
  - eapply Forall_In_unified_streams_nth; eauto.
  - eapply Forall_In_unified_streams_nth'; eauto.
Qed.

End UNIFIEDSTREAM.