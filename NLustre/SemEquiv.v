Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Coq.Sorting.Permutation.
Require Import Morphisms.

Require Import Coq.FSets.FMapPositive.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.Ordered.
Require Import Velus.NLustre.Stream.
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
       (Import OpAux   : OPERATORS_AUX Op)
       (Import Clks    : CLOCKS           Ids)
       (Import Syn     : NLSYNTAX         Ids Op       Clks)
       (Import Str     : STREAM               Op OpAux)
       (Import Ord     : ORDERED          Ids Op       Clks Syn)
       (Import Indexed : NLSEMANTICS      Ids Op OpAux Clks Syn Str Ord)
       (Import CoInd   : NLSEMANTICSCOIND Ids Op OpAux Clks Syn     Ord)
       (Import Interp  : NLINTERPRETOR    Ids Op OpAux Clks Syn Str Ord Indexed)
       (Import C2I     : COINDTOINDEXED   Ids Op OpAux Clks Syn Str Ord Indexed        CoInd)
       (Import I2C     : INDEXEDTOCOIND   Ids Op OpAux Clks Syn Str Ord Indexed Interp CoInd).

  Lemma tr_stream_sound:
    forall {A} (xs: stream A) n,
     Str_nth n (tr_stream xs) = xs n.
  Proof.
    unfold tr_stream, tr_stream_from.
    setoid_rewrite init_from_nth; auto.
  Qed.

  Lemma tr_Stream_sound:
    forall {A} (xs: Stream A) n,
      tr_Stream xs n = Str_nth n xs.
  Proof. reflexivity. Qed.




End SEMEQUIV.
