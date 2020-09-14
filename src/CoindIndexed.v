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
From Velus Require Import CoindToIndexed IndexedToCoind.

Module Type COINDINDEXED
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import CStr  : COINDSTREAMS Op OpAux)
       (Import IStr  : INDEXEDSTREAMS Op OpAux).

  Module Export CIStr := CoindToIndexedFun Op OpAux CStr IStr.
  Module Export ICStr := IndexedToCoindFun Op OpAux IStr CStr.

  Fact tr_stream_eqst {A} : forall (x : Stream A),
      ICStr.tr_stream (tr_Stream x) ≡ x.
  Proof.
    unfold ICStr.tr_stream, ICStr.tr_stream_from, tr_Stream.
    intros x.
    apply ntheq_eqst; intros n.
    rewrite ICStr.init_from_nth, Nat.add_0_r.
    reflexivity.
  Qed.

  Fact tr_history_equiv: forall H,
      Env.Equiv (@EqSt value) (ICStr.tr_history (CIStr.tr_history H)) H.
  Proof.
    intros H.
    unfold CIStr.tr_history, ICStr.tr_history, ICStr.tr_history_from.
    constructor; intros.
    - rewrite Env.Props.P.F.mapi_in_iff, Env.Props.P.F.map_in_iff. reflexivity.
    - unfold Env.MapsTo in H0. rewrite Env.gmapi in H0.
      apply option_map_inv_Some in H0 as [v [Hfind Hinit]]; subst.
      apply ntheq_eqst. intros n.
      rewrite ICStr.init_from_nth, Nat.add_0_r, Env.Props.P.F.map_o, H1; simpl; auto.
  Qed.

  Lemma sem_clock_equiv : forall H b ck bs,
      CStr.sem_clock H b ck bs <->
      IStr.sem_clock (tr_Stream b) (CIStr.tr_history H) ck (tr_Stream bs).
  Proof.
    intros; split.
    - apply CIStr.sem_clock_impl.
    - intro Hsem.
      apply ICStr.sem_clock_impl in Hsem.
      repeat rewrite tr_stream_eqst in Hsem. rewrite tr_history_equiv in Hsem.
      assumption.
  Qed.

End COINDINDEXED.

Module CoindIndexedFun
       (Op      : OPERATORS)
       (OpAux   : OPERATORS_AUX          Op)
       (CStr    : COINDSTREAMS           Op OpAux)
       (IStr    : INDEXEDSTREAMS         Op OpAux)
<: COINDINDEXED Op OpAux CStr IStr.
  Include COINDINDEXED Op OpAux CStr IStr.
End CoindIndexedFun.
