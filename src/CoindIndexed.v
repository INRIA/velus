From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Setoid.
From Coq Require Import Morphisms.
From Coq Require Import NPeano.
From Coq Require Import Program.Tactics.

From Velus Require Import Common.
From Velus Require Import FunctionalEnvironment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import IndexedStreams.
From Velus Require Import CoindStreams.
From Velus Require Import CoindToIndexed IndexedToCoind.

Module Type COINDINDEXED
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS Ids Op OpAux)
       (Import CStr  : COINDSTREAMS Ids Op OpAux Cks)
       (Import IStr  : INDEXEDSTREAMS Ids Op OpAux Cks).

  Module Export CIStr := CoindToIndexedFun Ids Op OpAux Cks CStr IStr.
  Module Export ICStr := IndexedToCoindFun Ids Op OpAux Cks IStr CStr.

  Fact tr_stream_eqst {A} : forall (x : Stream A),
      ICStr.tr_stream (tr_Stream x) ≡ x.
  Proof.
    unfold ICStr.tr_stream, ICStr.tr_stream_from, tr_Stream.
    intros x.
    apply ntheq_eqst; intros n.
    rewrite init_from_nth, Nat.add_0_r.
    reflexivity.
  Qed.

  Fact tr_history_equiv {K}: forall (H: @CStr.history K),
      FEnv.Equiv (@EqSt _) (ICStr.tr_history (CIStr.tr_history H)) H.
  Proof.
    intros H.
    unfold CIStr.tr_history, ICStr.tr_history, ICStr.tr_history_from.
    intros x. simpl_fenv.
    destruct (H x); simpl; constructor.
    apply ntheq_eqst. intros n.
    rewrite init_from_nth, Nat.add_0_r; auto.
  Qed.

  Lemma sem_var_equiv {K} : forall (H: @CStr.history K) x v,
      CStr.sem_var H x v <->
      IStr.sem_var (CIStr.tr_history H) x (tr_Stream v).
  Proof.
    intros; split.
    - apply CIStr.sem_var_impl.
    - intros Hsem.
      apply ICStr.sem_var_impl in Hsem.
      rewrite tr_stream_eqst in Hsem. rewrite tr_history_equiv in Hsem.
      assumption.
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
       (Ids     : IDS)
       (Op      : OPERATORS)
       (OpAux   : OPERATORS_AUX          Ids Op)
       (Cks     : CLOCKS                 Ids Op OpAux)
       (CStr    : COINDSTREAMS           Ids Op OpAux Cks)
       (IStr    : INDEXEDSTREAMS         Ids Op OpAux Cks)
<: COINDINDEXED Ids Op OpAux Cks CStr IStr.
  Include COINDINDEXED Ids Op OpAux Cks CStr IStr.
End CoindIndexedFun.
