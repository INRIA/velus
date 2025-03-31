From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import IndexedStreams.
From Velus Require Import CoindStreams.
From Velus Require Import CoindIndexed.

From Velus Require Import CoreExpr.CESemantics.
From Velus Require Import CoreExpr.CEInterpreter.
From Velus Require Import NLustre.NLIndexedSemantics.
From Velus Require Import NLustre.NLCoindSemantics.
From Velus Require Import NLustre.NLIndexedToCoind.
From Velus Require Import NLustre.NLCoindToIndexed.

Module Type NLSEMEQUIV
       (Import Ids    : IDS)
       (Import Op     : OPERATORS)
       (Import OpAux  : OPERATORS_AUX      Ids Op)
       (Import Cks    : CLOCKS             Ids Op OpAux)
       (Import CESyn  : CESYNTAX           Ids Op OpAux Cks)
       (Import Syn    : NLSYNTAX           Ids Op OpAux Cks CESyn)
       (Import IStr   : INDEXEDSTREAMS     Ids Op OpAux Cks)
       (Import CStr   : COINDSTREAMS       Ids Op OpAux Cks)
       (Import Ord    : NLORDERED          Ids Op OpAux Cks CESyn Syn)
       (CESem         : CESEMANTICS        Ids Op OpAux Cks CESyn     IStr)
       (Indexed       : NLINDEXEDSEMANTICS Ids Op OpAux Cks CESyn Syn IStr      Ord CESem)
       (Import Interp : CEINTERPRETER      Ids Op OpAux Cks CESyn     IStr          CESem)
       (CoInd         : NLCOINDSEMANTICS   Ids Op OpAux Cks CESyn Syn      CStr Ord)
       (CIStr         : COINDINDEXED       Ids Op OpAux Cks                CStr IStr)
       (IdxToCoind    : NLINDEXEDTOCOIND   Ids Op OpAux Cks CESyn Syn IStr CStr CIStr.ICStr Ord CESem Indexed Interp CoInd)
       (CoindToIdx    : NLCOINDTOINDEXED   Ids Op OpAux Cks CESyn Syn IStr CStr CIStr.CIStr Ord CESem Indexed        CoInd).

  Definition streams_equivalence {A} (xss: list (Stream A)) (xss': stream (list A)) :=
    forall n, Forall2 (fun xs x => xs # n = x) xss (xss' n).

  Record unified_streams A :=
    {
      coind_s :> list (Stream A);
      indexed_s :> stream (list A);
      equiv_s: streams_equivalence coind_s indexed_s
    }.

  Lemma indexed_equiv:
    forall {A} (xss: unified_streams A),
      CIStr.CIStr.tr_Streams xss ≈ xss.
  Proof.
    intros * n.
    destruct xss as (coind, idx, E); simpl.
    specialize (E n).
    induction E; simpl; auto with datatypes.
  Qed.

  Lemma EqSts_iff:
    forall A (xss xss': list (Stream A)),
      EqSts xss xss' <->
      forall n, List.map (Str_nth n) xss = List.map (Str_nth n) xss'.
  Proof.
    split; intros * E.
    - induction E as [|???? E']; simpl; auto.
      intro; f_equal; auto.
      now rewrite E'.
    - generalize dependent xss'; induction xss; simpl; intros.
      + assert (xss' = []) as ->; try reflexivity.
        specialize (E 0).
        eapply map_eq_nil; eauto.
      + assert (exists xs xss'', xss' = xs :: xss'') as (?&?& ->)
            by (specialize (E 0); destruct xss'; inv E; eauto).
        constructor.
        * simpl in E.
          apply ntheq_eqst; intro n.
          specialize (E n); inv E; auto.
        * apply IHxss.
          intro n; specialize (E n); inv E; auto.
  Qed.

  Lemma pointwise_eq_list:
    forall A (d: A) (l l': list A),
      length l = length l' ->
      (forall n, nth n l d = nth n l' d) ->
      l = l'.
  Proof.
    induction l; intros * Length Spec.
    - symmetry; apply length_zero_iff_nil; auto.
    - assert (exists a' l'', l' = a' :: l'') as (?& l'' &?)
          by (destruct l'; inv Length; eauto).
      subst.
      f_equal.
      + specialize (Spec 0); auto.
      + apply IHl; auto.
        simpl in Length; inversion Length as (Length').
        intro n; specialize (Spec (S n)); auto.
  Qed.

  Lemma coind_equiv:
    forall (xss: unified_streams svalue),
      EqSts (CIStr.ICStr.tr_streams xss) xss.
  Proof.
    intros.
    destruct xss as (coind, idx, E); simpl.
    apply EqSts_iff.
    intro n.
    eapply pointwise_eq_list with (d := absent).
    - rewrite 2 length_map.
      unfold CIStr.ICStr.tr_streams.
      rewrite CIStr.ICStr.tr_streams_from_length.
      specialize (E 0); now apply Forall2_length in E.
    - assert (forall n, length coind = length (idx n)) as Length
          by (intro k; specialize (E k); apply Forall2_length in E; auto).
      specialize (E n).
      apply Forall2_forall2 in E as (?&?).
      intro k.
      replace absent with (Str_nth n (Streams.const (@absent value)))
        by apply const_nth.
      rewrite 2 map_nth.
      unfold CIStr.ICStr.tr_streams, CIStr.ICStr.tr_streams_from.
      destruct (Compare_dec.le_lt_dec (length coind) k).
      + rewrite 2 nth_overflow; auto.
        rewrite CIStr.ICStr.seq_streams_length.
        rewrite <-Length; lia.
      + rewrite CIStr.ICStr.nth_seq_streams; try (rewrite <-Length; lia).
        unfold CIStr.ICStr.nth_tr_streams_from.
        rewrite init_from_nth.
        unfold CIStr.ICStr.streams_nth.
        symmetry; eapply H0; eauto.
        rewrite <-plus_n_O; eauto.
  Qed.

  Theorem equivalence:
    forall G f (xss yss: unified_streams svalue),
      CoInd.sem_node G f xss yss <-> Indexed.sem_node G f xss yss.
  Proof.
    split; intros * Sem.
    - apply CoindToIdx.implies in Sem.
      now rewrite <-2 indexed_equiv.
    - apply IdxToCoind.implies in Sem.
      now rewrite <-2 coind_equiv.
  Qed.
End NLSEMEQUIV.
