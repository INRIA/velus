From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
(* From Coq Require Import Sorting.Permutation. *)
(* From Coq Require Import Setoid. *)
(* From Coq Require Import Morphisms. *)
(* From Coq Require Import Program.Tactics. *)
(* From Coq Require Import NPeano. *)
From Coq Require Import Omega.

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

From Velus Require Import CoreExpr.CESemantics.
From Velus Require Import CoreExpr.CEInterpreter.
From Velus Require Import NLustre.NLIndexedSemantics.
From Velus Require Import NLustre.NLCoindSemantics.
From Velus Require Import NLustre.NLIndexedToCoind.
From Velus Require Import NLustre.NLCoindToIndexed.

(* From Coq Require Import Setoid. *)

Module Type NLSEMEQUIV
       (Import Ids    : IDS)
       (Import Op     : OPERATORS)
       (Import OpAux  : OPERATORS_AUX          Op)
       (Import CESyn  : CESYNTAX               Op)
       (Import Syn    : NLSYNTAX           Ids Op       CESyn)
       (Import IStr   : INDEXEDSTREAMS         Op OpAux)
       (Import CStr   : COINDSTREAMS           Op OpAux)
       (Import Ord    : NLORDERED          Ids Op       CESyn Syn)
       (CESem         : CESEMANTICS        Ids Op OpAux CESyn     IStr)
       (Indexed       : NLINDEXEDSEMANTICS Ids Op OpAux CESyn Syn IStr      Ord CESem)
       (Import Interp : CEINTERPRETER      Ids Op OpAux CESyn     IStr          CESem)
       (CoInd         : NLCOINDSEMANTICS   Ids Op OpAux CESyn Syn      CStr Ord)
       (IdxToCoind    : NLINDEXEDTOCOIND   Ids Op OpAux CESyn Syn IStr CStr Ord CESem Indexed Interp CoInd)
       (CoindToIdx    : NLCOINDTOINDEXED   Ids Op OpAux CESyn Syn IStr CStr Ord CESem Indexed        CoInd).

  (* Lemma inverse_1: *)
  (*   forall A (s: Stream A), *)
  (*     IdxToCoind.tr_stream (CoindToIdx.tr_Stream s) ≡ s. *)
  (* Proof. *)
  (*   intros. *)
  (*   apply ntheq_eqst; intro. *)
  (*   unfold IdxToCoind.tr_stream. *)
  (*   now rewrite IdxToCoind.init_from_nth, CoindToIdx.tr_Stream_nth, <-plus_n_O. *)
  (* Qed. *)

  (* Lemma inverse_2: *)
  (*   forall A (s: stream A), *)
  (*     CoindToIdx.tr_Stream (IdxToCoind.tr_stream s) ≈ s. *)
  (* Proof. *)
  (*   intros * n. *)
  (*   unfold IdxToCoind.tr_stream, IdxToCoind.tr_stream_from. *)
  (*   now rewrite CoindToIdx.tr_Stream_nth, IdxToCoind.init_from_nth, <-plus_n_O. *)
  (* Qed. *)

  Definition streams_equivalence {A} (xss: list (Stream A)) (xss': stream (list A)) :=
    forall n, Forall2 (fun xs x => xs # n = x) xss (xss' n).

  Record unified_streams A :=
    {
      coind_s :> list (Stream A);
      indexed_s :> stream (list A);
      equiv_s: streams_equivalence coind_s indexed_s
    }.

  Lemma indexed_equiv:
    forall (xss: unified_streams value),
      CoindToIdx.tr_Streams xss ≈ xss.
  Proof.
    intros * n.
    destruct xss as (coind, idx, E); simpl.
    specialize (E n).
    induction E; simpl; auto.
    f_equal; auto.
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
    - revert dependent xss'; induction xss; simpl; intros.
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
    forall (xss: unified_streams value),
      EqSts (IdxToCoind.tr_streams xss) xss.
  Proof.
    intros.
    destruct xss as (coind, idx, E); simpl.
    apply EqSts_iff.
    intro n.
    eapply pointwise_eq_list with (d := absent).
    - rewrite 2 map_length.
      unfold IdxToCoind.tr_streams.
      rewrite IdxToCoind.tr_streams_from_length.
      specialize (E 0); now apply Forall2_length in E.
    - assert (forall n, length coind = length (idx n)) as Length
          by (intro k; specialize (E k); apply Forall2_length in E; auto).
      specialize (E n).
      apply Forall2_forall2 in E as (?&?).
      intro k.
      replace absent with (Str_nth n (Streams.const absent))
        by apply const_nth.
      rewrite 2 map_nth.
      unfold IdxToCoind.tr_streams, IdxToCoind.tr_streams_from.
      destruct (Compare_dec.le_lt_dec (length coind) k).
      + rewrite 2 nth_overflow; auto.
        rewrite IdxToCoind.seq_streams_length.
        rewrite <-Length; omega.
      + rewrite IdxToCoind.nth_seq_streams; try (rewrite <-Length; omega).
        unfold IdxToCoind.nth_tr_streams_from.
        rewrite IdxToCoind.init_from_nth.
        unfold IdxToCoind.streams_nth.
        symmetry; eapply H0; eauto.
        rewrite <-plus_n_O; eauto.
  Qed.

  Theorem equivalence:
    forall G f (xss yss: unified_streams value),
      CoInd.sem_node G f xss yss <-> Indexed.sem_node G f xss yss.
  Proof.
    split; intros * Sem.
    - apply CoindToIdx.implies in Sem.
      now rewrite <-2 indexed_equiv.
    - apply IdxToCoind.implies in Sem.
      now rewrite <-2 coind_equiv.
  Qed.


(* Definition stream_equivalence {A} (xs: Stream A) (xs': stream A) := *)
(*   forall n, Str_nth n xs = xs' n. *)



(* Definition history_equivalence (H: CoInd.History) (H': Indexed.history) := *)
(*   forall x xs xs', *)
(*     (PM.MapsTo x xs H -> *)
(*      PM.MapsTo x xs' H' /\ stream_equivalence xs xs') *)
(*     /\ *)
(*     (PM.MapsTo x xs' H' -> *)
(*      PM.MapsTo x xs H /\ stream_equivalence xs xs'). *)

(* Record unified_stream A := *)
(*   { *)
(*     coind: Stream A; *)
(*     indexed: stream A; *)
(*     equiv: stream_equivalence coind indexed *)
(*   }. *)
(* Arguments coind [A] _. *)
(* Arguments indexed [A] _ _. *)
(* Arguments equiv [A] _ _. *)

(* Record unified_streams A := *)
(*   { *)
(*     coind_s: list (Stream A); *)
(*     indexed_s: stream (list A); *)
(*     equiv_s: streams_equivalence coind_s indexed_s *)
(*   }. *)
(* Arguments coind_s [A] _. *)
(* Arguments indexed_s [A] _ _. *)
(* Arguments equiv_s [A] _ _. *)

(* Record unified_history := *)
(*   { *)
(*     coind_h: CoInd.History; *)
(*     indexed_h: Indexed.history; *)
(*     equiv_h: history_equivalence coind_h indexed_h *)
(*   }. *)

(* Record unified_stream_assert A := *)
(*   { *)
(*     coind_assert: Stream A -> Prop; *)
(*     indexed_assert: stream A -> Prop; *)
(*     equiv_assert: *)
(*       forall xs, *)
(*         coind_assert (coind xs) <-> indexed_assert (indexed xs) *)
(*   }. *)

(*   Definition sem_var (H: unified_history) (x: ident) : unified_stream_assert value. *)
(*   Proof. *)
(*     eapply (Build_unified_stream_assert value *)
(*                                         (CoInd.sem_var (coind_h H) x) *)
(*                                         (Indexed.sem_var (fun _ => true) (indexed_h H) x)). *)
(*     split; intros Sem. *)
(*     - constructor. *)
(*       inv Sem. *)
(*       unfold Indexed.restr, tr_History. *)
(*       unfold PM.map. *)
(*       rewrite PM.gmapi. *)
(*       erewrite PM.find_1; eauto; simpl. *)
(*       + f_equal. *)
(*       + apply (proj1 (equiv_h H x xs' (indexed xs))); auto. *)
(*     - apply sem_var_inv in Sem as (? & ? & E). *)
(*       econstructor. *)
(*       + apply (proj2 (equiv_h H x (coind xs) x0)). *)
(*         now apply PM.find_2. *)
(*       + reflexivity. *)
(*   Qed. *)

(*   Lemma tr_stream_sound: *)
(*     forall {A} (xs: stream A), *)
(*      stream_equivalence (tr_stream xs) xs. *)
(*   Proof. *)
(*     unfold tr_stream, tr_stream_from, stream_equivalence. *)
(*     setoid_rewrite init_from_nth; auto. *)
(*   Qed. *)

(*   Lemma tr_Stream_sound: *)
(*     forall {A} (xs: Stream A), *)
(*       stream_equivalence xs (tr_Stream xs). *)
(*   Proof. now unfold stream_equivalence. Qed. *)

(*   Definition unified_from_indexed {A} (xs: stream A) : unified_stream A. *)
(*   Proof. *)
(*     eapply (Build_unified_stream _ _ xs), tr_stream_sound. *)
(*   Defined. *)

(*   Definition unified_from_coind {A} (xs: Stream A) : unified_stream A. *)
(*   Proof. *)
(*     eapply (Build_unified_stream _ xs), tr_Stream_sound. *)
(*   Defined. *)

End NLSEMEQUIV.
