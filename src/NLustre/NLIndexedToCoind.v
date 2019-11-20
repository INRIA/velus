(* *********************************************************************)
(*                                                                     *)
(*                 The Vélus verified Lustre compiler                  *)
(*                                                                     *)
(*             (c) 2019 Inria Paris (see the AUTHORS file)             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Setoid.
From Coq Require Import Morphisms.
From Coq Require Import Program.Tactics.
From Coq Require Import NPeano.
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

From Coq Require Import Setoid.

Module Type NLINDEXEDTOCOIND
       (Import Ids    : IDS)
       (Import Op     : OPERATORS)
       (Import OpAux  : OPERATORS_AUX          Op)
       (Import CESyn  : CESYNTAX               Op)
       (Import Syn    : NLSYNTAX           Ids Op       CESyn)
       (Import IStr   : INDEXEDSTREAMS         Op OpAux)
       (Import CStr   : COINDSTREAMS           Op OpAux)
       (Import Ord    : NLORDERED          Ids Op       CESyn Syn)
       (CESem         : CESEMANTICS        Ids Op OpAux CESyn     IStr)
       (Indexed       : NLINDEXEDSEMANTICS Ids Op OpAux CESyn Syn IStr Ord CESem)
       (Import Interp : CEINTERPRETER      Ids Op OpAux CESyn     IStr     CESem)
       (CoInd         : NLCOINDSEMANTICS   Ids Op OpAux CESyn Syn CStr Ord).

  Section Global.

    Variable G : global.

    (** * BASIC CORRESPONDENCES *)

    (** ** Definitions  *)

    (** A generic function to build a coinductive Stream. *)
    CoFixpoint init_from {A} (n: nat) (f: nat -> A) : Stream A :=
      f n ⋅ init_from (S n) f.

    (** Translate an indexed stream into a coinductive Stream.
        The [n]th element of the result Stream is the result of the application
        of the input stream on [n]. *)
    Definition tr_stream_from {A} (n: nat) (xs: stream A) : Stream A :=
      init_from n xs.

    Definition tr_stream {A} : stream A -> Stream A := tr_stream_from 0.

    (** Build a list of coinductive streams from an the integer range [0..m[. *)
    Definition seq_streams {A} (f: nat -> Stream A) (m: nat) : list (Stream A) :=
      List.map f (seq 0 m).

    (** Build the indexed stream corresponding to the [i]th elements of
        the input stream of lists. *)
    Definition streams_nth (k: nat) (xss: stream (list value)): stream value :=
      fun n => nth k (xss n) absent.

    (** Build a coinductive Stream extracting the [i]th element of the list
        obtained at each instant [n]. *)
    Definition nth_tr_streams_from (n: nat) (xss: stream (list value)) (k: nat)
      : Stream value :=
      tr_stream_from n (streams_nth k xss).

    (** Translate an indexed stream of list into a list of coinductive Streams
        using the two previous functions. *)
    Definition tr_streams_from (n: nat) (xss: stream (list value))
      : list (Stream value) :=
      seq_streams (nth_tr_streams_from n xss) (length (xss n)).

    Definition tr_streams: stream (list value) -> list (Stream value) :=
      tr_streams_from 0.

    Ltac unfold_tr_streams :=
      unfold tr_streams, tr_streams_from.

    (** Translate an history from indexed to coinductive world.
        Every element of the history is translated. *)
    Definition tr_history_from (n: nat) (H: CESem.history) : CoInd.History :=
      Env.mapi (fun x _ => init_from n (fun n => match Env.find x (H n) with
                                                 | Some v => v
                                                 | None => absent
                                                 end)) (H 0).

    Definition tr_history : CESem.history -> CoInd.History :=
      tr_history_from 0.

    (** ** Properties  *)

    (** A basic definition-rewriting lemma.  *)
    Lemma init_from_n:
      forall {A} (f: nat -> A) n,
        init_from n f = f n ⋅ init_from (S n) f.
    Proof.
      intros; now rewrite unfold_Stream at 1.
    Qed.

    (** [init_from] is compatible wrt to extensional equality. *)
    Add Parametric Morphism A : (@init_from A)
        with signature eq ==> eq_str ==> @EqSt A
          as init_from_morph.
    Proof.
      cofix Cofix. intros x xs xs' E.
      rewrite init_from_n; rewrite (init_from_n xs').
      constructor; simpl; auto.
    Qed.

    (** The [m]th element of the built stream, starting from [n],
        is the result of the application of [f] at [(m+n)]. *)
    Lemma init_from_nth:
      forall {A} m n (f: nat -> A),
        (init_from n f) # m = f (m + n).
    Proof.
      unfold Str_nth; induction m; intros; simpl; auto.
      now rewrite IHm, <-plus_n_Sm.
    Qed.

    (** Taking the tail of a built Stream from [n] is building it from [S n]. *)
    Lemma init_from_tl:
      forall {A} n (f: nat -> A),
        tl (init_from n f) = init_from (S n) f.
    Proof.
      intros; rewrite init_from_n; auto.
    Qed.

    (** A generalization for multiple tails. *)
    Lemma init_from_nth_tl:
      forall {A} n m (f: nat -> A),
        Str_nth_tl n (init_from m f) = init_from (n + m) f.
    Proof.
      induction n; intros; simpl; auto.
      now rewrite IHn, Nat.add_succ_r.
    Qed.

    (** The length of the range-built list of Streams is simply the difference
        between the bounds of the range.  *)
    Lemma seq_streams_length:
      forall {A} m (str: nat -> Stream A),
        length (seq_streams str m) = m.
    Proof.
      intros; unfold seq_streams.
      now rewrite map_length, seq_length.
    Qed.

    (** The [n]th element of the range-built list of Streams starting at 0 is
        the result of the function at [n]. *)
    Lemma nth_seq_streams:
      forall {A} m str n (xs_d: Stream A),
        n < m ->
        nth n (seq_streams str m) xs_d = str n.
    Proof.
      unfold seq_streams; intros.
      rewrite map_nth' with (d':=0); simpl.
      - rewrite seq_nth; auto; omega.
      - rewrite seq_length; omega.
    Qed.

    Corollary nth_tr_streams_from_nth:
      forall n k xss xs_d,
        k < length (xss n) ->
        nth k (tr_streams_from n xss) xs_d =
        nth_tr_streams_from n xss k.
    Proof.
      unfold_tr_streams.
      intros; now rewrite nth_seq_streams.
    Qed.

    (** A generalization of [tr_stream_from_tl] for lists. *)
    Lemma tr_streams_from_tl:
      forall n xss,
        wf_streams xss ->
        List.map (@tl value) (tr_streams_from n xss) = tr_streams_from (S n) xss.
    Proof.
      intros * Len.
      apply Forall2_eq, Forall2_forall2.
      split; unfold_tr_streams; rewrite map_length.
      - now rewrite 2 seq_streams_length.
      - intros * Hlen E1 E2; rewrite <-E1, <-E2.
        rewrite map_nth' with (d':=a); auto.
        rewrite seq_streams_length in Hlen.
        rewrite 2 nth_seq_streams; try omega.
        + reflexivity.
        + rewrite (Len n); omega.
    Qed.

    Lemma tr_streams_from_length:
      forall n xss,
        length (tr_streams_from n xss) = length (xss n).
    Proof.
      unfold_tr_streams; intros.
      rewrite seq_streams_length; simpl; omega.
    Qed.

    (** The counterpart of [tr_stream_from_tl] for histories. *)
    Lemma tr_history_from_tl:
      forall n H,
        CoInd.History_tl (tr_history_from n H) = tr_history_from (S n) H.
    Proof.
      now setoid_rewrite Env.mapi_mapi.
    Qed.

    (** If at instant [n], a property is true for all elements of the list
        obtained from the indexed stream, then it is true for the first element
        of the Streams starting at [n] in the translated list. *)
    Lemma Forall_In_tr_streams_from_hd:
      forall n P xss x,
        Forall P (xss n) ->
        In x (tr_streams_from n xss) ->
        P (hd x).
    Proof.
      unfold_tr_streams; intros * Ps Hin.
      apply In_nth with (d:=x) in Hin as (k & Len & Nth).
      rewrite seq_streams_length in Len.
      rewrite nth_seq_streams in Nth; auto.
      apply eq_EqSt in Nth.
      unfold nth_tr_streams_from in Nth.
      rewrite init_from_n in Nth.
      inversion Nth as (Hhd).
      rewrite <-Hhd; simpl.
      unfold streams_nth.
      eapply Forall_forall; eauto.
      apply nth_In; auto.
    Qed.

    Lemma Exists_In_tr_streams_from_hd:
      forall n P xss,
        List.Exists P (xss n) ->
        List.Exists (fun v => P (hd v)) (tr_streams_from n xss).
    Proof.
      intros * Hin.
      apply Exists_exists in Hin as (v & Hin & Hv).
      apply In_nth with (d:=absent) in Hin as (k & Len & Nth); subst.
      apply Exists_exists.
      exists (nth k (tr_streams_from n xss) (Streams.const absent)).
      split.
      - apply nth_In.
        rewrite tr_streams_from_length; auto.
      - rewrite nth_tr_streams_from_nth; auto.
    Qed.


    (** * SEMANTICS CORRESPONDENCE *)

    (** ** Variables *)

    (* (** An inversion principle for [sem_var]. *) *)
    (* Lemma sem_var_inv: *)
    (*   forall H x xs, *)
    (*     CESem.sem_var H x xs -> *)
    (*     exists xs', *)
    (*       Env.find x H = Some xs' *)
    (*       /\ xs ≈ xs'. *)
    (* Proof. *)
    (*   unfold CESem.sem_var, CESem.lift'. *)
    (*   intros * Sem. *)
    (*   destruct (Env.find x H) as [xs'|] eqn: E; simpl in *. *)
    (*   - exists xs'; intuition. *)
    (*     intro n; specialize (Sem n). *)
    (*     unfold CESem.sem_var_instant, CESem.restr_hist in Sem. *)
    (*     rewrite Env.Props.P.F.map_o in Sem. *)
    (*     setoid_rewrite E in Sem. *)
    (*     now inv Sem. *)
    (*   - specialize (Sem 0). *)
    (*     unfold CESem.sem_var_instant, CESem.restr_hist in Sem. *)
    (*     rewrite Env.Props.P.F.map_o in Sem. *)
    (*     now setoid_rewrite E in Sem. *)
    (* Qed. *)

    Lemma sem_var_impl_from:
      forall n H x xs,
        CESem.sem_var H x xs ->
        CoInd.sem_var (tr_history_from n H) x (tr_stream_from n xs).
    Proof.
      unfold CESem.sem_var, CESem.lift', CESem.sem_var_instant.
      intros * Sem.
      econstructor.
      - setoid_rewrite Env.gmapi.
        rewrite Sem; simpl; eauto.
      - unfold tr_stream_from.
        apply ntheq_eqst; intro.
        now rewrite 2 init_from_nth, Sem.
    Qed.

    Corollary sem_var_impl:
      forall H x xs,
        CESem.sem_var H x xs ->
        CoInd.sem_var (tr_history H) x (tr_stream xs).
    Proof. apply sem_var_impl_from. Qed.
    Hint Resolve sem_var_impl_from sem_var_impl.

    (** An inversion principle for [sem_vars]. *)
    Lemma sem_vars_inv_from:
      forall H xs xss,
        CESem.sem_vars H xs xss ->
        forall n,
          Forall2 (fun x k => CESem.sem_var H x (streams_nth k xss))
                  (skipn n xs) (seq n (length xs - n)).
    Proof.
      unfold CESem.sem_vars, CESem.lift.
      intros * Sem n.
      apply Forall2_forall2; split.
      - now rewrite skipn_length, seq_length.
      - intros x_d k_d n' x k Length Hskipn Hseq.
        rewrite skipn_length in Length.
        rewrite nth_skipn in Hskipn.
        rewrite nth_seq in Hseq; auto; subst.
        intro m; specialize (Sem m).
        apply Forall2_forall2 in Sem.
        eapply Sem; eauto.
        + now apply Nat.lt_add_lt_sub_r.
        + unfold streams_nth; eauto.
    Qed.

    Corollary sem_vars_inv:
      forall H xs xss,
        CESem.sem_vars H xs xss ->
        Forall2 (fun x k => CESem.sem_var H x (streams_nth k xss))
                xs (seq 0 (length xs)).
    Proof.
      intros * Sem; apply sem_vars_inv_from with (n:=0) in Sem.
      now rewrite Nat.sub_0_r in Sem.
    Qed.

    Corollary sem_vars_impl_from:
      forall n H xs xss,
      CESem.sem_vars H xs xss ->
      Forall2 (CoInd.sem_var (tr_history_from n H)) xs (tr_streams_from n xss).
    Proof.
      intros * Sem.
      assert (length xs = length (xss n)) as Length by
            (unfold CESem.sem_vars, CESem.lift in Sem; specialize (Sem n);
             now apply Forall2_length in Sem).
      apply Forall2_forall2; split.
      - now rewrite tr_streams_from_length.
      - apply sem_vars_inv in Sem.
        intros x_d xs_d n' x xs' En' Ex Exs'.
        apply Forall2_forall2 in Sem as (? & Sem).
        assert (nth n' (seq 0 (length xs)) 0 = n') as Nth by
              (rewrite <-(Nat.sub_0_r (length xs)), plus_n_O;
               apply nth_seq; rewrite Nat.sub_0_r; auto).
        eapply Sem in Nth; eauto.
        apply (sem_var_impl_from n) in Nth.
        subst.
        rewrite nth_tr_streams_from_nth; auto.
        now rewrite <-Length.
    Qed.

    Corollary sem_vars_impl:
      forall H xs xss,
      CESem.sem_vars H xs xss ->
      Forall2 (CoInd.sem_var (tr_history H)) xs (tr_streams xss).
    Proof. apply sem_vars_impl_from. Qed.
    Hint Resolve sem_vars_impl_from sem_vars_impl.

    (** ** exp level synchronous operators inversion principles

        The indexed semantics is inductive only instant-speaking, therefore we
        can't use usual tactics like inversion nor induction.
        We prove some lemmas to provide inversion-like tactics on the semantics
        of exps.
        These lemmas could be proven using the classical axiom of choice which
        gives, from an instant semantics entailment true at every instant,
        the existence of a stream verifying the general entailment.
        But we rather use the interpretor to seq_streams these witnesses, with 2
        benefits :
        1) this is a constructive way of obtaining a witness
        2) we don't rely on an axiom whose use would have to be be deeply
           justified since it would raise some logical contradictions in Coq
     *)

    (** This tactic automatically uses the interpretor to give a witness stream. *)
    Ltac interp_str b H x Sem :=
      let Sem_x := fresh "Sem_" x in
      let sol sem interp sound :=
          assert (sem b H x (interp b H x)) as Sem_x
              by (intro; match goal with n:nat |- _ => specialize (Sem n) end;
                  unfold interp, lift; inv Sem; erewrite <-sound; eauto)
      in
      let sol' sem interp sound :=
          assert (sem H x (interp H x)) as Sem_x
              by (intro; match goal with n:nat |- _ => specialize (Sem n) end;
                  unfold interp, lift'; inv Sem; erewrite <-sound; eauto)
      in
      match type of x with
      | exp => sol CESem.sem_exp interp_exp interp_exp_instant_sound
      | cexp => sol CESem.sem_cexp interp_cexp interp_cexp_instant_sound
      | ident => sol' CESem.sem_var interp_var interp_var_instant_sound
      | clock => sol CESem.sem_clock interp_clock interp_clock_instant_sound
      end.

    Lemma when_inv:
      forall H b e x k es,
        CESem.sem_exp b H (Ewhen e x k) es ->
        exists ys xs,
          CESem.sem_exp b H e ys
          /\ CESem.sem_var H x xs
          /\
          (forall n,
              (exists sc xc,
                  val_to_bool xc = Some k
                  /\ ys n = present sc
                  /\ xs n = present xc
                  /\ es n = present sc)
              \/
              (exists sc xc,
                  val_to_bool xc = Some (negb k)
                  /\ ys n = present sc
                  /\ xs n = present xc
                  /\ es n = absent)
              \/
              (ys n = absent
               /\ xs n = absent
               /\ es n = absent)).
    Proof.
      intros * Sem.
      interp_str b H e Sem.
      interp_str b H x Sem.
      do 2 eexists; intuition; eauto.
      specialize (Sem_e n); specialize (Sem_x n); specialize (Sem n); inv Sem.
      - left. exists sc, xc. repeat split; auto;
                               intuition CESem.sem_det.
      - right; left; exists sc, xc; intuition; try CESem.sem_det.
        now rewrite Bool.negb_involutive.
      - right; right; repeat split; auto; intuition CESem.sem_det.
    Qed.

    Lemma unop_inv:
      forall H b op e ty es,
        CESem.sem_exp b H (Eunop op e ty) es ->
        exists ys,
          CESem.sem_exp b H e ys
          /\
          (forall n,
              (exists c c',
                  ys n = present c
                  /\ sem_unop op c (typeof e) = Some c'
                  /\ es n = present c')
              \/
              (ys n = absent
               /\ es n = absent)).
    Proof.
      intros * Sem.
      interp_str b H e Sem.
      eexists; intuition; eauto.
      specialize (Sem_e n); specialize (Sem n); inv Sem.
      - left; exists c, c'; repeat split; auto; intuition CESem.sem_det.
      - right; repeat split; intuition CESem.sem_det.
    Qed.

    Lemma binop_inv:
      forall H b op e1 e2 ty es,
        CESem.sem_exp b H (Ebinop op e1 e2 ty) es ->
        exists ys zs,
          CESem.sem_exp b H e1 ys
          /\ CESem.sem_exp b H e2 zs
          /\
          (forall n,
              (exists c1 c2 c',
                  ys n = present c1
                  /\ zs n = present c2
                  /\ sem_binop op c1 (typeof e1) c2 (typeof e2) = Some c'
                  /\ es n = present c')
              \/
              (ys n = absent
               /\ zs n = absent
               /\ es n = absent)).
    Proof.
      intros * Sem.
      interp_str b H e1 Sem.
      interp_str b H e2 Sem.
      do 2 eexists; intuition; eauto.
      specialize (Sem_e1 n); specialize (Sem_e2 n); specialize (Sem n); inv Sem.
      - left; exists c1, c2, c'; repeat split; auto; intuition CESem.sem_det.
      - right; repeat split; auto; intuition CESem.sem_det.
    Qed.

    (** An inversion principle for [sem_clock] which also uses the interpretor. *)
    Lemma sem_clock_inv:
      forall H b bs ck x k,
        CESem.sem_clock b H (Con ck x k) bs ->
        exists bs' xs,
          CESem.sem_clock b H ck bs'
          /\ CESem.sem_var H x xs
          /\
          (forall n,
              (exists c,
                  bs' n = true
                  /\ xs n = present c
                  /\ val_to_bool c = Some k
                  /\ bs n = true)
              \/
              (bs' n = false
               /\ xs n = absent
               /\ bs n = false)
              \/
              (exists c,
                  bs' n = true
                  /\ xs n = present c
                  /\ val_to_bool c = Some (negb k)
                  /\ bs n = false)
          ).
    Proof.
      intros * Sem.
      interp_str b H ck Sem.
      interp_str b H x Sem.
      do 2 eexists; intuition; eauto.
      specialize (Sem_ck n); specialize (Sem_x n); specialize (Sem n); inv Sem.
      - left; exists c; repeat split; auto; intuition CESem.sem_det.
      - right; left; repeat split; auto; intuition CESem.sem_det.
      - right; right; exists c; intuition; try CESem.sem_det.
        now rewrite Bool.negb_involutive.
    Qed.

    (** We can then deduce the correspondence lemma for [sem_clock].
        We go by induction on the clock [ck] then we use the above inversion
        lemma. *)
    Corollary sem_clock_impl_from:
      forall H b ck bs,
        CESem.sem_clock b H ck bs ->
        forall n, CoInd.sem_clock (tr_history_from n H) (tr_stream_from n b) ck
                             (tr_stream_from n bs).
    Proof.
      induction ck; intros * Sem n.
      - constructor.
        revert Sem n; cofix CoFix; intros.
        rewrite init_from_n; rewrite (init_from_n bs).
        constructor; simpl; auto.
        specialize (Sem n); now inv Sem.
      - apply sem_clock_inv in Sem as (bs' & xs & Sem_bs' & Sem_xs & Spec).
        revert Spec n; cofix CoFix; intros.
        rewrite (init_from_n bs).
        apply IHck with (n:=n) in Sem_bs';
          rewrite (init_from_n bs') in Sem_bs'.
        apply (sem_var_impl_from n) in Sem_xs;
          rewrite (init_from_n xs) in Sem_xs.
        destruct (Spec n) as [|[]]; destruct_conjs;
        repeat match goal with H:_ n = _ |- _ => rewrite H in *; clear H end.
        + econstructor; eauto.
          rewrite init_from_tl, tr_history_from_tl; auto.
        + econstructor; eauto.
          rewrite init_from_tl, tr_history_from_tl; auto.
        + rewrite <-(Bool.negb_involutive b0).
          eapply CoInd.Son_abs2; eauto.
          rewrite init_from_tl, tr_history_from_tl; auto.
          rewrite Bool.negb_involutive; auto.
    Qed.
    Hint Resolve sem_clock_impl_from.

    Corollary sem_clock_impl:
      forall H b ck bs,
        CESem.sem_clock b H ck bs ->
        CoInd.sem_clock (tr_history H) (tr_stream b) ck (tr_stream bs).
    Proof. intros; apply sem_clock_impl_from; auto. Qed.
    Hint Resolve sem_clock_impl.

    (** ** Semantics of exps *)

    Ltac use_spec Spec :=
      match goal with
        n: nat |- _ =>
        let m := fresh "m" in
        intro m; repeat rewrite init_from_nth;
        specialize (Spec (m + n));
        repeat match goal with
                 H: _ \/ _ |- _ => destruct H
               end;
        destruct_conjs; firstorder
      end.

    (** State the correspondence for [exp].
        Goes by induction on [exp] and uses the previous inversion lemmas. *)
    Hint Constructors when lift1 lift2.
    Lemma sem_exp_impl_from:
      forall n H b e es,
        CESem.sem_exp b H e es ->
        CoInd.sem_exp (tr_history_from n H) (tr_stream_from n b) e
                       (tr_stream_from n es).
    Proof.
      intros * Sem.
      revert dependent H; revert b es n.
      induction e; intros * Sem; unfold CESem.sem_exp, CESem.lift in Sem.

      - constructor.
        apply const_spec; use_spec Sem; inv Sem; auto.

      - constructor.
        apply sem_var_impl_from.
        intros n'; specialize (Sem n').
        now inv Sem.

      - apply when_inv in Sem as (ys & xs & ? & ? & Spec).
        econstructor; eauto using sem_var_impl_from.
        apply when_spec; use_spec Spec.

      - apply unop_inv in Sem as (ys & ? & Spec).
        econstructor; eauto.
        apply lift1_spec; use_spec Spec.

      - apply binop_inv in Sem as (ys & zs & ? & ? & Spec).
        econstructor; eauto.
        apply lift2_spec; use_spec Spec.
    Qed.

    Corollary sem_exp_impl:
      forall H b e es,
        CESem.sem_exp b H e es ->
        CoInd.sem_exp (tr_history H) (tr_stream b) e (tr_stream es).
    Proof. apply sem_exp_impl_from. Qed.
    Hint Resolve sem_exp_impl_from sem_exp_impl.

    (** An inversion principle for lists of [exp]. *)
    Lemma sem_exps_inv:
      forall H b es ess,
        CESem.sem_exps b H es ess ->
        exists ess',
          Forall2 (CESem.sem_exp b H) es ess'
          /\ forall n, ess n = List.map (fun es => es n) ess'.
    Proof.
      intros * Sem.
      exists (interp_exps' b H es); split.
      - eapply interp_exps'_sound; eauto.
      - intro n; specialize (Sem n); induction Sem; simpl; auto.
        f_equal; auto.
        unfold interp_exp; now apply interp_exp_instant_sound.
    Qed.

    (** Generalization for lists of [exp]. *)
    Corollary sem_exps_impl_from:
      forall n H b es ess,
        CESem.sem_exps b H es ess ->
        Forall2 (CoInd.sem_exp (tr_history_from n H) (tr_stream_from n b)) es
                (tr_streams_from n ess).
    Proof.
      intros * Sem.
      apply sem_exps_inv in Sem as (ess' & Sem & Eess').
      assert (length es = length (ess n)) as Length by
          (rewrite Eess', map_length; simpl; eapply Forall2_length; eauto).
      apply Forall2_forall2; split.
      - unfold_tr_streams; rewrite seq_streams_length; simpl; omega.
      - intros; subst.
        rewrite nth_tr_streams_from_nth; try omega.
        apply sem_exp_impl_from.
        eapply (Forall2_forall2_eq _ _ (@eq_refl exp) (eq_str_refl))
          in Sem as (? & Sem).
        + eapply Sem; eauto.
          unfold streams_nth.
          intros k; rewrite Eess'.
          change absent with ((fun es => es k) (fun _ => absent)).
          rewrite map_nth; eauto.
        + unfold CESem.sem_exp; clear.
          intros ?? E ?? E' Sem; subst.
          eapply CESem.lift_eq_str; eauto; reflexivity.
    Qed.

    Corollary sem_exps_impl:
      forall H b es ess,
        CESem.sem_exps b H es ess ->
        Forall2 (CoInd.sem_exp (tr_history H) (tr_stream b)) es (tr_streams ess).
    Proof. apply sem_exps_impl_from. Qed.
    Hint Resolve sem_exps_impl_from sem_exps_impl.

    (** An inversion principle for annotated [exp]. *)
    Lemma sem_aexp_inv:
      forall H b e es ck,
        CESem.sem_aexp b H ck e es ->
        CESem.sem_exp b H e es
        /\ exists bs,
            CESem.sem_clock b H ck bs
            /\ forall n,
              bs n = match es n with
                     | present _ => true
                     | absent => false
                     end.
    Proof.
      intros * Sem; split.
      - intro n; specialize (Sem n); inv Sem; auto.
      - exists (fun n => match es n with
                 | present _ => true
                 | absent => false
                 end); split; intro n; specialize (Sem n); inv Sem; auto.
    Qed.

    (** We deduce from the previous lemmas the correspondence for annotated
        [exp]. *)
    Corollary sem_aexp_impl_from:
      forall n H b e es ck,
        CESem.sem_aexp b H ck e es ->
        CoInd.sem_aexp (tr_history_from n H) (tr_stream_from n b) ck e
                        (tr_stream_from n es).
    Proof.
      cofix Cofix; intros * Sem.
      pose proof Sem as Sem';
        apply sem_aexp_inv in Sem' as (Sem' & bs & Sem_ck & Ebs);
        apply (sem_exp_impl_from n) in Sem';
        apply sem_clock_impl_from with (n:=n) in Sem_ck.
      rewrite (init_from_n es) in *.
      rewrite (init_from_n bs), Ebs in Sem_ck.
      destruct (es n); econstructor; eauto;
        rewrite init_from_tl, tr_history_from_tl;
        apply Cofix; auto.
    Qed.

    Corollary sem_aexp_impl:
      forall H b e es ck,
        CESem.sem_aexp b H ck e es ->
        CoInd.sem_aexp (tr_history H) (tr_stream b) ck e (tr_stream es).
    Proof. apply sem_aexp_impl_from. Qed.
    Hint Resolve sem_aexp_impl_from sem_aexp_impl.

    (** ** cexp level synchronous operators inversion principles *)

    Lemma merge_inv:
      forall H b x t f es,
        CESem.sem_cexp b H (Emerge x t f) es ->
        exists xs ts fs,
          CESem.sem_var H x xs
          /\ CESem.sem_cexp b H t ts
          /\ CESem.sem_cexp b H f fs
          /\
          (forall n,
              (exists c,
                  xs n = present true_val
                  /\ ts n = present c
                  /\ fs n = absent
                  /\ es n = present c)
              \/
              (exists c,
                  xs n = present false_val
                  /\ ts n = absent
                  /\ fs n = present c
                  /\ es n = present c)
              \/
              (xs n = absent
               /\ ts n = absent
               /\ fs n = absent
               /\ es n = absent)).
    Proof.
      intros * Sem.
      interp_str b H x Sem.
      interp_str b H t Sem.
      interp_str b H f Sem.
      do 3 eexists; intuition; eauto.
      specialize (Sem_x n); specialize (Sem_t n); specialize (Sem_f n);
        specialize (Sem n); inv Sem.
      - left; exists c; repeat split; auto; intuition CESem.sem_det.
      - right; left; exists c; repeat split; auto; intuition CESem.sem_det.
      - right; right; repeat split; auto; intuition CESem.sem_det.
    Qed.

    Lemma ite_inv:
      forall H b le t f es,
        CESem.sem_cexp b H (Eite le t f) es ->
        exists les ts fs,
          CESem.sem_exp b H le les
          /\ CESem.sem_cexp b H t ts
          /\ CESem.sem_cexp b H f fs
          /\
          (forall n,
              (exists c b ct cf,
                  les n = present c
                  /\ val_to_bool c = Some b
                  /\ ts n = present ct
                  /\ fs n = present cf
                  /\ es n = if b then present ct else present cf)
              \/
              (les n = absent
               /\ ts n = absent
               /\ fs n = absent
               /\ es n = absent)).
    Proof.
      intros * Sem.
      interp_str b H le Sem.
      interp_str b H t Sem.
      interp_str b H f Sem.
      do 3 eexists; intuition; eauto.
      specialize (Sem_le n); specialize (Sem_t n); specialize (Sem_f n);
        specialize (Sem n); inv Sem.
      - left; exists c, b0, ct, cf; repeat split; auto; intuition CESem.sem_det.
      - right; repeat split; auto; intuition CESem.sem_det.
    Qed.

    Lemma exp_inv:
      forall H b le es,
        CESem.sem_cexp b H (Eexp le) es ->
        CESem.sem_exp b H le es.
    Proof.
      intros * Sem n.
      now specialize (Sem n); inv Sem.
    Qed.

    (** [fby] is not a predicate but a function, so we directly state the
        correspondence.  *)
    Lemma fby_impl_from:
      forall n c xs,
        tr_stream_from n (Indexed.fby c xs) ≡
        CoInd.fby (Indexed.hold c xs n) (tr_stream_from n xs).
    Proof.
      cofix Cofix; intros.
      rewrite init_from_n; rewrite (init_from_n xs).
      unfold Indexed.fby at 1.
      destruct (xs n) eqn: E.
      - constructor; simpl; auto.
        rewrite Indexed.hold_abs; auto.
      - constructor; simpl; auto.
        erewrite (Indexed.hold_pres v); eauto.
    Qed.

    Corollary fby_impl:
      forall c xs,
      tr_stream (Indexed.fby c xs) ≡ CoInd.fby c (tr_stream xs).
    Proof.
      now setoid_rewrite fby_impl_from.
    Qed.

    (** ** Semantics of cexps *)

    (** State the correspondence for [cexp].
        Goes by induction on [cexp] and uses the previous inversion lemmas. *)
    Hint Constructors merge ite.
    Lemma sem_cexp_impl_from:
      forall n H b e es,
        CESem.sem_cexp b H e es ->
        CoInd.sem_cexp (tr_history_from n H) (tr_stream_from n b) e
                       (tr_stream_from n es).
    Proof.
      intros * Sem.
      revert dependent H; revert b es n.
      induction e; intros * Sem; unfold CESem.sem_cexp, CESem.lift in Sem.

      - apply merge_inv in Sem as (xs & ts & fs & ? & ? & ? & Spec).
        econstructor; eauto.
        apply merge_spec; use_spec Spec.

      - apply ite_inv in Sem as (bs & ts & fs & ? & ? & ? & Spec).
        econstructor; eauto.
        apply ite_spec; use_spec Spec.
        destruct H4.
        + apply val_to_bool_true' in H8; subst; firstorder.
        + apply val_to_bool_false' in H8; subst; firstorder.

      - apply exp_inv in Sem; constructor; auto.
    Qed.

    Corollary sem_cexp_impl:
      forall H b e es,
        CESem.sem_cexp b H e es ->
        CoInd.sem_cexp (tr_history H) (tr_stream b) e (tr_stream es).
    Proof. apply sem_cexp_impl_from. Qed.
    Hint Resolve sem_cexp_impl_from sem_cexp_impl.

    (** An inversion principle for annotated [cexp]. *)
    Lemma sem_caexp_inv:
      forall H b e es ck,
        CESem.sem_caexp b H ck e es ->
        CESem.sem_cexp b H e es
        /\ exists bs,
            CESem.sem_clock b H ck bs
            /\ (forall n, bs n = match es n with
                           | present _ => true
                           | absent => false
                           end).
    Proof.
      intros * Sem; split.
      - intro n; specialize (Sem n); inv Sem; auto.
      - exists (fun n => match es n with
                 | present _ => true
                 | absent => false
                 end); split; intro n; specialize (Sem n); inv Sem; auto.
    Qed.

    (** We deduce from the previous lemmas the correspondence for annotated
        [cexp]. *)
    Corollary sem_caexp_impl_from:
      forall n H b e es ck,
        CESem.sem_caexp b H ck e es ->
        CoInd.sem_caexp (tr_history_from n H) (tr_stream_from n b) ck e
                        (tr_stream_from n es).
    Proof.
      cofix Cofix; intros * Sem.
      pose proof Sem as Sem';
        apply sem_caexp_inv in Sem' as (Sem' & bs & Sem_ck & Ebs);
        apply (sem_cexp_impl_from n) in Sem';
        apply sem_clock_impl_from with (n:=n) in Sem_ck.
      rewrite (init_from_n es) in *.
      rewrite (init_from_n bs), Ebs in Sem_ck.
      destruct (es n); econstructor; eauto;
        rewrite init_from_tl, tr_history_from_tl;
        apply Cofix; auto.
    Qed.

    Corollary sem_caexp_impl:
      forall H b e es ck,
        CESem.sem_caexp b H ck e es ->
        CoInd.sem_caexp (tr_history H) (tr_stream b) ck e (tr_stream es).
    Proof. apply sem_caexp_impl_from. Qed.
    Hint Resolve sem_caexp_impl_from sem_caexp_impl.

    (** * RESET CORRESPONDENCE  *)

    (** We state the correspondence for [bools_of]. *)
    Lemma bools_of_impl_from:
      forall n xs rs,
        CESem.bools_of xs rs ->
        CStr.bools_of (tr_stream_from n xs) (tr_stream_from n rs).
    Proof.
      cofix Cofix; intros * Rst.
      pose proof Rst.
      specialize (Rst n).
      rewrite (init_from_n xs), (init_from_n rs).
      destruct (xs n); constructor; auto.
    Qed.

    Corollary bools_of_impl:
      forall xs rs,
        CESem.bools_of xs rs ->
        CStr.bools_of (tr_stream xs) (tr_stream rs).
    Proof. apply bools_of_impl_from. Qed.

    (** ** Properties about [count] and [mask] *)

    (** State the correspondance for [count].  *)
    Lemma count_impl_from:
      forall n (r: stream bool),
        count_acc (if r n then IStr.count r n - 1 else IStr.count r n)
                  (tr_stream_from n r)
        ≡ tr_stream_from n (IStr.count r).
    Proof.
      (* cofix-based proof encounter the guardness criterion (Why ??)  *)
      intros; apply ntheq_eqst; intro m.
      unfold Str_nth; revert n; induction m; intro; simpl.
      - destruct (r n) eqn: R; auto.
        apply count_true_ge_1 in R; rewrite Minus.minus_Sn_m; omega.
      - rewrite <-IHm; simpl; destruct (r n) eqn: R; destruct (r (S n));
          try (apply count_true_ge_1 in R; rewrite Minus.minus_Sn_m; auto);
          try (rewrite Nat.sub_succ, Nat.sub_0_r); auto.
    Qed.

    (** Generalizing is too intricate: we can use the generalized lemma above to
        deduce this one which states the correspondence for [mask]. *)
    Corollary mask_impl:
      forall k (r: stream bool) xss,
        wf_streams xss ->
        EqSts (tr_streams (IStr.mask k r xss))
              (List.map (CStr.mask k (tr_stream r)) (tr_streams xss)).
    Proof.
      intros * Const; unfold tr_streams, tr_stream.
      apply Forall2_forall2; split.
      - rewrite map_length, 2 tr_streams_from_length, mask_length; auto.
      - intros d1 d2 n' xs1 xs2 Len Nth1 Nth2.
        rewrite tr_streams_from_length in Len.
        rewrite <-Nth1, <-Nth2.
        assert (n' < length (tr_streams_from 0 xss)) by
            (rewrite mask_length in Len; auto;
             rewrite tr_streams_from_length; auto).
        rewrite map_nth' with (d':=d2), nth_tr_streams_from_nth; auto.
        rewrite mask_length in Len; auto.
        rewrite nth_tr_streams_from_nth; auto.
        unfold CStr.mask, IStr.mask.
        apply ntheq_eqst; intro m.
        unfold nth_tr_streams_from.
        rewrite init_from_nth, mask_nth, init_from_nth.
        unfold CStr.count, streams_nth.
        pose proof (count_impl_from 0 r) as Count.
        assert ((if r 0 then IStr.count r 0 - 1 else IStr.count r 0) = 0) as E
            by (simpl; destruct (r 0); auto).
        rewrite E in Count; rewrite Count, init_from_nth, Nat.eqb_sym.
        destruct (IStr.count r (m + 0) =? k); auto.
        apply nth_all_absent.
    Qed.

    (** * FINAL LEMMAS *)

    (** Correspondence for [clocks_of], used to give a base clock for node
        applications. *)
    Lemma tr_clocks_of_from:
      forall n xss,
        wf_streams xss ->
        CStr.clocks_of (tr_streams_from n xss) ≡ tr_stream_from n (CESem.clock_of xss).
    Proof.
      cofix Cofix; intros.
      constructor; simpl.
      - unfold CESem.clock_of, CESem.clock_of_instant.
        destruct (existsb (fun v : value => v <>b absent) (xss n)) eqn: E.
        + assert (forall v, v <> absent <-> (v <>b absent) = true)
            by (unfold nequiv_decb; setoid_rewrite Bool.negb_true_iff;
                setoid_rewrite not_equiv_decb_equiv; reflexivity).
          rewrite <-Exists_existsb with (P := fun v => hd v <> absent); auto.
          rewrite <-Exists_existsb with (P := fun v => v <> absent) in E; auto.
          apply Exists_In_tr_streams_from_hd in E; auto.
        + unfold nequiv_decb in *.
          apply existsb_Forall_neg, forallb_Forall in E.
          apply existsb_Forall_neg, forallb_Forall, Forall_forall.
          intros * Hin.
          eapply Forall_In_tr_streams_from_hd in E; eauto.
      - rewrite tr_streams_from_tl; auto.
    Qed.

    Corollary tr_clocks_of:
      forall xss,
        wf_streams xss ->
        CStr.clocks_of (tr_streams xss) ≡ tr_stream (CESem.clock_of xss).
    Proof. apply tr_clocks_of_from. Qed.

    Lemma sem_clocked_var_inv:
      forall b H x xs ck,
        CESem.sem_var H x xs ->
        CESem.sem_clocked_var b H x ck ->
        exists bs,
          CESem.sem_clock b H ck bs
          /\ (forall n, bs n = true <-> xs n <> absent).
    Proof.
      intros * Var Sem.
      assert (CESem.sem_clock b H ck (interp_clock b H ck)) as SemCk.
      { intro n; specialize (Sem n); specialize (Var n); destruct Sem as (Sem & Sem').
        unfold interp_clock, lift.
        destruct (xs n).
        - erewrite <-interp_clock_instant_sound; eauto; apply Sem'; auto.
        - erewrite <-interp_clock_instant_sound; eauto; apply Sem; eauto.
      }
      exists (interp_clock b H ck); split; auto.
      intro n; specialize (Var n); specialize (SemCk n); specialize (Sem n);
        destruct Sem as (Sem & Sem').
      split.
      - intros E E'.
        rewrite E in SemCk; apply Sem in SemCk as (?&?).
        rewrite E' in Var.
        eapply CESem.sem_var_instant_det in Var; eauto; discriminate.
      - intro E; apply not_absent_present in E as (?& E).
        rewrite E in Var.
        assert (CESem.sem_clock_instant (b n) (H n) ck true)
          by (apply Sem; eauto).
        eapply CESem.sem_clock_instant_det; eauto.
    Qed.

    Lemma sem_clocked_var_impl_from:
      forall n H b x xs ck,
        CESem.sem_var H x xs ->
        CESem.sem_clocked_var b H x ck ->
        CoInd.sem_clocked_var (tr_history_from n H) (tr_stream_from n b) x ck.
    Proof.
      intros * Var Sem; eapply sem_clocked_var_inv in Sem as (bs & Clock & Spec); eauto.
      apply sem_var_impl_from with (n := n) in Var;
        apply sem_clock_impl_from with (n := n) in Clock.
      split; eauto.
      intros * Var'.
      eapply CoInd.sem_var_det in Var; eauto.
      eexists; split; eauto.
      rewrite Var.
      clear - Spec.
      generalize n; clear n.
      cofix COFIX; intros.
      rewrite init_from_n, (init_from_n bs).
      destruct (xs n) eqn: E.
      - assert (bs n = false) as ->
            by (rewrite <-Bool.not_true_iff_false, Spec; auto).
        constructor; auto.
      - assert (bs n = true) as ->
            by (apply Spec; intro; congruence).
        constructor; auto.
    Qed.

    Corollary sem_clocked_var_impl:
      forall H b x xs ck,
        CESem.sem_var H x xs ->
        CESem.sem_clocked_var b H x ck ->
        CoInd.sem_clocked_var (tr_history H) (tr_stream b) x ck.
    Proof. apply sem_clocked_var_impl_from. Qed.

    Lemma sem_clocked_vars_impl:
      forall H b xs xss,
        CESem.sem_vars H (List.map fst xs) xss ->
        CESem.sem_clocked_vars b H xs ->
        CoInd.sem_clocked_vars (tr_history H) (tr_stream b) xs.
    Proof.
      unfold CESem.sem_clocked_vars; intros * Vars Sem.
      apply Forall_forall; intros (x, ck) Hin.
      apply sem_vars_inv in Vars.
      pose proof Hin as Hin'.
      apply in_map with (f := fst) in Hin.
      eapply Forall2_in_left in Vars as (?&?&?); eauto.
      eapply sem_clocked_var_impl; eauto.
      intro n; specialize (Sem n).
      eapply Forall_forall in Sem; eauto.
    Qed.
    Hint Resolve sem_clocked_vars_impl.

    (** The final theorem stating the correspondence for nodes applications.
        We have to use a custom mutually recursive induction scheme [sem_node_mult]. *)
    Hint Constructors CoInd.sem_equation.
    Theorem implies:
      forall f xss oss,
        Indexed.sem_node G f xss oss ->
        CoInd.sem_node G f (tr_streams xss) (tr_streams oss).
    Proof.
      induction 1 as [| |????????????????? IH| |??????????? Heqs IH]
                       using Indexed.sem_node_mult with
          (P_equation := fun b H e =>
                           Indexed.sem_equation G b H e ->
                           CoInd.sem_equation G (tr_history H) (tr_stream b) e);
        eauto.

      - econstructor; eauto.
        rewrite tr_clocks_of; eauto.
        edestruct Indexed.sem_node_wf; eauto.

      - econstructor; eauto.
        + rewrite tr_clocks_of; eauto.
          eapply wf_streams_mask.
          intro k; destruct (IH k) as (Sem &?).
          apply Indexed.sem_node_wf in Sem as (?&?); eauto.
        + apply bools_of_impl; eauto.
        + intro k; destruct (IH k) as (?&?).
          rewrite <- 2 mask_impl; eauto;
            eapply wf_streams_mask; intro n'; destruct (IH n') as (Sem &?);
              apply Indexed.sem_node_wf in Sem as (?&?); eauto.

      - econstructor; eauto; subst.
        rewrite <-fby_impl; eauto.

      - subst.
        CESem.assert_const_length xss.
        econstructor; eauto.
        + rewrite tr_clocks_of; eauto.
          eapply sem_clocked_vars_impl; eauto.
          rewrite map_fst_idck; eauto.
        + apply Forall_forall; intros * Hin.
          rewrite tr_clocks_of; auto.
          eapply Forall_forall in Heqs; eapply Forall_forall in IH; eauto.
    Qed.

  End Global.

End NLINDEXEDTOCOIND.
