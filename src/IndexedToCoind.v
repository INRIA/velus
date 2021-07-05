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
From Velus Require Import Clocks.
From Velus Require Import IndexedStreams.
From Velus Require Import CoindStreams.

Module Type INDEXEDTOCOIND
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS Ids Op OpAux)
       (Import IStr  : INDEXEDSTREAMS Ids Op OpAux Cks)
       (Import CStr  : COINDSTREAMS Ids Op OpAux Cks).

  (** * BASIC CORRESPONDENCES *)

  (** ** Definitions  *)

  (** Translate an indexed stream into a coinductive Stream.
        The [n]th element of the result Stream is the result of the application
        of the input stream on [n]. *)
  Definition tr_stream_from {A} (n: nat) (xs: stream A) : Stream A :=
    init_from n xs.

  Definition tr_stream {A} : stream A -> Stream A := tr_stream_from 0.

  (** Build a list of coinductive streams from an the integer range [0..m]. *)
  Definition seq_streams {A} (f: nat -> Stream A) (m: nat) : list (Stream A) :=
    List.map f (seq 0 m).

  (** Build the indexed stream corresponding to the [i]th elements of
        the input stream of lists. *)
  Definition streams_nth (k: nat) (xss: stream (list svalue)): stream svalue :=
    fun n => nth k (xss n) absent.

  (** Build a coinductive Stream extracting the [i]th element of the list
        obtained at each instant [n]. *)
  Definition nth_tr_streams_from (n: nat) (xss: stream (list svalue)) (k: nat)
    : Stream svalue :=
    tr_stream_from n (streams_nth k xss).

  (** Translate an indexed stream of list into a list of coinductive Streams
        using the two previous functions. *)
  Definition tr_streams_from (n: nat) (xss: stream (list svalue))
    : list (Stream svalue) :=
    seq_streams (nth_tr_streams_from n xss) (length (xss n)).

  Definition tr_streams: stream (list svalue) -> list (Stream svalue) :=
    tr_streams_from 0.

  Ltac unfold_tr_streams :=
    unfold tr_streams, tr_streams_from.

  (** Translate an history from indexed to coinductive world.
        Every element of the history is translated. *)
  Definition tr_history_from (n: nat) (H: IStr.history) : history :=
    Env.mapi (fun x _ => init_from n (fun n => match Env.find x (H n) with
                                         | Some v => v
                                         | None => absent
                                         end)) (H 0).


  (** Translate an history from coinductive to indexed world.
      Every element of the history is translated.
   *)
  Definition tr_history : IStr.history -> history :=
    tr_history_from 0.

  (** The counterpart of [tr_stream_from_tl] for histories. *)
  Lemma tr_history_from_tl:
    forall n H,
      history_tl (tr_history_from n H) = tr_history_from (S n) H.
  Proof.
    now setoid_rewrite Env.mapi_mapi.
  Qed.

  (** ** Properties  *)

  (** [init_from] is compatible wrt to extensional equality. *)
  Add Parametric Morphism A : (@init_from A)
      with signature eq ==> eq_str ==> @EqSt A
        as init_from_morph.
  Proof.
    cofix Cofix. intros x xs xs' E.
    rewrite init_from_n; rewrite (init_from_n xs').
    constructor; simpl; auto.
  Qed.

  (** The length of the range-built list of Streams is simply the difference *)
  (*  between the bounds of the range.  *)
  Lemma seq_streams_length:
    forall {A} m (str: nat -> Stream A),
      length (seq_streams str m) = m.
  Proof.
    intros; unfold seq_streams.
    now rewrite map_length, seq_length.
  Qed.

  (** The [n]th element of the range-built list of Streams starting at 0 is *)
  (*  the result of the function at [n]. *)
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
      List.map (@tl _) (tr_streams_from n xss) = tr_streams_from (S n) xss.
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

  (** If at instant [n], a property is true for all elements of the list *)
  (*  obtained from the indexed stream, then it is true for the first element *)
  (*  of the Streams starting at [n] in the translated list. *)
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

  Lemma sem_var_impl_from:
    forall n H x xs,
      IStr.sem_var H x xs ->
      sem_var (tr_history_from n H) x (tr_stream_from n xs).
  Proof.
    unfold IStr.sem_var, IStr.lift', sem_var_instant.
    intros * Sem.
    econstructor.
    - unfold Env.MapsTo. setoid_rewrite Env.gmapi.
      rewrite Sem; simpl; eauto.
    - unfold tr_stream_from.
      apply ntheq_eqst; intro.
      now rewrite 2 init_from_nth, Sem.
  Qed.

  Corollary sem_var_impl:
    forall H x xs,
      IStr.sem_var H x xs ->
      sem_var (tr_history H) x (tr_stream xs).
  Proof. apply sem_var_impl_from. Qed.
  Hint Resolve sem_var_impl_from sem_var_impl.

  (** This tactic automatically uses the interpretor to give a witness stream. *)
  Ltac interp_str b H x Sem :=
    let Sem_x := fresh "Sem_" x in
    let sol sem interp complete :=
        assert (sem b H x (interp b H x)) as Sem_x
            by (intro; match goal with n:nat |- _ => specialize (Sem n) end;
                unfold interp, lift_interp; inv Sem; erewrite <-complete; eauto)
    in
    let sol' sem interp complete :=
        assert (sem H x (interp H x)) as Sem_x
            by (intro; match goal with n:nat |- _ => specialize (Sem n) end;
                unfold interp, lift_interp'; inv Sem; erewrite <-complete; eauto)
    in
    match type of x with
    | ident => sol' IStr.sem_var interp_var interp_var_instant_complete
    | clock => sol IStr.sem_clock interp_clock interp_clock_instant_complete
    end.

  (** An inversion principle for [sem_clock] which also uses the interpretor. *)
    Lemma sem_clock_inv:
      forall H b bs ck x t k,
        IStr.sem_clock b H (Con ck x (t, k)) bs ->
        exists bs' xs,
          IStr.sem_clock b H ck bs'
          /\ IStr.sem_var H x xs
          /\
          (forall n,
              (bs' n = true
               /\ xs n = present (Venum k)
               /\ bs n = true)
              \/
              (bs' n = false
               /\ xs n = absent
               /\ bs n = false)
              \/
              (exists k',
                  bs' n = true
                  /\ xs n = present (Venum k')
                  /\ k <> k'
                  /\ bs n = false)).
    Proof.
      intros * Sem.
      interp_str b H ck Sem.
      interp_str b H x Sem.
      do 2 eexists; intuition; eauto.
      specialize (Sem_ck n); specialize (Sem_x n); specialize (Sem n); inv Sem.
      - left; repeat split; auto; intuition IStr.sem_det.
      - right; left; repeat split; auto; intuition IStr.sem_det.
      - right; right; exists b'; intuition; try IStr.sem_det.
    Qed.

    (** We can then deduce the correspondence lemma for [sem_clock].
        We go by induction on the clock [ck] then we use the above inversion
        lemma. *)
    Corollary sem_clock_impl_from:
      forall H b ck bs,
        IStr.sem_clock b H ck bs ->
        forall n, CStr.sem_clock (tr_history_from n H) (tr_stream_from n b) ck
                            (tr_stream_from n bs).
    Proof.
      induction ck; intros * Sem n.
      - constructor.
        revert Sem n; cofix CoFix; intros.
        rewrite init_from_n; rewrite (init_from_n bs).
        constructor; simpl; auto.
        specialize (Sem n); now inv Sem.
      - destruct p. apply sem_clock_inv in Sem as (bs' & xs & Sem_bs' & Sem_xs & Spec).
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
        + eapply CStr.Son_abs2; eauto.
          rewrite init_from_tl, tr_history_from_tl; auto.
    Qed.
    Hint Resolve sem_clock_impl_from.

    Corollary sem_clock_impl:
      forall H b ck bs,
        IStr.sem_clock b H ck bs ->
        CStr.sem_clock (tr_history H) (tr_stream b) ck (tr_stream bs).
    Proof. intros; apply sem_clock_impl_from; auto. Qed.
    Hint Resolve sem_clock_impl.

End INDEXEDTOCOIND.

Module IndexedToCoindFun
       (Ids     : IDS)
       (Op      : OPERATORS)
       (OpAux   : OPERATORS_AUX          Ids Op)
       (Cks     : CLOCKS                 Ids Op OpAux)
       (IStr    : INDEXEDSTREAMS         Ids Op OpAux Cks)
       (CStr    : COINDSTREAMS           Ids Op OpAux Cks)
<: INDEXEDTOCOIND Ids Op OpAux Cks IStr CStr.
  Include INDEXEDTOCOIND Ids Op OpAux Cks IStr CStr.
End IndexedToCoindFun.
