Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Coq.Sorting.Permutation.
Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Program.Tactics.
Require Import NPeano.

Require Import Coq.FSets.FMapPositive.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.Ordered.
Require Import Velus.NLustre.Stream.
Require Import Velus.NLustre.Streams.

Require Import Velus.NLustre.NLSemantics.
Require Import Velus.NLustre.NLInterpretor.
Require Import Velus.NLustre.NLSemanticsCoInd.

Require Import Setoid.
Module Type INDEXEDTOCOIND
       (Import Ids    : IDS)
       (Import Op     : OPERATORS)
       (Import OpAux  : OPERATORS_AUX        Op)
       (Import Clks   : CLOCKS           Ids)
       (Import Syn    : NLSYNTAX         Ids Op Clks)
       (Import Str    : STREAM               Op OpAux)
       (Import Ord    : ORDERED          Ids Op       Clks Syn)
       (Indexed       : NLSEMANTICS      Ids Op OpAux Clks Syn Str Ord)
       (Import Interp : NLINTERPRETOR    Ids Op OpAux Clks Syn Str Ord Indexed)
       (CoInd         : NLSEMANTICSCOIND Ids Op OpAux Clks Syn Ord).

  Section Global.

    Variable G : global.

    (** * BASIC CORRESPONDENCES *)

    (** ** Definitions  *)

    (** Translate an indexed stream into a coinductive Stream.
        The [n]th element of the result Stream is the result of the application
        of the input stream on [n].
     *)
    CoFixpoint tr_stream_from {A} (n: nat) (xs: stream A) :=
      xs n ::: tr_stream_from (S n) xs.
    Definition tr_stream {A} : stream A -> Stream A := tr_stream_from 0.

    (** Translate an indexed stream of list into a list of coinductive streams.
        We build the resulting list index by index.
     *)
    CoFixpoint tr_streams_at_from {A} (n: nat) (d: A) (xss: stream (list A)) (k: nat)
      : Stream A :=
      nth k (xss n) d ::: tr_streams_at_from (S n) d xss k.

    Definition build {A} (str: nat -> Stream A) (max start: nat): list (Stream A) :=
      List.map str (seq start (max - start)).

    Definition tr_streams_from_restr' {A} (d: A) (m n: nat) (xss: stream (list A))
      : list (Stream A) :=
      build (tr_streams_at_from n d xss) (length (xss n)) m.

    Definition tr_streams_from_restr
      : nat -> nat -> stream (list value) -> list (Stream value) :=
      tr_streams_from_restr' absent.

    Definition tr_streams_from: nat -> stream (list value) -> list (Stream value) :=
      tr_streams_from_restr 0.

    Definition tr_streams: stream (list value) -> list (Stream value) :=
      tr_streams_from 0.

    Ltac unfold_tr_streams :=
      unfold tr_streams, tr_streams_from,
      tr_streams_from_restr, tr_streams_from_restr'.

    (** Translate an history from indexed to coinductive world.
        Every element of the history is translated.
     *)
    Definition tr_history_from (n: nat) (H: Indexed.history) : CoInd.history :=
      PM.map (tr_stream_from n) H.
    Definition tr_history := tr_history_from 0.

    (** ** Properties  *)

    Lemma tr_stream_from_n:
      forall {A} (xs: stream A) n,
        tr_stream_from n xs = xs n ::: tr_stream_from (S n) xs.
    Proof.
      intros.
      now rewrite unfold_Stream at 1.
    Qed.

    (** [tr_stream_from] is compatible wrt to extensional equality. *)
    Add Parametric Morphism A : (@tr_stream_from A)
        with signature eq ==> eq_str ==> @EqSt A
          as tr_stream_from_morph.
    Proof.
      cofix Cofix; intros ** xs xs' E.
      rewrite tr_stream_from_n; rewrite (tr_stream_from_n xs').
      constructor; simpl; auto.
    Qed.

    (** Taking the tail of a translated stream from [n] is translating it from
        [S n]. *)
    Lemma tr_stream_from_tl:
      forall {A} n (xs: stream A),
        tl (tr_stream_from n xs) = tr_stream_from (S n) xs.
    Proof.
      intros; rewrite tr_stream_from_n; auto.
    Qed.

    (* Lemma tr_stream_const: *)
    (*   forall {A} (c: A) n, *)
    (*     tr_stream (Streams.const c) n = c. *)
    (* Proof. *)
    (*   induction n; rewrite unfold_Stream at 1; simpl. *)
    (*   - now rewrite tr_stream_0. *)
    (*   - now rewrite tr_stream_S. *)
    (* Qed. *)

    (* (** [tr_stream] is compatible wrt to [EqSt]. *) *)
    (* Add Parametric Morphism A : (@tr_stream A) *)
    (*     with signature @EqSt A ==> eq ==> eq *)
    (*       as tr_stream_morph. *)
    (* Proof. *)
    (*   intros xs ys Exs n. *)
    (*   revert xs ys Exs; induction n; intros; destruct xs, ys; inv Exs. *)
    (*   - rewrite 2 tr_stream_0; auto. *)
    (*   - rewrite 2 tr_stream_S; auto. *)
    (* Qed. *)

    (* Fact tr_streams_app: *)
    (*   forall A (xss yss: list (Stream A)) n, *)
    (*     tr_streams (xss ++ yss) n = tr_streams xss n ++ tr_streams yss n. *)
    (* Proof. *)
    (*   intros; induction xss; simpl; auto. *)
    (*   f_equal; auto. *)
    (* Qed. *)

    Lemma build_length:
      forall {A} k (str: nat -> Stream A) m,
        length (build str k m) = k - m.
    Proof.
      intros; unfold build.
      now rewrite map_length, seq_length.
    Qed.

    Lemma nth_build:
      forall {A} k str n (xs_d: Stream A),
        n < k ->
        nth n (build str k 0) xs_d = str n.
    Proof.
      unfold build; intros.
      rewrite map_nth' with (d':=0); simpl.
      - rewrite seq_nth; auto; omega.
      - rewrite seq_length; omega.
    Qed.

    (** The counterpart of [tr_stream_from_tl] for lists of Streams.
        Direct proof of equality seems hard, so we use a trivial pointwise
        equality for lists. *)
    Lemma Forall2_pointwise:
      forall {A} (l1 l2: list A),
        Forall2 eq l1 l2 ->
        l1 = l2.
    Proof.
      induction 1; auto.
      f_equal; auto.
    Qed.

    Definition const_length_strs {A} (xss: stream (list A)) :=
      forall k, length (xss k) = length (xss (S k)).

    Lemma tr_streams_from_tl:
      forall n xss,
        const_length_strs xss ->
        List.map (@tl value) (tr_streams_from n xss) = tr_streams_from (S n) xss.
    Proof.
      intros ** Len.
      apply Forall2_pointwise.
      apply Forall2_forall2.
      split; unfold_tr_streams; rewrite map_length.
      - now rewrite 2 build_length, Len.
      - intros ** Hlen E1 E2; rewrite <-E1, <-E2.
        rewrite map_nth' with (d':=a); auto.
        rewrite build_length in Hlen.
        rewrite 2 nth_build; try omega.
        + reflexivity.
        + rewrite <-Len; omega.
    Qed.

    (** The counterpart of [tr_stream_from_tl] for histories. *)
    Lemma tr_history_from_tl:
      forall n H,
        CoInd.history_tl (tr_history_from n H) = tr_history_from (S n) H.
    Proof.
      now repeat setoid_rewrite pm_map_map.
    Qed.

    (** * SEMANTICS CORRESPONDENCE *)

    (** ** Variables *)

    (** An inversion principle for [sem_var]. *)
    Lemma sem_var_inv:
      forall H b x xs,
      Indexed.sem_var b H x xs ->
      exists xs',
        PM.find x H = Some xs'
        /\ xs ≈ xs'.
    Proof.
      unfold Indexed.sem_var, Indexed.lift.
      intros ** Sem.
      destruct (PM.find x H) as [xs'|] eqn: E; simpl in *.
      - exists xs'; intuition.
        intro n; specialize (Sem n).
        inversion_clear Sem as [Find].
        unfold Indexed.restr, PM.map in Find.
        rewrite PM.gmapi, E in Find.
        now inv Find.
      - specialize (Sem 0).
        inversion_clear Sem as [Find].
        unfold Indexed.restr, PM.map in Find.
        now rewrite PM.gmapi, E in Find.
    Qed.

    Lemma sem_var_impl_from:
      forall n H b x xs,
      Indexed.sem_var b H x xs ->
      CoInd.sem_var (tr_history_from n H) x (tr_stream_from n xs).
    Proof.
      intros ** Sem.
      apply sem_var_inv in Sem as (? & ? & E).
      econstructor.
      - apply PM.find_2.
        unfold tr_history_from, PM.map.
        rewrite PM.gmapi.
        now erewrite PM.find_1; eauto.
      - now rewrite E.
    Qed.

    Corollary sem_var_impl:
      forall H b x xs,
      Indexed.sem_var b H x xs ->
      CoInd.sem_var (tr_history H) x (tr_stream xs).
    Proof. apply sem_var_impl_from. Qed.

    (* Lemma tr_streams_from_nil: *)
    (*   forall n xss, *)
    (*     xss n = [] -> *)
    (*     tr_streams_from n xss = []. *)
    (* Proof. *)
    (*   intros ** E; unfold_tr_streams; now rewrite E. *)
    (* Qed. *)

    Lemma seq_cons:
      forall k m,
        m < k ->
        seq m (k - m) = m :: seq (S m) (k - S m).
    Proof.
      induction k; intros ** E; simpl.
      - omega.
      - destruct m; simpl.
        + now rewrite Nat.sub_0_r.
        + rewrite <- 2 seq_shift.
          rewrite IHk; auto.
          omega.
    Qed.

    Lemma build_cons:
      forall {A} k (str: nat -> Stream A) m,
        m < k ->
        build str k m = str m :: build str k (S m).
    Proof.
      unfold build.
      intros.
      rewrite seq_cons; auto.
    Qed.

    (* Lemma build_app: *)
    (*   forall {A} k (acc acc': list (Stream A)) str m, *)
    (*     build (acc ++ acc') str k m = build acc str k m ++ acc'. *)
    (* Proof. *)
    (*   induction k; intros; simpl; auto. *)
    (*   destruct m; simpl. *)
    (*   - now rewrite <-IHk, app_comm_cons. *)
    (*   - destruct (k <=? m); auto. *)
    (*     now rewrite <-IHk, app_comm_cons. *)
    (* Qed. *)

    (* Corollary build_cons: *)
    (*   forall {A} k a (acc: list (Stream A)) str m, *)
    (*     build (a :: acc) str k m = build [a] str k m ++ acc. *)
    (* Proof. *)
    (*   intros; rewrite cons_is_app. *)
    (*   apply build_app. *)
    (* Qed. *)

    (* Corollary build_nil: *)
    (*   forall {A} k (acc: list (Stream A)) str m, *)
    (*     build acc str k m = build [] str k m ++ acc. *)
    (* Proof. *)
    (*   intros; change acc with ([] ++ acc); eapply build_app. *)
    (* Qed. *)

    (* Lemma tr_streams_from_cons: *)
    (*   forall n xss x xs, *)
    (*     xss n = x :: xs -> *)
    (*     tr_streams_from n xss *)
    (*     = tr_streams_at_from n absent xss 0 :: tr_streams_from_restr 1 n xss. *)
    (* Proof. *)
    (*   intros ** E; unfold_tr_streams; rewrite E; simpl. *)
    (*   clear E; induction xs. *)
    (*   - simpl; auto. *)
    (*   - simpl. *)
    (*     rewrite build_cons, IHxs. *)
    (*     destruct (length xs <=? 0); auto. *)
    (*     symmetry; rewrite build_cons; auto. *)
    (* Qed. *)

    Definition streams_tl {A} (xss: stream (list A)): stream (list A) :=
      fun n => List.tl (xss n).

    Definition streams_nth {A} (k: nat) (a: A) (xss: stream (list A)): stream A :=
      fun n => nth k (xss n) a.

    Definition streams_hd {A}: A -> stream (list A) -> stream A := streams_nth 0.

    Lemma streams_tl_cons:
      forall {A} (xss: stream (list A)) x xs n,
        xss n = x :: xs ->
        xs = streams_tl xss n.
    Proof.
      intros ** E; unfold streams_tl; now rewrite E.
    Qed.

    Lemma streams_hd_cons:
      forall {A} a (xss: stream (list A)) x xs n,
        xss n = x :: xs ->
        x = streams_hd a xss n.
    Proof.
      intros ** E; unfold streams_hd, streams_nth; now rewrite E.
    Qed.

    Fixpoint drop {A} (n: nat) (l: list A) : list A :=
      match n with
      | 0 => l
      | S n => drop n (List.tl l)
      end.

    Lemma drop_nil:
      forall {A} n,
        @drop A n [] = [].
    Proof.
      induction n; simpl; auto.
    Qed.

    Lemma drop_cons:
      forall {A} n (xs: list A) x,
        n > 0 ->
        drop n (x :: xs) = drop (n - 1) xs.
    Proof.
      induction n; simpl; intros ** H.
      - omega.
      - now rewrite Nat.sub_0_r.
    Qed.

    Lemma tl_length:
      forall {A} (l: list A),
        length (List.tl l) = length l - 1.
    Proof.
      induction l; simpl; auto; omega.
    Qed.

    Lemma drop_length:
      forall {A} n (l: list A),
        length (drop n l) = length l - n.
    Proof.
      induction n; intros; simpl.
      - omega.
      - rewrite IHn, tl_length; omega.
    Qed.

    Lemma nth_drop:
      forall {A} (xs: list A) n' n x_d,
        nth n' (drop n xs) x_d = nth (n' + n) xs x_d.
    Proof.
      induction xs; intros; simpl.
      - rewrite drop_nil; simpl; destruct (n' + n); destruct n'; auto.
      - destruct n; simpl.
        + now rewrite <-plus_n_O.
        + destruct n'; simpl; rewrite IHxs; auto.
          now rewrite Plus.plus_Snm_nSm.
    Qed.

    Lemma nth_seq:
      forall {A} n' n (xs: list A) x,
        n' < length xs - n ->
        nth n' (seq n (length xs - n)) x = n' + n.
    Proof.
      intros; rewrite seq_nth; try omega.
    Qed.

    (** An inversion principle for [sem_vars]. *)
    Lemma sem_vars_inv_from:
      forall H b xs xss,
        Indexed.sem_vars b H xs xss ->
        forall n,
          Forall2 (fun x k => Indexed.sem_var b H x (streams_nth k absent xss))
                  (drop n xs) (seq n (length xs - n)).
    Proof.
      unfold Indexed.sem_vars, Indexed.lift.
      intros ** Sem n.
      apply Forall2_forall2; split.
      - now rewrite drop_length, seq_length.
      - intros x_d k_d n' x k Length Hdrop Hseq.
        rewrite drop_length in Length.
        rewrite nth_drop in Hdrop.
        rewrite nth_seq in Hseq; auto; subst.
        intro m; specialize (Sem m).
        apply Forall2_forall2 in Sem.
        eapply Sem; eauto.
        + now apply Nat.lt_add_lt_sub_r.
        + unfold streams_nth; eauto.
    Qed.

    Corollary sem_vars_inv:
      forall H b xs xss,
        Indexed.sem_vars b H xs xss ->
        Forall2 (fun x k => Indexed.sem_var b H x (streams_nth k absent xss))
                xs (seq 0 (length xs)).
    Proof.
      intros ** Sem; apply sem_vars_inv_from with (n:=0) in Sem.
      now rewrite Nat.sub_0_r in Sem.
    Qed.

    Lemma tr_stream_from_streams_nth:
      forall n k xss,
        tr_stream_from n (streams_nth k absent xss) ≡
        tr_streams_at_from n absent xss k.
    Proof.
      cofix Cofix; intros.
      constructor; simpl; auto.
    Qed.

    Corollary nth_tr_streams_from:
      forall n k xss xs_d,
        k < length (xss n) ->
        nth k (tr_streams_from n xss) xs_d =
        tr_streams_at_from n absent xss k.
    Proof.
      unfold_tr_streams.
      intros; now rewrite nth_build.
    Qed.

    Corollary tr_streams_from_length:
      forall n xss,
        length (tr_streams_from n xss) = length (xss n).
    Proof.
      unfold_tr_streams; intros.
      rewrite build_length; simpl; omega.
    Qed.

    Corollary sem_vars_impl_from:
      forall n H b xs xss,
      Indexed.sem_vars b H xs xss ->
      Forall2 (CoInd.sem_var (tr_history_from n H)) xs (tr_streams_from n xss).
    Proof.
      intros ** Sem.
      assert (length xs = length (xss n)) as Length by
            (unfold Indexed.sem_vars, Indexed.lift in Sem; specialize (Sem n);
             now apply Forall2_length in Sem).
      apply Forall2_forall2; split.
      - now rewrite tr_streams_from_length.
      - apply sem_vars_inv in Sem.
        intros x_d xs_d n' x xs' En' Ex Exs'.
        apply Forall2_forall2 in Sem as (? & Sem).
        assert (nth n' (seq 0 (length xs)) 0 = n') as Nth by
              (rewrite <-(Nat.sub_0_r (length xs)), plus_n_O; apply nth_seq; omega).
        eapply Sem in Nth; eauto.
        apply (sem_var_impl_from n) in Nth.
        subst.
        rewrite nth_tr_streams_from, <-tr_stream_from_streams_nth; auto.
        now rewrite <-Length.
    Qed.

    Corollary sem_vars_impl:
      forall H b xs xss,
      Indexed.sem_vars b H xs xss ->
      Forall2 (CoInd.sem_var (tr_history H)) xs (tr_streams xss).
    Proof. apply sem_vars_impl_from. Qed.

    (** ** Synchronization *)

    Lemma tr_streams_at_from_tl:
      forall {A} n m k (d: A) xss,
        Str_nth_tl n (tr_streams_at_from m d xss k) =
        tr_streams_at_from (n + m) d xss k.
    Proof.
      induction n; intros; simpl; auto.
      now rewrite IHn, Nat.add_succ_r.
    Qed.

    Lemma tr_streams_at_from_nth:
      forall {A} n m k (d: A) xss,
        Str_nth n (tr_streams_at_from m d xss k) = nth k (xss (n + m)) d.
    Proof.
      unfold Str_nth.
      induction n; intros; simpl; auto.
      now rewrite IHn, Nat.add_succ_r.
    Qed.

    Lemma Forall_In_tr_streams_nth:
      forall n P xss x,
        const_length_strs xss ->
        Forall P (xss n) ->
        In x (tr_streams xss) ->
        P (Str_nth n x).
    Proof.
      unfold_tr_streams; intros ** Length Ps Hin.
      apply In_ex_nth with (d:=x) in Hin as (k & Len & Nth).
      rewrite build_length, Nat.sub_0_r in Len.
      assert (length (xss 0) = length (xss n)) as E
          by (clear - Length; induction n; simpl; auto; now rewrite IHn, Length).
      pose proof Len; rewrite E in Len.
      rewrite nth_build in Nth; auto.
      apply eq_EqSt in Nth.
      apply (eqst_ntheq n) in Nth.
      rewrite <-Nth, tr_streams_at_from_nth, <-plus_n_O.
      eapply nth_In in Len.
      eapply In_Forall in Ps; eauto.
    Qed.

    Lemma Forall_In_tr_streams_nth':
      forall n P xss x,
        const_length_strs xss ->
        Forall (fun x => P (Str_nth n x)) (tr_streams xss) ->
        In x (xss n) ->
        P x.
    Proof.
      unfold_tr_streams; intros ** Length Ps Hin.
      assert (length (xss 0) = length (xss n)) as E
          by (clear - Length; induction n; simpl; auto; now rewrite IHn, Length).
      apply In_ex_nth with (d:=absent) in Hin as (k & Len & Nth); subst.
      pose proof Len; rewrite <-E in Len.
      rewrite (plus_n_O n), <-tr_streams_at_from_nth.
      eapply In_Forall in Ps; eauto.
      rewrite <-nth_tr_streams_from with (xs_d:=tr_streams_at_from 0 absent xss n);
        eauto.
      apply nth_In.
      now rewrite build_length, Nat.sub_0_r.
    Qed.

    Corollary Forall_tr_streams_nth:
      forall xss,
        const_length_strs xss ->
        forall n P,
          (Forall P (xss n) <-> Forall (fun x => P (Str_nth n x)) (tr_streams xss)).
    Proof.
      split; intros; apply Forall_forall; intros.
      - eapply Forall_In_tr_streams_nth; eauto.
      - eapply Forall_In_tr_streams_nth'; eauto.
    Qed.

    Lemma Forall_In_tr_streams_from_hd:
      forall n P xss x,
        Forall P (xss n) ->
        In x (tr_streams_from n xss) ->
        P (hd x).
    Proof.
      unfold_tr_streams; intros ** Ps Hin.
      apply In_ex_nth with (d:=x) in Hin as (k & Len & Nth).
      rewrite build_length, Nat.sub_0_r in Len.
      rewrite nth_build in Nth; auto.
      apply eq_EqSt in Nth.
      rewrite <-tr_stream_from_streams_nth in Nth.
      rewrite tr_stream_from_n in Nth.
      inversion Nth as (Hhd).
      rewrite <-Hhd; simpl.
      unfold streams_nth.
      eapply In_Forall; eauto.
      apply nth_In; auto.
    Qed.

    Lemma Forall_In_tr_streams_from_hd':
      forall n P xss x,
        Forall (fun x => P (hd x)) (tr_streams_from n xss) ->
        In x (xss n) ->
        P x.
    Proof.
      unfold_tr_streams; intros ** Ps Hin.
      apply In_ex_nth with (d:=absent) in Hin as (k & Len & Nth); subst.
      rewrite (plus_n_O n), <-tr_streams_at_from_nth.
      unfold Str_nth.
      eapply In_Forall in Ps; eauto.
      rewrite tr_streams_at_from_tl, <-plus_n_O.
      erewrite <-nth_build with (xs_d:=tr_streams_at_from 0 absent xss n); eauto.
      apply nth_In.
      now rewrite build_length, Nat.sub_0_r.
    Qed.

    Corollary Forall_tr_streams_from_hd:
      forall xss n P,
        Forall P (xss n) <-> Forall (fun x => P (hd x)) (tr_streams_from n xss).
    Proof.
      split; intros; apply Forall_forall; intros.
      - eapply Forall_In_tr_streams_from_hd; eauto.
      - eapply Forall_In_tr_streams_from_hd'; eauto.
    Qed.

    Lemma same_clock_impl:
      forall xss,
        const_length_strs xss ->
        Indexed.same_clock xss ->
        CoInd.same_clock (tr_streams xss).
    Proof.
      unfold Indexed.same_clock, Indexed.instant_same_clock.
      intros ** Same n.
      destruct (Same n) as [E|Ne].
      - left; apply Forall_tr_streams_nth with (P:=fun x => x = absent); auto.
      - right. apply Forall_tr_streams_nth with (P:=fun x => x <> absent); auto.
    Qed.

    Ltac contr := try match goal with
                      | H: ?x <> ?x |- _ => now contradict H
                      end.

    Lemma same_clock_app_impl:
      forall xss yss,
        (forall n, xss n <> []) ->
        (forall n, yss n <> []) ->
        const_length_strs xss ->
        const_length_strs yss ->
        Indexed.same_clock xss ->
        Indexed.same_clock yss ->
        (forall n, Indexed.absent_list (xss n) <-> Indexed.absent_list (yss n)) ->
        CoInd.same_clock (tr_streams xss ++ tr_streams yss).
   Proof.
      intros ** Nxss Nyss Cxss Cyss Hxss Hyss Same n.
      apply same_clock_impl in Hxss; apply same_clock_impl in Hyss; auto.
      unfold Indexed.same_clock, Indexed.instant_same_clock in Same;
        specialize (Same n);
        specialize (Hxss n); specialize (Hyss n);
        specialize (Nxss n); specialize (Nyss n).
      destruct Hxss as [Hxss|Hxss]; destruct Hyss as [Hyss|Hyss].
      - left; apply Forall_app; intuition.
      - rewrite <-Forall_tr_streams_nth with (P:=fun x => x = absent) in Hxss;
          rewrite <-Forall_tr_streams_nth with (P:=fun x => x <> absent) in Hyss; auto.
        rewrite Same in Hxss.
        clear - Hxss Hyss Nyss; induction (yss n); inv Hxss; inv Hyss; contr.
      - rewrite <-Forall_tr_streams_nth with (P:=fun x => x = absent) in Hyss;
          rewrite <-Forall_tr_streams_nth with (P:=fun x => x <> absent) in Hxss; auto.
        rewrite <-Same in Hyss.
        clear - Hxss Hyss Nxss; induction (xss n); inv Hxss; inv Hyss; contr.
      - right; apply Forall_app; intuition.
    Qed.

    (** ** lexp level synchronous operators inversion principles

        The indexed semantics is inductive only instant-speaking, therefore we
        can't use usual tactics like inversion nor induction.
        We prove some lemmas to provide inversion-like tactics on the semantics
        of lexps.
        These lemmas are proven using the classical axiom of choice which gives,
        from an instant semantics entailment true at every instant, the existence
        of a stream verifying the general entailment.
     *)

    (* Require Import ClassicalChoice. *)
    (* Lemma lift_choice: *)
    (*   forall {A B} (sem: bool -> Indexed.R -> A -> B -> Prop) b H x, *)
    (*     (forall n, exists v, sem (b n) (Indexed.restr H n) x v) -> *)
    (*     exists ys, Indexed.lift b sem H x ys. *)
    (* Proof. *)
    (*   unfold Indexed.lift. *)
    (*   intros ** Sem. *)
    (*   apply choice in Sem; auto. *)
    (* Qed. *)

    (* Ltac witness_str P Sem n xs Sem_x := *)
    (*   assert (exists xs, P xs) as (xs & Sem_x) by *)
    (*       (apply lift_choice; intro; specialize (Sem n); inv Sem; *)
    (*        eexists; eauto). *)

    Ltac interp_str b H x Sem :=
      let Sem_x := fresh "Sem_" x in
      let sol sem interp sound :=
          assert (sem b H x (interp b H x)) as Sem_x by
                (intro n; specialize (Sem n); unfold interp, lift;
                 inv Sem; erewrite <-sound; eauto)
      in
      match type of x with
      | lexp => sol Indexed.sem_lexp interp_lexp interp_lexp_instant_sound
      | cexp => sol Indexed.sem_cexp interp_cexp interp_cexp_instant_sound
      | ident => sol Indexed.sem_var interp_var interp_var_instant_sound
      | clock => sol Indexed.sem_clock interp_clock interp_clock_instant_sound
      end.

    Lemma when_inv:
      forall H b e x k es,
        Indexed.sem_lexp b H (Ewhen e x k) es ->
        exists ys xs,
          Indexed.sem_lexp b H e ys
          /\ Indexed.sem_var b H x xs
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
      intros ** Sem.
      interp_str b H e Sem.
      interp_str b H x Sem.
      do 2 eexists; intuition; eauto.
      specialize (Sem_e n); specialize (Sem_x n); specialize (Sem n); inv Sem.
      - left; exists sc, xc; intuition Indexed.sem_det.
      - right; left; exists sc, xc; intuition; try Indexed.sem_det.
        now rewrite Bool.negb_involutive.
      - right; right; intuition Indexed.sem_det.
    Qed.

    Lemma unop_inv:
      forall H b op e ty es,
        Indexed.sem_lexp b H (Eunop op e ty) es ->
        exists ys,
          Indexed.sem_lexp b H e ys
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
      intros ** Sem.
      interp_str b H e Sem.
      eexists; intuition; eauto.
      specialize (Sem_e n); specialize (Sem n); inv Sem.
      - left; exists c, c'; intuition Indexed.sem_det.
      - right; intuition Indexed.sem_det.
    Qed.

    Lemma binop_inv:
      forall H b op e1 e2 ty es,
        Indexed.sem_lexp b H (Ebinop op e1 e2 ty) es ->
        exists ys zs,
          Indexed.sem_lexp b H e1 ys
          /\ Indexed.sem_lexp b H e2 zs
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
      intros ** Sem.
      interp_str b H e1 Sem.
      interp_str b H e2 Sem.
      do 2 eexists; intuition; eauto.
      specialize (Sem_e1 n); specialize (Sem_e2 n); specialize (Sem n); inv Sem.
      - left; exists c1, c2, c'; intuition Indexed.sem_det.
      - right; intuition Indexed.sem_det.
    Qed.

    (** ** Semantics of clocks *)

    Ltac rewrite_strs :=
      repeat match goal with
               H: (_: stream value) (_: nat) = (_: value) |- _ => rewrite H in *
             end.

    (** An inversion principle for [sem_clock], requiring also the axiom of
        choice.  *)
    Lemma sem_clock_inv:
      forall H b bs ck x k,
        Indexed.sem_clock b H (Con ck x k) bs ->
        exists bs' xs,
          Indexed.sem_clock b H ck bs'
          /\ Indexed.sem_var b H x xs
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
      intros ** Sem.
      interp_str b H ck Sem.
      interp_str b H x Sem.
      do 2 eexists; intuition; eauto.
      specialize (Sem_ck n); specialize (Sem_x n); specialize (Sem n); inv Sem.
      - left; exists c; intuition Indexed.sem_det.
      - right; left; intuition Indexed.sem_det.
      - right; right; exists c; intuition; try Indexed.sem_det.
        now rewrite Bool.negb_involutive.
    Qed.

    (** We can then deduce the correspondence lemma for [sem_clock].
        We go by induction on the clock [ck] then we use the above inversion
        lemma. *)
    Corollary sem_clock_impl_from:
      forall H b ck bs,
        Indexed.sem_clock b H ck bs ->
        forall n, CoInd.sem_clock (tr_history_from n H) (tr_stream_from n b) ck
                             (tr_stream_from n bs).
    Proof.
      induction ck; intros ** Sem n.
      - constructor.
        revert Sem n; cofix; intros.
        rewrite tr_stream_from_n; rewrite (tr_stream_from_n bs).
        constructor; simpl; auto.
        specialize (Sem n); now inv Sem.
      - apply sem_clock_inv in Sem as (bs' & xs & Sem_bs' & Sem_xs & Spec).
        revert Spec n; cofix; intros.
        rewrite (tr_stream_from_n bs).
        apply IHck with (n:=n) in Sem_bs';
          rewrite (tr_stream_from_n bs') in Sem_bs'.
        apply (sem_var_impl_from n) in Sem_xs;
          rewrite (tr_stream_from_n xs) in Sem_xs.
        destruct (Spec n) as [|[]]; destruct_conjs; rewrite_strs.
        + econstructor; eauto.
          rewrite tr_stream_from_tl, tr_history_from_tl; auto.
        + econstructor; eauto.
          rewrite tr_stream_from_tl, tr_history_from_tl; auto.
        + rewrite <-(Bool.negb_involutive b0).
          eapply CoInd.Son_abs2; eauto.
          rewrite tr_stream_from_tl, tr_history_from_tl; auto.
          rewrite Bool.negb_involutive; auto.
    Qed.

    (** ** Semantics of lexps *)

    (** State the correspondence for [lexp].
        Goes by induction on [lexp]. *)
    Lemma sem_lexp_impl_from:
      forall n H b e es,
        Indexed.sem_lexp b H e es ->
        CoInd.sem_lexp (tr_history_from n H) (tr_stream_from n b) e
                       (tr_stream_from n es).
    Proof.
      intros ** Sem.
      revert dependent H; revert b es n.
      induction e; intros ** Sem; unfold Indexed.sem_lexp, Indexed.lift in Sem.

      - constructor.
        revert dependent es; revert b; revert n.
        cofix; intros.
        rewrite tr_stream_from_n; rewrite (tr_stream_from_n b).
        constructor; simpl.
        + specialize (Sem n);
            inversion_clear Sem as [? ? Hes| | | | | | | |];
            destruct (b n); auto.
        + destruct (b n); auto.

      - constructor.
        apply sem_var_impl_from with (b := b).
        intros n'; specialize (Sem n').
        now inv Sem.

      - apply when_inv in Sem as (ys & xs & ? & ? & Spec).
        econstructor; eauto using sem_var_impl_from.
        revert dependent n; revert Spec; cofix; intros.
        rewrite tr_stream_from_n;
          rewrite (tr_stream_from_n xs);
          rewrite (tr_stream_from_n es).
        destruct (Spec n) as [|[]]; destruct_conjs;
          rewrite_strs; auto using CoInd.when.

      - apply unop_inv in Sem as (ys & ? & Spec).
        econstructor; eauto.
        revert dependent n; revert Spec; cofix; intros.
        rewrite tr_stream_from_n; rewrite (tr_stream_from_n es).
        destruct (Spec n) as [|]; destruct_conjs;
          rewrite_strs; auto using CoInd.lift1.

      - apply binop_inv in Sem as (ys & zs & ? & ? & Spec).
        econstructor; eauto.
        revert dependent n; revert Spec; cofix; intros.
        rewrite tr_stream_from_n;
          rewrite (tr_stream_from_n zs);
          rewrite (tr_stream_from_n es).
        destruct (Spec n) as [|[]]; destruct_conjs;
          rewrite_strs; auto using CoInd.lift2.
    Qed.

    Corollary sem_lexp_impl:
      forall H b e es,
        Indexed.sem_lexp b H e es ->
        CoInd.sem_lexp (tr_history H) (tr_stream b) e (tr_stream es).
    Proof. apply sem_lexp_impl_from. Qed.

    (** An inversion principle for lists of [lexp]. *)
    Lemma sem_lexps_inv:
      forall H b es ess,
        Indexed.sem_lexps b H es ess ->
        exists ess',
          Forall2 (Indexed.sem_lexp b H) es ess'
          /\ forall n, ess n = List.map (fun es => es n) ess'.
    Proof.
      intros ** Sem.
      exists (interp_lexps' b H es); split.
      - eapply interp_lexps'_sound; eauto.
      - intro n; specialize (Sem n); induction Sem; simpl; auto.
        f_equal; auto.
        unfold interp_lexp; now apply interp_lexp_instant_sound.
    Qed.

    (** Generalization for lists of [lexp]. *)
    Corollary sem_lexps_impl_from:
      forall n H b es ess,
        Indexed.sem_lexps b H es ess ->
        Forall2 (CoInd.sem_lexp (tr_history_from n H) (tr_stream_from n b)) es
                (tr_streams_from n ess).
    Proof.
      intros ** Sem.
      apply sem_lexps_inv in Sem as (ess' & Sem & Eess').
      assert (length es = length (ess n)) as Length by
          (rewrite Eess', map_length; simpl; eapply Forall2_length; eauto).
      apply Forall2_forall2; split.
      - unfold_tr_streams; rewrite build_length; simpl; omega.
      - intros ** Nth; subst.
        rewrite nth_tr_streams_from; try omega.
        rewrite <-tr_stream_from_streams_nth.
        apply sem_lexp_impl_from.
        eapply (Forall2_forall2_eq _ _ (@eq_refl lexp) (eq_str_refl))
          in Sem as (? & Sem); try solve_proper.
        eapply Sem; eauto.
        unfold streams_nth.
        intros k; rewrite Eess'.
        change absent with ((fun es => es k) (fun _ => absent)).
        rewrite map_nth; eauto.
    Qed.

    Corollary sem_lexps_impl:
      forall H b es ess,
        Indexed.sem_lexps b H es ess ->
        Forall2 (CoInd.sem_lexp (tr_history H) (tr_stream b)) es (tr_streams ess).
    Proof. apply sem_lexps_impl_from. Qed.

    (** An inversion principle for annotated [lexp]. *)
    Lemma sem_laexp_inv:
      forall H b e es ck,
        Indexed.sem_laexp b H ck e es ->
        Indexed.sem_lexp b H e es
        /\ exists bs,
            Indexed.sem_clock b H ck bs
            /\ forall n,
              bs n = match es n with
                     | present _ => true
                     | absent => false
                     end.
    Proof.
      intros ** Sem; split.
      - intro n; specialize (Sem n); inv Sem; auto.
      - exists (fun n => match es n with
                 | present _ => true
                 | absent => false
                 end); split; intro n; specialize (Sem n); inv Sem; auto.
    Qed.

    (** We deduce from the previous lemmas the correspondence for annotated
        [lexp]. *)
    Corollary sem_laexp_impl_from:
      forall n H b e es ck,
        Indexed.sem_laexp b H ck e es ->
        CoInd.sem_laexp (tr_history_from n H) (tr_stream_from n b) ck e
                        (tr_stream_from n es).
    Proof.
      cofix Cofix; intros ** Sem.
      pose proof Sem as Sem';
        apply sem_laexp_inv in Sem' as (Sem' & bs & Sem_ck & Ebs);
        apply (sem_lexp_impl_from n) in Sem';
        apply sem_clock_impl_from with (n:=n) in Sem_ck.
      rewrite (tr_stream_from_n es) in *.
      rewrite (tr_stream_from_n bs), Ebs in Sem_ck.
      destruct (es n); econstructor; eauto;
        rewrite tr_stream_from_tl, tr_history_from_tl;
        apply Cofix; auto.
    Qed.

    Corollary sem_laexp_impl:
      forall H b e es ck,
        Indexed.sem_laexp b H ck e es ->
        CoInd.sem_laexp (tr_history H) (tr_stream b) ck e (tr_stream es).
    Proof. apply sem_laexp_impl_from. Qed.

    (* (** Specification for lists of annotated [lexp] (on the same clock). *) *)
    (* Lemma sem_laexps_index: *)
    (*   forall n H b ck les ess, *)
    (*     CoInd.sem_laexps H b ck les ess -> *)
    (*     (Indexed.sem_clock_instant (tr_stream b n) *)
    (*                                (Indexed.restr (tr_history H) n) ck false *)
    (*      /\ Indexed.sem_lexps_instant (tr_stream b n) *)
    (*                                  (Indexed.restr (tr_history H) n) les *)
    (*                                  (tr_streams ess n) *)
    (*      /\ tr_streams ess n = List.map (fun _ => absent) les) *)
    (*     \/ *)
    (*     (Indexed.sem_clock_instant (tr_stream b n) *)
    (*                                (Indexed.restr (tr_history H) n) ck true *)
    (*      /\ Indexed.sem_lexps_instant (tr_stream b n) *)
    (*                                  (Indexed.restr (tr_history H) n) les *)
    (*                                  (tr_streams ess n) *)
    (*      /\ Forall (fun e => e <> absent) (tr_streams ess n)). *)
    (* Proof. *)
    (*   induction n; intros ** Indexed. *)
    (*   - inversion_clear Indexed as [? ? ? ? ? ? Indexed' Hess Hck *)
    (*                                   |? ? ? ? ? ? Indexed' Hess Hck]; *)
    (*       apply (sem_clock_impl 0) in Hck; rewrite tr_stream_0 in Hck; *)
    (*         assert (Indexed.sem_lexps_instant (tr_stream b 0) *)
    (*                                           (Indexed.restr (tr_history H) 0) *)
    (*                                           les (tr_streams ess 0)) *)
    (*         by (clear Hess; induction Indexed' as [|? ? ? ? Indexed]; simpl; *)
    (*             constructor; [now apply sem_lexp_impl in Indexed *)
    (*                          | eapply IHIndexed', CoInd.sem_laexps_cons; eauto]). *)
    (*     + right. intuition; auto. *)
    (*       clear - Hess. *)
    (*       induction ess; inv Hess; constructor; auto. *)
    (*     + left. intuition; auto. *)
    (*       clear - Indexed' Hess. *)
    (*       induction Indexed'; inv Hess; simpl; auto. *)
    (*       f_equal; auto. *)
    (*   - destruct b; inversion_clear Indexed; *)
    (*       rewrite tr_stream_S, tr_history_tl, <-tr_streams_tl; auto. *)
    (* Qed. *)

    (** An inversion principle for lists of annotated [lexp]. *)
    Lemma sem_laexps_inv:
      forall H b es ess ck,
        Indexed.sem_laexps b H ck es ess ->
        Indexed.sem_lexps b H es ess
        /\ exists bs,
            Indexed.sem_clock b H ck bs
            /\ forall n,
              (exists vs,
                  ess n = List.map present vs
                  /\ bs n = true)
              \/ (ess n = List.map (fun _ => absent) es
                 /\ bs n = false).
    Proof.
      intros ** Sem; split.
      - intro n; specialize (Sem n); inv Sem; auto.
      - interp_str b H ck Sem.
        eexists; split; eauto.
        unfold interp_clock, lift.
        intro n; specialize (Sem n); inv Sem.
        + left; eexists; intuition; eauto.
          erewrite <-interp_clock_instant_sound; eauto.
        + right; intuition.
          erewrite <-interp_clock_instant_sound; eauto.
    Qed.

    Lemma build_n_n:
      forall {A} (str: nat -> Stream A) n,
        build str n n = [].
    Proof.
      unfold build; intros; now rewrite Nat.sub_diag.
    Qed.

    (** Generalization for lists of annotated [lexp] (on the same clock). *)
    Corollary sem_laexps_impl_from:
      forall n H b ck es ess,
        Indexed.sem_laexps b H ck es ess ->
        CoInd.sem_laexps (tr_history_from n H) (tr_stream_from n b) ck es
                         (tr_streams_from n ess).
    Proof.
      cofix Cofix; intros ** Sem.
      pose proof Sem as Sem'.
      apply sem_laexps_inv in Sem' as (Sem' & bs & Sem_ck & Ebs).
      assert (const_length_strs ess).
      { intro.
        apply sem_laexps_inv in Sem as (Sem & ? & ? & ?).
        specialize (Sem k); specialize (Sem' (S k)).
        apply Forall2_length in Sem; apply Forall2_length in Sem'.
        omega.
      }
      apply sem_clock_impl_from with (n:=n) in Sem_ck.
      rewrite (tr_stream_from_n bs) in Sem_ck.
      apply sem_lexps_impl_from with (n:=n) in Sem'.
      specialize (Ebs n); destruct Ebs as [(vs & Hess & Hbs)|(Hess & Hbs)];
        rewrite Hbs in Sem_ck.
      - eleft; eauto.
        + apply Forall_tr_streams_from_hd with (P:=fun x => x <> absent).
          rewrite Hess, Forall_map.
          clear; induction vs; constructor; auto.
          intro; discriminate.
        + rewrite tr_history_from_tl, tr_stream_from_tl, tr_streams_from_tl; auto.
      - eright; eauto.
        + apply Forall_tr_streams_from_hd with (P:=fun x => x = absent).
          rewrite Hess, Forall_map.
          clear; induction es; constructor; auto.
        + rewrite tr_history_from_tl, tr_stream_from_tl, tr_streams_from_tl; auto.
    Qed.

    Corollary sem_laexps_impl:
      forall H b ck es ess,
        Indexed.sem_laexps b H ck es ess ->
        CoInd.sem_laexps (tr_history H) (tr_stream b) ck es (tr_streams ess).
    Proof. apply sem_laexps_impl_from. Qed.

    (** ** cexp level synchronous operators inversion principles *)

    Lemma merge_inv:
      forall H b x t f es,
        Indexed.sem_cexp b H (Emerge x t f) es ->
        exists xs ts fs,
          Indexed.sem_var b H x xs
          /\ Indexed.sem_cexp b H t ts
          /\ Indexed.sem_cexp b H f fs
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
      intros ** Sem.
      interp_str b H x Sem.
      interp_str b H t Sem.
      interp_str b H f Sem.
      do 3 eexists; intuition; eauto.
      specialize (Sem_x n); specialize (Sem_t n); specialize (Sem_f n);
        specialize (Sem n); inv Sem.
      - left; exists c; intuition Indexed.sem_det.
      - right; left; exists c; intuition Indexed.sem_det.
      - right; right; intuition Indexed.sem_det.
    Qed.

    Lemma ite_inv:
      forall H b le t f es,
        Indexed.sem_cexp b H (Eite le t f) es ->
        exists les ts fs,
          Indexed.sem_lexp b H le les
          /\ Indexed.sem_cexp b H t ts
          /\ Indexed.sem_cexp b H f fs
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
      intros ** Sem.
      interp_str b H le Sem.
      interp_str b H t Sem.
      interp_str b H f Sem.
      do 3 eexists; intuition; eauto.
      specialize (Sem_le n); specialize (Sem_t n); specialize (Sem_f n);
        specialize (Sem n); inv Sem.
      - left; exists c, b0, ct, cf; intuition Indexed.sem_det.
      - right; intuition Indexed.sem_det.
    Qed.

    Lemma lexp_inv:
      forall H b le es,
        Indexed.sem_cexp b H (Eexp le) es ->
        Indexed.sem_lexp b H le es.
    Proof.
      intros ** Sem n.
      now specialize (Sem n); inv Sem.
    Qed.

    (** [fby] is not a predicate but a function, so we directly state the
        correspondence.  *)
    Lemma fby_from_impl:
      forall n c xs,
      tr_stream_from n (fby c xs) ≡ CoInd.fby (hold c xs n) (tr_stream_from n xs).
    Proof.
      cofix Cofix; intros.
      rewrite tr_stream_from_n; rewrite (tr_stream_from_n xs).
      unfold fby at 1.
      destruct (xs n) eqn: E.
      - constructor; simpl; auto.
        rewrite hold_abs; auto.
      - constructor; simpl; auto.
        erewrite (hold_pres c0); eauto.
    Qed.

    Corollary fby_impl:
      forall c xs,
      tr_stream (fby c xs) ≡ CoInd.fby c (tr_stream xs).
    Proof.
      now setoid_rewrite fby_from_impl.
    Qed.

    (** ** Semantics of cexps *)

    (** State the correspondence for [cexp].
        Goes by induction on the coinductive semantics of [cexp]. *)
    Lemma sem_cexp_impl_from:
      forall n H b e es,
        Indexed.sem_cexp b H e es ->
        CoInd.sem_cexp (tr_history_from n H) (tr_stream_from n b) e
                       (tr_stream_from n es).
    Proof.
      intros ** Sem.
      revert dependent H; revert b es n.
      induction e; intros ** Sem; unfold Indexed.sem_cexp, Indexed.lift in Sem.

      - apply merge_inv in Sem as (xs & ts & fs & ? & ? & ? & Spec).
        econstructor; eauto using sem_var_impl_from.
        revert dependent n; revert Spec; cofix; intros.
        rewrite tr_stream_from_n;
          rewrite (tr_stream_from_n ts);
          rewrite (tr_stream_from_n fs);
          rewrite (tr_stream_from_n es).
        destruct (Spec n) as [|[|[]]]; destruct_conjs;
          rewrite_strs; auto using CoInd.merge.

      - apply ite_inv in Sem as (bs & ts & fs & ? & ? & ? & Spec).
        econstructor; eauto using sem_lexp_impl_from.
        revert dependent n; revert Spec; cofix; intros.
        rewrite tr_stream_from_n;
          rewrite (tr_stream_from_n ts);
          rewrite (tr_stream_from_n fs);
          rewrite (tr_stream_from_n es).
        destruct (Spec n) as [|[]]; destruct_conjs;
          rewrite_strs; auto using CoInd.ite.
        destruct H4.
        + apply val_to_bool_true' in H8; subst; auto using CoInd.ite.
        + apply val_to_bool_false' in H8; subst; auto using CoInd.ite.

      - apply lexp_inv in Sem; constructor; auto using sem_lexp_impl_from.

    Qed.

    Corollary sem_cexp_impl:
      forall H b e es,
        Indexed.sem_cexp b H e es ->
        CoInd.sem_cexp (tr_history H) (tr_stream b) e (tr_stream es).
    Proof.
      intros; now apply sem_cexp_impl_from.
    Qed.

    (** An inversion principle for annotated [cexp]. *)
    Lemma sem_caexp_inv:
      forall H b e es ck,
        Indexed.sem_caexp b H ck e es ->
        Indexed.sem_cexp b H e es
        /\ exists bs,
            Indexed.sem_clock b H ck bs
            /\ (forall n, bs n = match es n with
                           | present _ => true
                           | absent => false
                           end).
    Proof.
      intros ** Sem; split.
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
        Indexed.sem_caexp b H ck e es ->
        CoInd.sem_caexp (tr_history_from n H) (tr_stream_from n b) ck e
                        (tr_stream_from n es).
    Proof.
      cofix Cofix; intros ** Sem.
      pose proof Sem as Sem';
        apply sem_caexp_inv in Sem' as (Sem' & bs & Sem_ck & Ebs);
        apply (sem_cexp_impl_from n) in Sem';
        apply sem_clock_impl_from with (n:=n) in Sem_ck.
      rewrite (tr_stream_from_n es) in *.
      rewrite (tr_stream_from_n bs), Ebs in Sem_ck.
      destruct (es n); econstructor; eauto;
        rewrite tr_stream_from_tl, tr_history_from_tl;
        apply Cofix; auto.
    Qed.

    Corollary sem_caexp_impl:
      forall H b e es ck,
        Indexed.sem_caexp b H ck e es ->
        CoInd.sem_caexp (tr_history H) (tr_stream b) ck e (tr_stream es).
    Proof. apply sem_caexp_impl_from. Qed.


    (** * RESET CORRESPONDENCE  *)

    Lemma tr_stream_reset_from:
      forall n xs,
        CoInd.reset_of (tr_stream_from n xs)
        ≡ tr_stream_from n (Indexed.reset_of xs).
    Proof.
      cofix; intros.
      rewrite tr_stream_from_n; rewrite (tr_stream_from_n (Indexed.reset_of xs)).
      unfold CoInd.reset_of, Indexed.reset_of in *.
      constructor; simpl; auto.
    Qed.

    Corollary tr_stream_reset:
      forall xs,
        CoInd.reset_of (tr_stream xs) ≡ tr_stream (Indexed.reset_of xs).
    Proof. apply tr_stream_reset_from. Qed.

   (*  (** ** Properties about [count] *) *)

   (*  (** If a reset occurs directly, the count can't be zero. *) *)
   (*  Remark count_true_not_0: *)
   (*    forall r n, *)
   (*      count (tr_stream (true ::: r)) n <> 0. *)
   (*  Proof. *)
   (*    intros; induction n; simpl. *)
   (*    - omega. *)
   (*    - rewrite tr_stream_S. *)
   (*      destruct (tr_stream r n); auto. *)
   (*  Qed. *)

   (*  (** If a reset occurs at [n], then the count at the same instant can't be *)
   (*      zero. *) *)
   (*  Remark count_true_not_0': *)
   (*    forall n r, *)
   (*      tr_stream r n = true -> *)
   (*      count (tr_stream r) n <> 0. *)
   (*  Proof. *)
   (*    induction n; simpl; intros r E; try rewrite E; auto. *)
   (*  Qed. *)

   (*  (** When a reset occurs initially, the count at [n] is the count at [n] *)
   (*      forgetting the first instant, plus one if no reset occurs at [n] when *)
   (*      shifting. *) *)
   (*  Lemma count_true_shift: *)
   (*    forall n r, *)
   (*      count (tr_stream (true ::: r)) n *)
   (*      = if tr_stream r n *)
   (*        then count (tr_stream r) n *)
   (*        else S (count (tr_stream r) n). *)
   (*  Proof. *)
   (*    induction n; simpl; intros. *)
   (*    - destruct (tr_stream r 0); auto. *)
   (*    - specialize (IHn r). *)
   (*      rewrite tr_stream_S. *)
   (*      destruct (tr_stream r n) eqn: E'; *)
   (*        destruct (tr_stream r (S n)); rewrite IHn; auto. *)
   (*  Qed. *)

   (*  (** When no reset occurs initially, the count at [n] is the count at [n] *)
   (*      forgetting the first instant, minus one if a reset occurs at [n] when *)
   (*      shifting. *) *)
   (*  Lemma count_false_shift: *)
   (*    forall n r, *)
   (*      count (tr_stream (false ::: r)) n *)
   (*      = if tr_stream r n *)
   (*        then count (tr_stream r) n - 1 *)
   (*        else count (tr_stream r) n. *)
   (*  Proof. *)
   (*    induction n; simpl; intros. *)
   (*    - destruct (tr_stream r 0); auto. *)
   (*    - specialize (IHn r). *)
   (*      rewrite tr_stream_S. *)
   (*      destruct (tr_stream r n) eqn: E'; *)
   (*        destruct (tr_stream r (S n)); rewrite IHn; try omega. *)
   (*      + apply Minus.minus_Sn_m, count_true_ge_1; auto. *)
   (*      + rewrite Minus.minus_Sn_m; try omega. *)
   (*        apply count_true_ge_1; auto. *)
   (*  Qed. *)

   (*  (** If a reset occurs at [n], then indexing the 0th mask at [n] falls *)
   (*      outside the clipping window, since the 0th mask is the clip before *)
   (*      the first reset. *) *)
   (*  Remark tr_stream_mask_true_0: *)
   (*    forall n r xs, *)
   (*    tr_stream r n = true -> *)
   (*    tr_stream (CoInd.mask_v 0 r xs) n = absent. *)
   (*  Proof. *)
   (*    induction n; intros ** E; rewrite unfold_Stream at 1; simpl; *)
   (*      unfold_Stv r; unfold_Stv xs; auto; try rewrite tr_stream_S. *)
   (*    - rewrite tr_stream_0 in E; discriminate. *)
   (*    - pose proof (tr_stream_const absent); auto. *)
   (*    - pose proof (tr_stream_const absent); auto. *)
   (*    - apply IHn. *)
   (*      rewrite tr_stream_S in E; auto. *)
   (*    - apply IHn. *)
   (*      rewrite tr_stream_S in E; auto. *)
   (*  Qed. *)

   (*  (** When a reset occurs initially and no reset occurs at [n] after shifting, *)
   (*      then indexing at [n] the [k']th mask is: *)
   (*      - indexing the source stream at [n] if [k'] is equal to the count minus *)
   (*        one *)
   (*      - absent otherwise. *) *)
   (*  Lemma tr_stream_mask_false_true: *)
   (*    forall n r xs k k', *)
   (*      tr_stream r n = false -> *)
   (*      count (tr_stream (true ::: r)) n = S k -> *)
   (*      tr_stream (CoInd.mask_v k' r xs) n *)
   (*      = if EqNat.beq_nat k k' then tr_stream xs n else absent. *)
   (*  Proof. *)
   (*    intros ** E C. *)
   (*    rewrite count_true_shift, E in C; injection C; clear C; intro C. *)
   (*    revert k' k r xs E C; induction n; simpl; intros. *)
   (*    - rewrite E in C. *)
   (*       destruct (EqNat.beq_nat k k') eqn: E'. *)
   (*      + apply EqNat.beq_nat_true in E'; subst. *)
   (*        unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1; *)
   (*          simpl; rewrite <-E'; repeat rewrite tr_stream_0; auto. *)
   (*        rewrite tr_stream_0 in E; discriminate. *)
   (*      + apply EqNat.beq_nat_false in E'. *)
   (*        unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1; *)
   (*          destruct k' as [|[]]; simpl; try (exfalso; now apply E'). *)
   (*        * pose proof (tr_stream_const absent); auto. *)
   (*        * apply tr_stream_0. *)
   (*    - destruct (EqNat.beq_nat k k') eqn: E'. *)
   (*      + apply EqNat.beq_nat_true in E'; subst. *)
   (*        unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1; *)
   (*          destruct k' as [|[]]; simpl; repeat rewrite tr_stream_S; *)
   (*            rewrite E in E'; try discriminate; rewrite tr_stream_S in E. *)
   (*        * inv E'; exfalso; eapply count_true_not_0; eauto. *)
   (*        * erewrite IHn; eauto. *)
   (*          rewrite count_true_shift, E in E'; injection E'; clear E'; intro E'. *)
   (*          rewrite E', <-plus_n_O, <-EqNat.beq_nat_refl; auto. *)
   (*        * rewrite count_true_shift, E in E'. inv E'. *)
   (*          erewrite IHn; auto. *)
   (*          rewrite <-plus_n_O, <-EqNat.beq_nat_refl; auto. *)
   (*        * rewrite count_false_shift, E in E'. *)
   (*          erewrite IHn; eauto; auto. *)
   (*        * rewrite count_false_shift, E in E'. *)
   (*          erewrite IHn; eauto; auto. *)
   (*        * rewrite count_false_shift, E in E'. *)
   (*          erewrite IHn, <-EqNat.beq_nat_refl; auto. *)
   (*      + apply EqNat.beq_nat_false in E'. *)
   (*        unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1; *)
   (*          destruct k' as [|[]]; simpl; rewrite E in C; subst; *)
   (*            repeat rewrite tr_stream_S; rewrite tr_stream_S in E; *)
   (*              try (exfalso; now apply E'). *)
   (*        * pose proof (tr_stream_const absent); auto. *)
   (*        * erewrite IHn; eauto. *)
   (*          rewrite count_true_shift, E, NPeano.Nat.succ_inj_wd_neg, *)
   (*          <-EqNat.beq_nat_false_iff in E'. *)
   (*          rewrite <-plus_n_O, E'; auto. *)
   (*        * erewrite IHn; eauto. *)
   (*          rewrite count_true_shift, E, NPeano.Nat.succ_inj_wd_neg, *)
   (*          <-EqNat.beq_nat_false_iff in E'. *)
   (*          rewrite <-plus_n_O, E'; auto. *)
   (*        * erewrite IHn; eauto. *)
   (*          rewrite count_false_shift, E, <-EqNat.beq_nat_false_iff in E'. *)
   (*          rewrite <-plus_n_O, E'; auto. *)
   (*        * erewrite IHn; eauto. *)
   (*          rewrite count_false_shift, E, <-EqNat.beq_nat_false_iff in E'. *)
   (*          rewrite <-plus_n_O, E'; auto. *)
   (*        * erewrite IHn; eauto. *)
   (*          rewrite count_false_shift, E, <-EqNat.beq_nat_false_iff in E'. *)
   (*          rewrite <-plus_n_O, E'; auto. *)
   (*  Qed. *)

   (*  (** When no reset occurs initially and a reset occurs at [n] after shifting, *)
   (*      then indexing at [n] the [(S k')]th mask is: *)
   (*      - indexing the source stream at [n] if [k'] is equal to the count *)
   (*      - absent otherwise. *) *)
   (*  Lemma tr_stream_mask_true_false: *)
   (*    forall n r xs k k', *)
   (*      tr_stream r n = true -> *)
   (*      count (tr_stream (false ::: r)) n = k -> *)
   (*      tr_stream (CoInd.mask_v (S k') r xs) n *)
   (*      = if EqNat.beq_nat k k' then tr_stream xs n else absent. *)
   (*  Proof. *)
   (*    intros ** E C. *)
   (*    rewrite count_false_shift, E in C. *)
   (*    revert k' k r xs E C; induction n; simpl; intros. *)
   (*    - rewrite E in C. *)
   (*      destruct (EqNat.beq_nat k k') eqn: E'. *)
   (*      + apply EqNat.beq_nat_true in E'; subst. *)
   (*        unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1; *)
   (*          simpl; rewrite <-E'; repeat rewrite tr_stream_0; auto. *)
   (*        rewrite tr_stream_0 in E; discriminate. *)
   (*      + apply EqNat.beq_nat_false in E'. *)
   (*        unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1; *)
   (*          destruct k' as [|[]]; simpl; try (exfalso; now apply E'). *)
   (*        * pose proof (tr_stream_const absent); auto. *)
   (*        * apply tr_stream_0. *)
   (*    - destruct (EqNat.beq_nat k k') eqn: E'. *)
   (*      + apply EqNat.beq_nat_true in E'; subst. *)
   (*        unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1; *)
   (*          destruct k' as [|[]]; simpl; repeat rewrite tr_stream_S; *)
   (*            rewrite E in E'; try discriminate; rewrite tr_stream_S in E; *)
   (*              simpl in E'; try rewrite <-Minus.minus_n_O in E'. *)
   (*        * exfalso; eapply count_true_not_0; eauto. *)
   (*        * erewrite IHn; eauto. *)
   (*          rewrite count_true_shift, E in E'. *)
   (*          rewrite E', <-plus_n_O, <-EqNat.beq_nat_refl; auto. *)
   (*        * rewrite count_true_shift, E in E'. *)
   (*          erewrite IHn; auto. *)
   (*          rewrite E'; simpl; rewrite <-plus_n_O, <-EqNat.beq_nat_refl; auto. *)
   (*        * rewrite count_false_shift, E in E'. *)
   (*          erewrite IHn; eauto; auto. *)
   (*        * rewrite count_false_shift, E in E'. *)
   (*          erewrite IHn; eauto; auto. *)
   (*        * rewrite count_false_shift, E in E'. *)
   (*          erewrite IHn, <-EqNat.beq_nat_refl; auto. *)
   (*      + apply EqNat.beq_nat_false in E'. *)
   (*        unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1; *)
   (*          destruct k' as [|[]]; simpl; rewrite E in C; subst; *)
   (*            repeat rewrite tr_stream_S; rewrite tr_stream_S in E; *)
   (*              simpl in E'; try rewrite <-Minus.minus_n_O in E'; *)
   (*              try (exfalso; now apply E'). *)
   (*        * apply tr_stream_mask_true_0; auto. *)
   (*        * erewrite IHn; eauto. *)
   (*          rewrite count_true_shift, E in E'. *)
   (*          rewrite <-plus_n_O. *)
   (*          apply count_true_not_0' in E. *)
   (*          destruct (count (tr_stream r) n) as [|[]]; *)
   (*            try (exfalso; now apply E); try (exfalso; now apply E'). *)
   (*          auto. *)
   (*        * erewrite IHn; eauto. *)
   (*          rewrite count_true_shift, E in E'. *)
   (*          apply count_true_not_0' in E. *)
   (*          destruct (count (tr_stream r) n) as [|[|]]; *)
   (*            try (exfalso; now apply E); simpl; auto. *)
   (*          rewrite 2 NPeano.Nat.succ_inj_wd_neg, <-EqNat.beq_nat_false_iff in E'. *)
   (*          rewrite <-plus_n_O, E'; auto. *)
   (*        * erewrite IHn; eauto. *)
   (*          rewrite count_false_shift, E, <-EqNat.beq_nat_false_iff in E'. *)
   (*          rewrite <-plus_n_O, E'; auto. *)
   (*        * erewrite IHn; eauto. *)
   (*          rewrite count_false_shift, E, <-EqNat.beq_nat_false_iff in E'. *)
   (*          rewrite <-plus_n_O, E'; auto. *)
   (*        * erewrite IHn; eauto. *)
   (*          rewrite count_false_shift, E, <-EqNat.beq_nat_false_iff in E'. *)
   (*          rewrite <-plus_n_O, E'; auto. *)
   (*  Qed. *)

   (* (** When the initial occurence of a reset is the same as at [n] after *)
   (*     shifting, then indexing at [n] the [k']th mask is: *)
   (*      - indexing the source stream at [n] if [k'] is equal to the count *)
   (*      - absent otherwise. *) *)
   (*  Lemma tr_stream_mask_same: *)
   (*    forall n b r xs k k', *)
   (*      tr_stream r n = b -> *)
   (*      count (tr_stream (b ::: r)) n = k -> *)
   (*      tr_stream (CoInd.mask_v k' r xs) n *)
   (*      = if EqNat.beq_nat k k' then tr_stream xs n else absent. *)
   (*  Proof. *)
   (*    intros ** E C. *)
   (*    destruct b. *)
   (*    - rewrite count_true_shift, E in C. *)
   (*      revert k' k r xs E C; induction n; simpl; intros. *)
   (*      + rewrite E in C. *)
   (*        destruct (EqNat.beq_nat k k') eqn: E'. *)
   (*        * apply EqNat.beq_nat_true in E'; subst. *)
   (*          unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1; *)
   (*            simpl; rewrite <-E'; repeat rewrite tr_stream_0; auto. *)
   (*          rewrite tr_stream_0 in E; discriminate. *)
   (*        *{ apply EqNat.beq_nat_false in E'. *)
   (*           unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1; *)
   (*             destruct k' as [|[]]; simpl; try (exfalso; now apply E'). *)
   (*           - pose proof (tr_stream_const absent); auto. *)
   (*           - apply tr_stream_0. *)
   (*         } *)
   (*      + destruct (EqNat.beq_nat k k') eqn: E'. *)
   (*        *{ apply EqNat.beq_nat_true in E'; subst. *)
   (*           unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1; *)
   (*             destruct k' as [|[]]; simpl; repeat rewrite tr_stream_S; *)
   (*               rewrite E in E'; try discriminate; rewrite tr_stream_S in E. *)
   (*           - inv E'; exfalso; eapply count_true_not_0; eauto. *)
   (*           - erewrite IHn; eauto. *)
   (*             inv E'; *)
   (*               rewrite count_true_shift, E, <-plus_n_O, *)
   (*               <-EqNat.beq_nat_refl; auto. *)
   (*           - injection E'; clear E'; intro E'. *)
   (*             rewrite count_false_shift in E'; rewrite E in E'. *)
   (*             apply NPeano.Nat.sub_0_le in E'. *)
   (*             pose proof (count_true_ge_1 _ _ E). *)
   (*             apply Le.le_antisym in E'; auto. *)
   (*             erewrite IHn; auto. *)
   (*             rewrite E', <-plus_n_O, <-EqNat.beq_nat_refl; auto. *)
   (*           - injection E'; clear E'; intro E'. *)
   (*             erewrite IHn; eauto. *)
   (*             inv E'; rewrite count_false_shift, E. *)
   (*             pose proof (count_true_ge_1 _ _ E). *)
   (*             rewrite Minus.minus_Sn_m; auto. *)
   (*             simpl; rewrite <-Minus.minus_n_O, <-plus_n_O, *)
   (*                    <-EqNat.beq_nat_refl; auto. *)
   (*         } *)
   (*        *{ apply EqNat.beq_nat_false in E'. *)
   (*           unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1; *)
   (*             destruct k' as [|[]]; simpl; rewrite E in C; subst; *)
   (*               repeat rewrite tr_stream_S; rewrite tr_stream_S in E; *)
   (*                 try (exfalso; now apply E'). *)
   (*           - pose proof (tr_stream_const absent); auto. *)
   (*           - erewrite IHn; eauto. *)
   (*             rewrite count_true_shift, E, NPeano.Nat.succ_inj_wd_neg, *)
   (*             <-EqNat.beq_nat_false_iff in E'. *)
   (*             rewrite <-plus_n_O, E'; auto. *)
   (*           - erewrite IHn; eauto. *)
   (*             rewrite count_true_shift, E, NPeano.Nat.succ_inj_wd_neg, *)
   (*             <-EqNat.beq_nat_false_iff in E'. *)
   (*             rewrite <-plus_n_O, E'; auto. *)
   (*           - erewrite IHn; eauto. *)
   (*             pose proof (count_true_ge_1 _ _ E). *)
   (*             rewrite count_false_shift, E, Minus.minus_Sn_m in E'; *)
   (*               auto; simpl in E'; *)
   (*                 rewrite <-Minus.minus_n_O, <-EqNat.beq_nat_false_iff in E'. *)
   (*             rewrite <-plus_n_O, E'; auto. *)
   (*           - erewrite IHn; eauto. *)
   (*             pose proof (count_true_ge_1 _ _ E). *)
   (*             rewrite count_false_shift, E, Minus.minus_Sn_m in E'; *)
   (*               auto; simpl in E'; *)
   (*                 rewrite <-Minus.minus_n_O, <-EqNat.beq_nat_false_iff in E'. *)
   (*             rewrite <-plus_n_O, E'; auto. *)
   (*           - erewrite IHn; eauto. *)
   (*             pose proof (count_true_ge_1 _ _ E). *)
   (*             rewrite count_false_shift, E, Minus.minus_Sn_m in E'; *)
   (*               auto; simpl in E'; *)
   (*                 rewrite <-Minus.minus_n_O, <-EqNat.beq_nat_false_iff in E'. *)
   (*             rewrite <-plus_n_O, E'; auto. *)
   (*         } *)

   (*    - rewrite count_false_shift, E in C. *)
   (*      revert k' k r xs E C; induction n; simpl; intros. *)
   (*      + rewrite E in C. *)
   (*        destruct (EqNat.beq_nat k k') eqn: E'. *)
   (*        * apply EqNat.beq_nat_true in E'; subst. *)
   (*          unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1; *)
   (*            simpl; rewrite <-E'; repeat rewrite tr_stream_0; auto. *)
   (*          rewrite tr_stream_0 in E; discriminate. *)
   (*        *{ apply EqNat.beq_nat_false in E'. *)
   (*           unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1; *)
   (*             destruct k' as [|[]]; simpl; try (exfalso; now apply E'). *)
   (*           - pose proof (tr_stream_const absent); auto. *)
   (*           - apply tr_stream_0. *)
   (*         } *)
   (*      + destruct (EqNat.beq_nat k k') eqn: E'. *)
   (*        *{ apply EqNat.beq_nat_true in E'; subst. *)
   (*           unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1; *)
   (*             destruct k' as [|[]]; simpl; repeat rewrite tr_stream_S; *)
   (*               rewrite E in E'; try discriminate; rewrite tr_stream_S in E. *)
   (*           - inv E'; exfalso; eapply count_true_not_0; eauto. *)
   (*           - erewrite tr_stream_mask_false_true; eauto; *)
   (*               rewrite <-EqNat.beq_nat_refl; auto. *)
   (*           - erewrite tr_stream_mask_false_true; eauto; *)
   (*               rewrite <-EqNat.beq_nat_refl; auto. *)
   (*           - erewrite IHn; eauto. *)
   (*             rewrite count_false_shift, E in E'. *)
   (*             rewrite <-plus_n_O, E'; auto. *)
   (*           - erewrite IHn; eauto. *)
   (*             rewrite count_false_shift, E in E'. *)
   (*             rewrite <-plus_n_O, E'; auto. *)
   (*           - erewrite IHn; eauto. *)
   (*             rewrite count_false_shift, E in E'. *)
   (*             rewrite <-plus_n_O, E', <-EqNat.beq_nat_refl; auto. *)
   (*         } *)
   (*        *{ apply EqNat.beq_nat_false in E'. *)
   (*           unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1; *)
   (*             destruct k' as [|[]]; simpl; rewrite E in C; subst; *)
   (*               repeat rewrite tr_stream_S; rewrite tr_stream_S in E; *)
   (*                 try (exfalso; now apply E'). *)
   (*           - pose proof (tr_stream_const absent); auto. *)
   (*           - erewrite IHn; eauto. *)
   (*             rewrite count_true_shift, E, NPeano.Nat.succ_inj_wd_neg, *)
   (*             <-EqNat.beq_nat_false_iff in E'. *)
   (*             rewrite <-plus_n_O, E'; auto. *)
   (*           - erewrite IHn; eauto. *)
   (*             rewrite count_true_shift, E, NPeano.Nat.succ_inj_wd_neg, *)
   (*             <-EqNat.beq_nat_false_iff in E'. *)
   (*             rewrite <-plus_n_O, E'; auto. *)
   (*           - erewrite IHn; eauto. *)
   (*             rewrite count_false_shift, E, <-EqNat.beq_nat_false_iff in E'. *)
   (*             rewrite <-plus_n_O, E'; auto. *)
   (*           - erewrite IHn; eauto. *)
   (*             rewrite count_false_shift, E, <-EqNat.beq_nat_false_iff in E'. *)
   (*             rewrite <-plus_n_O, E'; auto. *)
   (*           - erewrite IHn; eauto. *)
   (*             rewrite count_false_shift, E, <-EqNat.beq_nat_false_iff in E'. *)
   (*             rewrite <-plus_n_O, E'; auto. *)
   (*         } *)
   (*  Qed. *)

   (*  Ltac auto_f_equal H := *)
   (*    f_equal; *)
   (*    [ idtac | *)
   (*      erewrite H; eauto; unfold mask; simpl; rewrite tr_stream_S; *)
   (*      repeat match goal with *)
   (*             | H: tr_stream _ _ = _ |- _ => rewrite H *)
   (*             | H: count ?x _ = _ |- _ => rewrite H *)
   (*             | H:  EqNat.beq_nat _ _ = _ |- _ => rewrite H *)
   (*             end; auto]. *)

   (*  (** State the correspondence for [mask]. *) *)
   (*  Lemma mask_impl: *)
   (*    forall k r xss n, *)
   (*       tr_streams (List.map (CoInd.mask_v k r) xss) n *)
   (*      = mask (Indexed.all_absent xss) k (tr_stream r) (tr_streams xss) n. *)
   (*  Proof. *)
   (*    induction xss as [|xs]; *)
   (*      simpl; intros. *)
   (*    - unfold mask. *)
   (*      destruct (EqNat.beq_nat k (count (tr_stream r) n)); auto. *)
   (*    - induction n. *)
   (*      + unfold_St xs; unfold_Stv r; unfold CoInd.mask_v, mask; *)
   (*          rewrite unfold_Stream at 1; simpl; *)
   (*          destruct k as [|[]]; simpl; f_equal; *)
   (*            erewrite IHxss; eauto; unfold mask; auto. *)
   (*      + unfold_St xs; unfold_Stv r; unfold CoInd.mask_v, mask. *)
   (*        *{ rewrite unfold_Stream at 1; simpl. *)
   (*           destruct k as [|[]]; simpl. *)
   (*           - repeat rewrite tr_stream_S. *)
   (*             destruct (tr_stream r n) eqn: E. *)
   (*             + auto_f_equal IHxss. *)
   (*               pose proof (tr_stream_const absent); auto. *)
   (*             + destruct (count (tr_stream (true ::: r)) n) eqn: E'. *)
   (*               * exfalso; eapply count_true_not_0; eauto. *)
   (*               * auto_f_equal IHxss. *)
   (*                 pose proof (tr_stream_const absent); auto. *)
   (*           - repeat rewrite tr_stream_S. *)
   (*             destruct (tr_stream r n) eqn: E. *)
   (*             + destruct (count (tr_stream (true ::: r)) n) eqn: E'. *)
   (*               * exfalso; eapply count_true_not_0; eauto. *)
   (*               * auto_f_equal IHxss. *)
   (*                 apply tr_stream_mask_true_0; auto. *)
   (*             + destruct (count (tr_stream (true ::: r)) n) as [|[]] eqn: E'. *)
   (*               * exfalso; eapply count_true_not_0; eauto. *)
   (*               * auto_f_equal IHxss. *)
   (*                 erewrite tr_stream_mask_false_true; eauto; auto. *)
   (*               * auto_f_equal IHxss. *)
   (*                 erewrite tr_stream_mask_false_true; eauto; auto. *)
   (*           - repeat rewrite tr_stream_S. *)
   (*             destruct (tr_stream r n) eqn: E. *)
   (*             + destruct (count (tr_stream (true ::: r)) n) eqn: E'. *)
   (*               * exfalso; eapply count_true_not_0; eauto. *)
   (*               *{ destruct (EqNat.beq_nat n0 n1) eqn: E''; auto_f_equal IHxss. *)
   (*                  - erewrite tr_stream_mask_same; eauto. *)
   (*                    apply EqNat.beq_nat_true, eq_S, *)
   (*                    EqNat.beq_nat_true_iff in E''; *)
   (*                      rewrite NPeano.Nat.eqb_sym, E''; auto. *)
   (*                  - erewrite tr_stream_mask_same; eauto. *)
   (*                    apply EqNat.beq_nat_false, not_eq_S, *)
   (*                    EqNat.beq_nat_false_iff in E''; *)
   (*                      rewrite NPeano.Nat.eqb_sym, E''; auto. *)
   (*                } *)
   (*             + destruct (count (tr_stream (true ::: r)) n) as [|[]] eqn: E'. *)
   (*               * exfalso; eapply count_true_not_0; eauto. *)
   (*               * auto_f_equal IHxss. *)
   (*                 erewrite tr_stream_mask_false_true; eauto; auto. *)
   (*               *{ destruct (EqNat.beq_nat n0 n1) eqn: E''; auto_f_equal IHxss. *)
   (*                  - erewrite tr_stream_mask_false_true; eauto. *)
   (*                    apply EqNat.beq_nat_true, eq_S, *)
   (*                    EqNat.beq_nat_true_iff in E''; *)
   (*                      rewrite NPeano.Nat.eqb_sym, E''; auto. *)
   (*                  - erewrite tr_stream_mask_false_true; eauto. *)
   (*                    apply EqNat.beq_nat_false, not_eq_S, *)
   (*                    EqNat.beq_nat_false_iff in E''; *)
   (*                      rewrite NPeano.Nat.eqb_sym, E''; auto. *)
   (*                } *)
   (*         } *)

   (*        *{ rewrite unfold_Stream at 1; simpl. *)
   (*           destruct k as [|[]]; simpl. *)
   (*           - repeat rewrite tr_stream_S. *)
   (*             destruct (tr_stream r n) eqn: E. *)
   (*             + auto_f_equal IHxss. *)
   (*               apply tr_stream_mask_true_0; auto. *)
   (*             + destruct (count (tr_stream (false ::: r)) n) eqn: E'; *)
   (*                 auto_f_equal IHxss; erewrite tr_stream_mask_same; eauto; auto. *)
   (*           - repeat rewrite tr_stream_S. *)
   (*             destruct (tr_stream r n) eqn: E. *)
   (*             + destruct (count (tr_stream (false ::: r)) n) eqn: E'; *)
   (*                 auto_f_equal IHxss; *)
   (*                 erewrite tr_stream_mask_true_false; eauto; auto. *)
   (*             + destruct (count (tr_stream (false ::: r)) n) as [|[]] eqn: E'; *)
   (*                 auto_f_equal IHxss; erewrite tr_stream_mask_same; eauto; auto. *)
   (*           - repeat rewrite tr_stream_S. *)
   (*             destruct (tr_stream r n) eqn: E. *)
   (*             + destruct (count (tr_stream (false ::: r)) n) eqn: E'. *)
   (*               * auto_f_equal IHxss. *)
   (*                 erewrite tr_stream_mask_true_false; eauto; auto. *)
   (*               *{ destruct (EqNat.beq_nat n0 n1) eqn: E''; auto_f_equal IHxss. *)
   (*                  - erewrite tr_stream_mask_true_false; eauto. *)
   (*                    apply EqNat.beq_nat_true, eq_S, *)
   (*                    EqNat.beq_nat_true_iff in E''; *)
   (*                      rewrite NPeano.Nat.eqb_sym, E''; auto. *)
   (*                  - erewrite tr_stream_mask_true_false; eauto. *)
   (*                    apply EqNat.beq_nat_false, not_eq_S, *)
   (*                    EqNat.beq_nat_false_iff in E''; *)
   (*                      rewrite NPeano.Nat.eqb_sym, E''; auto. *)
   (*                } *)
   (*             + destruct (count (tr_stream (false ::: r)) n) as [|[]] eqn: E'. *)
   (*               * auto_f_equal IHxss. *)
   (*                 erewrite tr_stream_mask_same; eauto; auto. *)
   (*               * auto_f_equal IHxss. *)
   (*                 erewrite tr_stream_mask_same; eauto; auto. *)
   (*               *{ destruct (EqNat.beq_nat n0 n1) eqn: E''; auto_f_equal IHxss. *)
   (*                  - erewrite tr_stream_mask_same; eauto. *)
   (*                    apply EqNat.beq_nat_true, eq_S, eq_S, *)
   (*                    EqNat.beq_nat_true_iff in E''; *)
   (*                      rewrite NPeano.Nat.eqb_sym, E''; auto. *)
   (*                  - erewrite tr_stream_mask_same; eauto. *)
   (*                    apply EqNat.beq_nat_false, not_eq_S, not_eq_S, *)
   (*                    EqNat.beq_nat_false_iff in E''; *)
   (*                      rewrite NPeano.Nat.eqb_sym, E''; auto. *)
   (*                } *)
   (*         } *)
   (*  Qed. *)

    (** * FINAL LEMMAS *)


    (* Remark all_absent_tr_streams: *)
    (*   forall A n (xss: list (Stream A)), *)
    (*     Indexed.all_absent (tr_streams xss n) = Indexed.all_absent xss. *)
    (* Proof. *)
    (*   induction xss; simpl; auto; now f_equal. *)
    (* Qed. *)
    Lemma forallb_exists:
      forall A (f: A -> bool) (l: list A),
        forallb f l = false <-> (exists x : A, In x l /\ f x = false).
    Proof.
      induction l as [|a]; simpl; split; intro H; try discriminate.
      - destruct H as (? & ? & ?); contradiction.
      - apply Bool.andb_false_iff in H as [H|H].
        + exists a; intuition.
        + apply IHl in H as (x & ? & ?).
          exists x; intuition.
      - destruct H as (? & [] & ?).
        + subst; apply Bool.andb_false_intro1; auto.
        + apply Bool.andb_false_intro2, IHl.
          exists x; intuition.
    Qed.

    (** Correspondence for [clocks_of], used to give a base clock for node
        applications. *)
    Lemma tr_clocks_of_from:
      forall n xss bk,
        const_length_strs xss ->
        Indexed.clock_of xss bk ->
        CoInd.clocks_of (tr_streams_from n xss) ≡ tr_stream_from n bk.
    Proof.
      cofix Cofix; intros ** Clock.
      constructor; simpl.
      - unfold Indexed.clock_of in Clock.
        destruct (bk n) eqn: E.
        + apply forallb_forall.
          intros; eapply Forall_In_tr_streams_from_hd; eauto.
          apply Clock in E.
          clear - E.
          induction (xss n); constructor; inv E; auto.
          apply Bool.negb_true_iff; now apply not_equiv_decb_equiv.
        + apply forallb_exists.
          apply Bool.not_true_iff_false in E.
          rewrite <-Clock in E.
          unfold Indexed.present_list in E.
          apply decidable_Exists_not_Forall, Exists_exists in E.
          *{ destruct E as (x & Hin & Hx).
             apply In_ex_nth with (d:=x) in Hin as (k & Len & Nth).
             eexists.
             split.
             - unfold_tr_streams.
               apply nth_In; rewrite build_length, Nat.sub_0_r; eauto.
             - instantiate (1:=Streams.const absent).
               rewrite nth_build; auto; simpl.
               subst; apply Bool.negb_false_iff; now apply equiv_decb_equiv.
           }
          *{ intros; destruct x.
             - left; auto.
             - right; intro; discriminate.
           }
      - rewrite tr_streams_from_tl; auto.
    Qed.

    Lemma tr_clocks_of:
      forall xss bk,
        const_length_strs xss ->
        Indexed.clock_of xss bk ->
        CoInd.clocks_of (tr_streams xss) ≡ tr_stream bk.
    Proof. apply tr_clocks_of_from. Qed.

    (** The final theorem stating the correspondence for equations, nodes and
        reset applications. The conjunctive shape is mandatory to use the
        mutually recursive induction scheme [sem_equation_node_ind]. *)
    Theorem implies:
      (forall b H e,
          Indexed.sem_equation G b H e ->
          CoInd.sem_equation G (tr_history H) (tr_stream b) e)
      /\
      (forall f xss oss,
          Indexed.sem_node G f xss oss ->
          CoInd.sem_node G f (tr_streams xss) (tr_streams oss))
      /\
      (forall f r xss oss,
          Indexed.sem_reset G f r xss oss ->
          CoInd.sem_reset G f (tr_stream r) (tr_streams xss) (tr_streams oss)).
    Proof.
      apply Indexed.sem_equation_node_ind.
      - econstructor.
        + apply sem_caexp_impl; eauto.
        + eapply sem_var_impl; eauto.
      - econstructor; eauto.
        + apply sem_laexps_impl; auto.
        + apply sem_vars_impl with (b:=bk); auto.
      - econstructor; auto.
        + apply sem_laexps_impl; eauto.
        + apply sem_var_impl with (b:=bk); eauto.
        + rewrite tr_stream_reset; eauto.
        + apply sem_vars_impl with (b:=bk); eauto.
      - econstructor; auto; subst.
        + apply sem_laexp_impl; eauto.
        + rewrite <-fby_impl.
          apply sem_var_impl with (b:=bk); auto.
      - intros ** IHNode.
        constructor; intro.
        specialize (IHNode n).
        (* pose proof (mask_impl n r xss) as Hxss. *)
        (* pose proof (mask_impl n r yss) as Hyss. *)
        (* rewrite 2 all_absent_tr_streams. *)
        (* eapply Indexed.sem_node_compat; eauto. *)
        admit.
      - intros ** Hin Hout ? ? ? ? ?.
        Ltac assert_const_length xss :=
          match goal with
            H: Indexed.sem_vars _ _ _ xss |- _ =>
            let H' := fresh in
            assert (const_length_strs xss)
              by (intro k; pose proof H as H';
                  unfold Indexed.sem_vars, Indexed.lift in *;
                  specialize (H k); specialize (H' (S k));
                  apply Forall2_length in H; apply Forall2_length in H';
                  now rewrite H in H')
          end.
        assert_const_length xss; assert_const_length yss.
        econstructor; eauto.
        + apply sem_vars_impl with (b:=bk); eauto.
        + apply sem_vars_impl with (b:=bk); eauto.
        + apply same_clock_app_impl; auto.
          * unfold Indexed.sem_vars, Indexed.lift in *.
            intros k E; specialize (Hin k); apply Forall2_length in Hin.
            rewrite map_length in Hin.
            pose proof n.(n_ingt0) as Nin.
            rewrite Hin, E in Nin; contradict Nin; simpl; omega.
          * unfold Indexed.sem_vars, Indexed.lift in *.
            intros k E; specialize (Hout k); apply Forall2_length in Hout.
            rewrite map_length in Hout.
            pose proof n.(n_outgt0) as Nout.
            rewrite Hout, E in Nout; contradict Nout; simpl; omega.
        + apply Forall_impl with (P:=CoInd.sem_equation G (tr_history H)
                                                        (tr_stream bk)); auto.
          intro; rewrite tr_clocks_of; eauto.
    Qed.

    Definition equation_impl := proj1 implies.
    Definition node_impl := proj1 (proj2 implies).
    Definition reset_impl := proj2 (proj2 implies).

  End Global.

End INDEXEDTOCOIND.
