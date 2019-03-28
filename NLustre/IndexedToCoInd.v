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
Require Import Velus.CoreExpr.CESyntax.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.Ordered.
Require Import Velus.CoreExpr.Stream.
Require Import Velus.NLustre.Streams.

Require Import Velus.CoreExpr.CESemantics.
Require Import Velus.NLustre.NLSemantics.
Require Import Velus.NLustre.NLInterpretor.
Require Import Velus.NLustre.NLSemanticsCoInd.

Require Import Setoid.
Module Type INDEXEDTOCOIND
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import OpAux   : OPERATORS_AUX        Op)
       (Import Clks    : CLOCKS           Ids)
       (Import CESyn : CESYNTAX         Op)
       (Import Syn     : NLSYNTAX         Ids Op       Clks CESyn)
       (Import Str     : STREAM               Op OpAux)
       (Import Ord     : ORDERED          Ids Op       Clks CESyn Syn)
       (ExprIdx        : CESEMANTICS  Ids Op OpAux Clks CESyn     Str)
       (Indexed        : NLSEMANTICS      Ids Op OpAux Clks CESyn Syn Str Ord ExprIdx)
       (Import Interp  : NLINTERPRETOR    Ids Op OpAux Clks CESyn Str         ExprIdx)
       (CoInd          : NLSEMANTICSCOIND Ids Op OpAux Clks CESyn Syn).

  Section Global.

    Variable G : global.

    (** * BASIC CORRESPONDENCES *)

    (** ** Definitions  *)

    (** A generic function to build a coinductive Stream. *)
    CoFixpoint init_from {A} (n: nat) (f: nat -> A) : Stream A :=
      f n ::: init_from (S n) f.

    (** Translate an indexed stream into a coinductive Stream.
        The [n]th element of the result Stream is the result of the application
        of the input stream on [n]. *)
    Definition tr_stream_from {A} (n: nat) (xs: stream A) : Stream A :=
      init_from n xs.

    Definition tr_stream {A} : stream A -> Stream A := tr_stream_from 0.

    (** Build a list of indexed streams from an integer range. *)
    Definition seq_streams {A} (str_i: nat -> Stream A) (last_i first_i: nat)
      : list (Stream A) :=
      List.map str_i (seq first_i (last_i - first_i)).

    (** Build the indexed stream corresponding to the [i]th elements of
        the input stream of lists. *)
    Definition streams_nth (i: nat) (xss: stream (list value)): stream value :=
      fun n => nth i (xss n) absent.

    (** Build a coinductive Stream extracting the [i]th element of the list
        obtained at each instant [n]. *)
    Definition nth_tr_streams_from (n: nat) (xss: stream (list value)) (i: nat)
      : Stream value :=
      init_from n (streams_nth i xss).

    (** Translate an indexed stream of list into a list of coinductive Streams
        using the two previous functions. *)
    Definition tr_streams_from (n: nat) (xss: stream (list value))
      : list (Stream value) :=
      seq_streams (nth_tr_streams_from n xss) (length (xss n)) 0.

    Definition tr_streams: stream (list value) -> list (Stream value) :=
      tr_streams_from 0.

    Ltac unfold_tr_streams :=
      unfold tr_streams, tr_streams_from.

    (** Translate an history from indexed to coinductive world.
        Every element of the history is translated. *)
    Definition tr_history_from (n: nat) (H: ExprIdx.history) : CoInd.History :=
      Env.map (tr_stream_from n) H.

    Definition tr_history : ExprIdx.history -> CoInd.History :=
      tr_history_from 0.

    (** ** Properties  *)

    (** A basic definition-rewriting lemma.  *)
    Lemma init_from_n:
      forall {A} (f: nat -> A) n,
        init_from n f = f n ::: init_from (S n) f.
    Proof.
      intros; now rewrite unfold_Stream at 1.
    Qed.

    (** [init_from] is compatible wrt to extensional equality. *)
    Add Parametric Morphism A : (@init_from A)
        with signature eq ==> eq_str ==> @EqSt A
          as init_from_morph.
    Proof.
      cofix Cofix; intros ** xs xs' E.
      rewrite init_from_n; rewrite (init_from_n xs').
      constructor; simpl; auto.
    Qed.

    (** The [m]th element of the built stream, starting from [n],
        is the result of the application of [f] at [(m+n)]. *)
    Lemma init_from_nth:
      forall {A} m n (f: nat -> A),
        Str_nth m (init_from n f) = f (m + n).
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
      forall {A} k (str: nat -> Stream A) m,
        length (seq_streams str k m) = k - m.
    Proof.
      intros; unfold seq_streams.
      now rewrite map_length, seq_length.
    Qed.

    (** The [n]th element of the range-built list of Streams starting at 0 is
        the result of the function at [n]. *)
    Lemma nth_seq_streams:
      forall {A} k str n (xs_d: Stream A),
        n < k ->
        nth n (seq_streams str k 0) xs_d = str n.
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
      intros ** Len.
      apply Forall2_eq, Forall2_forall2.
      split; unfold_tr_streams; rewrite map_length.
      - now rewrite 2 seq_streams_length, Len.
      - intros ** Hlen E1 E2; rewrite <-E1, <-E2.
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
      now repeat setoid_rewrite Env.map_map.
    Qed.

    (** If at instant [n], a property is true for all elements of the list
        obtained from the indexed stream, then it is true for the [n]th element
        of the Streams in the translated list. *)
    Lemma Forall_In_tr_streams_nth:
      forall n P xss x,
        wf_streams xss ->
        Forall P (xss n) ->
        In x (tr_streams xss) ->
        P (Str_nth n x).
    Proof.
      unfold_tr_streams; intros ** Length Ps Hin.
      apply In_ex_nth with (d:=x) in Hin as (k & Len & Nth).
      rewrite seq_streams_length, Nat.sub_0_r in Len.
      assert (length (xss 0) = length (xss n)) as E
          by (clear - Length; induction n; simpl; auto; now rewrite IHn, Length).
      pose proof Len; rewrite E in Len.
      rewrite nth_seq_streams in Nth; auto.
      apply eq_EqSt in Nth.
      apply (eqst_ntheq n) in Nth.
      rewrite <-Nth; unfold nth_tr_streams_from; rewrite init_from_nth, <-plus_n_O.
      eapply nth_In in Len.
      eapply Forall_forall in Ps; eauto.
    Qed.

    (** This states the converse of the previous lemma. *)
    Lemma Forall_In_tr_streams_nth':
      forall n P xss x,
        wf_streams xss ->
        Forall (fun x => P (Str_nth n x)) (tr_streams xss) ->
        In x (xss n) ->
        P x.
    Proof.
      unfold_tr_streams; intros ** Length Ps Hin.
      assert (length (xss 0) = length (xss n)) as E
          by (clear - Length; induction n; simpl; auto; now rewrite IHn, Length).
      apply In_ex_nth with (d:=absent) in Hin as (k & Len & Nth); subst.
      pose proof Len; rewrite <-E in Len.
      change (nth k (xss n) absent) with (streams_nth k xss n).
      rewrite (plus_n_O n), <-init_from_nth.
      eapply Forall_forall in Ps; eauto.
      change (init_from 0 (streams_nth k xss)) with (nth_tr_streams_from 0 xss k).
      rewrite <-nth_tr_streams_from_nth with (xs_d:=nth_tr_streams_from 0 xss n);
        eauto.
      apply nth_In.
      now rewrite seq_streams_length, Nat.sub_0_r.
    Qed.

    Corollary Forall_tr_streams_nth:
      forall xss,
        wf_streams xss ->
        forall n P,
          (Forall P (xss n) <-> Forall (fun x => P (Str_nth n x)) (tr_streams xss)).
    Proof.
      split; intros; apply Forall_forall; intros.
      - eapply Forall_In_tr_streams_nth; eauto.
      - eapply Forall_In_tr_streams_nth'; eauto.
    Qed.

    (** A more specific version of [Forall_In_tr_streams_nth]. *)
    Lemma Forall_In_tr_streams_from_hd:
      forall n P xss x,
        Forall P (xss n) ->
        In x (tr_streams_from n xss) ->
        P (hd x).
    Proof.
      unfold_tr_streams; intros ** Ps Hin.
      apply In_ex_nth with (d:=x) in Hin as (k & Len & Nth).
      rewrite seq_streams_length, Nat.sub_0_r in Len.
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

    Lemma Forall_In_tr_streams_from_hd':
      forall n P xss x,
        Forall (fun x => P (hd x)) (tr_streams_from n xss) ->
        In x (xss n) ->
        P x.
    Proof.
      unfold_tr_streams; intros ** Ps Hin.
      apply In_ex_nth with (d:=absent) in Hin as (k & Len & Nth); subst.
      change (nth k (xss n) absent) with (streams_nth k xss n).
      rewrite (plus_n_O n), <-init_from_nth.
      eapply Forall_forall in Ps; eauto.
      rewrite init_from_nth_tl, <-plus_n_O.
      change (init_from n (streams_nth k xss)) with (nth_tr_streams_from n xss k).
      rewrite <-nth_tr_streams_from_nth with (xs_d:=nth_tr_streams_from 0 xss n);
        eauto.
      apply nth_In.
      now rewrite seq_streams_length, Nat.sub_0_r.
    Qed.

    Corollary Forall_tr_streams_from_hd:
      forall xss n P,
        Forall P (xss n) <-> Forall (fun x => P (hd x)) (tr_streams_from n xss).
    Proof.
      split; intros; apply Forall_forall; intros.
      - eapply Forall_In_tr_streams_from_hd; eauto.
      - eapply Forall_In_tr_streams_from_hd'; eauto.
    Qed.

    (** * SEMANTICS CORRESPONDENCE *)

    (** ** Variables *)

    (** An inversion principle for [sem_var]. *)
    Lemma sem_var_inv:
      forall H x xs,
      ExprIdx.sem_var H x xs ->
      exists xs',
        Env.find x H = Some xs'
        /\ xs ≈ xs'.
    Proof.
      unfold ExprIdx.sem_var, ExprIdx.lift'.
      intros ** Sem.
      destruct (Env.find x H) as [xs'|] eqn: E; simpl in *.
      - exists xs'; intuition.
        intro n; specialize (Sem n).
        unfold ExprIdx.sem_var_instant, ExprIdx.restr_hist in Sem.
        rewrite Env.Props.P.F.map_o, E in Sem.
        now inv Sem.
      - specialize (Sem 0).
        unfold ExprIdx.sem_var_instant, ExprIdx.restr_hist in Sem.
        now rewrite Env.Props.P.F.map_o, E in Sem.
    Qed.

    Lemma sem_var_impl_from:
      forall n H x xs,
      ExprIdx.sem_var H x xs ->
      CoInd.sem_var (tr_history_from n H) x (tr_stream_from n xs).
    Proof.
      intros ** Sem.
      apply sem_var_inv in Sem as (? & Find & E).
      econstructor.
      - unfold tr_history_from.
        rewrite Env.Props.P.F.map_o, Find; simpl; eauto.
      - now rewrite E.
    Qed.

    Corollary sem_var_impl:
      forall H x xs,
      ExprIdx.sem_var H x xs ->
      CoInd.sem_var (tr_history H) x (tr_stream xs).
    Proof. apply sem_var_impl_from. Qed.
    Hint Resolve sem_var_impl_from sem_var_impl.

    (** An inversion principle for [sem_vars]. *)
    Lemma sem_vars_inv_from:
      forall H xs xss,
        ExprIdx.sem_vars H xs xss ->
        forall n,
          Forall2 (fun x k => ExprIdx.sem_var H x (streams_nth k xss))
                  (drop n xs) (seq n (length xs - n)).
    Proof.
      unfold ExprIdx.sem_vars, ExprIdx.lift.
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
      forall H xs xss,
        ExprIdx.sem_vars H xs xss ->
        Forall2 (fun x k => ExprIdx.sem_var H x (streams_nth k xss))
                xs (seq 0 (length xs)).
    Proof.
      intros ** Sem; apply sem_vars_inv_from with (n:=0) in Sem.
      now rewrite Nat.sub_0_r in Sem.
    Qed.

    Corollary sem_vars_impl_from:
      forall n H xs xss,
      ExprIdx.sem_vars H xs xss ->
      Forall2 (CoInd.sem_var (tr_history_from n H)) xs (tr_streams_from n xss).
    Proof.
      intros ** Sem.
      assert (length xs = length (xss n)) as Length by
            (unfold ExprIdx.sem_vars, ExprIdx.lift in Sem; specialize (Sem n);
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
        rewrite nth_tr_streams_from_nth; auto.
        now rewrite <-Length.
    Qed.

    Corollary sem_vars_impl:
      forall H xs xss,
      ExprIdx.sem_vars H xs xss ->
      Forall2 (CoInd.sem_var (tr_history H)) xs (tr_streams xss).
    Proof. apply sem_vars_impl_from. Qed.
    Hint Resolve sem_vars_impl_from sem_vars_impl.

    (** ** Synchronization *)

    Lemma same_clock_impl:
      forall xss,
        wf_streams xss ->
        ExprIdx.same_clock xss ->
        CoInd.same_clock (tr_streams xss).
    Proof.
      unfold ExprIdx.same_clock, ExprIdx.instant_same_clock.
      intros ** Same n.
      destruct (Same n) as [E|Ne].
      - left; apply Forall_tr_streams_nth with (P:=fun x => x = absent); auto.
      - right. apply Forall_tr_streams_nth with (P:=fun x => x <> absent); auto.
    Qed.
    Hint Resolve same_clock_impl.

    Ltac contr := try match goal with
                      | H: ?x <> ?x |- _ => now contradict H
                      end.

    Lemma same_clock_app_impl:
      forall xss yss,
        (forall n, xss n <> []) ->
        (forall n, yss n <> []) ->
        wf_streams xss ->
        wf_streams yss ->
        ExprIdx.same_clock xss ->
        ExprIdx.same_clock yss ->
        (forall n, absent_list (xss n) <-> absent_list (yss n)) ->
        CoInd.same_clock (tr_streams xss ++ tr_streams yss).
   Proof.
      intros ** Nxss Nyss Cxss Cyss Hxss Hyss Same n.
      apply same_clock_impl in Hxss; apply same_clock_impl in Hyss; auto.
      unfold ExprIdx.same_clock, ExprIdx.instant_same_clock in Same;
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
   Hint Resolve same_clock_app_impl.

    (** ** lexp level synchronous operators inversion principles

        The indexed semantics is inductive only instant-speaking, therefore we
        can't use usual tactics like inversion nor induction.
        We prove some lemmas to provide inversion-like tactics on the semantics
        of lexps.
        These lemmas could be proven using the classical axiom of choice which
        gives, from an instant semantics entailment true at every instant,
        the existence of a stream verifying the general entailment.
        But we rather use the interpretor to seq_streams these witnesses, with 2
        benefits :
        1) this is a constructive way of obtaining a witness
        2) we don't rely on an axiom whose use would have to be be deeply
           justified since it would raise some logical contradictions in Coq
     *)

    (** Require Import ClassicalChoice.
        Lemma lift_choice:
          forall {A B} (sem: bool -> Indexed.R -> A -> B -> Prop) b H x,
            (forall n, exists v, sem (b n) (ExprIdx.restr_hist H n) x v) ->
            exists ys, ExprIdx.lift b sem H x ys.
        Proof.
          unfold ExprIdx.lift.
          intros ** Sem.
          apply choice in Sem; auto.
        Qed.
    *)

   (** This tactic automatically uses the interpretor to give a witness stream. *)
    Ltac interp_str b H x Sem :=
      let Sem_x := fresh "Sem_" x in
      let sol sem interp sound :=
          assert (sem b H x (interp b H x)) as Sem_x by
                (intro n; specialize (Sem n); unfold interp, lift;
                 inv Sem; erewrite <-sound; eauto)
      in
      let sol' sem interp sound :=
          assert (sem H x (interp H x)) as Sem_x by
                (intro n; specialize (Sem n); unfold interp, lift';
                 inv Sem; erewrite <-sound; eauto)
      in
      match type of x with
      | lexp => sol ExprIdx.sem_lexp interp_lexp interp_lexp_instant_sound
      | cexp => sol ExprIdx.sem_cexp interp_cexp interp_cexp_instant_sound
      | ident => sol' ExprIdx.sem_var interp_var interp_var_instant_sound
      | clock => sol ExprIdx.sem_clock interp_clock interp_clock_instant_sound
      end.

    Lemma when_inv:
      forall H b e x k es,
        ExprIdx.sem_lexp b H (Ewhen e x k) es ->
        exists ys xs,
          ExprIdx.sem_lexp b H e ys
          /\ ExprIdx.sem_var H x xs
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
      - left; exists sc, xc; intuition ExprIdx.sem_det.
      - right; left; exists sc, xc; intuition; try ExprIdx.sem_det.
        now rewrite Bool.negb_involutive.
      - right; right; intuition ExprIdx.sem_det.
    Qed.

    Lemma unop_inv:
      forall H b op e ty es,
        ExprIdx.sem_lexp b H (Eunop op e ty) es ->
        exists ys,
          ExprIdx.sem_lexp b H e ys
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
      - left; exists c, c'; intuition ExprIdx.sem_det.
      - right; intuition ExprIdx.sem_det.
    Qed.

    Lemma binop_inv:
      forall H b op e1 e2 ty es,
        ExprIdx.sem_lexp b H (Ebinop op e1 e2 ty) es ->
        exists ys zs,
          ExprIdx.sem_lexp b H e1 ys
          /\ ExprIdx.sem_lexp b H e2 zs
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
      - left; exists c1, c2, c'; intuition ExprIdx.sem_det.
      - right; intuition ExprIdx.sem_det.
    Qed.

    (** ** Semantics of clocks *)

    Ltac rewrite_strs :=
      repeat match goal with
               H: (_: stream value) (_: nat) = (_: value) |- _ => rewrite H in *
             end.

    (** An inversion principle for [sem_clock] which also uses the interpretor. *)
    Lemma sem_clock_inv:
      forall H b bs ck x k,
        ExprIdx.sem_clock b H (Con ck x k) bs ->
        exists bs' xs,
          ExprIdx.sem_clock b H ck bs'
          /\ ExprIdx.sem_var H x xs
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
      - left; exists c; intuition ExprIdx.sem_det.
      - right; left; intuition ExprIdx.sem_det.
      - right; right; exists c; intuition; try ExprIdx.sem_det.
        now rewrite Bool.negb_involutive.
    Qed.

    (** We can then deduce the correspondence lemma for [sem_clock].
        We go by induction on the clock [ck] then we use the above inversion
        lemma. *)
    Corollary sem_clock_impl_from:
      forall H b ck bs,
        ExprIdx.sem_clock b H ck bs ->
        forall n, CoInd.sem_clock (tr_history_from n H) (tr_stream_from n b) ck
                             (tr_stream_from n bs).
    Proof.
      induction ck; intros ** Sem n.
      - constructor.
        revert Sem n; cofix; intros.
        rewrite init_from_n; rewrite (init_from_n bs).
        constructor; simpl; auto.
        specialize (Sem n); now inv Sem.
      - apply sem_clock_inv in Sem as (bs' & xs & Sem_bs' & Sem_xs & Spec).
        revert Spec n; cofix; intros.
        rewrite (init_from_n bs).
        apply IHck with (n:=n) in Sem_bs';
          rewrite (init_from_n bs') in Sem_bs'.
        apply (sem_var_impl_from n) in Sem_xs;
          rewrite (init_from_n xs) in Sem_xs.
        destruct (Spec n) as [|[]]; destruct_conjs; rewrite_strs.
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

    (** ** Semantics of lexps *)

    Ltac use_spec Spec :=
      match goal with
        n: nat |- _ =>
        pose proof (Spec n);
        repeat match goal with
                 H: _ \/ _ |- _ => destruct H
               end;
        destruct_conjs; rewrite_strs; auto
      end.

    (** State the correspondence for [lexp].
        Goes by induction on [lexp] and uses the previous inversion lemmas. *)
    Hint Constructors CoInd.when CoInd.lift1 CoInd.lift2.
    Lemma sem_lexp_impl_from:
      forall n H b e es,
        ExprIdx.sem_lexp b H e es ->
        CoInd.sem_lexp (tr_history_from n H) (tr_stream_from n b) e
                       (tr_stream_from n es).
    Proof.
      intros ** Sem.
      revert dependent H; revert b es n.
      induction e; intros ** Sem; unfold ExprIdx.sem_lexp, ExprIdx.lift in Sem.

      - constructor.
        revert dependent es; revert b; revert n.
        cofix; intros.
        rewrite init_from_n; rewrite (init_from_n b).
        constructor; simpl.
        + specialize (Sem n);
            inversion_clear Sem as [? ? Hes| | | | | | | |];
            destruct (b n); auto.
        + destruct (b n); auto.

      - constructor.
        apply sem_var_impl_from.
        intros n'; specialize (Sem n').
        now inv Sem.

      - apply when_inv in Sem as (ys & xs & ? & ? & Spec).
        econstructor; eauto using sem_var_impl_from.
        revert dependent n; revert Spec; cofix; intros.
        rewrite init_from_n;
          rewrite (init_from_n xs);
          rewrite (init_from_n es).
        use_spec Spec.

      - apply unop_inv in Sem as (ys & ? & Spec).
        econstructor; eauto.
        revert dependent n; revert Spec; cofix; intros.
        rewrite init_from_n; rewrite (init_from_n es).
        use_spec Spec.

      - apply binop_inv in Sem as (ys & zs & ? & ? & Spec).
        econstructor; eauto.
        revert dependent n; revert Spec; cofix; intros.
        rewrite init_from_n;
          rewrite (init_from_n zs);
          rewrite (init_from_n es).
        use_spec Spec.
    Qed.

    Corollary sem_lexp_impl:
      forall H b e es,
        ExprIdx.sem_lexp b H e es ->
        CoInd.sem_lexp (tr_history H) (tr_stream b) e (tr_stream es).
    Proof. apply sem_lexp_impl_from. Qed.
    Hint Resolve sem_lexp_impl_from sem_lexp_impl.

    (** An inversion principle for lists of [lexp]. *)
    Lemma sem_lexps_inv:
      forall H b es ess,
        ExprIdx.sem_lexps b H es ess ->
        exists ess',
          Forall2 (ExprIdx.sem_lexp b H) es ess'
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
        ExprIdx.sem_lexps b H es ess ->
        Forall2 (CoInd.sem_lexp (tr_history_from n H) (tr_stream_from n b)) es
                (tr_streams_from n ess).
    Proof.
      intros ** Sem.
      apply sem_lexps_inv in Sem as (ess' & Sem & Eess').
      assert (length es = length (ess n)) as Length by
          (rewrite Eess', map_length; simpl; eapply Forall2_length; eauto).
      apply Forall2_forall2; split.
      - unfold_tr_streams; rewrite seq_streams_length; simpl; omega.
      - intros ** Nth; subst.
        rewrite nth_tr_streams_from_nth; try omega.
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
        ExprIdx.sem_lexps b H es ess ->
        Forall2 (CoInd.sem_lexp (tr_history H) (tr_stream b)) es (tr_streams ess).
    Proof. apply sem_lexps_impl_from. Qed.
    Hint Resolve sem_lexps_impl_from sem_lexps_impl.

    (** An inversion principle for annotated [lexp]. *)
    Lemma sem_laexp_inv:
      forall H b e es ck,
        ExprIdx.sem_laexp b H ck e es ->
        ExprIdx.sem_lexp b H e es
        /\ exists bs,
            ExprIdx.sem_clock b H ck bs
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
        ExprIdx.sem_laexp b H ck e es ->
        CoInd.sem_laexp (tr_history_from n H) (tr_stream_from n b) ck e
                        (tr_stream_from n es).
    Proof.
      cofix Cofix; intros ** Sem.
      pose proof Sem as Sem';
        apply sem_laexp_inv in Sem' as (Sem' & bs & Sem_ck & Ebs);
        apply (sem_lexp_impl_from n) in Sem';
        apply sem_clock_impl_from with (n:=n) in Sem_ck.
      rewrite (init_from_n es) in *.
      rewrite (init_from_n bs), Ebs in Sem_ck.
      destruct (es n); econstructor; eauto;
        rewrite init_from_tl, tr_history_from_tl;
        apply Cofix; auto.
    Qed.

    Corollary sem_laexp_impl:
      forall H b e es ck,
        ExprIdx.sem_laexp b H ck e es ->
        CoInd.sem_laexp (tr_history H) (tr_stream b) ck e (tr_stream es).
    Proof. apply sem_laexp_impl_from. Qed.
    Hint Resolve sem_laexp_impl_from sem_laexp_impl.

    (** An inversion principle for lists of annotated [lexp]. *)
    Lemma sem_laexps_inv:
      forall H b es ess ck,
        ExprIdx.sem_laexps b H ck es ess ->
        ExprIdx.sem_lexps b H es ess
        /\ exists bs,
            ExprIdx.sem_clock b H ck bs
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

    (** Generalization for lists of annotated [lexp]. *)
    Corollary sem_laexps_impl_from:
      forall n H b ck es ess,
        ExprIdx.sem_laexps b H ck es ess ->
        CoInd.sem_laexps (tr_history_from n H) (tr_stream_from n b) ck es
                         (tr_streams_from n ess).
    Proof.
      cofix Cofix; intros ** Sem.
      pose proof Sem as Sem'.
      apply sem_laexps_inv in Sem' as (Sem' & bs & Sem_ck & Ebs).
      assert (wf_streams ess).
      { intros k k'.
        apply sem_laexps_inv in Sem as (Sem & ? & ? & ?).
        specialize (Sem k); specialize (Sem' k').
        apply Forall2_length in Sem; apply Forall2_length in Sem'.
        omega.
      }
      apply sem_clock_impl_from with (n:=n) in Sem_ck.
      rewrite (init_from_n bs) in Sem_ck.
      apply sem_lexps_impl_from with (n:=n) in Sem'.
      specialize (Ebs n); destruct Ebs as [(vs & Hess & Hbs)|(Hess & Hbs)];
        rewrite Hbs in Sem_ck.
      - eleft; eauto.
        + apply Forall_tr_streams_from_hd with (P:=fun x => x <> absent).
          rewrite Hess, Forall_map.
          clear; induction vs; constructor; auto.
          intro; discriminate.
        + rewrite tr_history_from_tl, init_from_tl, tr_streams_from_tl; auto.
      - eright; eauto.
        + apply Forall_tr_streams_from_hd with (P:=fun x => x = absent).
          rewrite Hess, Forall_map.
          clear; induction es; constructor; auto.
        + rewrite tr_history_from_tl, init_from_tl, tr_streams_from_tl; auto.
    Qed.

    Corollary sem_laexps_impl:
      forall H b ck es ess,
        ExprIdx.sem_laexps b H ck es ess ->
        CoInd.sem_laexps (tr_history H) (tr_stream b) ck es (tr_streams ess).
    Proof. apply sem_laexps_impl_from. Qed.
    Hint Resolve sem_laexps_impl_from sem_laexps_impl.

    (** ** cexp level synchronous operators inversion principles *)

    Lemma merge_inv:
      forall H b x t f es,
        ExprIdx.sem_cexp b H (Emerge x t f) es ->
        exists xs ts fs,
          ExprIdx.sem_var H x xs
          /\ ExprIdx.sem_cexp b H t ts
          /\ ExprIdx.sem_cexp b H f fs
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
      - left; exists c; intuition ExprIdx.sem_det.
      - right; left; exists c; intuition ExprIdx.sem_det.
      - right; right; intuition ExprIdx.sem_det.
    Qed.

    Lemma ite_inv:
      forall H b le t f es,
        ExprIdx.sem_cexp b H (Eite le t f) es ->
        exists les ts fs,
          ExprIdx.sem_lexp b H le les
          /\ ExprIdx.sem_cexp b H t ts
          /\ ExprIdx.sem_cexp b H f fs
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
      - left; exists c, b0, ct, cf; intuition ExprIdx.sem_det.
      - right; intuition ExprIdx.sem_det.
    Qed.

    Lemma lexp_inv:
      forall H b le es,
        ExprIdx.sem_cexp b H (Eexp le) es ->
        ExprIdx.sem_lexp b H le es.
    Proof.
      intros ** Sem n.
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
        erewrite (Indexed.hold_pres c0); eauto.
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
    Hint Constructors CoInd.merge CoInd.ite.
    Lemma sem_cexp_impl_from:
      forall n H b e es,
        ExprIdx.sem_cexp b H e es ->
        CoInd.sem_cexp (tr_history_from n H) (tr_stream_from n b) e
                       (tr_stream_from n es).
    Proof.
      intros ** Sem.
      revert dependent H; revert b es n.
      induction e; intros ** Sem; unfold ExprIdx.sem_cexp, ExprIdx.lift in Sem.

      - apply merge_inv in Sem as (xs & ts & fs & ? & ? & ? & Spec).
        econstructor; eauto.
        revert dependent n; revert Spec; cofix; intros.
        rewrite init_from_n;
          rewrite (init_from_n ts);
          rewrite (init_from_n fs);
          rewrite (init_from_n es).
        use_spec Spec.

      - apply ite_inv in Sem as (bs & ts & fs & ? & ? & ? & Spec).
        econstructor; eauto.
        revert dependent n; revert Spec; cofix; intros.
        rewrite init_from_n;
          rewrite (init_from_n ts);
          rewrite (init_from_n fs);
          rewrite (init_from_n es).
        use_spec Spec.
        destruct H4.
        + apply val_to_bool_true' in H8; subst; auto.
        + apply val_to_bool_false' in H8; subst; auto.

      - apply lexp_inv in Sem; constructor; auto.
    Qed.

    Corollary sem_cexp_impl:
      forall H b e es,
        ExprIdx.sem_cexp b H e es ->
        CoInd.sem_cexp (tr_history H) (tr_stream b) e (tr_stream es).
    Proof. apply sem_cexp_impl_from. Qed.
    Hint Resolve sem_cexp_impl_from sem_cexp_impl.

    (** An inversion principle for annotated [cexp]. *)
    Lemma sem_caexp_inv:
      forall H b e es ck,
        ExprIdx.sem_caexp b H ck e es ->
        ExprIdx.sem_cexp b H e es
        /\ exists bs,
            ExprIdx.sem_clock b H ck bs
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
        ExprIdx.sem_caexp b H ck e es ->
        CoInd.sem_caexp (tr_history_from n H) (tr_stream_from n b) ck e
                        (tr_stream_from n es).
    Proof.
      cofix Cofix; intros ** Sem.
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
        ExprIdx.sem_caexp b H ck e es ->
        CoInd.sem_caexp (tr_history H) (tr_stream b) ck e (tr_stream es).
    Proof. apply sem_caexp_impl_from. Qed.
    Hint Resolve sem_caexp_impl_from sem_caexp_impl.

    (** * RESET CORRESPONDENCE  *)

    (** We state the correspondence for [reset_of]. *)
    Lemma reset_of_impl_from:
      forall n xs rs,
        ExprIdx.reset_of xs rs ->
        CoInd.reset_of (tr_stream_from n xs) (tr_stream_from n rs).
    Proof.
      cofix Cofix; intros ** Rst.
      pose proof Rst.
      specialize (Rst n).
      rewrite (init_from_n xs), (init_from_n rs).
      destruct (xs n); constructor; auto.
    Qed.

    Corollary reset_of_impl:
      forall xs rs,
        ExprIdx.reset_of xs rs ->
        CoInd.reset_of (tr_stream xs) (tr_stream rs).
    Proof. apply reset_of_impl_from. Qed.

    (** ** Properties about [count] and [mask] *)

    (** State the correspondance for [count].  *)
    Lemma count_impl_from:
      forall n (r: stream bool),
        CoInd.count_acc (if r n then count r n - 1 else count r n)
                        (tr_stream_from n r)
        ≡ tr_stream_from n (count r).
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
      forall k k' (r: stream bool) xss,
        wf_streams xss ->
        EqSts value
              (tr_streams (mask (all_absent (xss k')) k r xss))
              (List.map (CoInd.mask_v k (tr_stream r)) (tr_streams xss)).
    Proof.
      intros ** Const; unfold tr_streams, tr_stream.
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
        unfold CoInd.mask_v, mask.
        apply ntheq_eqst; intro m.
        unfold nth_tr_streams_from.
        rewrite init_from_nth, CoInd.mask_nth, init_from_nth.
        unfold CoInd.count, streams_nth.
        pose proof (count_impl_from 0 r) as Count.
        assert ((if r 0 then count r 0 - 1 else count r 0) = 0) as E
            by (simpl; destruct (r 0); auto).
        rewrite E in Count; rewrite Count, init_from_nth, Nat.eqb_sym.
        destruct (EqNat.beq_nat (count r (m + 0)) k); auto.
        apply nth_all_absent.
    Qed.

    (** * FINAL LEMMAS *)

    (** Correspondence for [clocks_of], used to give a base clock for node
        applications. *)
    Lemma tr_clocks_of_from:
      forall n xss bk,
        wf_streams xss ->
        ExprIdx.clock_of xss bk ->
        CoInd.clocks_of (tr_streams_from n xss) ≡ tr_stream_from n bk.
    Proof.
      cofix Cofix; intros ** Clock.
      constructor; simpl.
      - unfold ExprIdx.clock_of in Clock.
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
          unfold present_list in E.
          apply decidable_Exists_not_Forall, Exists_exists in E.
          *{ destruct E as (x & Hin & Hx).
             apply In_ex_nth with (d:=x) in Hin as (k & Len & Nth).
             eexists.
             split.
             - unfold_tr_streams.
               apply nth_In; rewrite seq_streams_length, Nat.sub_0_r; eauto.
             - instantiate (1:=Streams.const absent).
               rewrite nth_seq_streams; auto; simpl.
               subst; apply Bool.negb_false_iff; now apply equiv_decb_equiv.
           }
          *{ intros; destruct x.
             - left; auto.
             - right; intro; discriminate.
           }
      - rewrite tr_streams_from_tl; auto.
    Qed.

    Lemma sem_clocked_vars_impl:
      forall H b xs,
        ExprIdx.sem_clocked_vars b H xs ->
        CoInd.sem_clocked_vars (tr_history H) (tr_stream b) xs.
    Proof.
    Admitted.
    Hint Resolve sem_clocked_vars_impl.

    Lemma tr_clocks_of:
      forall xss bk,
        wf_streams xss ->
        ExprIdx.clock_of xss bk ->
        CoInd.clocks_of (tr_streams xss) ≡ tr_stream bk.
    Proof. apply tr_clocks_of_from. Qed.

    (** The final theorem stating the correspondence for nodes applications.
        We have to use a custom mutually recursive induction scheme [sem_node_mult]. *)
    Hint Constructors CoInd.sem_equation.
    Theorem implies:
      forall f xss oss,
        Indexed.sem_node G f xss oss ->
        CoInd.sem_node G f (tr_streams xss) (tr_streams oss).
    Proof.
      induction 1 as [| | | |???? IHNode|] using Indexed.sem_node_mult with
          (P_equation := fun b H e =>
                           Indexed.sem_equation G b H e ->
                           CoInd.sem_equation G (tr_history H) (tr_stream b) e)
          (P_reset := fun f r xss oss =>
                        Indexed.sem_reset G f r xss oss ->
                        CoInd.sem_reset G f (tr_stream r) (tr_streams xss) (tr_streams oss));
        eauto.
      - econstructor; eauto.
        apply reset_of_impl; auto.

      - econstructor; eauto; subst.
        rewrite <-fby_impl; eauto.
        apply sem_var_impl; congruence.

      - constructor; intro k; specialize (IHNode k); destruct IHNode.
        inversion_clear H as [???? HNode].
        rewrite <- 2 mask_impl; eauto;
          eapply wf_streams_mask; intro n'; specialize (HNode n');
            apply Indexed.sem_node_wf in HNode as (? & ?); eauto.

      - pose proof n.(n_ingt0); pose proof n.(n_outgt0).
        Ltac assert_not_nil xss :=
          match goal with
            H: ExprIdx.sem_vars _ _ xss |- _ =>
            let k := fresh in
            let E := fresh in
            assert (forall k, xss k <> []) by
                (intro k; unfold ExprIdx.sem_vars, ExprIdx.lift in H;
                 specialize (H k); intro E; rewrite E in H;
                 apply Forall2_length in H; rewrite map_length in H;
                 simpl in H; omega)
          end.
        assert_not_nil xss; assert_not_nil yss.
        ExprIdx.assert_const_length xss; ExprIdx.assert_const_length yss.
        econstructor; eauto.
        + rewrite tr_clocks_of; eauto.
        + apply Forall_impl_In with (P:=Indexed.sem_equation G bk H); auto.
          intros e ?.
          rewrite tr_clocks_of; eauto.
          pattern e; eapply Forall_forall; eauto.
    Qed.

  End Global.

End INDEXEDTOCOIND.
