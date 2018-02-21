Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Coq.Sorting.Permutation.
Require Import Morphisms.
Require Import Coq.Program.Tactics.

Require Import Coq.FSets.FMapPositive.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.Ordered.
Require Import Velus.NLustre.Stream.
Require Import Velus.NLustre.Streams.

Require Import Velus.NLustre.NLSemantics.
Require Import Velus.NLustre.NLSemanticsCoInd.

Require Import Setoid.
Module Type INDEXEDTOCOIND
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX        Op)
       (Import Clks  : CLOCKS           Ids)
       (Import Syn   : NLSYNTAX         Ids Op Clks)
       (Import Str   : STREAM               Op OpAux)
       (Import Ord   : ORDERED          Ids Op       Clks Syn)
       (Indexed      : NLSEMANTICS      Ids Op OpAux Clks Syn Str Ord)
       (CoInd        : NLSEMANTICSCOIND Ids Op OpAux Clks Syn Ord).

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

    (** Translate a stream of list into a list of Streams.
        We build the resulting list index by index.
     *)
    CoFixpoint tr_streams_at_from {A} (n: nat) (d: A) (xss: stream (list A)) (k: nat)
      : Stream A :=
      nth k (xss n) d ::: tr_streams_at_from (n + 1) d xss k.
    Definition tr_streams {A} (xss: stream (list A)) (d: A) : list (Stream A) :=
      let str := tr_streams_at_from 0 d xss in
      let fix build acc k :=
          match k with
          | 0 => acc
          | S k => build (str k :: acc) k
          end
      in
      build [] (length (xss 0)).

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

    (** Indexing a translated Stream at [0] is taking the head of the source
        Stream. *)
    Corollary tr_stream_0:
      forall {A} (xs: stream A),
        tr_stream xs = xs 0 ::: tr_stream_from 1 xs.
    Proof.
      intros.
      unfold tr_stream; apply tr_stream_from_n.
    Qed.

    Lemma tr_stream_EqSt_from:
      forall {A} n (xs xs': stream A),
      (forall n : nat, xs n = xs' n) ->
      tr_stream_from n xs ≡ tr_stream_from n xs'.
    Proof.
      cofix Cofix; intros ** E.
      (* Why the f**k can't we use directly `rewrite unfold_Stream` ? *)
      destruct (tr_stream_from n xs) eqn: Exs;
        destruct (tr_stream_from n xs') eqn: Exs'.
      rewrite unfold_Stream in Exs at 1;
        rewrite unfold_Stream in Exs' at 1; simpl in *.
      inv Exs; inv Exs'.
      constructor; simpl; auto.
    Qed.

    Lemma tr_stream_EqSt:
      forall {A} (xs xs': stream A),
      (forall n : nat, xs n = xs' n) ->
      tr_stream xs ≡ tr_stream xs'.
    Proof.
      intros; now apply tr_stream_EqSt_from.
    Qed.

    (* (** Indexing a translated Stream at [S n] is indexing the tail of the source *)
    (*     Stream at [n]. *) *)
    (* Lemma tr_stream_S: *)
    (*   forall {A} (xs: Stream A) x n, *)
    (*     tr_stream (x ::: xs) (S n) = tr_stream xs n. *)
    (* Proof. reflexivity. Qed. *)

    (** Another version of the previous lemma.  *)
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

    (* (** The counterpart of [tr_stream_tl] for lists of Streams. *) *)
    (* Lemma tr_streams_tl: *)
    (*   forall xss n, *)
    (*     tr_streams (List.map (tl (A:=value)) xss) n = tr_streams xss (S n). *)
    (* Proof. *)
    (*   intros; induction xss; simpl; auto. *)
    (*   f_equal; auto. *)
    (* Qed. *)

    (** The counterpart of [tr_stream_tl] for histories. *)
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
        /\ forall n, xs n = xs' n.
    Proof.
      unfold Indexed.sem_var, Indexed.lift.
      intros ** Sem.
      destruct (PM.find x H) as [xs'|] eqn: E; simpl in *.
      - exists xs'; intuition.
        specialize (Sem n).
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
      apply sem_var_inv in Sem; destruct_conjs.
      econstructor.
      - apply PM.find_2.
        unfold tr_history_from, PM.map.
        rewrite PM.gmapi.
        now erewrite PM.find_1; eauto.
      - now apply tr_stream_EqSt_from.
    Qed.

    Corollary sem_var_impl:
      forall H b x xs,
      Indexed.sem_var b H x xs ->
      CoInd.sem_var (tr_history H) x (tr_stream xs).
    Proof.
      intros; eapply sem_var_impl_from; eauto.
    Qed.

    (* Lemma sem_vars_exists: *)
    (*   forall H b xs xss, *)
    (*   Indexed.sem_vars b H xs xss -> *)
    (*   exists xss', *)
    (*     (forall n, Forall2 (fun x xs' => PM.find x (Indexed.restr H n) = Some xs') xs (xss' n)) *)
    (*     /\ forall n, Forall2 eq (xss n) (xss' n). *)
    (* Proof. *)
    (*   unfold Indexed.sem_vars, Indexed.lift. *)
    (*   intros ** Sem. *)
    (*   edestruct Sem. unfold Indexed.sem_vars in Sem.  Sem.  *)
    (*   destruct (PM.find x H) as [v|] eqn: E; simpl in *. *)
    (*   - exists v; intuition. *)
    (*     specialize (Sem n). *)
    (*     inversion_clear Sem as [Find]. *)
    (*     unfold Indexed.restr, PM.map in Find. *)
    (*     rewrite PM.gmapi, E in Find. *)
    (*     now inv Find. *)
    (*   - specialize (Sem 0). *)
    (*     inversion_clear Sem as [Find]. *)
    (*     unfold Indexed.restr, PM.map in Find. *)
    (*     now rewrite PM.gmapi, E in Find. *)
    (* Qed. *)

    Corollary sem_vars_impl:
      forall H b xs xss,
      Indexed.sem_vars b H xs xss ->
      Forall2 (CoInd.sem_var (tr_history H)) xs (tr_streams xss absent).
    Proof.
      unfold Indexed.sem_vars, Indexed.lift; intros ** Sem.
      induction xs.
      - specialize (Sem 0).
        inversion Sem as [E' E|].
        unfold tr_streams.
        rewrite <-E; simpl; auto.
      - Admitted.

    (* (** ** Synchronization *) *)

    (* Lemma same_clock_impl: *)
    (*   forall xss, *)
    (*     CoInd.same_clock xss -> *)
    (*     Indexed.same_clock (tr_streams xss). *)
    (* Proof. *)
    (*   unfold Indexed.same_clock, Indexed.instant_same_clock. *)
    (*   intros. *)
    (*   destruct (H n) as [E|Ne]. *)
    (*   - left; induction xss; simpl; constructor; inv E; auto. *)
    (*     apply IHxss; auto. *)
    (*     eapply CoInd.same_clock_cons; eauto. *)
    (*   - right; induction xss; simpl; constructor; inv Ne; auto. *)
    (*     apply IHxss; eauto using CoInd.same_clock_cons. *)
    (* Qed. *)

    (* Lemma same_clock_app_impl: *)
    (*   forall xss yss, *)
    (*     xss <> [] -> *)
    (*     yss <> [] -> *)
    (*     CoInd.same_clock (xss ++ yss) -> *)
    (*     forall n, Indexed.absent_list (tr_streams xss n) *)
    (*          <-> Indexed.absent_list (tr_streams yss n). *)
    (* Proof. *)
    (*   intros ** Hxss Hyss Same n. *)
    (*   apply same_clock_impl in Same. *)
    (*   unfold Indexed.same_clock, Indexed.instant_same_clock in Same; *)
    (*     specialize (Same n). *)
    (*   split; intros Indexed. *)
    (*   - destruct Same as [E|Ne]. *)
    (*     + rewrite tr_streams_app in E; apply Forall_app in E; tauto. *)
    (*     + rewrite tr_streams_app in Ne; apply Forall_app in Ne as [NIndexed]. *)
    (*       induction xss; simpl in *; inv NIndexed; try now inv Indexed. *)
    (*       now contradict Hxss. *)
    (*   - destruct Same as [E|Ne]. *)
    (*     + rewrite tr_streams_app in E; apply Forall_app in E; tauto. *)
    (*     + rewrite tr_streams_app in Ne; apply Forall_app in Ne as [? NIndexed]. *)
    (*       induction yss; simpl in *; inv NIndexed; try now inv Indexed. *)
    (*       now contradict Hyss. *)
    (* Qed. *)

    (** ** lexp level synchronous operators specifications

        The indexed semantics is inductive only instant-speaking, therefore we
        can't use usual tactics like inversion nor induction.
        We prove some lemmas to provide inversion-like tactics on the semantics
        of lexps.
        These lemmas are proven using the classical axiom of choice which gives,
        from an instant semantics entailment true at every instant, the existence
        of a stream verifying the general entailment.
     *)

    (* Lemma const_index: *)
    (*   forall n xs c b, *)
    (*     xs ≡ CoInd.const c b -> *)
    (*     tr_stream xs n = if tr_stream b n then present (sem_const c) else absent. *)
    (* Proof. *)
    (*   induction n; intros ** E; *)
    (*     unfold_Stv b; unfold_Stv xs; inv E; simpl in *; try discriminate; *)
    (*       repeat rewrite tr_stream_0; repeat rewrite tr_stream_S; auto. *)
    (* Qed. *)

    (* Fixpoint when_xs (es: stream value) (k: bool) (n: nat) := *)
    (*   match es n with *)
    (*   | present sc => *)
    (*     match when_ys es k n with *)
    (*     | present y => *)
    (*       if sc ==b y then *)
    (*         present (if k then true_val else false_val) *)
    (*       else absent *)
    (*     | absent => absent *)
    (*     end *)
    (*   | absent => *)
    (*     match when_ys es k n with *)
    (*     | present y => *)
    (*       present (if k then false_val else true_val) *)
    (*     | absent => absent *)
    (*     end *)
    (*   end *)

    (* with *)
    (* when_ys es k n := *)
    (*   match es n with *)
    (*   | present sc => *)
    (*     match when_xs es k n with *)
    (*     | present xc => *)
    (*       match val_to_bool xc with *)
    (*       | Some k' => *)
    (*         if k ==b k' then *)
    (*           present sc *)
    (*         else absent *)
    (*       | None => absent *)
    (*       end *)
    (*     | absent => absent *)
    (*     end *)
    (*   | absent => *)
    (*     match when_xs es k n with *)
    (*     | present xc => *)
    (*       match val_to_bool xc with *)
    (*       | Some k' => *)
    (*         if k ==b k' then *)
    (*           present true_val *)
    (*         else absent *)
    (*       | None => absent *)
    (*       end *)
    (*     | absent => absent *)
    (*     end *)
    (*   end. *)

    (* Fixpoint when_xs (es: stream value) (k: bool) (n: nat) := *)
    (*   match es n with *)
    (*   | present sc => *)
    (*     present (if k then true_val else false_val) *)
    (*   | absent => *)
    (*     match when_ys es k n with *)
    (*     | present y => *)
    (*       present (if k then false_val else true_val) *)
    (*     | absent => absent *)
    (*     end *)
    (*   end *)

    (* with *)
    (* when_ys es k n := *)
    (*   match es n with *)
    (*   | present sc => *)
    (*     match when_xs es k n with *)
    (*     | present xc => *)
    (*       match val_to_bool xc with *)
    (*       | Some k' => *)
    (*         if k ==b k' then *)
    (*           present sc *)
    (*         else absent *)
    (*       | None => absent *)
    (*       end *)
    (*     | absent => absent *)
    (*     end *)
    (*   | absent => *)
    (*     match when_xs es k n with *)
    (*     | present xc => *)
    (*       match val_to_bool xc with *)
    (*       | Some k' => *)
    (*         if k ==b k' then *)
    (*           present true_val *)
    (*         else absent *)
    (*       | None => absent *)
    (*       end *)
    (*     | absent => absent *)
    (*     end *)
    (*   end. *)

    Require Import ClassicalChoice.
    Lemma lift_choice:
      forall {A B} (sem: bool -> Indexed.R -> A -> B -> Prop) b H x,
        (forall n, exists v, sem (b n) (Indexed.restr H n) x v) ->
        exists ys, Indexed.lift b sem H x ys.
    Proof.
      unfold Indexed.lift.
      intros ** Sem.
      apply choice in Sem; auto.
    Qed.

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
      assert (exists ys, Indexed.sem_lexp b H e ys) as (ys & Sem_e) by
            (apply lift_choice; intro; specialize (Sem n); inv Sem;
             eexists; eauto).
      assert (exists xs, Indexed.sem_var b H x xs) as (xs & Sem_x) by
             (apply lift_choice; intro; specialize (Sem n); inv Sem;
             eexists; eauto).
      exists ys, xs; intuition.
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
      assert (exists ys, Indexed.sem_lexp b H e ys) as (ys & Sem_e) by
            (apply lift_choice; intro; specialize (Sem n); inv Sem;
             eexists; eauto).
      exists ys; intuition.
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
      assert (exists ys, Indexed.sem_lexp b H e1 ys) as (ys & Sem_e1) by
            (apply lift_choice; intro; specialize (Sem n); inv Sem;
             eexists; eauto).
      assert (exists zs, Indexed.sem_lexp b H e2 zs) as (zs & Sem_e2) by
             (apply lift_choice; intro; specialize (Sem n); inv Sem;
             eexists; eauto).
      exists ys, zs; intuition.
      specialize (Sem_e1 n); specialize (Sem_e2 n); specialize (Sem n); inv Sem.
      - left; exists c1, c2, c'; intuition Indexed.sem_det.
      - right; intuition Indexed.sem_det.
    Qed.

    (** ** Semantics of clocks *)

    Ltac rewrite_strs :=
      repeat match goal with
               H: (_: stream value) (_: nat) = (_: value) |- _ => rewrite H in *
             end.

    (* (** Give an indexed specification for [sem_clock] in the previous style, *)
    (*     with added complexity as [sem_clock] depends on [H] and [b]. *)
    (*     We go by induction on the clock [ck] then by induction on [n] and *)
    (*     inversion of the coinductive hypothesis as before. *) *)
    (* Lemma sem_clock_index: *)
    (*   forall n H b ck bs, *)
    (*     CoInd.sem_clock H b ck bs -> *)
    (*     (ck = Cbase *)
    (*      /\ tr_stream b n = tr_stream bs n) *)
    (*     \/ *)
    (*     (exists ck' x k c, *)
    (*         ck = Con ck' x k *)
    (*         /\ Indexed.sem_clock_instant *)
    (*             (tr_stream b n) (Indexed.restr (tr_history H) n) ck' true *)
    (*         /\ Indexed.sem_var_instant (Indexed.restr (tr_history H) n) x *)
    (*                                   (present c) *)
    (*         /\ val_to_bool c = Some k *)
    (*         /\ tr_stream bs n = true) *)
    (*     \/ *)
    (*     (exists ck' x k, *)
    (*         ck = Con ck' x k *)
    (*         /\ Indexed.sem_clock_instant *)
    (*             (tr_stream b n) (Indexed.restr (tr_history H) n) ck' false *)
    (*         /\ Indexed.sem_var_instant (Indexed.restr (tr_history H) n) x absent *)
    (*         /\ tr_stream bs n = false) *)
    (*     \/ *)
    (*     (exists ck' x k c, *)
    (*         ck = Con ck' x (negb k) *)
    (*         /\ Indexed.sem_clock_instant *)
    (*             (tr_stream b n) (Indexed.restr (tr_history H) n) ck' true *)
    (*         /\ Indexed.sem_var_instant (Indexed.restr (tr_history H) n) x *)
    (*                                   (present c) *)
    (*         /\ val_to_bool c = Some k *)
    (*         /\ tr_stream bs n = false). *)
    (* Proof. *)
    (*   Hint Constructors Indexed.sem_clock_instant. *)
    (*   Local Ltac rew_0 := *)
    (*     try match goal with *)
    (*           H: tr_stream _ _ = _ |- _ => now rewrite tr_stream_0 in H *)
    (*         end. *)
    (*   intros n H b ck; revert n H b; induction ck as [|ck ? x k]. *)
    (*   - inversion_clear 1 as [? ? ? Eb| | |]. *)
    (*     left; intuition. *)
    (*     now rewrite Eb. *)
    (*   - intro n; revert x k; induction n; intros x k H bk bk' Indexed. *)
    (*     + inversion_clear Indexed as [|? ? ? ? ? ? ? ? ? IndexedCk Hvar *)
    (*                                  |? ? ? ? ? ? ? ? IndexedCk Hvar *)
    (*                                  |? ? ? ? ? ? ? ? ? IndexedCk Hvar]. *)
    (*       * right; left. *)
    (*         apply sem_var_impl with (b:=tr_stream bk) in Hvar; *)
    (*           unfold Indexed.sem_var, Indexed.lift in Hvar ; specialize (Hvar 0); *)
    (*             rewrite tr_stream_0 in Hvar. *)
    (*         do 4 eexists; intuition; eauto. *)
    (*         apply (IHck 0) in IndexedCk as [(? & E)|[|[]]]; destruct_conjs; *)
    (*           subst; eauto; rew_0. *)
    (*         rewrite E, tr_stream_0; constructor. *)
    (*       * right; right; left. *)
    (*         apply sem_var_impl with (b:=tr_stream bk) in Hvar; *)
    (*           unfold Indexed.sem_var, Indexed.lift in Hvar ; specialize (Hvar 0); *)
    (*             rewrite tr_stream_0 in Hvar. *)
    (*         do 3 eexists; intuition. *)
    (*         apply (IHck 0) in IndexedCk as [(? & E)|[|[]]]; destruct_conjs; *)
    (*           subst; eauto; rew_0. *)
    (*         rewrite E, tr_stream_0; constructor. *)
    (*       * right; right; right. *)
    (*         apply sem_var_impl with (b:=tr_stream bk) in Hvar; *)
    (*           unfold Indexed.sem_var, Indexed.lift in Hvar; specialize (Hvar 0); *)
    (*             rewrite tr_stream_0 in Hvar. *)
    (*         do 4 eexists; intuition; eauto. *)
    (*         apply (IHck 0) in IndexedCk as [(? & E)|[|[]]]; destruct_conjs; *)
    (*           subst; eauto; rew_0. *)
    (*         rewrite E, tr_stream_0; constructor. *)
    (*     + inversion_clear Indexed; rewrite <-tr_stream_tl, tr_history_tl; eauto. *)
    (* Qed. *)

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
      assert (exists bs', Indexed.sem_clock b H ck bs') as (bs' & Sem_ck) by
            (apply lift_choice; intro; specialize (Sem n); inv Sem;
             eexists; eauto).
      assert (exists xs, Indexed.sem_var b H x xs) as (xs & Sem_x) by
            (apply lift_choice; intro; specialize (Sem n); inv Sem;
             eexists; eauto).
      exists bs', xs; intuition.
      specialize (Sem_ck n); specialize (Sem_x n); specialize (Sem n); inv Sem.
      - left; exists c; intuition Indexed.sem_det.
      - right; left; intuition Indexed.sem_det.
      - right; right; exists c; intuition; try Indexed.sem_det.
        now rewrite Bool.negb_involutive.
    Qed.

    (** We can then deduce the correspondence lemma for [sem_clock]. *)
    Corollary sem_clock_impl_from:
      forall H b ck bs,
        Indexed.sem_clock b H ck bs ->
        forall n, CoInd.sem_clock (tr_history_from n H) (tr_stream_from n b) ck (tr_stream_from n bs).
    Proof.
      induction ck; intros ** Sem n.
      - constructor.
        revert Sem n; cofix; intros.
        rewrite tr_stream_from_n; rewrite (tr_stream_from_n bs).
        constructor; simpl; auto.
        specialize (Sem n); now inv Sem.
      - apply sem_clock_inv in Sem as (bs' & xs & Sem_bs' & Sem_xs & Spec).
        revert Spec n; cofix Cofix; intros.
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
        CoInd.sem_lexp (tr_history_from n H) (tr_stream_from n b) e (tr_stream_from n es).
    Proof.
      (* Won't work cause [n] is fixed and therefore coinductive subproofs
         are undoable *)
      (* unfold tr_history, tr_stream; generalize 0. *)
      (* intros ** Sem. *)
      (* specialize (Sem n). *)
      (* induction e. *)

      (* - constructor. *)
      (*   revert dependent es; revert b. *)
      (*   cofix Cofix; intros. *)
      (*   rewrite tr_stream_from_n; rewrite (tr_stream_from_n b). *)
      (*   constructor; simpl. *)
      (*   + inversion_clear Sem as [? ? Hes| | | | | | | |]; *)
      (*       destruct (b n); auto. *)
      (*   + destruct (b n); auto. *)
      (* remember (es n). *)
      (* (* set (v := es n) in Sem. *) *)
      (* induction Sem as [? ? E| | | | | | | |]; subst. *)

      (* - constructor. *)
      (*   revert dependent es; revert b; revert n. *)
      (*   cofix Cofix; intros. *)
      (*   rewrite tr_stream_from_n; rewrite (tr_stream_from_n b). *)
      (*   constructor; simpl. *)
      (*   + now destruct (b n). *)
      (*   + destruct (b n); auto. *)
      (*     * apply Cofix. *)

      (* unfold tr_history, tr_stream; generalize 0; intros ** Sem; revert n es Sem. *)

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

    (** State the correspondence for [lexp].
        Goes by induction on [lexp]. *)
    Lemma sem_lexp_impl:
      forall H b e es,
        Indexed.sem_lexp b H e es ->
        CoInd.sem_lexp (tr_history H) (tr_stream b) e (tr_stream es).
    Proof.
      intros; now apply sem_lexp_impl_from.
    Qed.

    (* Lemma tl_const: *)
    (*   forall c b bs, *)
    (*     tl (CoInd.const c (b ::: bs)) = CoInd.const c bs. *)
    (* Proof. *)
    (*   intros. *)
    (*   destruct b; auto. *)
    (* Qed. *)

    (* (** Give an indexed specification for annotated [lexp], using the previous *)
    (*     lemma. *) *)
    (* Lemma sem_laexp_index: *)
    (*   forall n H b ck le es, *)
    (*     CoInd.sem_laexp H b ck le es -> *)
    (*     (Indexed.sem_clock_instant (tr_stream b n) *)
    (*                                (Indexed.restr (tr_history H) n) ck false *)
    (*      /\ Indexed.sem_lexp_instant *)
    (*          (tr_stream b n) (Indexed.restr (tr_history H) n) le absent *)
    (*      /\ tr_stream es n = absent) *)
    (*     \/ *)
    (*     (exists e, *)
    (*         Indexed.sem_clock_instant (tr_stream b n) *)
    (*                                   (Indexed.restr (tr_history H) n) ck true *)
    (*         /\ Indexed.sem_lexp_instant *)
    (*             (tr_stream b n) (Indexed.restr (tr_history H) n) le (present e) *)
    (*         /\ tr_stream es n = present e). *)
    (* Proof. *)
    (*   induction n; intros ** Indexed. *)
    (*   - inversion_clear Indexed as [? ? ? ? ? ? ? Indexed' Hck *)
    (*                                   |? ? ? ? ? ? Indexed' Hck]; *)
    (*       apply sem_lexp_impl in Indexed'; specialize (Indexed' 0); *)
    (*         repeat rewrite tr_stream_0; repeat rewrite tr_stream_0 in Indexed'; *)
    (*           apply (sem_clock_impl 0) in Hck; rewrite tr_stream_0 in Hck. *)
    (*     + right. eexists; intuition; auto. *)
    (*     + left; intuition. *)
    (*   - inversion_clear Indexed as [? ? ? ? ? ? ? Indexed'|? ? ? ? ? ? Indexed']; *)
    (*       apply sem_lexp_impl in Indexed'; *)
    (*       rewrite tr_stream_S, tr_history_tl; eauto. *)
    (* Qed. *)

    Lemma sem_laexp_inv:
      forall H b e es ck,
        Indexed.sem_laexp b H ck e es ->
        Indexed.sem_lexp b H e es
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

    (** We deduce from the previous lemma the correspondence for annotated
        [lexp]. *)
    Corollary sem_laexp_impl:
      forall n H b e es ck,
        Indexed.sem_laexp b H ck e es ->
        CoInd.sem_laexp (tr_history_from n H) (tr_stream_from n b) ck e (tr_stream_from n es).
    Proof.
      (* unfold Indexed.sem_laexp, Indexed.lift. *)
      cofix Cofix; intros ** Sem.
      (* cofix_str; intros ** Sem. *)
      pose proof Sem as Sem';
        apply sem_laexp_inv in Sem' as (Sem' & bs & Sem_ck & Ebs);
        apply (sem_lexp_impl_from n) in Sem'.
      rewrite (tr_stream_from_n es) in *.
      specialize (Sem n); inv Sem; rewrite <-H0 in *.
      + econstructor; auto.
        pose proof (sem_clock_impl_from H b b ck).
          rewrite (tr_stream_from_n es) in Impl.
        *{ specialize (Sem n); inv Sem.
           - rewrite E in *; discriminate.
           - contradiction.
          subst. contradict E.
          contradiction.
          intuition.

      induction Sem.
      apply (sem_laexp_index n) in Indexed as [(? & ? & Hes)|(? & ? & ? & Hes)];
        rewrite Hes; auto using Indexed.sem_laexp_instant.
    Qed.

    (** Specification for lists of annotated [lexp] (on the same clock). *)
    Lemma sem_laexps_index:
      forall n H b ck les ess,
        CoInd.sem_laexps H b ck les ess ->
        (Indexed.sem_clock_instant (tr_stream b n)
                                   (Indexed.restr (tr_history H) n) ck false
         /\ Indexed.sem_lexps_instant (tr_stream b n)
                                     (Indexed.restr (tr_history H) n) les
                                     (tr_streams ess n)
         /\ tr_streams ess n = List.map (fun _ => absent) les)
        \/
        (Indexed.sem_clock_instant (tr_stream b n)
                                   (Indexed.restr (tr_history H) n) ck true
         /\ Indexed.sem_lexps_instant (tr_stream b n)
                                     (Indexed.restr (tr_history H) n) les
                                     (tr_streams ess n)
         /\ Forall (fun e => e <> absent) (tr_streams ess n)).
    Proof.
      induction n; intros ** Indexed.
      - inversion_clear Indexed as [? ? ? ? ? ? Indexed' Hess Hck
                                      |? ? ? ? ? ? Indexed' Hess Hck];
          apply (sem_clock_impl 0) in Hck; rewrite tr_stream_0 in Hck;
            assert (Indexed.sem_lexps_instant (tr_stream b 0)
                                              (Indexed.restr (tr_history H) 0)
                                              les (tr_streams ess 0))
            by (clear Hess; induction Indexed' as [|? ? ? ? Indexed]; simpl;
                constructor; [now apply sem_lexp_impl in Indexed
                             | eapply IHIndexed', CoInd.sem_laexps_cons; eauto]).
        + right. intuition; auto.
          clear - Hess.
          induction ess; inv Hess; constructor; auto.
        + left. intuition; auto.
          clear - Indexed' Hess.
          induction Indexed'; inv Hess; simpl; auto.
          f_equal; auto.
      - destruct b; inversion_clear Indexed;
          rewrite tr_stream_S, tr_history_tl, <-tr_streams_tl; auto.
    Qed.

    (** Generalization for lists of annotated [lexp] (on the same clock). *)
    Corollary sem_laexps_impl:
      forall H b ck es ess,
        CoInd.sem_laexps H b ck es ess ->
        Indexed.sem_laexps (tr_stream b) (tr_history H) ck es (tr_streams ess).
    Proof.
      intros ** Indexed n.
      apply (sem_laexps_index n) in Indexed as [(? & ? & Hes)|(? & ? & Hes)].
      - eright; eauto.
      - assert (exists vs, tr_streams ess n = List.map present vs) as (vs & ?).
        { clear - Hes.
          induction ess as [|es].
          - exists nil; auto.
          - simpl in *; inversion_clear Hes as [|? ? E].
            destruct (tr_stream es n) as [|v]; try now contradict E.
            apply IHess in H as (vs & ?).
            exists (v :: vs); simpl.
            f_equal; auto.
        }
        left with (cs := vs); eauto.
    Qed.

    (** ** cexp level synchronous operators specifications *)

    Lemma merge_index:
      forall n xs ts fs rs,
        CoInd.merge xs ts fs rs ->
        (tr_stream xs n = absent
         /\ tr_stream ts n = absent
         /\ tr_stream fs n = absent
         /\ tr_stream rs n = absent)
        \/
        (exists t,
            tr_stream xs n = present true_val
            /\ tr_stream ts n = present t
            /\ tr_stream fs n = absent
            /\ tr_stream rs n = present t)
        \/
        (exists f,
            tr_stream xs n = present false_val
            /\ tr_stream ts n = absent
            /\ tr_stream fs n = present f
            /\ tr_stream rs n = present f).
    Proof.
      induction n; intros ** Merge.
      - inv Merge; repeat rewrite tr_stream_0; intuition.
        + right; left. eexists; intuition.
        + right; right. eexists; intuition.
      - inv Merge; repeat rewrite tr_stream_S; auto.
    Qed.

    Lemma ite_index:
      forall n xs ts fs rs,
        CoInd.ite xs ts fs rs ->
        (tr_stream xs n = absent
         /\ tr_stream ts n = absent
         /\ tr_stream fs n = absent
         /\ tr_stream rs n = absent)
        \/
        (exists t f,
            tr_stream xs n = present true_val
            /\ tr_stream ts n = present t
            /\ tr_stream fs n = present f
            /\ tr_stream rs n = present t)
        \/
        (exists t f,
            tr_stream xs n = present false_val
            /\ tr_stream ts n = present t
            /\ tr_stream fs n = present f
            /\ tr_stream rs n = present f).
    Proof.
      induction n; intros ** Ite.
      - inv Ite; repeat rewrite tr_stream_0; intuition.
        + right; left. do 2 eexists; now intuition.
        + right; right. do 2 eexists; now intuition.
      - inv Ite; repeat rewrite tr_stream_S; auto.
    Qed.

    (** [fby] is not a predicate but a function, so we directly state the
        correspondence.  *)
    Lemma fby_impl:
      forall n c xs,
      tr_stream (CoInd.fby c xs) n = fby c (tr_stream xs) n.
    Proof.
      induction n; intros.
      - unfold_Stv xs; rewrite unfold_Stream at 1;
          unfold fby; simpl; now rewrite tr_stream_0.
      - unfold_Stv xs; rewrite unfold_Stream at 1;
          unfold fby; simpl; repeat rewrite tr_stream_S;
            rewrite IHn; unfold fby;
              destruct (tr_stream xs n); auto; f_equal;
                clear IHn; induction n; simpl; auto;
                  rewrite tr_stream_S; destruct (tr_stream xs n); auto.
    Qed.

    (** ** Semantics of cexps *)

    (** State the correspondence for [cexp].
        Goes by induction on the coinductive semantics of [cexp]. *)
    Lemma sem_cexp_impl:
      forall H b e es,
        CoInd.sem_cexp H b e es ->
        Indexed.sem_cexp (tr_stream b) (tr_history H) e (tr_stream es).
    Proof.
      induction 1 as [? ? ? ? ? ? ? ? ? Hvar Ht ? ? ? Hmerge
                    |? ? ? ? ? ? ? ? ? He Ht ? ? ? Hite
                    |? ? ? ? He]; intro n.
      - specialize (IHsem_cexp1 n).
        specialize (IHsem_cexp2 n).
        apply sem_var_impl with (b := tr_stream b) in Hvar; eauto.
        unfold Indexed.sem_var, Indexed.lift in Hvar.
        specialize (Hvar n).
        rename H0_ into Hf.
        apply (merge_index n) in Hmerge
          as [(Hxs & Hts & Hfs & Hos)
             |[(? & Hxs & Hts & Hfs & Hos)
              |(? & Hxs & Hts & Hfs & Hos)]];
          rewrite Hos; rewrite Hts in IHsem_cexp1; rewrite Hfs in IHsem_cexp2;
            rewrite Hxs in Hvar; try (now constructor; auto).
        apply Indexed.Smerge_false; auto.

      - specialize (IHsem_cexp1 n).
        specialize (IHsem_cexp2 n).
        eapply sem_lexp_impl in He.
        specialize (He n).
        apply (ite_index n) in Hite
          as [(Hes & Hts & Hfs & Hos)
             |[(ct & cf & Hes & Hts & Hfs & Hos)
              |(ct & cf & Hes & Hts & Hfs & Hos)]];
          rewrite Hos; rewrite Hts in IHsem_cexp1; rewrite Hfs in IHsem_cexp2;
            rewrite Hes in He.
        + constructor; auto.
        + change (present ct) with (if true then present ct else present cf).
          econstructor; eauto.
          apply val_to_bool_true.
        + change (present cf) with (if false then present ct else present cf).
          econstructor; eauto.
          apply val_to_bool_false.

      - apply sem_lexp_impl in He.
        specialize (He n).
        constructor; auto.
    Qed.

    (** Give an indexed specification for annotated [cexp], using the previous
        lemma.  *)
    Lemma sem_caexp_index:
      forall n H b ck le es,
        CoInd.sem_caexp H b ck le es ->
        (Indexed.sem_clock_instant (tr_stream b n)
                                   (Indexed.restr (tr_history H) n) ck false
         /\ Indexed.sem_cexp_instant
             (tr_stream b n) (Indexed.restr (tr_history H) n) le absent
         /\ tr_stream es n = absent)
        \/
        (exists e,
            Indexed.sem_clock_instant (tr_stream b n)
                                      (Indexed.restr (tr_history H) n) ck true
            /\ Indexed.sem_cexp_instant
                (tr_stream b n) (Indexed.restr (tr_history H) n) le (present e)
            /\ tr_stream es n = present e).
    Proof.
      induction n; intros ** Indexed.
      - inversion_clear Indexed as [? ? ? ? ? ? ? Indexed' Hck
                                      |? ? ? ? ? ? Indexed' Hck];
          apply sem_cexp_impl in Indexed'; specialize (Indexed' 0);
            repeat rewrite tr_stream_0; repeat rewrite tr_stream_0 in Indexed';
              apply (sem_clock_impl 0) in Hck; rewrite tr_stream_0 in Hck.
        + right. eexists; intuition; auto.
        + left; intuition.
      - inversion_clear Indexed as [? ? ? ? ? ? ? Indexed'|? ? ? ? ? ? Indexed'];
          apply sem_cexp_impl in Indexed';
          repeat rewrite tr_stream_S; rewrite tr_history_tl; eauto.
    Qed.

    (** We deduce from the previous lemma the correspondence for annotated
        [cexp]. *)
    Corollary sem_caexp_impl:
      forall H b e es ck,
        CoInd.sem_caexp H b ck e es ->
        Indexed.sem_caexp (tr_stream b) (tr_history H) ck e (tr_stream es).
    Proof.
      intros ** Indexed n.
      apply (sem_caexp_index n) in Indexed as [(? & ? & Hes)|(? & ? & ? & Hes)];
        rewrite Hes; now constructor.
    Qed.

    Lemma tr_stream_reset:
      forall n xs,
        tr_stream (CoInd.reset_of xs) n = Indexed.reset_of (tr_stream xs) n.
    Proof.
      induction n; intros.
      - unfold_Stv xs; unfold Indexed.reset_of;
          rewrite unfold_Stream at 1; simpl; rewrite tr_stream_0; auto.
      - unfold_Stv xs; unfold Indexed.reset_of;
          rewrite unfold_Stream at 1; simpl; auto;
            eapply IHn.
    Qed.

    (** * RESET CORRESPONDENCE  *)

    (** ** Properties about [count] *)

    (** If a reset occurs directly, the count can't be zero. *)
    Remark count_true_not_0:
      forall r n,
        count (tr_stream (true ::: r)) n <> 0.
    Proof.
      intros; induction n; simpl.
      - omega.
      - rewrite tr_stream_S.
        destruct (tr_stream r n); auto.
    Qed.

    (** If a reset occurs at [n], then the count at the same instant can't be
        zero. *)
    Remark count_true_not_0':
      forall n r,
        tr_stream r n = true ->
        count (tr_stream r) n <> 0.
    Proof.
      induction n; simpl; intros r E; try rewrite E; auto.
    Qed.

    (** When a reset occurs initially, the count at [n] is the count at [n]
        forgetting the first instant, plus one if no reset occurs at [n] when
        shifting. *)
    Lemma count_true_shift:
      forall n r,
        count (tr_stream (true ::: r)) n
        = if tr_stream r n
          then count (tr_stream r) n
          else S (count (tr_stream r) n).
    Proof.
      induction n; simpl; intros.
      - destruct (tr_stream r 0); auto.
      - specialize (IHn r).
        rewrite tr_stream_S.
        destruct (tr_stream r n) eqn: E';
          destruct (tr_stream r (S n)); rewrite IHn; auto.
    Qed.

    (** When no reset occurs initially, the count at [n] is the count at [n]
        forgetting the first instant, minus one if a reset occurs at [n] when
        shifting. *)
    Lemma count_false_shift:
      forall n r,
        count (tr_stream (false ::: r)) n
        = if tr_stream r n
          then count (tr_stream r) n - 1
          else count (tr_stream r) n.
    Proof.
      induction n; simpl; intros.
      - destruct (tr_stream r 0); auto.
      - specialize (IHn r).
        rewrite tr_stream_S.
        destruct (tr_stream r n) eqn: E';
          destruct (tr_stream r (S n)); rewrite IHn; try omega.
        + apply Minus.minus_Sn_m, count_true_ge_1; auto.
        + rewrite Minus.minus_Sn_m; try omega.
          apply count_true_ge_1; auto.
    Qed.

    (** If a reset occurs at [n], then indexing the 0th mask at [n] falls
        outside the clipping window, since the 0th mask is the clip before
        the first reset. *)
    Remark tr_stream_mask_true_0:
      forall n r xs,
      tr_stream r n = true ->
      tr_stream (CoInd.mask_v 0 r xs) n = absent.
    Proof.
      induction n; intros ** E; rewrite unfold_Stream at 1; simpl;
        unfold_Stv r; unfold_Stv xs; auto; try rewrite tr_stream_S.
      - rewrite tr_stream_0 in E; discriminate.
      - pose proof (tr_stream_const absent); auto.
      - pose proof (tr_stream_const absent); auto.
      - apply IHn.
        rewrite tr_stream_S in E; auto.
      - apply IHn.
        rewrite tr_stream_S in E; auto.
    Qed.

    (** When a reset occurs initially and no reset occurs at [n] after shifting,
        then indexing at [n] the [k']th mask is:
        - indexing the source stream at [n] if [k'] is equal to the count minus
          one
        - absent otherwise. *)
    Lemma tr_stream_mask_false_true:
      forall n r xs k k',
        tr_stream r n = false ->
        count (tr_stream (true ::: r)) n = S k ->
        tr_stream (CoInd.mask_v k' r xs) n
        = if EqNat.beq_nat k k' then tr_stream xs n else absent.
    Proof.
      intros ** E C.
      rewrite count_true_shift, E in C; injection C; clear C; intro C.
      revert k' k r xs E C; induction n; simpl; intros.
      - rewrite E in C.
         destruct (EqNat.beq_nat k k') eqn: E'.
        + apply EqNat.beq_nat_true in E'; subst.
          unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
            simpl; rewrite <-E'; repeat rewrite tr_stream_0; auto.
          rewrite tr_stream_0 in E; discriminate.
        + apply EqNat.beq_nat_false in E'.
          unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
            destruct k' as [|[]]; simpl; try (exfalso; now apply E').
          * pose proof (tr_stream_const absent); auto.
          * apply tr_stream_0.
      - destruct (EqNat.beq_nat k k') eqn: E'.
        + apply EqNat.beq_nat_true in E'; subst.
          unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
            destruct k' as [|[]]; simpl; repeat rewrite tr_stream_S;
              rewrite E in E'; try discriminate; rewrite tr_stream_S in E.
          * inv E'; exfalso; eapply count_true_not_0; eauto.
          * erewrite IHn; eauto.
            rewrite count_true_shift, E in E'; injection E'; clear E'; intro E'.
            rewrite E', <-plus_n_O, <-EqNat.beq_nat_refl; auto.
          * rewrite count_true_shift, E in E'. inv E'.
            erewrite IHn; auto.
            rewrite <-plus_n_O, <-EqNat.beq_nat_refl; auto.
          * rewrite count_false_shift, E in E'.
            erewrite IHn; eauto; auto.
          * rewrite count_false_shift, E in E'.
            erewrite IHn; eauto; auto.
          * rewrite count_false_shift, E in E'.
            erewrite IHn, <-EqNat.beq_nat_refl; auto.
        + apply EqNat.beq_nat_false in E'.
          unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
            destruct k' as [|[]]; simpl; rewrite E in C; subst;
              repeat rewrite tr_stream_S; rewrite tr_stream_S in E;
                try (exfalso; now apply E').
          * pose proof (tr_stream_const absent); auto.
          * erewrite IHn; eauto.
            rewrite count_true_shift, E, NPeano.Nat.succ_inj_wd_neg,
            <-EqNat.beq_nat_false_iff in E'.
            rewrite <-plus_n_O, E'; auto.
          * erewrite IHn; eauto.
            rewrite count_true_shift, E, NPeano.Nat.succ_inj_wd_neg,
            <-EqNat.beq_nat_false_iff in E'.
            rewrite <-plus_n_O, E'; auto.
          * erewrite IHn; eauto.
            rewrite count_false_shift, E, <-EqNat.beq_nat_false_iff in E'.
            rewrite <-plus_n_O, E'; auto.
          * erewrite IHn; eauto.
            rewrite count_false_shift, E, <-EqNat.beq_nat_false_iff in E'.
            rewrite <-plus_n_O, E'; auto.
          * erewrite IHn; eauto.
            rewrite count_false_shift, E, <-EqNat.beq_nat_false_iff in E'.
            rewrite <-plus_n_O, E'; auto.
    Qed.

    (** When no reset occurs initially and a reset occurs at [n] after shifting,
        then indexing at [n] the [(S k')]th mask is:
        - indexing the source stream at [n] if [k'] is equal to the count
        - absent otherwise. *)
    Lemma tr_stream_mask_true_false:
      forall n r xs k k',
        tr_stream r n = true ->
        count (tr_stream (false ::: r)) n = k ->
        tr_stream (CoInd.mask_v (S k') r xs) n
        = if EqNat.beq_nat k k' then tr_stream xs n else absent.
    Proof.
      intros ** E C.
      rewrite count_false_shift, E in C.
      revert k' k r xs E C; induction n; simpl; intros.
      - rewrite E in C.
        destruct (EqNat.beq_nat k k') eqn: E'.
        + apply EqNat.beq_nat_true in E'; subst.
          unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
            simpl; rewrite <-E'; repeat rewrite tr_stream_0; auto.
          rewrite tr_stream_0 in E; discriminate.
        + apply EqNat.beq_nat_false in E'.
          unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
            destruct k' as [|[]]; simpl; try (exfalso; now apply E').
          * pose proof (tr_stream_const absent); auto.
          * apply tr_stream_0.
      - destruct (EqNat.beq_nat k k') eqn: E'.
        + apply EqNat.beq_nat_true in E'; subst.
          unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
            destruct k' as [|[]]; simpl; repeat rewrite tr_stream_S;
              rewrite E in E'; try discriminate; rewrite tr_stream_S in E;
                simpl in E'; try rewrite <-Minus.minus_n_O in E'.
          * exfalso; eapply count_true_not_0; eauto.
          * erewrite IHn; eauto.
            rewrite count_true_shift, E in E'.
            rewrite E', <-plus_n_O, <-EqNat.beq_nat_refl; auto.
          * rewrite count_true_shift, E in E'.
            erewrite IHn; auto.
            rewrite E'; simpl; rewrite <-plus_n_O, <-EqNat.beq_nat_refl; auto.
          * rewrite count_false_shift, E in E'.
            erewrite IHn; eauto; auto.
          * rewrite count_false_shift, E in E'.
            erewrite IHn; eauto; auto.
          * rewrite count_false_shift, E in E'.
            erewrite IHn, <-EqNat.beq_nat_refl; auto.
        + apply EqNat.beq_nat_false in E'.
          unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
            destruct k' as [|[]]; simpl; rewrite E in C; subst;
              repeat rewrite tr_stream_S; rewrite tr_stream_S in E;
                simpl in E'; try rewrite <-Minus.minus_n_O in E';
                try (exfalso; now apply E').
          * apply tr_stream_mask_true_0; auto.
          * erewrite IHn; eauto.
            rewrite count_true_shift, E in E'.
            rewrite <-plus_n_O.
            apply count_true_not_0' in E.
            destruct (count (tr_stream r) n) as [|[]];
              try (exfalso; now apply E); try (exfalso; now apply E').
            auto.
          * erewrite IHn; eauto.
            rewrite count_true_shift, E in E'.
            apply count_true_not_0' in E.
            destruct (count (tr_stream r) n) as [|[|]];
              try (exfalso; now apply E); simpl; auto.
            rewrite 2 NPeano.Nat.succ_inj_wd_neg, <-EqNat.beq_nat_false_iff in E'.
            rewrite <-plus_n_O, E'; auto.
          * erewrite IHn; eauto.
            rewrite count_false_shift, E, <-EqNat.beq_nat_false_iff in E'.
            rewrite <-plus_n_O, E'; auto.
          * erewrite IHn; eauto.
            rewrite count_false_shift, E, <-EqNat.beq_nat_false_iff in E'.
            rewrite <-plus_n_O, E'; auto.
          * erewrite IHn; eauto.
            rewrite count_false_shift, E, <-EqNat.beq_nat_false_iff in E'.
            rewrite <-plus_n_O, E'; auto.
    Qed.

   (** When the initial occurence of a reset is the same as at [n] after
       shifting, then indexing at [n] the [k']th mask is:
        - indexing the source stream at [n] if [k'] is equal to the count
        - absent otherwise. *)
    Lemma tr_stream_mask_same:
      forall n b r xs k k',
        tr_stream r n = b ->
        count (tr_stream (b ::: r)) n = k ->
        tr_stream (CoInd.mask_v k' r xs) n
        = if EqNat.beq_nat k k' then tr_stream xs n else absent.
    Proof.
      intros ** E C.
      destruct b.
      - rewrite count_true_shift, E in C.
        revert k' k r xs E C; induction n; simpl; intros.
        + rewrite E in C.
          destruct (EqNat.beq_nat k k') eqn: E'.
          * apply EqNat.beq_nat_true in E'; subst.
            unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
              simpl; rewrite <-E'; repeat rewrite tr_stream_0; auto.
            rewrite tr_stream_0 in E; discriminate.
          *{ apply EqNat.beq_nat_false in E'.
             unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
               destruct k' as [|[]]; simpl; try (exfalso; now apply E').
             - pose proof (tr_stream_const absent); auto.
             - apply tr_stream_0.
           }
        + destruct (EqNat.beq_nat k k') eqn: E'.
          *{ apply EqNat.beq_nat_true in E'; subst.
             unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
               destruct k' as [|[]]; simpl; repeat rewrite tr_stream_S;
                 rewrite E in E'; try discriminate; rewrite tr_stream_S in E.
             - inv E'; exfalso; eapply count_true_not_0; eauto.
             - erewrite IHn; eauto.
               inv E';
                 rewrite count_true_shift, E, <-plus_n_O,
                 <-EqNat.beq_nat_refl; auto.
             - injection E'; clear E'; intro E'.
               rewrite count_false_shift in E'; rewrite E in E'.
               apply NPeano.Nat.sub_0_le in E'.
               pose proof (count_true_ge_1 _ _ E).
               apply Le.le_antisym in E'; auto.
               erewrite IHn; auto.
               rewrite E', <-plus_n_O, <-EqNat.beq_nat_refl; auto.
             - injection E'; clear E'; intro E'.
               erewrite IHn; eauto.
               inv E'; rewrite count_false_shift, E.
               pose proof (count_true_ge_1 _ _ E).
               rewrite Minus.minus_Sn_m; auto.
               simpl; rewrite <-Minus.minus_n_O, <-plus_n_O,
                      <-EqNat.beq_nat_refl; auto.
           }
          *{ apply EqNat.beq_nat_false in E'.
             unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
               destruct k' as [|[]]; simpl; rewrite E in C; subst;
                 repeat rewrite tr_stream_S; rewrite tr_stream_S in E;
                   try (exfalso; now apply E').
             - pose proof (tr_stream_const absent); auto.
             - erewrite IHn; eauto.
               rewrite count_true_shift, E, NPeano.Nat.succ_inj_wd_neg,
               <-EqNat.beq_nat_false_iff in E'.
               rewrite <-plus_n_O, E'; auto.
             - erewrite IHn; eauto.
               rewrite count_true_shift, E, NPeano.Nat.succ_inj_wd_neg,
               <-EqNat.beq_nat_false_iff in E'.
               rewrite <-plus_n_O, E'; auto.
             - erewrite IHn; eauto.
               pose proof (count_true_ge_1 _ _ E).
               rewrite count_false_shift, E, Minus.minus_Sn_m in E';
                 auto; simpl in E';
                   rewrite <-Minus.minus_n_O, <-EqNat.beq_nat_false_iff in E'.
               rewrite <-plus_n_O, E'; auto.
             - erewrite IHn; eauto.
               pose proof (count_true_ge_1 _ _ E).
               rewrite count_false_shift, E, Minus.minus_Sn_m in E';
                 auto; simpl in E';
                   rewrite <-Minus.minus_n_O, <-EqNat.beq_nat_false_iff in E'.
               rewrite <-plus_n_O, E'; auto.
             - erewrite IHn; eauto.
               pose proof (count_true_ge_1 _ _ E).
               rewrite count_false_shift, E, Minus.minus_Sn_m in E';
                 auto; simpl in E';
                   rewrite <-Minus.minus_n_O, <-EqNat.beq_nat_false_iff in E'.
               rewrite <-plus_n_O, E'; auto.
           }

      - rewrite count_false_shift, E in C.
        revert k' k r xs E C; induction n; simpl; intros.
        + rewrite E in C.
          destruct (EqNat.beq_nat k k') eqn: E'.
          * apply EqNat.beq_nat_true in E'; subst.
            unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
              simpl; rewrite <-E'; repeat rewrite tr_stream_0; auto.
            rewrite tr_stream_0 in E; discriminate.
          *{ apply EqNat.beq_nat_false in E'.
             unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
               destruct k' as [|[]]; simpl; try (exfalso; now apply E').
             - pose proof (tr_stream_const absent); auto.
             - apply tr_stream_0.
           }
        + destruct (EqNat.beq_nat k k') eqn: E'.
          *{ apply EqNat.beq_nat_true in E'; subst.
             unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
               destruct k' as [|[]]; simpl; repeat rewrite tr_stream_S;
                 rewrite E in E'; try discriminate; rewrite tr_stream_S in E.
             - inv E'; exfalso; eapply count_true_not_0; eauto.
             - erewrite tr_stream_mask_false_true; eauto;
                 rewrite <-EqNat.beq_nat_refl; auto.
             - erewrite tr_stream_mask_false_true; eauto;
                 rewrite <-EqNat.beq_nat_refl; auto.
             - erewrite IHn; eauto.
               rewrite count_false_shift, E in E'.
               rewrite <-plus_n_O, E'; auto.
             - erewrite IHn; eauto.
               rewrite count_false_shift, E in E'.
               rewrite <-plus_n_O, E'; auto.
             - erewrite IHn; eauto.
               rewrite count_false_shift, E in E'.
               rewrite <-plus_n_O, E', <-EqNat.beq_nat_refl; auto.
           }
          *{ apply EqNat.beq_nat_false in E'.
             unfold_Stv r; unfold_St xs; rewrite unfold_Stream at 1;
               destruct k' as [|[]]; simpl; rewrite E in C; subst;
                 repeat rewrite tr_stream_S; rewrite tr_stream_S in E;
                   try (exfalso; now apply E').
             - pose proof (tr_stream_const absent); auto.
             - erewrite IHn; eauto.
               rewrite count_true_shift, E, NPeano.Nat.succ_inj_wd_neg,
               <-EqNat.beq_nat_false_iff in E'.
               rewrite <-plus_n_O, E'; auto.
             - erewrite IHn; eauto.
               rewrite count_true_shift, E, NPeano.Nat.succ_inj_wd_neg,
               <-EqNat.beq_nat_false_iff in E'.
               rewrite <-plus_n_O, E'; auto.
             - erewrite IHn; eauto.
               rewrite count_false_shift, E, <-EqNat.beq_nat_false_iff in E'.
               rewrite <-plus_n_O, E'; auto.
             - erewrite IHn; eauto.
               rewrite count_false_shift, E, <-EqNat.beq_nat_false_iff in E'.
               rewrite <-plus_n_O, E'; auto.
             - erewrite IHn; eauto.
               rewrite count_false_shift, E, <-EqNat.beq_nat_false_iff in E'.
               rewrite <-plus_n_O, E'; auto.
           }
    Qed.

    Ltac auto_f_equal H :=
      f_equal;
      [ idtac |
        erewrite H; eauto; unfold mask; simpl; rewrite tr_stream_S;
        repeat match goal with
               | H: tr_stream _ _ = _ |- _ => rewrite H
               | H: count ?x _ = _ |- _ => rewrite H
               | H:  EqNat.beq_nat _ _ = _ |- _ => rewrite H
               end; auto].

    (** State the correspondence for [mask]. *)
    Lemma mask_impl:
      forall k r xss n,
         tr_streams (List.map (CoInd.mask_v k r) xss) n
        = mask (Indexed.all_absent xss) k (tr_stream r) (tr_streams xss) n.
    Proof.
      induction xss as [|xs];
        simpl; intros.
      - unfold mask.
        destruct (EqNat.beq_nat k (count (tr_stream r) n)); auto.
      - induction n.
        + unfold_St xs; unfold_Stv r; unfold CoInd.mask_v, mask;
            rewrite unfold_Stream at 1; simpl;
            destruct k as [|[]]; simpl; f_equal;
              erewrite IHxss; eauto; unfold mask; auto.
        + unfold_St xs; unfold_Stv r; unfold CoInd.mask_v, mask.
          *{ rewrite unfold_Stream at 1; simpl.
             destruct k as [|[]]; simpl.
             - repeat rewrite tr_stream_S.
               destruct (tr_stream r n) eqn: E.
               + auto_f_equal IHxss.
                 pose proof (tr_stream_const absent); auto.
               + destruct (count (tr_stream (true ::: r)) n) eqn: E'.
                 * exfalso; eapply count_true_not_0; eauto.
                 * auto_f_equal IHxss.
                   pose proof (tr_stream_const absent); auto.
             - repeat rewrite tr_stream_S.
               destruct (tr_stream r n) eqn: E.
               + destruct (count (tr_stream (true ::: r)) n) eqn: E'.
                 * exfalso; eapply count_true_not_0; eauto.
                 * auto_f_equal IHxss.
                   apply tr_stream_mask_true_0; auto.
               + destruct (count (tr_stream (true ::: r)) n) as [|[]] eqn: E'.
                 * exfalso; eapply count_true_not_0; eauto.
                 * auto_f_equal IHxss.
                   erewrite tr_stream_mask_false_true; eauto; auto.
                 * auto_f_equal IHxss.
                   erewrite tr_stream_mask_false_true; eauto; auto.
             - repeat rewrite tr_stream_S.
               destruct (tr_stream r n) eqn: E.
               + destruct (count (tr_stream (true ::: r)) n) eqn: E'.
                 * exfalso; eapply count_true_not_0; eauto.
                 *{ destruct (EqNat.beq_nat n0 n1) eqn: E''; auto_f_equal IHxss.
                    - erewrite tr_stream_mask_same; eauto.
                      apply EqNat.beq_nat_true, eq_S,
                      EqNat.beq_nat_true_iff in E'';
                        rewrite NPeano.Nat.eqb_sym, E''; auto.
                    - erewrite tr_stream_mask_same; eauto.
                      apply EqNat.beq_nat_false, not_eq_S,
                      EqNat.beq_nat_false_iff in E'';
                        rewrite NPeano.Nat.eqb_sym, E''; auto.
                  }
               + destruct (count (tr_stream (true ::: r)) n) as [|[]] eqn: E'.
                 * exfalso; eapply count_true_not_0; eauto.
                 * auto_f_equal IHxss.
                   erewrite tr_stream_mask_false_true; eauto; auto.
                 *{ destruct (EqNat.beq_nat n0 n1) eqn: E''; auto_f_equal IHxss.
                    - erewrite tr_stream_mask_false_true; eauto.
                      apply EqNat.beq_nat_true, eq_S,
                      EqNat.beq_nat_true_iff in E'';
                        rewrite NPeano.Nat.eqb_sym, E''; auto.
                    - erewrite tr_stream_mask_false_true; eauto.
                      apply EqNat.beq_nat_false, not_eq_S,
                      EqNat.beq_nat_false_iff in E'';
                        rewrite NPeano.Nat.eqb_sym, E''; auto.
                  }
           }

          *{ rewrite unfold_Stream at 1; simpl.
             destruct k as [|[]]; simpl.
             - repeat rewrite tr_stream_S.
               destruct (tr_stream r n) eqn: E.
               + auto_f_equal IHxss.
                 apply tr_stream_mask_true_0; auto.
               + destruct (count (tr_stream (false ::: r)) n) eqn: E';
                   auto_f_equal IHxss; erewrite tr_stream_mask_same; eauto; auto.
             - repeat rewrite tr_stream_S.
               destruct (tr_stream r n) eqn: E.
               + destruct (count (tr_stream (false ::: r)) n) eqn: E';
                   auto_f_equal IHxss;
                   erewrite tr_stream_mask_true_false; eauto; auto.
               + destruct (count (tr_stream (false ::: r)) n) as [|[]] eqn: E';
                   auto_f_equal IHxss; erewrite tr_stream_mask_same; eauto; auto.
             - repeat rewrite tr_stream_S.
               destruct (tr_stream r n) eqn: E.
               + destruct (count (tr_stream (false ::: r)) n) eqn: E'.
                 * auto_f_equal IHxss.
                   erewrite tr_stream_mask_true_false; eauto; auto.
                 *{ destruct (EqNat.beq_nat n0 n1) eqn: E''; auto_f_equal IHxss.
                    - erewrite tr_stream_mask_true_false; eauto.
                      apply EqNat.beq_nat_true, eq_S,
                      EqNat.beq_nat_true_iff in E'';
                        rewrite NPeano.Nat.eqb_sym, E''; auto.
                    - erewrite tr_stream_mask_true_false; eauto.
                      apply EqNat.beq_nat_false, not_eq_S,
                      EqNat.beq_nat_false_iff in E'';
                        rewrite NPeano.Nat.eqb_sym, E''; auto.
                  }
               + destruct (count (tr_stream (false ::: r)) n) as [|[]] eqn: E'.
                 * auto_f_equal IHxss.
                   erewrite tr_stream_mask_same; eauto; auto.
                 * auto_f_equal IHxss.
                   erewrite tr_stream_mask_same; eauto; auto.
                 *{ destruct (EqNat.beq_nat n0 n1) eqn: E''; auto_f_equal IHxss.
                    - erewrite tr_stream_mask_same; eauto.
                      apply EqNat.beq_nat_true, eq_S, eq_S,
                      EqNat.beq_nat_true_iff in E'';
                        rewrite NPeano.Nat.eqb_sym, E''; auto.
                    - erewrite tr_stream_mask_same; eauto.
                      apply EqNat.beq_nat_false, not_eq_S, not_eq_S,
                      EqNat.beq_nat_false_iff in E'';
                        rewrite NPeano.Nat.eqb_sym, E''; auto.
                  }
           }
    Qed.

    (** * FINAL LEMMAS *)


    Remark all_absent_tr_streams:
      forall A n (xss: list (Stream A)),
        Indexed.all_absent (tr_streams xss n) = Indexed.all_absent xss.
    Proof.
      induction xss; simpl; auto; now f_equal.
    Qed.

    (** Correspondence for [clocks_of], used to give a base clock for node
        applications. *)
    Lemma tr_clocks_of:
      forall xss,
        Indexed.clock_of (tr_streams xss) (tr_stream (CoInd.clocks_of xss)).
    Proof.
      split; intros ** H.
      - revert dependent xss; induction n; intros; induction xss as [|xs];
          rewrite unfold_Stream at 1; simpl in *;
          try rewrite tr_stream_0; try rewrite tr_stream_S; auto.
        + inversion_clear H as [|? ? ToMap Forall].
          apply andb_true_intro; split.
          * unfold_St xs; rewrite tr_stream_0 in ToMap.
            apply Bool.negb_true_iff; rewrite not_equiv_decb_equiv; intro E.
            contradiction.
          * apply IHxss in Forall.
            clear - Forall; induction xss as [|xs]; simpl; auto.
        + inversion_clear H.
          apply IHn. constructor.
          * now rewrite tr_stream_tl.
          * fold (@tr_streams value).
            now rewrite tr_streams_tl.
      - revert dependent xss; induction n; intros; induction xss as [|xs];
          simpl in *; constructor.
        + rewrite unfold_Stream in H at 1; simpl in H;
            rewrite tr_stream_0 in H; apply andb_prop in H as [].
          unfold_St xs; rewrite tr_stream_0; simpl in *.
          intro; subst; discriminate.
        + apply IHxss.
          rewrite unfold_Stream in H at 1; simpl in H;
            rewrite tr_stream_0 in H; apply andb_prop in H as [? Forall].
          clear - Forall; induction xss; rewrite unfold_Stream at 1; simpl;
            now rewrite tr_stream_0.
        + rewrite unfold_Stream in H at 1; simpl in H; rewrite tr_stream_S in H.
          apply IHn in H; inv H.
          now rewrite <-tr_stream_tl.
        + rewrite unfold_Stream in H at 1; simpl in H; rewrite tr_stream_S in H.
          apply IHn in H; inv H.
          now rewrite <-tr_streams_tl.
    Qed.

    (** The final theorem stating the correspondence for equations, nodes and
        reset applications. The conjunctive shape is mandatory to use the
        mutually recursive induction scheme [sem_equation_node_ind]. *)
    Theorem implies:
      (forall H b e,
          CoInd.sem_equation G H b e ->
          Indexed.sem_equation G (tr_stream b) (tr_history H) e)
      /\
      (forall f xss oss,
          CoInd.sem_node G f xss oss ->
          Indexed.sem_node G f (tr_streams xss) (tr_streams oss))
      /\
      (forall f r xss oss,
          CoInd.sem_reset G f r xss oss ->
          Indexed.sem_reset G f (tr_stream r) (tr_streams xss) (tr_streams oss)).
    Proof.
      apply CoInd.sem_equation_node_ind.
      - econstructor.
        + apply sem_var_impl; eauto.
        + apply sem_caexp_impl; auto.
      - econstructor; eauto.
        + apply sem_laexps_impl; auto.
        + apply sem_vars_impl; auto.
      - econstructor; auto.
        + apply sem_laexps_impl; eauto.
        + apply sem_vars_impl; eauto.
        + apply sem_var_impl; eauto.
        + eapply Indexed.sem_reset_compat.
          * intro; apply tr_stream_reset.
          * eauto.
      - econstructor; auto; subst.
        + apply sem_laexp_impl; eauto.
        + unfold Indexed.sem_var, Indexed.lift; intro.
          rewrite <-fby_impl.
          apply sem_var_impl; auto.
          exact (tr_stream b).
      - intros ** IHNode.
        constructor; intro.
        specialize (IHNode n).
        pose proof (mask_impl n r xss) as Hxss.
        pose proof (mask_impl n r yss) as Hyss.
        rewrite 2 all_absent_tr_streams.
        eapply Indexed.sem_node_compat; eauto.
      - intros ** Hin Hout Same ? ?. econstructor; eauto.
        + apply tr_clocks_of.
        + apply sem_vars_impl; eauto.
        + apply sem_vars_impl; eauto.
        + now apply CoInd.same_clock_app_l, same_clock_impl in Same.
        + now apply CoInd.same_clock_app_r, same_clock_impl in Same.
        + apply same_clock_app_impl; auto.
          * intro; subst.
            apply Forall2_length in Hin; simpl in *.
            unfold CoInd.idents in Hin; rewrite map_length in Hin.
            pose proof n.(n_ingt0) as Nin.
            rewrite Hin in Nin; contradict Nin; apply Lt.lt_irrefl.
          * intro; subst.
            apply Forall2_length in Hout; simpl in *.
            unfold CoInd.idents in Hout; rewrite map_length in Hout.
            pose proof n.(n_outgt0) as Nout.
            rewrite Hout in Nout; contradict Nout; apply Lt.lt_irrefl.
    Qed.

    Definition equation_impl := proj1 implies.
    Definition node_impl := proj1 (proj2 implies).
    Definition reset_impl := proj2 (proj2 implies).

  End Global.

End INDEXEDTOCOIND.
