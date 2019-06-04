From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Morphisms.
From Coq Require Import Program.Tactics.
From Coq Require Import Omega.

From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import CoreExpr.Stream.
From Velus Require Import Streams.

From Velus Require Import CoreExpr.CESemantics.
From Velus Require Import NLustre.NLSemantics.
From Velus Require Import NLustre.NLSemanticsCoInd.

From Coq Require Import Setoid.

Module Type COINDTOINDEXED
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import OpAux   : OPERATORS_AUX        Op)
       (Import CESyn   : CESYNTAX             Op)
       (Import Syn     : NLSYNTAX         Ids Op       CESyn)
       (Import Str     : STREAM               Op OpAux)
       (Import Strs    : STREAMS              Op OpAux)
       (Import Ord     : NLORDERED        Ids Op       CESyn Syn)
       (CESem          : CESEMANTICS      Ids Op OpAux CESyn     Str)
       (Indexed        : NLSEMANTICS      Ids Op OpAux CESyn Syn Str Ord CESem)
       (CoInd          : NLSEMANTICSCOIND Ids Op OpAux CESyn Syn Strs).

  Section Global.

    Variable G : global.

    (** * BASIC CORRESPONDENCES *)

    (** ** Definitions  *)

    (** Translate a coinductive Stream into an indexed stream.
        The result stream is the function which associates the [n]th element of
        the input Stream to each [n].
     *)
    Definition tr_Stream {A} (xs: Stream A) : stream A :=
      fun n => Str_nth n xs.

    (** Translate a list of Streams into a stream of list.
        - if the input list is void, the result is the constantly void stream
        - else, the result is the function associating to each [n] the list
          built by the translated stream of the head of the input list indexed
          at [n] consed to the result of the recursive call, also indexed at [n].
     *)
    Fixpoint tr_Streams {A} (xss: list (Stream A)) : stream (list A) :=
      match xss with
      | [] => fun n => []
      | xs :: xss => fun n => tr_Stream xs n :: tr_Streams xss n
      end.

    (** Translate an history from coinductive to indexed world.
        Every element of the history is translated.
     *)
    Definition tr_History (H: CoInd.History) : CESem.history :=
      Env.map tr_Stream H.

    (** ** Properties  *)

    (** Indexing a translated Stream at [0] is taking the head of the source
        Stream. *)
    Lemma tr_Stream_0:
      forall {A} (xs: Stream A) x,
        tr_Stream (x ::: xs) 0 = x.
    Proof. reflexivity. Qed.

    (** Indexing a translated Stream at [S n] is indexing the tail of the source
        Stream at [n]. *)
    Lemma tr_Stream_S:
      forall {A} (xs: Stream A) x n,
        tr_Stream (x ::: xs) (S n) = tr_Stream xs n.
    Proof. reflexivity. Qed.

    (** Another version of the previous lemma.  *)
    Lemma tr_Stream_tl:
      forall {A} (xs: Stream A) n,
        tr_Stream (tl xs) n = tr_Stream xs (S n).
    Proof. reflexivity. Qed.

    (** A generalized version *)
    Lemma tr_Stream_nth:
      forall {A} n (xs: Stream A),
        tr_Stream xs n = Str_nth n xs.
    Proof. reflexivity. Qed.

    Lemma tr_Stream_const:
      forall {A} (c: A) n,
        tr_Stream (Streams.const c) n = c.
    Proof.
      induction n; rewrite unfold_Stream at 1; simpl.
      - now rewrite tr_Stream_0.
      - now rewrite tr_Stream_S.
    Qed.

    (** [tr_Stream] is compatible wrt to [EqSt]. *)
    Add Parametric Morphism A : (@tr_Stream A)
        with signature @EqSt A ==> eq ==> eq
          as tr_Stream_morph.
    Proof.
      intros xs ys Exs n.
      revert xs ys Exs; induction n; intros; destruct xs, ys; inv Exs.
      - rewrite 2 tr_Stream_0; auto.
      - rewrite 2 tr_Stream_S; auto.
    Qed.

    Fact tr_Streams_app:
      forall A (xss yss: list (Stream A)) n,
        tr_Streams (xss ++ yss) n = tr_Streams xss n ++ tr_Streams yss n.
    Proof.
      intros; induction xss; simpl; auto.
      f_equal; auto.
    Qed.

    (** The counterpart of [tr_Stream_tl] for lists of Streams. *)
    Lemma tr_Streams_tl:
      forall xss n,
        tr_Streams (List.map (tl (A:=value)) xss) n = tr_Streams xss (S n).
    Proof.
      intros; induction xss; simpl; auto.
      f_equal; auto.
    Qed.

    Lemma tr_Streams_hd:
      forall xss,
        tr_Streams xss 0 = List.map (hd (A:=value)) xss.
    Proof.
      intros; induction xss; simpl; auto.
      destruct a; simpl.
      rewrite tr_Stream_0.
      f_equal; auto.
    Qed.

    (** The counterpart of [tr_Stream_tl] for histories. *)
    Lemma tr_History_tl:
      forall n H,
        CESem.restr_hist (tr_History H) (S n)
        = CESem.restr_hist (tr_History (CoInd.History_tl H)) n.
    Proof.
      now repeat setoid_rewrite Env.map_map.
    Qed.

    (** * SEMANTICS CORRESPONDENCE *)

    (** ** Variables *)

    Lemma sem_var_impl:
      forall H x xs,
      CoInd.sem_var H x xs ->
      CESem.sem_var (tr_History H) x (tr_Stream xs).
    Proof.
      intros * Find n.
      unfold CESem.sem_var_instant.
      inversion_clear Find as [???? Find' E].
      unfold CESem.restr_hist, tr_History.
      unfold Env.map.
      rewrite 2 Env.gmapi, Find', E; simpl; auto.
    Qed.
    Hint Resolve sem_var_impl.

    Corollary sem_vars_impl:
      forall H xs xss,
      Forall2 (CoInd.sem_var H) xs xss ->
      CESem.sem_vars (tr_History H) xs (tr_Streams xss).
    Proof.
      unfold CESem.sem_vars, CESem.lift'.
      induction 1 as [|? ? ? ? Find];
        simpl; intro; constructor; auto.
      - apply sem_var_impl; auto.
      - apply IHForall2.
    Qed.
    Hint Resolve sem_vars_impl.

    (** ** lexp level synchronous operators specifications

        To ease the use of coinductive hypotheses to prove non-coinductive
        goals, we give for each coinductive predicate an indexed specification,
        reflecting the shapes of the involved streams pointwise speaking.
        In general this specification is a disjunction with a factor for each
        case of the predicate.
        The corresponding lemmas simply go by induction on [n] and by inversion
        of the coinductive hypothesis.
     *)

    Lemma const_index:
      forall n xs c b,
        xs ≡ CoInd.const c b ->
        tr_Stream xs n = if tr_Stream b n then present (sem_const c) else absent.
    Proof.
      induction n; intros * E;
        unfold_Stv b; unfold_Stv xs; inv E; simpl in *; try discriminate;
          repeat rewrite tr_Stream_0; repeat rewrite tr_Stream_S; auto.
    Qed.

    Lemma when_index:
      forall n k xs cs rs,
        CoInd.when k xs cs rs ->
        (tr_Stream xs n = absent
         /\ tr_Stream cs n = absent
         /\ tr_Stream rs n = absent)
        \/
        (exists x c,
            tr_Stream xs n = present x
            /\ tr_Stream cs n = present c
            /\ val_to_bool c = Some (negb k)
            /\ tr_Stream rs n = absent)
        \/
        (exists x c,
            tr_Stream xs n = present x
            /\ tr_Stream cs n = present c
            /\ val_to_bool c = Some k
            /\ tr_Stream rs n = present x).
    Proof.
      induction n; intros * When.
      - inv When; repeat rewrite tr_Stream_0; intuition.
        + right; left. do 2 eexists; intuition.
        + right; right. do 2 eexists; intuition.
      - inv When; repeat rewrite tr_Stream_S; auto.
    Qed.

    Lemma lift1_index:
      forall n op t xs ys,
        CoInd.lift1 op t xs ys ->
        (tr_Stream xs n = absent /\ tr_Stream ys n = absent)
        \/
        (exists x y,
            tr_Stream xs n = present x
            /\ sem_unop op x t = Some y
            /\ tr_Stream ys n = present y).
    Proof.
      induction n; intros * Lift1.
      - inv Lift1; repeat rewrite tr_Stream_0; intuition.
        right. do 2 eexists; intuition; auto.
      - inv Lift1; repeat rewrite tr_Stream_S; auto.
    Qed.

    Lemma lift2_index:
      forall n op t1 t2 xs ys zs,
        CoInd.lift2 op t1 t2 xs ys zs ->
        (tr_Stream xs n = absent
         /\ tr_Stream ys n = absent
         /\ tr_Stream zs n = absent)
        \/
        (exists x y z,
            tr_Stream xs n = present x
            /\ tr_Stream ys n = present y
            /\ sem_binop op x t1 y t2 = Some z
            /\ tr_Stream zs n = present z).
    Proof.
      induction n; intros * Lift2.
      - inv Lift2; repeat rewrite tr_Stream_0; intuition.
        right. do 3 eexists; intuition; auto.
      - inv Lift2; repeat rewrite tr_Stream_S; auto.
    Qed.

    (** ** Semantics of clocks *)

    (** Give an indexed specification for [sem_clock] in the previous style,
        with added complexity as [sem_clock] depends on [H] and [b].
        We go by induction on the clock [ck] then by induction on [n] and
        inversion of the coinductive hypothesis as before. *)
    Hint Constructors CESem.sem_clock_instant.
    Lemma sem_clock_index:
      forall n H b ck bs,
        CoInd.sem_clock H b ck bs ->
        (ck = Cbase
         /\ tr_Stream b n = tr_Stream bs n)
        \/
        (exists ck' x k c,
            ck = Con ck' x k
            /\ CESem.sem_clock_instant
                (tr_Stream b n) (CESem.restr_hist (tr_History H) n) ck' true
            /\ CESem.sem_var_instant (CESem.restr_hist (tr_History H) n) x
                                      (present c)
            /\ val_to_bool c = Some k
            /\ tr_Stream bs n = true)
        \/
        (exists ck' x k,
            ck = Con ck' x k
            /\ CESem.sem_clock_instant
                (tr_Stream b n) (CESem.restr_hist (tr_History H) n) ck' false
            /\ CESem.sem_var_instant (CESem.restr_hist (tr_History H) n) x absent
            /\ tr_Stream bs n = false)
        \/
        (exists ck' x k c,
            ck = Con ck' x (negb k)
            /\ CESem.sem_clock_instant
                (tr_Stream b n) (CESem.restr_hist (tr_History H) n) ck' true
            /\ CESem.sem_var_instant (CESem.restr_hist (tr_History H) n) x
                                      (present c)
            /\ val_to_bool c = Some k
            /\ tr_Stream bs n = false).
    Proof.
      Local Ltac rew_0 :=
        try match goal with
              H: tr_Stream _ _ = _ |- _ => now rewrite tr_Stream_0 in H
            end.
      intros n H b ck; revert n H b; induction ck as [|ck ? x k].
      - inversion_clear 1 as [? ? ? Eb| | |].
        left; intuition.
        now rewrite Eb.
      - intro n; revert x k; induction n; intros x k H bk bk' Indexed.
        + inversion_clear Indexed as [|? ? ? ? ? ? ? ? ? IndexedCk Hvar
                                     |? ? ? ? ? ? ? ? IndexedCk Hvar
                                     |? ? ? ? ? ? ? ? ? IndexedCk Hvar].
          * right; left.
            apply sem_var_impl in Hvar;
              unfold CESem.sem_var, CESem.lift in Hvar ; specialize (Hvar 0);
                rewrite tr_Stream_0 in Hvar.
            do 4 eexists; intuition; eauto.
            apply (IHck 0) in IndexedCk as [(? & E)|[|[]]]; destruct_conjs;
              subst; eauto; rew_0.
            rewrite E, tr_Stream_0; constructor.
          * right; right; left.
            apply sem_var_impl in Hvar;
              unfold CESem.sem_var, CESem.lift in Hvar ; specialize (Hvar 0);
                rewrite tr_Stream_0 in Hvar.
            do 3 eexists; intuition.
            apply (IHck 0) in IndexedCk as [(? & E)|[|[]]]; destruct_conjs;
              subst; eauto; rew_0.
            rewrite E, tr_Stream_0; constructor.
          * right; right; right.
            apply sem_var_impl in Hvar;
              unfold CESem.sem_var, CESem.lift in Hvar; specialize (Hvar 0);
                rewrite tr_Stream_0 in Hvar.
            do 4 eexists; intuition; eauto.
            apply (IHck 0) in IndexedCk as [(? & E)|[|[]]]; destruct_conjs;
              subst; eauto; rew_0.
            rewrite E, tr_Stream_0; constructor.
        + inversion_clear Indexed; rewrite <-tr_Stream_tl, tr_History_tl; eauto.
    Qed.

    (** We can then deduce the correspondence lemma for [sem_clock]. *)
    Corollary sem_clock_impl:
      forall H b ck bs,
        CoInd.sem_clock H b ck bs ->
        CESem.sem_clock (tr_Stream b) (tr_History H) ck (tr_Stream bs).
    Proof.
      intros * Indexed n.
      apply (sem_clock_index n) in Indexed. destruct Indexed as [|[|[|]]];
                                              destruct_conjs;
        match goal with H: tr_Stream _ _ = _ |- _ => rewrite H end;
        subst; eauto.
    Qed.
    Hint Resolve sem_clock_impl.

    (* (** Give an indexed specification for annotated [var]. *) *)
    (* Lemma sem_avar_index: *)
    (*   forall n H b ck x vs, *)
    (*     CoInd.sem_avar H b ck x vs -> *)
    (*     (CESem.sem_clock_instant (tr_Stream b n) *)
    (*                                (CESem.restr_hist (tr_History H) n) ck false *)
    (*      /\ CESem.sem_var_instant (CESem.restr_hist (tr_History H) n) x absent *)
    (*      /\ tr_Stream vs n = absent) *)
    (*     \/ *)
    (*     (exists v, *)
    (*         CESem.sem_clock_instant (tr_Stream b n) *)
    (*                                   (CESem.restr_hist (tr_History H) n) ck true *)
    (*         /\ CESem.sem_var_instant (CESem.restr_hist (tr_History H) n) x (present v) *)
    (*         /\ tr_Stream vs n = present v). *)
    (* Proof. *)
    (*   induction n; intros * Indexed. *)
    (*   - inversion_clear Indexed as [? ? ? ? ? ? ? Indexed' Hck *)
    (*                                   |? ? ? ? ? ? Indexed' Hck]; *)
    (*       apply sem_var_impl with (b:=tr_Stream b) in Indexed'; specialize (Indexed' 0); *)
    (*         repeat rewrite tr_Stream_0; repeat rewrite tr_Stream_0 in Indexed'; *)
    (*           apply (sem_clock_impl 0) in Hck; rewrite tr_Stream_0 in Hck. *)
    (*     + right. eexists; intuition; auto. *)
    (*     + left; intuition. *)
    (*   - inversion_clear Indexed as [? ? ? ? ? ? ? Indexed'|? ? ? ? ? ? Indexed']; *)
    (*       apply sem_var_impl with (b:=tr_Stream b) in Indexed'; *)
    (*       rewrite tr_Stream_S, tr_History_tl; eauto. *)
    (* Qed. *)

    (* (** We deduce from the previous lemma the correspondence for annotated *)
    (*     [var]. *) *)
    (* Hint Constructors Indexed.sem_avar_instant. *)
    (* Corollary sem_avar_impl: *)
    (*   forall H b x vs ck, *)
    (*     CoInd.sem_avar H b ck x vs -> *)
    (*     Indexed.sem_avar (tr_Stream b) (tr_History H) ck x (tr_Stream vs). *)
    (* Proof. *)
    (*   intros * Indexed n. *)
    (*   apply (sem_avar_index n) in Indexed as [(? & ? & Hes)|(? & ? & ? & Hes)]; *)
    (*     rewrite Hes; auto. *)
    (* Qed. *)
    (* Hint Resolve sem_avar_impl. *)

    (** ** Semantics of lexps *)

    (** State the correspondence for [lexp].
        Goes by induction on the coinductive semantics of [lexp]. *)
    Hint Constructors CESem.sem_lexp_instant.
    Lemma sem_lexp_impl:
      forall H b e es,
        CoInd.sem_lexp H b e es ->
        CESem.sem_lexp (tr_Stream b) (tr_History H) e (tr_Stream es).
    Proof.
      induction 1 as [? ? ? ? Hconst
                            |? ? ? ? ? Hvar
                            |? ? ? ? ? ? ? ? ? ? Hvar Hwhen
                            |? ? ? ? ? ? ? ? ? Hlift1
                            |? ? ? ? ? ? ? ? ? ? ? ? ? Hlift2]; intro n.
      - apply (const_index n) in Hconst; rewrite Hconst.
        destruct (tr_Stream b n); eauto.
      - apply sem_var_impl in Hvar; eauto.
      - specialize (IHsem_lexp n).
        apply sem_var_impl in Hvar.
        unfold CESem.sem_var, CESem.lift in Hvar.
        specialize (Hvar n).
        apply (when_index n) in Hwhen
          as [(Hes & Hxs & Hos)
             |[(? & ? & Hes & Hxs & ? & Hos)
              |(? & ? & Hes & Hxs & ? & Hos)]];
          rewrite Hos; rewrite Hes in IHsem_lexp; rewrite Hxs in Hvar;
            eauto.
        rewrite <-(Bool.negb_involutive k); eauto.
      - specialize (IHsem_lexp n).
        apply (lift1_index n) in Hlift1; destruct Hlift1
          as [(Hes & Hos)|(? & ? & Hes & ? & Hos)];
          rewrite Hos; rewrite Hes in IHsem_lexp; eauto.
      - specialize (IHsem_lexp1 n).
        specialize (IHsem_lexp2 n).
        apply (lift2_index n) in Hlift2; destruct Hlift2
          as [(Hes1 & Hes2 & Hos)|(? & ? & ? & Hes1 & Hes2 & ? & Hos)];
          rewrite Hos; rewrite Hes1 in IHsem_lexp1; rewrite Hes2 in IHsem_lexp2;
            eauto.
    Qed.
    Hint Resolve sem_lexp_impl.

    Corollary sem_lexps_impl:
      forall H b es ess,
        Forall2 (CoInd.sem_lexp H b) es ess ->
        CESem.sem_lexps (tr_Stream b) (tr_History H) es (tr_Streams ess).
    Proof.
      induction 1; simpl; constructor.
      - apply sem_lexp_impl; auto.
      - apply IHForall2.
    Qed.
    Hint Resolve sem_lexps_impl.

    (** Give an indexed specification for annotated [lexp], using the previous
        lemma. *)
    Lemma sem_laexp_index:
      forall n H b ck le es,
        CoInd.sem_laexp H b ck le es ->
        (CESem.sem_clock_instant (tr_Stream b n)
                                   (CESem.restr_hist (tr_History H) n) ck false
         /\ CESem.sem_lexp_instant
             (tr_Stream b n) (CESem.restr_hist (tr_History H) n) le absent
         /\ tr_Stream es n = absent)
        \/
        (exists e,
            CESem.sem_clock_instant (tr_Stream b n)
                                      (CESem.restr_hist (tr_History H) n) ck true
            /\ CESem.sem_lexp_instant
                (tr_Stream b n) (CESem.restr_hist (tr_History H) n) le (present e)
            /\ tr_Stream es n = present e).
    Proof.
      induction n; intros * Indexed.
      - inversion_clear Indexed as [? ? ? ? ? ? ? Indexed' Hck
                                      |? ? ? ? ? ? Indexed' Hck];
          apply sem_lexp_impl in Indexed'; specialize (Indexed' 0);
            repeat rewrite tr_Stream_0; repeat rewrite tr_Stream_0 in Indexed';
              eapply (sem_clock_impl) in Hck; specialize (Hck 0); rewrite tr_Stream_0 in Hck.
        + right. eexists; intuition; auto.
        + left; intuition.
      - inversion_clear Indexed as [? ? ? ? ? ? ? Indexed'|? ? ? ? ? ? Indexed'];
          apply sem_lexp_impl in Indexed';
          rewrite tr_Stream_S, tr_History_tl; eauto.
    Qed.

    (** We deduce from the previous lemma the correspondence for annotated
        [lexp]. *)
    (* Hint Constructors CESem.sem_laexp_instant. *)
    Corollary sem_laexp_impl:
      forall H b e es ck,
        CoInd.sem_laexp H b ck e es ->
        CESem.sem_laexp (tr_Stream b) (tr_History H) ck e (tr_Stream es).
    Proof.
      intros * Indexed n.
      apply (sem_laexp_index n) in Indexed;
        destruct Indexed as [(? & ? & Hes)|(? & ? & ? & Hes)];
        rewrite Hes; constructor; auto.
    Qed.
    Hint Resolve sem_laexp_impl.

    (** ** cexp level synchronous operators specifications *)

    Lemma merge_index:
      forall n xs ts fs rs,
        CoInd.merge xs ts fs rs ->
        (tr_Stream xs n = absent
         /\ tr_Stream ts n = absent
         /\ tr_Stream fs n = absent
         /\ tr_Stream rs n = absent)
        \/
        (exists t,
            tr_Stream xs n = present true_val
            /\ tr_Stream ts n = present t
            /\ tr_Stream fs n = absent
            /\ tr_Stream rs n = present t)
        \/
        (exists f,
            tr_Stream xs n = present false_val
            /\ tr_Stream ts n = absent
            /\ tr_Stream fs n = present f
            /\ tr_Stream rs n = present f).
    Proof.
      induction n; intros * Merge.
      - inv Merge; repeat rewrite tr_Stream_0; intuition.
        + right; left. eexists; intuition.
        + right; right. eexists; intuition.
      - inv Merge; repeat rewrite tr_Stream_S; auto.
    Qed.

    Lemma ite_index:
      forall n xs ts fs rs,
        CoInd.ite xs ts fs rs ->
        (tr_Stream xs n = absent
         /\ tr_Stream ts n = absent
         /\ tr_Stream fs n = absent
         /\ tr_Stream rs n = absent)
        \/
        (exists t f,
            tr_Stream xs n = present true_val
            /\ tr_Stream ts n = present t
            /\ tr_Stream fs n = present f
            /\ tr_Stream rs n = present t)
        \/
        (exists t f,
            tr_Stream xs n = present false_val
            /\ tr_Stream ts n = present t
            /\ tr_Stream fs n = present f
            /\ tr_Stream rs n = present f).
    Proof.
      induction n; intros * Ite.
      - inv Ite; repeat rewrite tr_Stream_0; intuition.
        + right; left. do 2 eexists; now intuition.
        + right; right. do 2 eexists; now intuition.
      - inv Ite; repeat rewrite tr_Stream_S; auto.
    Qed.

    (** [fby] is not a predicate but a function, so we directly state the
        correspondence.  *)
    Lemma fby_impl:
      forall c xs,
      tr_Stream (CoInd.fby c xs) ≈ Indexed.fby c (tr_Stream xs).
    Proof.
      intros * n; revert c xs.
      induction n; intros.
      - unfold_Stv xs; rewrite unfold_Stream at 1;
          unfold Indexed.fby; simpl; now rewrite tr_Stream_0.
      - unfold_Stv xs; rewrite unfold_Stream at 1;
          unfold Indexed.fby; simpl; repeat rewrite tr_Stream_S;
            rewrite IHn; unfold Indexed.fby;
              destruct (tr_Stream xs n); auto; f_equal;
                clear IHn; induction n; simpl; auto;
                  rewrite tr_Stream_S; destruct (tr_Stream xs n); auto.
    Qed.

    (** ** Semantics of cexps *)

    (** State the correspondence for [cexp].
        Goes by induction on the coinductive semantics of [cexp]. *)
    Hint Constructors CESem.sem_cexp_instant.
    Lemma sem_cexp_impl:
      forall H b e es,
        CoInd.sem_cexp H b e es ->
        CESem.sem_cexp (tr_Stream b) (tr_History H) e (tr_Stream es).
    Proof.
      induction 1 as [? ? ? ? ? ? ? ? ? Hvar Ht ? ? ? Hmerge
                    |? ? ? ? ? ? ? ? ? He Ht ? ? ? Hite
                    |? ? ? ? He]; intro n.
      - specialize (IHsem_cexp1 n).
        specialize (IHsem_cexp2 n).
        apply sem_var_impl in Hvar; eauto.
        unfold CESem.sem_var, CESem.lift in Hvar.
        specialize (Hvar n).
        rename H0_ into Hf.
        apply (merge_index n) in Hmerge
          as [(Hxs & Hts & Hfs & Hos)
             |[(? & Hxs & Hts & Hfs & Hos)
              |(? & Hxs & Hts & Hfs & Hos)]];
          rewrite Hos; rewrite Hts in IHsem_cexp1; rewrite Hfs in IHsem_cexp2;
            rewrite Hxs in Hvar; auto.

      - specialize (IHsem_cexp1 n).
        specialize (IHsem_cexp2 n).
        eapply sem_lexp_impl in He.
        specialize (He n).
        apply (ite_index n) in Hite
          as [(Hes & Hts & Hfs & Hos)
             |[(ct & cf & Hes & Hts & Hfs & Hos)
              |(ct & cf & Hes & Hts & Hfs & Hos)]];
          rewrite Hos; rewrite Hts in IHsem_cexp1; rewrite Hfs in IHsem_cexp2;
            rewrite Hes in He; auto.
        + change (present ct) with (if true then present ct else present cf).
          eapply CESem.Site_eq; eauto.
          apply val_to_bool_true.
        + change (present cf) with (if false then present ct else present cf).
          eapply CESem.Site_eq; eauto.
          apply val_to_bool_false.

      - apply sem_lexp_impl in He; auto.
    Qed.
    Hint Resolve sem_cexp_impl.

    (** Give an indexed specification for annotated [cexp], using the previous
        lemma.  *)
    Lemma sem_caexp_index:
      forall n H b ck le es,
        CoInd.sem_caexp H b ck le es ->
        (CESem.sem_clock_instant (tr_Stream b n)
                                   (CESem.restr_hist (tr_History H) n) ck false
         /\ CESem.sem_cexp_instant
             (tr_Stream b n) (CESem.restr_hist (tr_History H) n) le absent
         /\ tr_Stream es n = absent)
        \/
        (exists e,
            CESem.sem_clock_instant (tr_Stream b n)
                                      (CESem.restr_hist (tr_History H) n) ck true
            /\ CESem.sem_cexp_instant
                (tr_Stream b n) (CESem.restr_hist (tr_History H) n) le (present e)
            /\ tr_Stream es n = present e).
    Proof.
      induction n; intros * Indexed.
      - inversion_clear Indexed as [? ? ? ? ? ? ? Indexed' Hck
                                      |? ? ? ? ? ? Indexed' Hck];
          apply sem_cexp_impl in Indexed'; specialize (Indexed' 0);
            repeat rewrite tr_Stream_0; repeat rewrite tr_Stream_0 in Indexed';
              apply sem_clock_impl in Hck; specialize (Hck 0); rewrite tr_Stream_0 in Hck.
        + right. eexists; intuition; auto.
        + left; intuition.
      - inversion_clear Indexed as [? ? ? ? ? ? ? Indexed'|? ? ? ? ? ? Indexed'];
          apply sem_cexp_impl in Indexed';
          repeat rewrite tr_Stream_S; rewrite tr_History_tl; eauto.
    Qed.

    (** We deduce from the previous lemma the correspondence for annotated
        [cexp]. *)
    Corollary sem_caexp_impl:
      forall H b e es ck,
        CoInd.sem_caexp H b ck e es ->
        CESem.sem_caexp (tr_Stream b) (tr_History H) ck e (tr_Stream es).
    Proof.
      intros * Indexed n.
      apply (sem_caexp_index n) in Indexed; destruct Indexed
        as [(? & ? & Hes)|(? & ? & ? & Hes)];
        rewrite Hes; constructor; auto.
    Qed.
    Hint Resolve sem_caexp_impl.

    (** * RESET CORRESPONDENCE  *)

    (** We state the correspondence for [reset_of]. *)
    Lemma reset_of_impl:
      forall xs rs,
        CoInd.reset_of xs rs ->
        CESem.reset_of (tr_Stream xs) (tr_Stream rs).
    Proof.
      intros ** n; revert dependent xs; revert rs.
      induction n; intros * Rst.
      - unfold_Stv xs; unfold_Stv rs; rewrite tr_Stream_0; auto;
          inv Rst; simpl in *; auto.
      - unfold_Stv xs; unfold_Stv rs; rewrite 2 tr_Stream_S;
          inv Rst; simpl in *; auto.
    Qed.

    (** ** Properties about [count] and [mask] *)

    (** When a reset occurs initially, the count at [n] is the count at [n]
        forgetting the first instant, plus one if no reset occurs at [n] when
        shifting. *)
    Lemma count_true_shift:
      forall n r,
        Str.count (tr_Stream (true ::: r)) n
        = if tr_Stream r n
          then Str.count (tr_Stream r) n
          else S (Str.count (tr_Stream r) n).
    Proof.
      induction n; simpl; intros.
      - destruct (tr_Stream r 0); auto.
      - specialize (IHn r).
        rewrite tr_Stream_S.
        destruct (tr_Stream r n) eqn: E';
          destruct (tr_Stream r (S n)); rewrite IHn; auto.
    Qed.

    (** When no reset occurs initially, the count at [n] is the count at [n]
        forgetting the first instant, minus one if a reset occurs at [n] when
        shifting. *)
    Lemma count_false_shift:
      forall n r,
        Str.count (tr_Stream (false ::: r)) n
        = if tr_Stream r n
          then Str.count (tr_Stream r) n - 1
          else Str.count (tr_Stream r) n.
    Proof.
      induction n; simpl; intros.
      - destruct (tr_Stream r 0); auto.
      - specialize (IHn r).
        rewrite tr_Stream_S.
        destruct (tr_Stream r n) eqn: E';
          destruct (tr_Stream r (S n)); rewrite IHn; try omega.
        + apply Minus.minus_Sn_m, count_true_ge_1; auto.
        + rewrite Minus.minus_Sn_m; try omega.
          apply count_true_ge_1; auto.
    Qed.

    (** State the correspondence for [count]. *)
    Lemma count_impl:
      forall r,
        tr_Stream (Strs.count r) ≈ Str.count (tr_Stream r).
    Proof.
      intros ** n.
      unfold Strs.count.
      revert r; induction n; intros; simpl.
      - rewrite (unfold_Stream (count_acc 0 r)); simpl.
        rewrite tr_Stream_0; auto.
      - rewrite (unfold_Stream (count_acc 0 r)); simpl.
        rewrite tr_Stream_S. destruct (hd r) eqn: R.
        + unfold tr_Stream at 1; unfold tr_Stream in IHn; unfold Str_nth in *.
          rewrite count_S_nth, IHn.
          destruct r; simpl in *; rewrite R, count_true_shift, tr_Stream_S.
          now destruct (tr_Stream r n).
        + rewrite IHn.
          destruct r; simpl in *; rewrite R, count_false_shift, tr_Stream_S.
          destruct (tr_Stream r n) eqn: R'; auto.
          apply count_true_ge_1 in R'; rewrite Minus.minus_Sn_m; omega.
    Qed.

    (** State the correspondence for [mask]. *)
    Lemma mask_impl:
      forall k r xss,
        tr_Streams (List.map (Strs.mask k r) xss)
        ≈ Str.mask k (tr_Stream r) (tr_Streams xss).
    Proof.
      induction xss as [|xs];
        simpl; intros * n; unfold Str.mask in *.
      - destruct (k =? Str.count (tr_Stream r) n); auto.
      - rewrite tr_Stream_nth, mask_nth.
        rewrite IHxss.
        rewrite <-count_impl, Nat.eqb_sym.
        unfold tr_Stream; destruct (k =? Str_nth n (Strs.count r)); auto.
    Qed.


    (** * FINAL LEMMAS *)


    (** Correspondence for [clocks_of], used to give a base clock for node
        applications. *)
    Lemma tr_clocks_of:
      forall xss,
        CESem.clock_of (tr_Streams xss) ≈ tr_Stream (CoInd.clocks_of xss).
    Proof.
      unfold CESem.clock_of.
      intros xss n; revert dependent xss; induction n; intros.
      - rewrite unfold_Stream at 1; simpl; rewrite tr_Stream_0, tr_Streams_hd.
        induction xss; simpl; auto.
        f_equal; auto.
      - rewrite unfold_Stream at 1; simpl.
        rewrite tr_Stream_S, <-tr_Streams_tl; auto.
    Qed.
    Hint Resolve tr_clocks_of.

    (** Give an indexed specification for Streams synchronization. *)
    Lemma synchronized_index:
      forall xs bs,
        CoInd.synchronized xs bs ->
        forall n, tr_Stream bs n = true <-> tr_Stream xs n <> absent.
    Proof.
      intros * Sync n; revert dependent xs; revert bs; induction n; intros.
      - inversion_clear Sync; rewrite 2 tr_Stream_0; intuition; discriminate.
      - rewrite <-2 tr_Stream_tl; apply IHn.
        inv Sync; auto.
    Qed.

    Lemma sem_clocked_var_impl:
      forall H b x ck xs,
        CoInd.sem_var H x xs ->
        CoInd.sem_clocked_var H b x ck ->
        CESem.sem_clocked_var (tr_Stream b) (tr_History H) x ck.
    Proof.
      intros * Var (Sem & Sem').
      pose proof Var as Var'.
      apply Sem in Var as (bs & Clock & Sync); rename Var' into Var.
      apply sem_var_impl in Var;
        apply sem_clock_impl in Clock.
      pose proof (synchronized_index _ _ Sync) as Spec.
      intro n; specialize (Var n); specialize (Clock n).
      split; split.
      - intros * Clock'.
        eapply CESem.sem_clock_instant_det in Clock; eauto.
        symmetry in Clock; apply Spec, not_absent_present in Clock as (?& E).
        rewrite E in Var; eauto.
      - intros (?& Var').
        eapply CESem.sem_var_instant_det in Var; eauto.
        assert (tr_Stream bs n = true) as <-; auto.
        apply Spec; intro; congruence.
      - intros * Clock'.
        eapply CESem.sem_clock_instant_det in Clock; eauto.
        symmetry in Clock; rewrite <-Bool.not_true_iff_false, Spec in Clock.
        assert (tr_Stream xs n = absent) as <-; auto.
        apply Decidable.not_not in Clock; auto.
        apply decidable_eq_value.
      - intros Var'.
        eapply CESem.sem_var_instant_det in Var; eauto.
        assert (tr_Stream bs n = false) as <-; auto.
        rewrite <-Bool.not_true_iff_false, Spec; auto.
    Qed.

    Lemma sem_clocked_vars_impl:
      forall H b xcs xss,
        Forall2 (CoInd.sem_var H) (List.map fst xcs) xss ->
        CoInd.sem_clocked_vars H b xcs ->
        CESem.sem_clocked_vars (tr_Stream b) (tr_History H) xcs.
    Proof.
      intros * Vars Sem n.
      apply Forall_forall; intros (x, ck) Hin; simpl.
      pose proof Hin as Hin'.
      apply in_map with (f := fst) in Hin.
      eapply Forall2_in_left in Vars as (?&?&?); eauto.
      eapply sem_clocked_var_impl; eauto.
      eapply Forall_forall in Sem; eauto; auto.
    Qed.
    Hint Resolve sem_clocked_vars_impl.

    (** The final theorem stating the correspondence for nodes applications.
        We have to use a custom mutually recursive induction scheme [sem_node_mult]. *)
    Hint Constructors Indexed.sem_equation.
    Theorem implies:
      forall f xss oss,
        CoInd.sem_node G f xss oss ->
        Indexed.sem_node G f (tr_Streams xss) (tr_Streams oss).
    Proof.
      induction 1 as [| | | |???? IHNode|???????? Same Heqs IH]
                       using CoInd.sem_node_mult with
          (P_equation := fun H b e =>
                           CoInd.sem_equation G H b e ->
                           Indexed.sem_equation G (tr_Stream b) (tr_History H) e)
          (P_reset := fun f r xss oss =>
                        CoInd.sem_reset G f r xss oss ->
                        Indexed.sem_reset G f (tr_Stream r) (tr_Streams xss) (tr_Streams oss));
        eauto.

      - econstructor; eauto.
        intro; rewrite tr_clocks_of; auto.
        apply sem_clock_impl; auto.

      - econstructor; eauto.
        + intro; rewrite tr_clocks_of; auto.
          apply sem_clock_impl; auto.
        + apply reset_of_impl; auto.

      - econstructor; auto; subst; eauto.
        rewrite <-fby_impl; reflexivity.

      - constructor; intro k.
        specialize (IHNode k).
        now rewrite <- 2 mask_impl.

      - econstructor; eauto.
        + intro; rewrite tr_clocks_of; auto.
          eapply sem_clocked_vars_impl; auto.
          rewrite map_fst_idck; eauto.
        + apply Forall_forall; intros * Hin.
          rewrite tr_clocks_of.
          eapply Forall_forall in IH; eauto; eapply Forall_forall in Heqs; eauto.
    Qed.

  End Global.

End COINDTOINDEXED.
