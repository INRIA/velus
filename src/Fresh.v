From Coq Require Import List Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Setoid Morphisms.

From Velus Require Import Common.
From Velus Require Import Environment.

(** * Fresh name generation *)

(** The fresh monad (with memory) : generates new names and keeps
    a record of each name generated along with some information

    The file is structured as such:

    - a signature FRESHKERNEL, which exposes the kernel features of the monad
    - a functor FreshKernel which implements the previous signature,
      and contains some gruesome definitions details that we prefer to hide
    - a functor Fresh that includes FreshKernel and also offers some additional lemmas.
      This module should be instanciated using an IDS module that contains, among other things,
      the gensym function used for name generation
 *)
Module Type FRESHKERNEL
       (Import Ids : IDS).

  (** The Monad manipulates a state, parameterized by a prefix with which to generate identifiers.
      The state exposes a list of the identifiers generated
      by the monad, paired with some data *)
  Section st.
    Parameter fresh_st : ident -> Type -> Type.
    Context {pref : ident} {B : Type}.
    Parameter st_anns : fresh_st pref B -> list (ident * B).
    Definition st_ids (st : fresh_st pref B) := map fst (st_anns st).
  End st.

  Global Hint Unfold st_ids : list.

  Definition Fresh pref (A B : Type) : Type := fresh_st pref B -> A * fresh_st pref B.

  (** By construction, the state only contains
      identifier prefixed by [prefix] and that are all distinct *)
  Section validity.
    Context {prefix : ident} {B : Type}.
    Conjecture st_valid_NoDup : forall (st : fresh_st prefix B),
        NoDup (st_ids st).
    Conjecture st_valid_prefixed : forall (st : fresh_st prefix B),
        Forall (fun x => exists n hint, x = gensym prefix hint n) (st_ids st).
  End validity.

  (** [st_follows] forms an inclusion relation over the contents of the states.
      We show below that every primimitive Fresh operation produces a new state
      that follows the previous one *)
  Section follows.
    Context {prefix : ident} {B : Type}.
    Parameter st_follows : fresh_st prefix B -> fresh_st prefix B -> Prop.
    Conjecture st_follows_refl : Reflexive st_follows.
    Conjecture st_follows_trans : Transitive st_follows.
    Conjecture st_follows_incl : forall st st',
        st_follows st st' ->
        incl (st_anns st) (st_anns st').
  End follows.

  (** The initial state is empty. *)
  Section init.
    Context {prefix : ident} {B : Type}.
    Parameter init_st : fresh_st prefix B.
    Conjecture init_st_anns : st_anns init_st = [].
  End init.

  (** The central function for fresh identifier generation,
      [fresh_ident prefix hint d] generates a new identifier prefixed by [prefix] and
      associated with data [d] in the new state.
      If a value is passed for [hint], it will show up in the generated identifier.
      [fresh_ident prefix d] preserves validity as long as [prefix] is the correct one *)
  Section fresh_ident.
    Context {prefix : ident} {B : Type}.
    Parameter fresh_ident : option ident -> B -> Fresh prefix ident B.

    Conjecture fresh_ident_anns : forall hint b id st st',
        fresh_ident hint b st = (id, st') ->
        st_anns st' = (id, b)::(st_anns st).

    Conjecture fresh_ident_st_follows : forall hint b id st st',
        fresh_ident hint b st = (id, st') ->
        st_follows st st'.

    Conjecture fresh_ident_prefixed : forall hint b id st st',
        fresh_ident hint b st = (id, st') ->
        exists n hint, id = gensym prefix hint n.
  End fresh_ident.

  Section ret.
    Context {pref : ident} {A B : Type}.
    Parameter ret : A -> Fresh pref A B.
    Conjecture ret_spec : forall a st,
        ret a st = (a, st).
  End ret.

  Section bind.
    Context {pref : ident} {A A' B : Type}.
    Parameter bind : Fresh pref A B -> (A -> Fresh pref A' B) -> Fresh pref A' B.
    Conjecture bind_spec : forall (x : Fresh pref A B) (k : A -> Fresh pref A' B) st a' st'',
        (bind x k) st = (a', st'') <->
        exists a, exists st', (x st = (a, st') /\ k a st' = (a', st'')).
  End bind.

  Section bind2.
    Context {pref : ident} {A1 A2 A' B : Type}.
    Parameter bind2 : Fresh pref (A1 * A2) B -> (A1 -> A2 -> Fresh pref A' B) -> Fresh pref A' B.
    Conjecture bind2_spec : forall (x : Fresh pref (A1 * A2) B) (k : A1 -> A2 -> Fresh pref A' B) st a' st'',
        (bind2 x k) st = (a', st'') <->
        exists a1, exists a2, exists st', (x st = ((a1, a2), st') /\ k a1 a2 st' = (a', st'')).
  End bind2.
End FRESHKERNEL.

Module FreshKernel(Import Ids : IDS) : FRESHKERNEL(Ids).
  Section st.
    Record fresh_st' (pref : ident) (B : Type) : Type :=
      { st_next : ident;
        st_anns : list (ident * B);
        (* There is no duplicates in generated idents *)
        st_nodup : NoDupMembers st_anns;
        (* The next ident is greater than all generated idents *)
        st_prefs : Forall (fun id => exists x hint, id = gensym pref hint x /\ Pos.lt x st_next) (map fst st_anns)
      }.
    Definition fresh_st pref B := fresh_st' pref B.
    Context {pref : ident} {B : Type}.
    Definition st_ids (st : fresh_st pref B) := map fst (st_anns _ _ st).
  End st.

  Arguments st_anns {_} {_}.

  Definition Fresh pref (A B : Type) : Type := fresh_st pref B -> A * fresh_st pref B.

  Section ret.
    Context {pref : ident} {A B : Type}.
    Definition ret (a : A) : Fresh pref A B := fun st => (a, st).

    Fact ret_spec : forall a st,
        ret a st = (a, st).
    Proof.
      intros a st. reflexivity.
    Qed.
  End ret.

  Section validity.
    Context {pref : ident} {B : Type}.

    Fact AtomOrGensym_gensym_injective : forall prefs pref hint x,
        AtomOrGensym prefs (gensym pref hint x) ->
        PS.In pref prefs.
    Proof.
      intros * [Hat|(?&?&?&?&Hgen)].
      - exfalso. eapply gensym_not_atom; eauto.
      - eapply gensym_injective in Hgen as (?&?); subst; auto.
    Qed.

    Fact st_valid_NoDup : forall (st: fresh_st pref B),
        NoDup (st_ids st).
    Proof.
      intros.
      apply fst_NoDupMembers, st_nodup.
    Qed.

    Fact st_valid_prefixed : forall (st: fresh_st pref B),
        Forall (fun x => exists n hint, x = gensym pref hint n) (st_ids st).
    Proof.
      intros. unfold st_ids.
      pose proof (st_prefs _ _ st) as Hprefs.
      simpl_Forall; subst; eauto.
    Qed.
  End validity.

  Section follows.
    Context {pref : ident} {B : Type}.

    Definition st_follows (st st' : fresh_st pref B) :=
      incl (st_anns st) (st_anns st').

    Fact st_follows_refl : Reflexive st_follows.
    Proof. intros st. unfold st_follows. reflexivity. Qed.

    Fact st_follows_trans : Transitive st_follows.
    Proof.
      unfold Transitive. intros.
      unfold st_follows in *.
      etransitivity; eauto.
    Qed.

    Fact st_follows_incl : forall st st',
        st_follows st st' ->
        incl (st_anns st) (st_anns st').
    Proof. intuition. Qed.
  End follows.

  Section init.
    Context {pref : ident} {B : Type}.

    Program Definition init_st : fresh_st pref B :=
      {| st_next := xH; st_anns := []; |}.
    Next Obligation. constructor. Qed.

    Fact init_st_anns : st_anns init_st = [].
    Proof. intros. reflexivity.
    Qed.
  End init.

  Section fresh_ident.
    Context {pref : ident} {B : Type}.

    Program Definition fresh_ident hint (b : B) : Fresh pref ident B :=
      fun st =>
        let id := gensym pref hint (st_next _ _ st) in
        (id, {| st_next := Pos.succ (st_next _ _ st);
                st_anns := (id, b)::st_anns st |}).
    Next Obligation.
      constructor. 2:apply st_nodup.
      pose proof (st_prefs _ _ st) as Hf.
      rewrite fst_InMembers. intros Hin. simpl_Forall.
      apply gensym_injective in H as (_&?); subst.
      eapply Pos.lt_irrefl; eauto.
    Qed.
    Next Obligation.
      pose proof (st_prefs _ _ st) as Hf.
      constructor; simpl_Forall; repeat esplit; eauto.
      - apply Pos.lt_succ_diag_r.
      - etransitivity; eauto. apply Pos.lt_succ_diag_r.
    Qed.

    Fact fresh_ident_anns : forall hint b id st st',
        fresh_ident hint b st = (id, st') ->
        st_anns st' = (id, b)::(st_anns st).
    Proof.
      intros.
      destruct st. inv H.
      reflexivity.
    Qed.

    Fact fresh_ident_st_follows :
      forall hint (b : B) id st st',
        fresh_ident hint b st = (id, st') ->
        st_follows st st'.
    Proof.
      intros ??? [] [] Hfresh.
      simpl in *; inv Hfresh; simpl.
      unfold st_follows in *; simpl in *.
      apply incl_tl. reflexivity.
    Qed.

    Fact fresh_ident_prefixed : forall hint b id st st',
        fresh_ident hint b st = (id, st') ->
        exists x hint, id = gensym pref hint x.
    Proof.
      intros ??? [] ? Hfresh. inv Hfresh; eauto.
    Qed.
  End fresh_ident.

  Section bind.
    Context {pref : ident} {A A' B : Type}.

    Definition bind (x : Fresh pref A B) (k : A -> Fresh pref A' B) : Fresh pref A' B :=
      fun st => let '(a, st') := x st in k a st'.

    Lemma bind_spec : forall (x : Fresh pref A B) (k : A -> Fresh pref A' B) st a' st'',
        (bind x k) st = (a', st'') <->
        exists a, exists st', (x st = (a, st') /\ k a st' = (a', st'')).
    Proof.
      intros x k st a' st''. split; intros.
      - unfold bind in H.
        destruct (x st) as [a st']. exists a. exists st'.
        split; auto.
      - destruct H as [a [st' [H1 H2]]]. unfold bind.
        rewrite H1. assumption.
    Qed.
  End bind.

  Section bind2.
    Context {pref : ident} {A1 A2 A' B : Type}.

    Definition bind2 (x: Fresh pref (A1 * A2) B) (k: A1 -> A2 -> Fresh pref A' B) : Fresh pref A' B :=
      fun n => let '((a1, a2), n') := x n in k a1 a2 n'.

    Lemma bind2_spec : forall (x : Fresh pref (A1 * A2) B) (k : A1 -> A2 -> Fresh pref A' B) st a' st'',
        (bind2 x k) st = (a', st'') <->
        exists a1, exists a2, exists st', (x st = ((a1, a2), st') /\ k a1 a2 st' = (a', st'')).
    Proof.
      intros x k st a' st''. split; intros.
      - unfold bind2 in H.
        destruct (x st) as [[a1 a2] st']. exists a1. exists a2. exists st'.
        split; auto.
      - destruct H as [a1 [a2 [st' [H1 H2]]]]. unfold bind2.
        rewrite H1. assumption.
    Qed.
  End bind2.
End FreshKernel.

Module Fresh(Ids : IDS).
  Module Ker := FreshKernel(Ids).
  Include Ker.

  Section Instances.
    Context {prefix : ident} {B : Type}.
    Global Instance st_follows_Reflexive : Reflexive (@st_follows prefix B) := st_follows_refl.
    Global Instance st_follows_Transitive : Transitive (@st_follows prefix B) := st_follows_trans.
  End Instances.

  Module Facts.

    Section st.
      Context {pref : ident} {B : Type}.

      Fact st_anns_ids_In : forall (st : fresh_st pref B) id,
          (exists b, In (id, b) (st_anns st)) <-> In id (st_ids st).
      Proof.
        intros.
        split; intros.
        - destruct H as [b H].
          unfold st_ids. rewrite in_map_iff.
          exists (id, b); auto.
        - unfold st_ids in H. rewrite in_map_iff in H.
          destruct H as [[? b] [? H]]; simpl in *; subst.
          exists b. assumption.
      Qed.
    End st.

    Fact contradict_AtomOrGensym : forall pref prefs hint n,
        ~PS.In pref prefs ->
        ~Ids.AtomOrGensym prefs (Ids.gensym pref hint n).
    Proof.
      intros * Hnin [Hat|(?&?&?&?&Hgen)].
      - eapply Ids.gensym_not_atom; eauto.
      - eapply Ids.gensym_injective in Hgen as (?&?); subst; eauto.
    Qed.

    Section st_valid.
      Context {pref : ident} {B : Type}.

      Fact st_valid_AtomOrGensym_nIn : forall prefs (st : fresh_st pref B) x,
          ~PS.In pref prefs ->
          Ids.AtomOrGensym prefs x ->
          ~In x (st_ids st).
      Proof.
        intros * Hnin Hat Hin.
        specialize (st_valid_prefixed st) as Hst. simpl_Forall; subst.
        eapply contradict_AtomOrGensym in Hat; eauto.
      Qed.
    End st_valid.

    Section fresh_ident.
      Context {pref : ident} {B : Type}.

      Fact fresh_ident_In : forall hint (b : B) id (st st': fresh_st pref B),
          fresh_ident hint b st = (id, st') ->
          In (id, b) (st_anns st').
      Proof.
        intros. apply fresh_ident_anns in H.
        rewrite H. constructor. reflexivity.
      Qed.

      Corollary fresh_ident_Inids : forall hint (b : B) id (st st': fresh_st pref B),
          fresh_ident hint b st = (id, st') ->
          In id (st_ids st').
      Proof.
        intros * Hfresh.
        apply fresh_ident_In in Hfresh.
        unfold st_ids. rewrite in_map_iff.
        exists (id, b); auto.
      Qed.

      Fact fresh_ident_vars_perm : forall hint (b : B) id (st st': fresh_st pref B),
          fresh_ident hint b st = (id, st') ->
          Permutation (id::(st_ids st)) (st_ids st').
      Proof.
        intros. apply fresh_ident_anns in H.
        unfold st_ids in *. rewrite H.
        reflexivity.
      Qed.

      Fact fresh_ident_nIn : forall hint (b : B) id (st st': fresh_st pref B),
          fresh_ident hint b st = (id, st') ->
          ~List.In id (st_ids st).
      Proof.
        intros * Hfresh.
        specialize (st_valid_NoDup st') as Hvalid.
        apply fresh_ident_vars_perm in Hfresh.
        unfold st_ids in *.
        rewrite <- Hfresh in Hvalid. inv Hvalid.
        assumption.
      Qed.

      Fact fresh_ident_nIn' : forall prefs hint (b : B) id (st st': fresh_st pref B) aft,
          ~PS.In pref prefs ->
          Forall (Ids.AtomOrGensym prefs) aft ->
          fresh_ident hint b st = (id, st') ->
          ~In id aft.
      Proof.
        intros * Hnin Hat Hfresh Hin.
        simpl_Forall.
        eapply st_valid_AtomOrGensym_nIn; eauto using fresh_ident_Inids.
      Qed.

    End fresh_ident.
  End Facts.

  Module Tactics.
    Ltac inv_bind :=
      simpl in *;
      match goal with
      | H : context c [ret _ _] |- _ =>
        rewrite ret_spec in H
      | H : (_, _) = (_, _) |- _ =>
        inv H
      | H : bind _ _ _ = (_, _) |- _ =>
        apply bind_spec in H; destruct H as [? [? [? ?]]]; simpl in *
      | H : bind2 _ _ _ = (_, _) |- _ =>
        apply bind2_spec in H; destruct H as [? [? [? [? ?]]]]; simpl in *
      | |- context c [ret _ _] =>
        rewrite ret_spec
      | |- bind _ _ _ = (_, _) =>
        rewrite bind_spec; repeat esplit
      | |- bind2 _ _ _ = (_, _) =>
        rewrite bind2_spec; repeat esplit
      end.
  End Tactics.

  Module Notations.
    Declare Scope fresh_monad_scope.

    (** [do] notation, inspired by CompCert's error monad *)
    Notation "'do' X <- A ; B" :=
      (bind A (fun X => B))
        (at level 200, X name, A at level 100, B at level 200): fresh_monad_scope.

    Notation "'do' ( X , Y ) <- A ; B" :=
      (bind2 A (fun X Y => B))
        (at level 200, X name, Y name, A at level 100, B at level 200): fresh_monad_scope.
  End Notations.

  Section mmap.
    Import Tactics Notations.
    Open Scope fresh_monad_scope.
    Context {pref: ident} {A A1 B : Type}.
    Variable k : A -> Fresh pref A1 B.

    Fixpoint mmap a :=
      match a with
      | nil => ret nil
      | hd::tl => do a1 <- k hd;
                do a1s <- mmap tl;
                ret (a1::a1s)
      end.

    Fact mmap_values : forall a st a1s st',
        mmap a st = (a1s, st') ->
        Forall2 (fun a a1 => exists st'', exists st''', k a st'' = (a1, st''')) a a1s.
    Proof.
      induction a; intros st a1s st' Hfold; simpl in *; repeat inv_bind.
      - constructor.
      - specialize (IHa _ _ _ H0).
        constructor; eauto.
    Qed.

    Fact mmap_st_follows : forall a a1s st st',
        mmap a st = (a1s, st') ->
        Forall (fun a => forall a1 st st', k a st = (a1, st') -> st_follows st st') a ->
        st_follows st st'.
    Proof.
      induction a; intros * Hmap Hforall;
        simpl in *; repeat inv_bind; auto.
      - reflexivity.
      - inv Hforall.
        etransitivity; eauto.
    Qed.

    Fact mmap_length : forall a1s a2s st st',
        mmap a1s st = (a2s, st') ->
        length a2s = length a1s.
    Proof.
      induction a1s; intros * Hmap; repeat inv_bind; simpl in *; auto.
      f_equal; eauto.
    Qed.

    Fact mmap_values_follows : forall a st a1s st',
        (forall a a1 st st', k a st = (a1, st') -> st_follows st st') ->
        mmap a st = (a1s, st') ->
        Forall2 (fun a a1 =>
                   exists st'' st''',
                     st_follows st st''
                     /\ k a st'' = (a1, st''')) a a1s.
    Proof.
      induction a; intros * Hfollows Hfold; simpl in *; repeat inv_bind.
      - constructor.
      - constructor.
        + repeat esplit; [|eauto]. reflexivity.
        + eapply IHa in H0; eauto.
          simpl_Forall. repeat esplit; [|eauto]. etransitivity; eauto.
    Qed.

  End mmap.

  Section mmap2.
    Import Tactics Notations.
    Open Scope fresh_monad_scope.
    Context {pref : ident} {A A1 A2 B : Type}.
    Variable k : A -> Fresh pref (A1 * A2) B.

    Fixpoint mmap2 a :=
      match a with
      | nil => ret (nil, nil)
      | hd::tl => do (a1, a2) <- k hd;
                do (a1s, a2s) <- mmap2 tl;
                ret (a1::a1s, a2::a2s)
      end.

    Fact mmap2_values : forall a st a1s a2s st',
        mmap2 a st = (a1s, a2s, st') ->
        Forall3 (fun a a1 a2 => exists st'', exists st''', k a st'' = (a1, a2, st''')) a a1s a2s.
    Proof.
      induction a; intros st a1s a2s st' Hfold; simpl in *; repeat inv_bind.
      - constructor.
      - specialize (IHa _ _ _ _ H0).
        constructor; eauto.
    Qed.

    Fact mmap2_values_follows : forall a st a1s a2s st',
        (forall a a1 a2 st st', k a st = (a1, a2, st') -> st_follows st st') ->
        mmap2 a st = (a1s, a2s, st') ->
        Forall3 (fun a a1 a2 =>
                   exists st'' st''',
                     st_follows st st''
                     /\ k a st'' = (a1, a2, st''')) a a1s a2s.
    Proof.
      induction a; intros * Hfollows Hfold; simpl in *; repeat inv_bind.
      - constructor.
      - constructor.
        + repeat esplit; [|eauto]. reflexivity.
        + eapply IHa in H0; eauto.
          eapply Forall3_impl_In; [|eauto]; intros; destruct_conjs.
          do 3 esplit; [|eauto]. etransitivity; eauto.
    Qed.

    Fact mmap2_st_follows : forall a a1s a2s st st',
        mmap2 a st = (a1s, a2s, st') ->
        Forall (fun a => forall a1 a2 st st', k a st = (a1, a2, st') -> st_follows st st') a ->
        st_follows st st'.
    Proof.
      induction a; intros a1s a2s st st' Hmap Hforall;
        simpl in *; repeat inv_bind; auto.
      - reflexivity.
      - inv Hforall.
        etransitivity; eauto.
    Qed.

    Fact mmap2_length_1 : forall a st a1s a2s st',
        mmap2 a st = (a1s, a2s, st') ->
        length a1s = length a.
    Proof.
      induction a; intros * Map; simpl in Map;
        repeat inv_bind; simpl; f_equal; eauto.
    Qed.
  End mmap2.

  Global Hint Resolve fresh_ident_st_follows : fresh.
  Global Hint Resolve st_follows_incl : fresh.
  Global Hint Resolve mmap2_st_follows : fresh.
End Fresh.
