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
    Proof. auto with *. Qed.
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

    Fact mlength_map : forall a1s a2s st st',
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

  Import Tactics Notations.
  Open Scope fresh_monad_scope.

  Section mmap2.
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

  (** Generate a bunch of fresh identifiers *)
  Section fresh_idents.
    Context {pref : ident} {B : Type}.

    Definition fresh_idents (xs : list (ident * B)) : Fresh pref _ B :=
      mmap (fun '(x, ann) => do lx <- fresh_ident (Some x) ann;
                          ret (x, lx, ann)) xs.

    Lemma fresh_idents_In : forall xs xs' st st',
        fresh_idents xs st = (xs', st') ->
        forall x ann, In (x, ann) xs ->
                 exists lx, In (x, lx, ann) xs'.
    Proof.
      intros * Hfresh * Hin.
      apply mmap_values, Forall2_ignore2 in Hfresh. simpl_Forall.
      repeat inv_bind. eauto.
    Qed.

    Lemma fresh_idents_In' : forall xs xs' st st',
        fresh_idents xs st = (xs', st') ->
        forall x lx ann, In (x, lx, ann) xs' ->
                    In (x, ann) xs.
    Proof.
      intros * Hfresh * Hin.
      apply mmap_values, Forall2_ignore1 in Hfresh. simpl_Forall.
      repeat inv_bind. eauto.
    Qed.

    Lemma fresh_idents_fst : forall xs xs' st st',
        fresh_idents xs st = (xs', st') ->
        map fst (map fst xs') = map fst xs.
    Proof.
      intros * Hfresh. apply mmap_values in Hfresh.
      induction Hfresh; destruct_conjs; repeat inv_bind; auto.
    Qed.

    Corollary fresh_idents_InMembers : forall xs xs' st st',
        fresh_idents xs st = (xs', st') ->
        forall x, InMembers x xs <-> InMembers x (map fst xs').
    Proof.
      intros * Hfresh ?.
      erewrite ? fst_InMembers, fresh_idents_fst; eauto. reflexivity.
    Qed.

    Corollary fresh_idents_NoDupMembers : forall xs xs' st st',
        NoDupMembers xs ->
        fresh_idents xs st = (xs', st') ->
        NoDupMembers (map fst xs').
    Proof.
      intros * Hnd Hfresh.
      rewrite fst_NoDupMembers in Hnd.
      erewrite fst_NoDupMembers, fresh_idents_fst; eauto.
    Qed.

    Import Permutation.

    Lemma fresh_idents_Perm : forall xs xs' sub st st',
        NoDupMembers xs ->
        fresh_idents xs st = (xs', st') ->
        Permutation (map (fun '((_, lx), _) => lx) xs')
          (map (fun x => or_default x (Env.find x (Env.adds' (map fst xs') sub))) (map fst xs)).
    Proof.
      induction xs as [|(?&?)]; intros * Nd Fr; inv Nd; repeat inv_bind; auto.
      simpl.
      rewrite IHxs; eauto.
      setoid_rewrite Env.find_gsss'; simpl.
      2:{ intros InM. eapply fresh_idents_InMembers in InM; eauto. }
      constructor; auto.
    Qed.

    Lemma fresh_idents_st_follows : forall xs xs' st st',
        fresh_idents xs st = (xs', st') ->
        st_follows st st'.
    Proof.
      intros * Hfresh.
      eapply mmap_st_follows in Hfresh; eauto.
      simpl_Forall. repeat inv_bind. eauto with fresh.
    Qed.

    Fact fresh_idents_prefixed : forall xs xs' st st',
        fresh_idents xs st = (xs', st') ->
        Forall (fun '(_, lx, _) => exists n hint, lx = Ids.gensym pref hint n) xs'.
    Proof.
      intros * Hfresh.
      eapply mmap_values, Forall2_ignore1 in Hfresh. simpl_Forall. repeat inv_bind.
      eapply fresh_ident_prefixed in H1; auto.
    Qed.

    Fact fresh_idents_In_ids : forall xs xs' st st',
        fresh_idents xs st = (xs', st') ->
        Forall (fun '(_, lx, _) => In lx (st_ids st')) xs'.
    Proof.
      unfold fresh_idents.
      induction xs; intros; destruct_conjs; repeat inv_bind; constructor; eauto.
      apply Facts.fresh_ident_Inids in H. eapply incl_map; [|eauto].
      eapply st_follows_incl, mmap_st_follows; eauto.
      simpl_Forall. repeat inv_bind; eauto with fresh.
    Qed.

    Fact fresh_idents_nIn_ids : forall xs xs' st st',
        fresh_idents xs st = (xs', st') ->
        Forall (fun '(_, lx, _) => ~In lx (st_ids st)) xs'.
    Proof.
      unfold fresh_idents.
      induction xs; intros; destruct_conjs; repeat inv_bind; constructor; eauto.
      - eapply Facts.fresh_ident_nIn in H; eauto.
      - eapply IHxs in H0.
        simpl_Forall. contradict H0.
        eapply incl_map; eauto.
        apply st_follows_incl; eauto with fresh.
    Qed.

    Lemma fresh_idents_anns : forall xs xs' st st',
        fresh_idents xs st = (xs', st') ->
        Permutation (st_anns st') (map (fun '(_, lx, ann) => (lx, ann)) xs'++st_anns st).
    Proof.
      induction xs as [|(?&?)]; intros * Fr; repeat inv_bind; simpl; auto.
      erewrite IHxs; eauto.
      erewrite fresh_ident_anns; eauto with datatypes.
      now rewrite Permutation_middle.
    Qed.

    Corollary fresh_idents_In_anns : forall xs xs' st st',
        fresh_idents xs st = (xs', st') ->
        Forall (fun '(_, lx, ann) => In (lx, ann) (st_anns st')) xs'.
    Proof.
      intros * Fr.
      simpl_Forall. erewrite fresh_idents_anns; eauto.
      apply in_app_iff. left. solve_In.
    Qed.

  End fresh_idents.
End Fresh.
