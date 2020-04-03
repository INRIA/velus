From Coq Require Import List Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Classes.RelationClasses.

From Velus Require Import Common Ident.

(** * Fresh name generation *)

(** The fresh monad (with memory) : generates new names and keeps
    a record of each name generated along with some information *)
Module Type FRESH.

  Section st.
    Parameter fresh_st : Type -> Type.
    Context {B : Type}.
    Parameter st_anns : fresh_st B -> list (ident * B).
    Definition st_ids (st : fresh_st B) := map fst (st_anns st).
  End st.

  Definition Fresh (A B : Type) : Type := fresh_st B -> A * fresh_st B.

  Section ret.
    Context {A B : Type}.
    Parameter ret : A -> Fresh A B.
    Axiom ret_spec : forall a st,
        ret a st = (a, st).
  End ret.

  Section validity.
    Context {B : Type}.
    Parameter fresh_st_valid : fresh_st B -> Prop.
    Axiom st_valid_NoDupMembers : forall st,
        fresh_st_valid st ->
        NoDupMembers (st_anns st).
  End validity.

  Section follows.
    Context {B : Type}.
    Parameter smallest_ident : fresh_st B -> ident.
    Axiom smallest_ident_In : forall st x,
        In x (st_ids st) ->
        Pos.le (smallest_ident st) x.
    Parameter fresh_st_follows : fresh_st B -> fresh_st B -> Prop.
    Axiom st_follows_refl : Reflexive fresh_st_follows.
    Axiom st_follows_trans : Transitive fresh_st_follows.
    Axiom st_follows_smallest : forall st st',
        fresh_st_follows st st' ->
        Pos.le (smallest_ident st) (smallest_ident st').
    Axiom st_follows_incl : forall st st',
        fresh_st_follows st st' ->
        incl (st_anns st) (st_anns st').
  End follows.

  Section init.
    Context {B : Type}.
    Parameter init_st : ident -> fresh_st B.
    Axiom init_st_anns : forall id, st_anns (init_st id) = [].
    Axiom init_st_valid : forall id, fresh_st_valid (init_st id).
    Axiom init_st_follows : forall id st',
        fresh_st_follows (init_st id) st' ->
        Forall (fun id' => Pos.le id id') (st_ids st').
    Axiom init_st_smallest : forall id,
        smallest_ident (init_st id) = id.
  End init.

  Section fresh_ident.
    Context {B : Type}.
    Parameter fresh_ident : B -> Fresh ident B.

    Axiom fresh_ident_anns : forall b id st st',
        fresh_ident b st = (id, st') ->
        st_anns st' = (id, b)::(st_anns st).

    Axiom fresh_ident_st_valid : forall b id st st',
        fresh_ident b st = (id, st') ->
        fresh_st_valid st ->
        fresh_st_valid st'.
    Axiom fresh_ident_st_follows : forall b id st st',
        fresh_ident b st = (id, st') ->
        fresh_st_follows st st'.
    End fresh_ident.

  Section bind.
    Context {A A' B : Type}.
    Parameter bind : Fresh A B -> (A -> Fresh A' B) -> Fresh A' B.
    Axiom bind_spec : forall (x : Fresh A B) (k : A -> Fresh A' B) st a' st'',
        (bind x k) st = (a', st'') <->
        exists a, exists st', (x st = (a, st') /\ k a st' = (a', st'')).
  End bind.

  Section bind2.
    Context {A1 A2 A' B : Type}.
    Parameter bind2 : Fresh (A1 * A2) B -> (A1 -> A2 -> Fresh A' B) -> Fresh A' B.
    Axiom bind2_spec : forall (x : Fresh (A1 * A2) B) (k : A1 -> A2 -> Fresh A' B) st a' st'',
        (bind2 x k) st = (a', st'') <->
        exists a1, exists a2, exists st', (x st = ((a1, a2), st') /\ k a1 a2 st' = (a', st'')).
  End bind2.
End FRESH.

Module Fresh : FRESH.
  Section st.
    Definition fresh_st (B : Type) : Type := (ident * list (ident * B)).
    Context {B : Type}.
    Definition st_anns (st : fresh_st B) := snd st.
    Definition st_ids (st : fresh_st B) := map fst (st_anns st).
  End st.

  Definition Fresh (A B : Type) : Type := fresh_st B -> A * fresh_st B.

  Section ret.
    Context {A B : Type}.
    Definition ret (a : A) : Fresh A B := fun st => (a, st).

    Fact ret_spec : forall a st,
        ret a st = (a, st).
    Proof.
      intros a st. reflexivity.
    Qed.
  End ret.

  Section validity.
    Context {B : Type}.
    (** The state is valid if the next ident is greater than all generated idents,
        and if there is no duplicates in generated idents *)
    Definition fresh_st_valid (st : fresh_st B) : Prop :=
      let '(n, l) := st in
      Forall (fun '(x, _) => Pos.lt x n) l /\ NoDupMembers l.

    Fact st_valid_NoDupMembers : forall st,
        fresh_st_valid st ->
        NoDupMembers (st_anns st).
    Proof.
      intros st Hfresh.
      destruct st; simpl in *.
      destruct Hfresh. assumption.
    Qed.
  End validity.

  Section follows.
    Context {B : Type}.
    (** Smallest identifier defined in the state *)
    Definition smallest_ident (st : fresh_st B) : positive :=
      let (n, l) := st in
      fold_right Pos.min n (List.map fst l).

    Fact smallest_ident_In : forall st x,
        In x (st_ids st) ->
        Pos.le (smallest_ident st) x.
    Proof.
      intros [n l] x Hin; simpl in *.
      unfold st_ids in Hin; simpl in Hin.
      eapply min_fold_in in Hin. eauto.
    Qed.

    (** The smallest ident of `st` is less or equal to the smallest
      ident of `st'` *)
    Definition fresh_st_follows (st st' : fresh_st B) :=
      incl (snd st) (snd st') /\
      Pos.le (smallest_ident st) (smallest_ident st').

    Fact st_follows_refl : Reflexive fresh_st_follows.
    Proof.
      intros st. unfold fresh_st_follows.
      split; reflexivity.
    Qed.

    Fact st_follows_trans : Transitive fresh_st_follows.
    Proof.
      unfold Transitive. intros.
      unfold fresh_st_follows in *.
      destruct H; destruct H0.
      split; etransitivity; eauto.
    Qed.

    Fact st_follows_smallest : forall st st',
        fresh_st_follows st st' ->
        Pos.le (smallest_ident st) (smallest_ident st').
    Proof.
      intros st st' Hfollows.
      destruct Hfollows. assumption.
    Qed.

    Fact st_follows_incl : forall st st',
        fresh_st_follows st st' ->
        incl (st_anns st) (st_anns st').
    Proof.
      intros st st' Hfollows.
      destruct Hfollows. assumption.
    Qed.
  End follows.

  Section init.
    Context {B : Type}.

    Definition init_st ident : fresh_st B := (ident, []).

    Fact init_st_anns : forall id, st_anns (init_st id) = [].
    Proof. intros. reflexivity.
    Qed.

    Fact init_st_valid : forall id, fresh_st_valid (init_st id).
    Proof. intros id. unfold init_st. repeat constructor.
    Qed.

    Fact init_st_follows : forall id st',
        fresh_st_follows (init_st id) st' ->
        Forall (fun id' => Pos.le id id') (st_ids st').
    Proof.
      intros id st' Hfollows.
      unfold init_st in Hfollows.
      destruct Hfollows as [_ Hle]. destruct st'. simpl in *.
      rewrite Forall_forall. intros x HIn. unfold st_ids in HIn. simpl in HIn.
      eapply min_fold_in in HIn.
      etransitivity; eauto.
    Qed.

    Fact init_st_smallest : forall id,
        smallest_ident (init_st id) = id.
    Proof.
      intros id. reflexivity.
    Qed.
  End init.

  Section fresh_ident.
    Context {B : Type}.

    Definition fresh_ident (b : B) : Fresh ident B :=
      fun '(n, l) => (n, (Pos.succ n, (cons (n, b) l))).

    Fact fresh_ident_anns : forall b id st st',
        fresh_ident b st = (id, st') ->
        st_anns st' = (id, b)::(st_anns st).
    Proof.
      intros.
      destruct st. inv H.
      reflexivity.
    Qed.

    Fact fresh_ident_st_valid :
      forall (b : B) id st st',
        fresh_ident b st = (id, st') ->
        fresh_st_valid st ->
        fresh_st_valid st'.
    Proof.
      intros b res st st' Hfresh Hvalid.
      destruct st as [n l]; destruct st' as [n' l'].
      simpl in Hfresh; inv Hfresh.
      destruct Hvalid.
      repeat constructor; auto.
      + apply Positive_as_DT.lt_succ_diag_r.
      + eapply Forall_impl; eauto.
        intros [x _] Hlt'.
        apply Positive_as_OT.lt_lt_succ; auto.
      + intro contra.
        induction l; inv H; simpl in *; auto.
        destruct a as [x ann].
        destruct contra; subst; inv H0; auto.
        apply Pos.lt_irrefl in H3; auto.
    Qed.

    Fact fresh_ident_st_follows :
      forall (b : B) id st st',
        fresh_ident b st = (id, st') ->
        fresh_st_follows st st'.
    Proof.
      intros b res st st' Hfresh.
      destruct st as [n l]; destruct st' as [n' l'].
      simpl in *; inv Hfresh; simpl.
      unfold fresh_st_follows, smallest_ident in *; simpl in *.
      split.
      - apply incl_tl. reflexivity.
      - induction l as [|[a ?]]; simpl in *.
        + rewrite Pos.min_glb_iff.
          split.
          * reflexivity.
          * apply Pos.lt_le_incl.
            apply Pos.lt_succ_diag_r.
        + rewrite Pos.min_glb_iff in *.
          destruct IHl as [IHl1 IHl2].
          split.
          * etransitivity; eauto.
            eapply Pos.le_min_r.
          * eapply Pos.min_le_compat_l; eauto.
    Qed.
  End fresh_ident.

  Section bind.
    Context {A A' B : Type}.

    Definition bind (x : Fresh A B) (k : A -> Fresh A' B) : Fresh A' B :=
      fun st => let '(a, st') := x st in k a st'.

    Lemma bind_spec : forall (x : Fresh A B) (k : A -> Fresh A' B) st a' st'',
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
    Context {A1 A2 A' B : Type}.

    Definition bind2 (x: Fresh (A1 * A2) B) (k: A1 -> A2 -> Fresh A' B) : Fresh A' B :=
      fun n => let '((a1, a2), n') := x n in k a1 a2 n'.

    Lemma bind2_spec : forall (x : Fresh (A1 * A2) B) (k : A1 -> A2 -> Fresh A' B) st a' st'',
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
End Fresh.

Section Instances.
  Context {B : Type}.
  Global Instance st_follows_refl : Reflexive (@Fresh.fresh_st_follows B) := Fresh.st_follows_refl.
  Global Instance st_follows_trans : Transitive (@Fresh.fresh_st_follows B) := Fresh.st_follows_trans.
End Instances.

Module Facts.
  Import Fresh.

  Section st.
    Context {B : Type}.

    Fact st_anns_ids_In : forall (st : fresh_st B) id,
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

  Section fresh_ident.
    Context {B : Type}.

    Fact fresh_ident_In : forall (b : B) id st st',
        fresh_ident b st = (id, st') ->
        In (id, b) (st_anns st').
    Proof.
      intros. apply fresh_ident_anns in H.
      rewrite H. constructor. reflexivity.
    Qed.

    Fact fresh_ident_vars_perm : forall (b : B) id st st',
        fresh_ident b st = (id, st') ->
        Permutation (id::(st_ids st)) (st_ids st').
    Proof.
      intros. apply fresh_ident_anns in H.
      unfold st_ids in *. rewrite H.
      reflexivity.
    Qed.
  End fresh_ident.
End Facts.

Module Tactics.
  Import Fresh.
  Ltac inv_bind :=
    match goal with
    | H : context c [ret _ _] |- _ =>
      rewrite ret_spec in H
    | H : (_, _) = (_, _) |- _ =>
      inv H
    | H : bind _ _ _ = (_, _) |- _ =>
      apply bind_spec in H; destruct H as [? [? [? ?]]]; simpl
    | H : bind2 _ _ _ = (_, _) |- _ =>
      apply bind2_spec in H; destruct H as [? [? [? [? ?]]]]; simpl
    | |- context c [ret _ _] =>
      rewrite ret_spec
    | |- bind _ _ _ = (_, _) =>
      rewrite bind_spec
    | |- bind2 _ _ _ = (_, _) =>
      rewrite bind2_spec
    end.
End Tactics.

Module Notations.
  Import Fresh.
  (** [do] notation, inspired by CompCert's error monad *)
  Notation "'do' X <- A ; B" :=
    (bind A (fun X => B))
      (at level 200, X ident, A at level 100, B at level 200): fresh_monad_scope.

  Notation "'do' ( X , Y ) <- A ; B" :=
    (bind2 A (fun X Y => B))
      (at level 200, X ident, Y ident, A at level 100, B at level 200): fresh_monad_scope.
End Notations.

Section map_bind2.
  Import Fresh Tactics Notations.
  Open Scope fresh_monad_scope.
  Context {A A1 A2 B : Type}.
  Variable k : A -> Fresh (A1 * A2) B.

  Fixpoint map_bind2 a :=
    match a with
    | nil => ret (nil, nil)
    | hd::tl => do (a1, a2) <- k hd;
              do (a1s, a2s) <- map_bind2 tl;
              ret (a1::a1s, a2::a2s)
    end.

  Fact map_bind2_values : forall a st a1s a2s st',
      map_bind2 a st = (a1s, a2s, st') ->
      Forall3 (fun a a1 a2 => exists st'', exists st''', k a st'' = (a1, a2, st''')) a a1s a2s.
  Proof.
    induction a; intros st a1s a2s st' Hfold; simpl in *; repeat inv_bind.
    - constructor.
    - specialize (IHa _ _ _ _ H0).
      constructor; eauto.
  Qed.

  Fact map_bind2_st_valid : forall a a1s a2s st st',
      map_bind2 a st = (a1s, a2s, st') ->
      Forall (fun a => forall a1 a2 st st', k a st = (a1, a2, st') -> fresh_st_valid st -> fresh_st_valid st') a ->
      fresh_st_valid st ->
      fresh_st_valid st'.
  Proof.
    induction a; intros a1s a2s st st' Hmap Hforall Hvalid;
      simpl in *; repeat inv_bind; auto.
    inv Hforall. eapply IHa; eauto.
  Qed.

  Fact map_bind2_st_follows : forall a a1s a2s st st',
      map_bind2 a st = (a1s, a2s, st') ->
      Forall (fun a => forall a1 a2 st st', k a st = (a1, a2, st') -> fresh_st_follows st st') a ->
      fresh_st_follows st st'.
  Proof.
    induction a; intros a1s a2s st st' Hmap Hforall;
      simpl in *; repeat inv_bind; auto.
    - reflexivity.
    - inv Hforall.
      etransitivity; eauto.
  Qed.
End map_bind2.

Hint Resolve Fresh.st_follows_smallest.
Hint Resolve Fresh.fresh_ident_st_follows.
Hint Resolve Fresh.fresh_ident_st_valid.
Hint Resolve map_bind2_st_valid.
Hint Resolve map_bind2_st_follows.
