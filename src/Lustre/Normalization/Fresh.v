From Coq Require Import List Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Classes.RelationClasses.

From Velus Require Import Common Ident.

(** * Fresh name generation *)

(** The fresh monad (with memory) : generates new names and keeps
    a record of each name generated along with some information *)
Definition fresh_st (B : Type) : Type := (ident * list (ident * B)).
Definition Fresh (A B : Type) : Type := fresh_st B -> A * fresh_st B.

(** Pure value *)
Definition ret {A B} (a : A) : Fresh A B := fun st => (a, st).

Section validity.
  Context {B : Type}.

  (** The state is valid if the next ident is greater than all generated idents,
    and if there is no duplicates in generated idents *)
  Definition fresh_st_valid (st : fresh_st B) : Prop :=
    let '(n, l) := st in
    Forall (fun '(x, _) => Pos.lt x n) l /\ NoDupMembers l.
End validity.

Section follows.
  Context {B : Type}.

  (** Smallest identifier defined in the state *)
  Definition smallest_ident (st : fresh_st B) : positive :=
    let (n, l) := st in
    fold_right Pos.min n (List.map fst l).

  (** The smallest ident of `st` is less or equal to the smallest
      ident of `st'` *)
  Definition fresh_st_follows (st st' : fresh_st B) :=
    incl (snd st) (snd st') /\
    Pos.le (smallest_ident st) (smallest_ident st').

  Global Instance st_follows_refl : Reflexive fresh_st_follows.
  Proof.
    intros st. unfold fresh_st_follows.
    split; reflexivity.
  Qed.

  Global Instance st_follows_trans : Transitive fresh_st_follows.
  Proof.
    unfold Transitive. intros.
    unfold fresh_st_follows in *.
    destruct H; destruct H0.
    split; etransitivity; eauto.
  Qed.
End follows.

Section fresh_ident.
  Context {B : Type}.

  (** The counter is incremented with each call to `fresh_name` *)
  Definition fresh_ident (b : B) : Fresh ident B :=
    fun '(n, l) => (n, (Pos.succ n, (cons (n, b) l))).

  Fact fresh_ident_st_valid :
    forall (b : B) res st st',
      fresh_ident b st = (res, st') ->
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
    forall (b : B) res st st',
      fresh_ident b st = (res, st') ->
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

  Fact fresh_ident_vars_perm : forall (b : B) id st st',
      fresh_ident b st = (id, st') ->
      Permutation (id::(map fst (snd st))) (map fst (snd st')).
  Proof.
    intros b id st st' Hfresh.
    destruct st; destruct st'; simpl in *.
    inv Hfresh. simpl. reflexivity.
  Qed.
End fresh_ident.

Section bind.
  Context {A A' B : Type}.

  Definition bind (x : Fresh A B) (k : A -> Fresh A' B) : Fresh A' B :=
    fun st => let '(a, st') := x st in k a st'.

  Lemma bind_inv : forall (x : Fresh A B) (k : A -> Fresh A' B) st a' st'',
      (bind x k) st = (a', st'') ->
      exists a, exists st', (x st = (a, st') /\ k a st' = (a', st'')).
  Proof.
    intros x k st a' st'' Hbind.
    unfold bind in Hbind.
    destruct (x st) as [a st']. exists a. exists st'.
    split; auto.
  Qed.
End bind.

Section bind2.
  Context {A1 A2 A' B : Type}.

  Definition bind2 (x: Fresh (A1 * A2) B) (k: A1 -> A2 -> Fresh A' B) : Fresh A' B :=
    fun n => let '((a1, a2), n') := x n in k a1 a2 n'.

  Lemma bind2_inv : forall (x : Fresh (A1 * A2) B) (k : A1 -> A2 -> Fresh A' B) st a' st'',
      (bind2 x k) st = (a', st'') ->
      exists a1, exists a2, exists st', (x st = ((a1, a2), st') /\ k a1 a2 st' = (a', st'')).
  Proof.
    intros x k st a' st'' Hbind.
    unfold bind2 in Hbind.
    destruct (x st) as [[a1 a2] st']. exists a1. exists a2. exists st'.
    split; auto.
  Qed.
End bind2.

Ltac inv_bind :=
  match goal with
  | H : ret _ _ = _ |- ?G =>
    unfold ret in H; inv H; simpl
  | H : bind _ _ _ = (_, _) |- _ =>
    apply bind_inv in H; destruct H as [? [? [? ?]]]; simpl
  | H : bind2 _ _ _ = (_, _) |- _ =>
    apply bind2_inv in H; destruct H as [? [? [? [? ?]]]]; simpl
  | |- ret _ _ = _ =>
    unfold ret; simpl
  | |- bind _ _ _ = (_, _) =>
    unfold bind; simpl
  | |- bind2 _ _ _ = (_, _, _) =>
    unfold bind2; simpl
  end.

(** [do] notation, inspired by CompCert's error monad *)
Notation "'do' X <- A ; B" :=
  (bind A (fun X => B))
    (at level 200, X ident, A at level 100, B at level 200): fresh_monad_scope.

Notation "'do' ( X , Y ) <- A ; B" :=
  (bind2 A (fun X Y => B))
    (at level 200, X ident, Y ident, A at level 100, B at level 200): fresh_monad_scope.

Section map_bind2.
  Context {A A1 A2 B : Type}.
  Variable k : A -> Fresh (A1 * A2) B.

  Open Scope list.
  Open Scope fresh_monad_scope.
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
    induction a; intros st a1s a2s st' Hfold; simpl in *.
    - inv Hfold. constructor.
    - repeat inv_bind.
      specialize (IHa _ _ _ _ H0).
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

Hint Resolve fresh_ident_st_follows.
Hint Resolve fresh_ident_st_valid.
Hint Resolve map_bind2_st_valid.
Hint Resolve map_bind2_st_follows.
