(** * Fresh name generation *)

From Velus Require Import Common.
From Velus Require Import Lustre.LSyntax.

(** The fresh monad (with memory) : generates new names and keeps
    a record of each name generated along with some information *)
Definition fresh_st (B : Type) : Type := (ident * list (ident * B)).
Definition Fresh (A B : Type) : Type := fresh_st B -> A * fresh_st B.

(** Pure value *)
Definition ret {A B} (a : A) : Fresh A B := fun st => (a, st).

(** The counter is incremented with each call to `fresh_name` *)
Definition fresh_ident {B} (b : B) : Fresh ident B :=
  fun '(n, l) => (n, (Pos.succ n, (cons (n, b) l))).

Section bind.
  Context {A A' B : Type}.

  Definition bind (x : Fresh A B) (k : A -> Fresh A' B) : Fresh A' B :=
    fun st => let '(a, st') := x st in k a st'.

  Fact bind_inv : forall (x : Fresh A B) (k : A -> Fresh A' B) st a' st'',
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

  Fact bind2_inv : forall (x : Fresh (A1 * A2) B) (k : A1 -> A2 -> Fresh A' B) st a' st'',
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
  | H : ret ?x ?st = ?v |- ?G =>
    unfold ret in H; inv H; simpl
  | H : (bind ?x ?k) ?st = (?a, ?st') |- ?G =>
    apply bind_inv in H; destruct H as [? [? [? ?]]]; simpl
  | H : (bind2 ?x ?k) ?st = (?a, ?st') |- ?G =>
    apply bind2_inv in H; destruct H as [? [? [? [? ?]]]]; simpl
  | _ => fail
  end.

(** [do] notation, inspired by CompCert's error monad *)
Notation "'do' X <- A ; B" :=
  (bind A (fun X => B))
    (at level 200, X ident, A at level 100, B at level 200): fresh_monad_scope.

Notation "'do' ( X , Y ) <- A ; B" :=
  (bind2 A (fun X Y => B))
    (at level 200, X ident, Y ident, A at level 100, B at level 200): fresh_monad_scope.

From Coq Require Import List.

Section Fb2.
  Context {A A1 A2 B : Type}.
  Variable k : A -> Fresh (A1 * A2) B.

  Open Scope list.
  Open Scope fresh_monad_scope.
  Fixpoint fold_bind2 a :=
    match a with
    | nil => ret (nil, nil)
    | hd::tl => do (a1, a2) <- k hd;
                do (a1s, a2s) <- fold_bind2 tl;
                ret (a1::a1s, a2::a2s)
    end.

  Fact fold_bind2_values : forall a st a1s a2s st',
      fold_bind2 a st = (a1s, a2s, st') ->
      Forall3 (fun a a1 a2 => exists st'', exists st''', k a st'' = (a1, a2, st''')) a a1s a2s.
  Proof.
    induction a; intros st a1s a2s st' Hfold; simpl in *.
    - inv Hfold. constructor.
    - repeat inv_bind.
      specialize (IHa _ _ _ _ H0).
      constructor; eauto.
  Qed.
End Fb2.
