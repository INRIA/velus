
From Velus Require Import Common.

From compcert Require Import lib.Coqlib.
From compcert Require Import cfrontend.Clight.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From compcert Require Import common.Errors.
From Coq Require Import Classes.RelationClasses.

Open Scope error_monad_scope.

(* Extensions to CompCert libraries. *)

(** Conversions. *)

Lemma NoDup_norepet:
  forall {A} (l: list A),
    NoDup l <-> list_norepet l.
Proof.
  induction l; split; constructor.
  - now inversion H.
  - apply IHl; now inversion H.
  - now inversion H.
  - apply IHl; now inversion H.
Qed.

Lemma NoDupMembers_disjoint:
  forall l1 l2,
    NoDupMembers (l1 ++ l2) ->
    list_disjoint (var_names l1) (var_names l2).
Proof.
  unfold list_disjoint, var_names.
  intros l1 l2 H x y Hx Hy.
  apply in_map_iff in Hx; destruct Hx as ((x', tx) & Ex & Hx);
    apply in_map_iff in Hy; destruct Hy as ((y', ty) & Ey & Hy);
      simpl in *; subst.
  intro E; subst.
  apply in_split in Hx; destruct Hx as (lx & lx' & Hx);
    apply in_split in Hy; destruct Hy as (ly & ly' & Hy);
      subst.
  rewrite <-app_assoc in H.
  apply NoDupMembers_app_r in H.
  rewrite <-app_comm_cons, nodupmembers_cons in H.
  destruct H as [Notin]; apply Notin.
  apply InMembers_app; right; apply InMembers_app; right; apply inmembers_eq.
Qed.

Lemma list_drop_skipn:
  forall {A} (xs: list A) n,
    Coqlib.list_drop n xs = skipn n xs.
Proof.
  induction xs, n; simpl; auto.
Qed.

Lemma list_forall2_Forall2:
  forall {A B} P (xs: list A) (ys: list B),
    Coqlib.list_forall2 P xs ys <-> Forall2 P xs ys.
Proof.
  induction xs as [|x xs IH].
  now split; inversion 1; auto using Coqlib.list_forall2_nil.
  split; intro HH; inversion_clear HH; constructor; auto; apply IH; auto.
Qed.

(** The error monad. *)

Section Mmaps.

  Context {A B S: Type}.

  Definition mmaps (f: S -> A -> res (S * B)) : S -> list A -> res (S * list B) :=
    fix mmaps (s: S) (xs: list A) {struct xs} : res (S * list B) :=
      match xs with
      | nil => OK (s, nil)
      | x :: xs' => do (s', y) <- f s x;
                    do (s'', ys) <- mmaps s' xs';
                    OK (s'', y :: ys)
      end.

  Lemma mmaps_spec:
    forall (P: S -> S -> B -> Prop) (R: S -> S -> Prop)
           (I: list B -> Prop) (IS: S -> Prop)
           (f: S -> A -> res (S * B)) xs ys s s',
      mmaps f s xs = OK (s', ys) ->
      Reflexive R ->
      Transitive R ->
      I [] ->
      IS s ->
      (forall s s' y, P s s' y ->
                         (forall r,  R r  s  -> P r s' y)
                      /\ (forall t', R s' t' -> P s t' y)) ->
      (forall x y s s',
          In x xs ->
          IS s ->
          f s x = OK (s', y) ->
          P s s' y /\ R s s' /\ IS s') ->
      (forall y ys s s' s'',
          P s s' y ->
          Forall (P s' s'') ys ->
          R s s' ->
          R s' s'' ->
          I ys ->
          I (y :: ys)) ->
      Forall (P s s') ys /\ R s s' /\ I ys /\ IS s'.
  Proof.
    intros P R I IS f xs ys s s' Hmm HRefl HTrans HInil HIS0 HPR Hf HPI.
    revert xs ys s s' Hf Hmm HIS0.
    induction xs as [|x xs IH]; simpl.
    now inversion_clear 2; auto.
    intros ys s s' Hf Hmm HIS.
    monadInv Hmm.
    match goal with H:f _ _ = OK (_, ?w) |- _ =>
      rename w into y; apply Hf in H; try destruct H as (HP & HR' & HIS'); auto end.
    match goal with H:mmaps _ ?s _ = OK (_, ?ws) |- _ =>
      rename s into t, ws into ys; apply IH in H;
        try destruct H as (Hfa & HR & HI & HIS'') end; auto.
    2: now intros; eapply Hf; eauto.
    pose proof (HTrans _ _ _ HR' HR).
    repeat split; eauto.
    constructor.
    now apply HPR in HP; destruct HP; auto.
    apply Forall_forall.
    intros y' Hin.
    apply Forall_forall with (1:=Hfa) in Hin.
    apply HPR in Hin.
    destruct Hin as (HP1 & HP2).
    now apply HP1.
  Qed.

  Lemma mmaps_weak_spec:
    forall (I: S -> Prop) (R: B -> Prop)
           (f: S -> A -> res (S * B)) xs s ys s',
      mmaps f s xs = OK (s', ys) ->
      I s ->
      (forall x s y s',
          I s ->
          In x xs ->
          f s x = OK (s', y) ->
          I s' /\ R y) ->
      I s' /\ Forall R ys.
  Proof.
    induction xs as [|x xs IH]; simpl; intros * Hmm HI Hone; monadInv Hmm.
    now auto.
    match goal with Hf:f _ _ = OK _ |- _ =>
      apply Hone with (1:=HI) in Hf; auto; destruct Hf end.
    rewrite Forall_cons2, (and_comm (R x1)), <-and_assoc; eauto.
  Qed.

  Lemma mmaps_weak_spec':
  forall (R: B -> Prop)
         (f: S -> A -> res (S * B)) xs s ys s',
    mmaps f s xs = OK (s', ys) ->
    (forall x s y s',
        In x xs ->
        f s x = OK (s', y) ->
        R y) ->
    Forall R ys.
  Proof.
    intros * Hmm Hy.
    eapply mmaps_weak_spec with (I:=fun s=>True);
      eauto using Forall_forall.
  Qed.

End Mmaps.

Definition mfoldl {A B: Type} (f: A -> B -> res A) : A -> list B -> res A :=
  fix mfoldl s xs {struct xs} :=
    match xs with
    | nil => OK s
    | x :: xs' => do s' <- f s x;
                    mfoldl s' xs'
    end.

Lemma OK_OK:
  forall {A} (x: A) y,
    OK x = OK y <-> x = y.
Proof.
  intros; split; intro HH; subst; auto. now monadInv HH.
Qed.

Definition mmapacc {A S T: Type} (acc: S -> T -> S) (f: A -> res T)
  : S -> list A -> res S :=
  fix mmapacc (s: S) (xs: list A) {struct xs} : res S :=
    match xs with
    | nil => OK s
    | x :: xs' => do r <- f x;
                    mmapacc (acc s r) xs'
    end.

Lemma mmap_skipn:
  forall {A B} (f: A -> res B) xs ys n,
    mmap f xs = OK ys ->
    mmap f (skipn n xs) = OK (skipn n ys).
Proof.
  induction xs as [|x xs IH].
  now inversion_clear 1; setoid_rewrite skipn_nil; auto.
  intros ys n Hmm.
  simpl in *. monadInv Hmm.
  destruct n; simpl.
  2:now apply IH.
  rewrite EQ; rewrite EQ1. auto.
Qed.

Open Scope nat.

Lemma mmapacc_plus_shift:
  forall {A} f (xs: list A) m1 m2 n,
    mmapacc plus f (m1 + m2) xs = OK n ->
    mmapacc plus f m1 xs = OK (n - m2) /\ m2 <= n.
Proof.
  induction xs as [|x xs IH]; intros m1 m2 n Hm; simpl in *; monadInv Hm.
  now subst; rewrite OK_OK; omega.
  rewrite EQ. simpl.
  rewrite Plus.plus_comm, Plus.plus_assoc, (Plus.plus_comm x0 m1) in EQ0.
  apply IH in EQ0. auto.
Qed.

(** More monad syntax and tactics *)

Definition bind22 {A B C D: Type} (f: res (A * (B * C))) (g: A -> B -> C -> res D) : res D :=
  match f with
  | OK (x, (y, z)) => g x y z
  | Error msg => Error msg
  end.

Module DoNotation.

  Notation "'do' ( X , ( Y , Z ) ) <- A ; B" :=
    (bind22 A (fun X Y Z => B))
      (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200)
    : error_monad_scope.

End DoNotation.

Remark bind22_inversion:
  forall {A B C D: Type} (f: res (A*(B*C))) (g: A -> B -> C -> res D) {z: D},
    bind22 f g = OK z ->
    exists w, exists x, exists y, f = OK (w, (x, y)) /\ g w x y = OK z.
Proof.
  intros until z. destruct f; simpl.
  repeat destruct p; simpl; intros. exists a; exists b; exists c; auto.
  intros; discriminate.
Qed.

(* Duplicate the tactic from CompCert/common/Errors and add a case
     for bind22. *)
Ltac monadInv2 H :=
  match type of H with
  | (OK _ = OK _) =>
    inversion H; clear H; try subst
  | (Error _ = OK _) =>
    discriminate
  | (bind ?F ?G = OK ?X) =>
    let x := fresh "x" in (
      let EQ1 := fresh "EQ" in (
        let EQ2 := fresh "EQ" in (
          destruct (bind_inversion F G H) as [x [EQ1 EQ2]];
          clear H;
          try (monadInv2 EQ2))))
  | (bind2 ?F ?G = OK ?X) =>
    let x1 := fresh "x" in (
      let x2 := fresh "x" in (
        let EQ1 := fresh "EQ" in (
          let EQ2 := fresh "EQ" in (
            destruct (bind2_inversion F G H) as [x1 [x2 [EQ1 EQ2]]];
            clear H;
            try (monadInv2 EQ2)))))
  | (bind22 ?F ?G = OK ?X) =>
    let x1 := fresh "x" in (
      let x2 := fresh "x" in (
        let x3 := fresh "x" in (
          let EQ1 := fresh "EQ" in (
            let EQ2 := fresh "EQ" in (
              destruct (bind22_inversion F G H) as [x1 [x2 [x3 [EQ1 EQ2]]]];
              clear H;
              try (monadInv2 EQ2))))))
  | (match ?X with left _ => _ | right _ => assertion_failed end = OK _) =>
    destruct X; [try (monadInv2 H) | discriminate]
  | (match (negb ?X) with true => _ | false => assertion_failed end = OK _) =>
    destruct X as [] eqn:?; [discriminate | try (monadInv2 H)]
  | (match ?X with true => _ | false => assertion_failed end = OK _) =>
    destruct X as [] eqn:?; [try (monadInv2 H) | discriminate]
  | (mmap ?F ?L = OK ?M) =>
    generalize (mmap_inversion F L H); intro
  end.

Close Scope nat.
Close Scope error_monad_scope.
