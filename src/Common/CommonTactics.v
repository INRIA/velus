Ltac inv H := inversion H; clear H; subst.

Ltac cases :=
  repeat match goal with
         | H: context [ match negb ?x with _ => _ end ] |- _ =>
           destruct x; simpl; try solve [inv H; auto]
         | H: context [ match ?x with _ => _ end ] |- _ =>
           destruct x; try solve [inv H; auto]
         | |- context [ match negb ?x with _ => _ end ] =>
           destruct x; simpl
         | |- context [ match ?x with _ => _ end ] =>
           destruct x
         end; auto.

Ltac cases_eqn E :=
  repeat match goal with
         | H: context [ match negb ?x with _ => _ end ] |- _ =>
           let E := fresh E in
           destruct x eqn: E; simpl; try solve [inv H; auto]
         | H: context [ match ?x with _ => _ end ] |- _ =>
           let E := fresh E in
           destruct x eqn: E; try solve [inv H; auto]
         | |- context [ match negb ?x with _ => _ end ] =>
           let E := fresh E in
           destruct x eqn: E; simpl
         | |- context [ match ?x with _ => _ end ] =>
           let E := fresh E in
           destruct x eqn: E
         end; auto.

Ltac cases_in H :=
  repeat match type of H with
         | context [ match negb ?x with _ => _ end ] =>
           destruct x; simpl; try solve [inv H; auto]
         | context [ match ?x with _ => _ end ] =>
           destruct x; try solve [inv H; auto]
         end; auto.

Create HintDb conjs.

Ltac destruct_conjs :=
  autounfold with conjs in *;
  repeat
    match goal with
    | H: exists _, _ |- _ => destruct H
    | H: _ /\ _ |- _ => destruct H
    | x: _ * _ |- _ => destruct x
    end; simpl in *.

Lemma option_map_inv:
  forall {A B} (f: A -> B) oa b,
    option_map f oa = Some b ->
    exists a, oa = Some a /\ b = f a.
Proof.
  unfold option_map; intros * E.
  cases; inv E; eauto.
Qed.

Lemma option_map_None:
  forall {A B} (f: A -> B) oa,
    option_map f oa = None <-> oa = None.
Proof.
  unfold option_map; intros; cases; intuition; discriminate.
Qed.

Ltac inv_equalities :=
  destruct_conjs; subst;
  repeat
    match goal with
    | H: (_, _) = (_, _) |- _ => inv H
    | H: option_map _ _ = Some _ |- _ =>
        let Hf := fresh "Hf" in
        let Heq := fresh "Heq" in
        apply option_map_inv in H as (?&Hf&Heq); destruct_conjs
    | H: option_map _ _ = None |- _ =>
        apply option_map_None in H; subst
    end.

(* Tactics for manipulating hypotheses without renaming them.
   Lighter-weight (but less expressive) than match goal with.

   https://stackoverflow.com/a/55998007/

   E.g.,
      take (_ /\ _) and destruct it as (P1 & P2)
      take (sem _ _ _) and inversion it.
      take (_ \/ _) and rename it into HD.
 *)
Tactic Notation "summon" uconstr(ty) "as" ident(id) :=
  match goal with H : _ |- _ => pose (id := H : ty); clear id; rename H into id end.

Tactic Notation "take" uconstr(ty) "and" tactic(tac) :=
  let new_it := fresh "it"
  in try (rename it into new_it);
     summon ty as it; tac;
     try (rename new_it into it).

