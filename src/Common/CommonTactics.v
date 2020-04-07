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

