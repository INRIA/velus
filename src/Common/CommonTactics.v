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
