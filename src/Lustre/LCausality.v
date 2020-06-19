From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Permutation.

From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.

From Velus Require Import Lustre.LSyntax.

(** * Lustre causality *)

(**
  Causality judgement over a Lustre program
  *)

Module Type LCAUSALITY
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import Syn : LSYNTAX Ids Op).

  Inductive Is_free_left (x : ident) : exp -> Prop :=
  | IFLvar : forall a,
      Is_free_left x (Evar x a)
  | IFLunop : forall op e a,
      Is_free_left x e ->
      Is_free_left x (Eunop op e a)
  | IFLbinop : forall op e1 e2 a,
      Is_free_left x e1
      \/ Is_free_left x e2 ->
      Is_free_left x (Ebinop op e1 e2 a)
  | IFLfby : forall e0s es a,
      Exists (Is_free_left x) e0s ->
      Is_free_left x (Efby e0s es a)
  | IFLwhen : forall es y b a,
      x = y
      \/ Exists (Is_free_left x) es ->
      Is_free_left x (Ewhen es y b a)
  | IFLmerge : forall ets efs y a,
      x = y
      \/ Exists (Is_free_left x) ets
      \/ Exists (Is_free_left x) efs ->
      Is_free_left x (Emerge y ets efs a)
  | IFLite : forall e ets efs a,
      Is_free_left x e
      \/ Exists (Is_free_left x) ets
      \/ Exists (Is_free_left x) efs ->
      Is_free_left x (Eite e ets efs a)
  | IFLapp : forall f es a,
      Exists (Is_free_left x) es ->
      Is_free_left x (Eapp f es None a)
  | IFLreset : forall f es r a,
      Exists (Is_free_left x) (r :: es) ->
      Is_free_left x (Eapp f es (Some r) a).

  Inductive Is_causal (inputs : list ident) : list equation -> Prop :=
  | ICnil:
      Is_causal inputs []
  | ICcons: forall eq eqs,
      Is_causal inputs eqs ->
      (forall x, Exists (Is_free_left x) (snd eq) ->
            In x (vars_defined eqs) \/ In x inputs) ->
      Is_causal inputs (eq :: eqs).
  Hint Constructors Is_causal.

  (* TODO: link with check_graph_spec *)
  Definition node_causal (n : node) :=
    exists eqs, Permutation (n_eqs n) eqs
           /\ Is_causal (map fst (n_in n)) eqs.

End LCAUSALITY.

Module LCausality
       (Ids  : IDS)
       (Op   : OPERATORS)
       (Syn  : LSYNTAX Ids Op)
       <: LCAUSALITY Ids Op Syn.
  Include LCAUSALITY Ids Op Syn.
End LCausality.
