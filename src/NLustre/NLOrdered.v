From Coq Require Import PArith.
From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.

(** * Ordering of nodes *)

(**

The compilation of a whole program is only correct if that program satisfies
the [Ordered_nodes] predicate, which states that a node may only call nodes
that were defined earlier.

 *)

Module Type NLORDERED
       (Ids          : IDS)
       (Op           : OPERATORS)
       (OpAux        : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import CESyn : CESYNTAX      Ids Op OpAux Cks)
       (Import Syn   : NLSYNTAX Ids  Op OpAux Cks CESyn).

  Inductive Is_node_in_eq : ident -> equation -> Prop :=
  | INI: forall x ck f e r, Is_node_in_eq f (EqApp x ck f e r).

  Definition Is_node_in (f: ident) (eqs: list equation) : Prop :=
    List.Exists (Is_node_in_eq f) eqs.

  Definition Ordered_nodes :=
    Ordered_program (fun f node => Is_node_in f node.(n_eqs)).

  (** ** Properties of [Is_node_in] *)

  Section Is_node_Properties.

    Lemma not_Is_node_in_cons:
      forall n eq eqs,
        ~ Is_node_in n (eq::eqs) <-> ~Is_node_in_eq n eq /\ ~Is_node_in n eqs.
    Proof.
      intros n eq eqs.
      split; intro HH.
      - split; intro; apply HH; unfold Is_node_in; intuition.
      - destruct HH; inversion_clear 1; intuition.
    Qed.

    Lemma Is_node_in_Forall:
      forall n eqs,
        ~Is_node_in n eqs <-> List.Forall (fun eq=>~Is_node_in_eq n eq) eqs.
    Proof.
      induction eqs as [|eq eqs IH];
      [split; [now constructor|now inversion 2]|].
      split; intro HH.
      - apply not_Is_node_in_cons in HH.
        destruct HH as [Heq Heqs].
        constructor; [exact Heq|apply IH with (1:=Heqs)].
      - apply not_Is_node_in_cons.
        inversion_clear HH as [|? ? Heq Heqs].
        apply IH in Heqs.
        intuition.
    Qed.

  End Is_node_Properties.

  (** ** Properties of [Ordered_nodes] *)

  Lemma Ordered_nodes_append:
    forall G G' enums externs,
      Ordered_nodes (Global enums externs (G ++ G'))
      -> Ordered_nodes (Global enums externs G').
  Proof.
    intros * Ord.
    eapply Ordered_program_append' in Ord as (?&?); simpl in *; eauto.
  Qed.

  Lemma find_node_other_not_Is_node_in:
    forall f nd G nd' enums externs,
      Ordered_nodes (Global enums externs (nd::G))
      -> find_node f (Global enums externs G) = Some nd'
      -> ~Is_node_in nd.(n_name) nd'.(n_eqs).
  Proof.
    intros * Ord Find.
    apply option_map_inv in Find as ((?&?)&?&?); simpl in *; subst.
    eapply find_unit_other_not_Is_called_in in Ord; eauto; simpl; auto.
  Qed.

  Lemma find_node_not_Is_node_in:
    forall f nd G,
      Ordered_nodes G
      -> find_node f G = Some nd
      -> ~Is_node_in nd.(n_name) nd.(n_eqs).
  Proof.
    intros * Ord Find.
    apply option_map_inv in Find as ((?&?)& Find &?); simpl in *; subst.
    assert (n_name n = f) as -> by (apply find_unit_In in Find as []; auto).
    eapply not_Is_called_in_self in Ord; eauto.
  Qed.

  Lemma find_node_not_Is_node_in_eq:
    forall G f g n enums externs,
      Ordered_nodes (Global enums externs G) ->
      Forall (fun n' => ~(g = n'.(n_name))) G ->
      find_node f (Global enums externs G) = Some n ->
      Forall (fun eq => ~ Is_node_in_eq g eq) n.(n_eqs).
  Proof.
    intros * Ord Hnn Find.
    apply option_map_inv in Find as ((?&?)&?&?); simpl in *; subst.
    eapply find_unit_not_Is_called_in in Ord; eauto.
    - apply Forall_Exists_neg; eauto.
    - apply find_unit_None; auto.
  Qed.

End NLORDERED.

Module NLOrderedFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS        Ids Op OpAux)
       (CESyn : CESYNTAX      Ids Op OpAux Cks)
       (Syn   : NLSYNTAX Ids  Op OpAux Cks CESyn)
       <: NLORDERED Ids Op OpAux Cks CESyn Syn.
  Include NLORDERED Ids Op OpAux Cks CESyn Syn.
End NLOrderedFun.
