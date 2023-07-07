From Coq Require Import PArith.
From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.IsVariable.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import NLustre.Memories.

(** * No duplication of variables *)

(**

  The [NoDup_def] predicate states that variables are only defined
  once. This is asking for some sort of SSA.

 *)

Module Type NODUP
       (Ids          : IDS)
       (Op           : OPERATORS)
       (OpAux        : OPERATORS_AUX  Ids Op)
       (Import Cks   : CLOCKS     Ids Op OpAux)
       (Import CESyn : CESYNTAX   Ids Op OpAux Cks)
       (Import Syn   : NLSYNTAX   Ids Op OpAux Cks CESyn)
       (Import Mem   : MEMORIES   Ids Op OpAux Cks CESyn Syn)
       (Import IsD   : ISDEFINED  Ids Op OpAux Cks CESyn Syn Mem)
       (Import IsV   : ISVARIABLE Ids Op OpAux Cks CESyn Syn Mem IsD).

  Inductive NoDup_defs : list equation -> Prop :=
  | NDDNil: NoDup_defs nil
  | NDDCons: forall eq eqs,
      NoDup_defs eqs ->
      (forall x, Is_defined_in_eq x eq -> ~Is_defined_in x eqs) ->
      NoDup_defs (eq :: eqs).

  (** ** Properties *)

  Lemma NoDup_defs_cons:
    forall eq eqs,
      NoDup_defs (eq :: eqs) -> NoDup_defs eqs.
  Proof.
    intros eq eqs Hndd.
    destruct eq; inversion_clear Hndd; assumption.
  Qed.

  (* TODO is this useful ? *)
  (* Lemma not_Is_variable_in_memories: *)
  (*   forall x eqs, *)
  (*     PS.In x (memories eqs) *)
  (*     -> NoDup_defs eqs *)
  (*     -> ~Is_variable_in x eqs. *)
  (* Proof. *)
  (*   intros x eqs Hinm Hndd Hvar. *)

  (*   induction eqs as [ | eq eqs IHeqs ]. *)
  (*   - inv Hvar. *)
  (*   - unfold memories in *; simpl in *. *)
  (*     inv Hndd. *)
  (*     apply In_fold_left_memory_eq in Hinm as [Hinm|Hinm]; inv Hvar; eauto. *)
  (*     + apply In_fold_left_memory_eq_defined_eq, Is_defined_inP in Hinm. *)
  (*       take (forall x, _ -> ~ Is_defined_in x _) and *)
  (*            eapply it; eauto using Is_variable_in_eq_Is_defined_in_eq. *)
  (*     + take (Is_variable_in_eq _ _) and inv it; simpl in *; inv Hinm. *)
  (*     + apply In_memory_eq_In_defined_eq, Is_defined_in_eqP in Hinm. *)
  (*       take (forall x, _ -> ~ Is_defined_in x _) and *)
  (*            eapply it; eauto using Is_variable_in_Is_defined_in. *)
  (* Qed. *)

  Lemma NoDup_defs_NoDup_vars_defined:
    forall eqs,
      NoDup (vars_defined eqs) ->
      NoDup (lasts_defined eqs) ->
      NoDup_defs eqs.
  Proof.
    unfold vars_defined, lasts_defined.
    induction eqs as [|eq eqs]; simpl; intros * VD LD.
    - auto using NoDup_defs.
    - simpl.
      constructor; eauto using NoDup_app_r.
      intros ? Hdef1 Hdef2. destruct x.
      + eapply NoDup_app_In in VD. eapply VD.
        * apply Is_defined_in_vars_defined; eauto.
        * apply Is_defined_in_var_defined; eauto.
      + eapply NoDup_app_In in LD. eapply LD.
        * apply Is_defined_in_lasts_defined; eauto.
        * apply Is_defined_in_last_defined; eauto.
  Qed.

  Lemma NoDup_defs_node:
    forall n,
      NoDup_defs n.(n_eqs).
  Proof.
    intros.
    apply NoDup_defs_NoDup_vars_defined; auto using NoDup_var_defined_n_eqs, NoDup_last_defined_n_eqs.
  Qed.

End NODUP.

Module NoDupFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX  Ids Op)
       (Cks   : CLOCKS     Ids Op OpAux)
       (CESyn : CESYNTAX   Ids Op OpAux Cks)
       (Syn   : NLSYNTAX   Ids Op OpAux Cks CESyn)
       (Mem   : MEMORIES   Ids Op OpAux Cks CESyn Syn)
       (IsD   : ISDEFINED  Ids Op OpAux Cks CESyn Syn Mem)
       (IsV   : ISVARIABLE Ids Op OpAux Cks CESyn Syn Mem IsD)
       <: NODUP Ids Op OpAux Cks CESyn Syn Mem IsD IsV.
  Include NODUP Ids Op OpAux Cks CESyn Syn Mem IsD IsV.
End NoDupFun.
