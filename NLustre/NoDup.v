Require Import PArith.
Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Rustre.Common.
Require Import Rustre.Operators.
Require Import Rustre.NLustre.Syntax.
Require Import Rustre.NLustre.IsVariable.
Require Import Rustre.NLustre.IsDefined.
Require Import Rustre.NLustre.Memories.

(** * No duplication of variables *)

(**

  The [NoDup_def] predicate states that variables are only defined
  once. This is asking for some sort of SSA.

  Remark: [Ordered_nodes] is implied by [Welldef_global].

 *)

(* TODO: the dispatch on all constructors seems rather unnecessary,
this generically amounts to:

<<
  forall x, Is_defined_in_eq x eq -> ~Is_defined_in x eqs
>>
 *)

Module Type NODUP
       (Ids : IDS)
       (Op  : OPERATORS)
       (Import Syn : SYNTAX Ids Op)
       (Import Mem : MEMORIES Ids Op Syn)
       (Import IsD : ISDEFINED Ids Op Syn Mem)
       (Import IsV : ISVARIABLE Ids Op Syn Mem IsD).

  Inductive NoDup_defs : list equation -> Prop :=
  | NDDNil: NoDup_defs nil
  | NDDEqDef:
      forall x ck e eqs,
        NoDup_defs eqs ->
        ~Is_defined_in_eqs x eqs ->
        NoDup_defs (EqDef x ck e :: eqs)
  | NDDEqApp:
      forall xs ck f e eqs,
        NoDup_defs eqs ->
        (forall x, In x xs -> ~Is_defined_in_eqs x eqs) ->
        NoDup_defs (EqApp xs ck f e :: eqs)
  | NDDEqFby:
      forall x ck v e eqs,
        NoDup_defs eqs ->
        ~Is_defined_in_eqs x eqs ->
        NoDup_defs (EqFby x ck v e :: eqs).

  (** ** Properties *)

  Lemma NoDup_defs_cons:
    forall eq eqs,
      NoDup_defs (eq :: eqs) -> NoDup_defs eqs.
  Proof.
    intros eq eqs Hndd.
    destruct eq; inversion_clear Hndd; assumption.
  Qed.

  Lemma not_Is_variable_in_memories:
    forall x eqs,
      PS.In x (memories eqs)
      -> NoDup_defs eqs
      -> ~Is_variable_in_eqs x eqs.
  Proof.
    intros x eqs Hinm Hndd Hvar.

    induction eqs as [ | eq eqs IHeqs ].
    - inv Hvar.
    - assert (NoDup_defs eqs)
        by now eapply NoDup_defs_cons; eauto.

      unfold memories in *; simpl in *.
      destruct eq; simpl in *;
      match goal with
      | _ : context[ EqFby _ _ _ _ ] |- _ =>
        idtac
      | _ =>
        (* Case: eq ~ EqApp or eq ~ EqDef *)
        (assert (Is_defined_in_eqs x eqs)
          by now apply Is_defined_in_memories);
        (assert (Is_variable_in_eqs x eqs)
          by now inv Hvar; auto; exfalso; inv Hndd;
            match goal with
            | H: Is_variable_in_eq ?x (EqDef ?i _ _) |- _ => inv H
            | H: Is_variable_in_eq ?x (EqApp ?i _ _ _) |- _ => inv H
            end; firstorder);
        now apply IHeqs
      end.
      (* Case: eq ~ EqFby *)
      rewrite In_fold_left_memory_eq in Hinm.
      destruct Hinm.
      * assert (Is_defined_in_eqs x eqs)
          by now apply Is_defined_in_memories.
        assert (Is_variable_in_eqs x eqs)
          by now inv Hvar; auto; exfalso; inv Hndd;
            match goal with
            | H: Is_variable_in_eq ?x (EqFby ?i _ _ _) |- _ => inv H
            end.
        now apply IHeqs.
      * assert (x = i) as ->.
        {
          rewrite PSF.add_iff in H0.
          destruct H0; auto.
          exfalso; eapply not_In_empty; eauto.
        }

        assert (~ Is_variable_in_eqs i eqs)
          by now apply not_Is_defined_in_not_Is_variable_in;
          inv Hndd.

        assert (~ Is_variable_in_eq i (EqFby i c c0 l))
          by now intro His_var; inv His_var.

        now inv Hvar.
  Qed.

End NODUP.

Module NoDupFun
       (Ids : IDS)
       (Op  : OPERATORS)
       (Import Syn : SYNTAX Ids Op)
       (Import Mem : MEMORIES Ids Op Syn)
       (Import IsD : ISDEFINED Ids Op Syn Mem)
       (Import IsV : ISVARIABLE Ids Op Syn Mem IsD)
       <: NODUP Ids Op Syn Mem IsD IsV.

  Include NODUP Ids Op Syn Mem IsD IsV.

End NoDupFun.
