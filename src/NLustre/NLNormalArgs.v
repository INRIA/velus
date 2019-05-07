Require Import Velus.Common.Common.
Require Import Velus.Operators.
Require Import Velus.CoreExpr.CESyntax.
Require Import Velus.Clocks.
Require Import Velus.NLustre.NLSyntax.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type NLNORMALARGS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import CESyn : CESYNTAX     Op)
       (Import Syn   : NLSYNTAX Ids Op CESyn).

(** The [normal_args] predicate defines a normalization condition on
      node arguments -- those that are not on the base clock can only
      be instantiated with constants or variables -- that is necessary
      for correct generation of Obc/Clight.

      To see why this is necessary. Consider the NLustre equation: y =
            f(1, 3 when ck / x)

      with x on the clock ck, and y on the base clock. The generated
            Obc code is y := f(1, 3 / x)

      which has no semantics when ck = false, since x = None then 3 /
      x is not given a meaning.

      Consider what would happen were the semantics of 3 / x =
      None. There are two possible problems.

      If x is a local variable, then x = None in Obc implies that x =
      VUndef in Clight and 3 / VUndef has no semantics. I.e., the Obc
      program having a semantics would not be enough to guarantee that
      the Clight program generated from it does.

      If x is a state variable, then x = None in Obc implies that x
      could be anything in Clight (though it would be defined since
      state variables are stored in a global structure). We might then
      prove that x is never 0 (when ck = true) in the original Lustre
      program. This would guarantee the absence of division by zero in
      the generated Obc (since x is None when ck = false), but not in
      the generated Clight code; since None in Obc means "don't care"
      in Clight, x may well contain the value 0 when ck is false (for
      instance, if ck = false at the first reaction).
 *)


  Inductive normal_args_eq (G: global) : equation -> Prop :=
  | CEqDef:
      forall x ck ce,
        normal_args_eq G (EqDef x ck ce)
  | CEqApp:
      forall xs ck f les r n,
        find_node f G = Some n ->
        Forall2 noops_lexp (map dck n.(n_in)) les ->
        normal_args_eq G (EqApp xs ck f les r)
  | CEqFby:
      forall x ck v0 le,
        normal_args_eq G (EqFby x ck v0 le).

  Definition normal_args_node (G: global) (n: node) : Prop :=
    Forall (normal_args_eq G) n.(n_eqs).

  Fixpoint normal_args (G: list node) : Prop :=
    match G with
    | [] => True
    | n :: G' => normal_args_node G n /\ normal_args G'
    end.

  (* Lemma normal_args_node_cons: *)
  (*   forall node G, *)
  (*     normal_args_node (node :: G) node -> *)
  (*     ~ Is_node_in node.(n_name) node.(n_eqs) -> *)
  (*     normal_args_node G node. *)
  (* Proof. *)
  (*   intros node G Hnarg Hord. *)
  (*   apply Forall_forall. *)
  (*   intros eq Hin. *)
  (*   destruct eq as [|ys ck f les|]; eauto using normal_args_eq. *)
  (*   apply In_Forall with (2:=Hin) in Hnarg. *)
  (*   inversion_clear Hnarg as [|? ? ? ? ? Hfind Hnargs|]. *)
  (*   apply find_node_other in Hfind; *)
  (*     eauto using normal_args_eq. *)
  (*   apply Is_node_in_Forall, In_Forall with (2:=Hin) in Hord. *)
  (*   intro; subst; auto using Is_node_in_eq. *)
  (* Qed. *)
End NLNORMALARGS.

Module NLNormalArgsFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (CESyn : CESYNTAX     Op)
       (Syn   : NLSYNTAX Ids Op CESyn)
<: NLNORMALARGS Ids Op CESyn Syn.
  Include NLNORMALARGS Ids Op CESyn Syn.
End NLNormalArgsFun.
