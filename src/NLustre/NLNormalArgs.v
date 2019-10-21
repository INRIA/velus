(* *********************************************************************)
(*                                                                     *)
(*                 The Vélus verified Lustre compiler                  *)
(*                                                                     *)
(*             (c) 2019 Inria Paris (see the AUTHORS file)             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import CoreExpr.
From Velus Require Import Clocks.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.NLTyping.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type NLNORMALARGS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import CESyn : CESYNTAX      Op)
       (Import CETyp : CETYPING  Ids Op CESyn)
       (Import Syn   : NLSYNTAX  Ids Op CESyn)
       (Import Ord   : NLORDERED Ids Op CESyn Syn)
       (Import Typ   : NLTYPING Ids Op CESyn Syn Ord CETyp).

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
  | NAEqDef:
      forall x ck ce,
        normal_args_eq G (EqDef x ck ce)
  | NAEqApp:
      forall xs ck f les r n,
        find_node f G = Some n ->
        Forall2 noops_exp (map (fun '(_, (_, ck)) => ck) n.(n_in)) les ->
        normal_args_eq G (EqApp xs ck f les r)
  | NAEqFby:
      forall x ck v0 le,
        normal_args_eq G (EqFby x ck v0 le).

  Definition normal_args_node (G: global) (n: node) : Prop :=
    Forall (normal_args_eq G) n.(n_eqs).

  Fixpoint normal_args (G: list node) : Prop :=
    match G with
    | [] => True
    | n :: G' => normal_args_node G n /\ normal_args G'
    end.

  Lemma normal_args_node_cons:
    forall node G,
      normal_args_node (node :: G) node ->
      ~ Is_node_in node.(n_name) node.(n_eqs) ->
      normal_args_node G node.
  Proof.
    intros node G Hnarg Hord.
    apply Forall_forall.
    intros eq Hin.
    destruct eq as [|ys ck f les|]; eauto using normal_args_eq.
    eapply Forall_forall in Hnarg; eauto.
    inversion_clear Hnarg as [|? ? ? ? ? ? Hfind Hnargs|].
    apply find_node_other in Hfind; eauto using normal_args_eq.
    rewrite Is_node_in_Forall in Hord.
    eapply Forall_forall in Hord; eauto.
    intro; subst; auto using Is_node_in_eq.
  Qed.

  Lemma normal_args_node_cons':
    forall node G,
      normal_args_node G node ->
      ~ Is_node_in node.(n_name) node.(n_eqs) ->
      normal_args_node (node :: G) node.
  Proof.
    intros node G Hnarg Hord.
    apply Forall_forall.
    intros eq Hin.
    destruct eq as [|ys ck f les|]; eauto using normal_args_eq.
    eapply Forall_forall in Hnarg; eauto.
    inversion_clear Hnarg as [|? ? ? ? ? ? Hfind Hnargs|].
    rewrite <-find_node_other in Hfind; eauto using normal_args_eq.
    rewrite Is_node_in_Forall in Hord.
    eapply Forall_forall in Hord; eauto.
    intro; subst; auto using Is_node_in_eq.
  Qed.

  Lemma normal_args_node_cons'':
    forall n G,
      normal_args_node G n ->
      wt_node G n ->
      Forall (fun n' => ~(n.(n_name) = n'.(n_name))) G ->
      normal_args_node (n :: G) n.
  Proof.
    intros n G Hnarg WTn FA.
    apply Forall_not_find_node_None in FA.
    apply normal_args_node_cons'; auto.
    unfold wt_node in WTn.
    apply Is_node_in_Forall.
    apply Forall_impl_In with (2:=WTn).
    intros eq Ieq WTeq.
    inversion 1; subst.
    inversion WTeq; subst;
      match goal with H1:find_node _ _ = _, H2:find_node _ _ = _ |- _ =>
                      rewrite H1 in H2; clear H1 end; discriminate.
  Qed.

End NLNORMALARGS.

Module NLNormalArgsFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (CESyn : CESYNTAX      Op)
       (CETyp : CETYPING  Ids Op CESyn)
       (Syn   : NLSYNTAX  Ids Op CESyn)
       (Ord   : NLORDERED Ids Op CESyn Syn)
       (Typ   : NLTYPING  Ids Op CESyn Syn Ord CETyp)
<: NLNORMALARGS Ids Op CESyn CETyp Syn Ord Typ.
  Include NLNORMALARGS Ids Op CESyn CETyp Syn Ord Typ.
End NLNormalArgsFun.

