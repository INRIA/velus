From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import Operators.
From Velus Require Import CoreExpr.CESyntax CoreExpr.CETyping.
From Velus Require Import Clocks.
From Velus Require Import NLustre.NLSyntax NLustre.NLOrdered NLustre.NLTyping.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type NLNORMALARGS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS    Ids Op OpAux)
       (Import CESyn : CESYNTAX  Ids Op OpAux Cks)
       (Import CETyp : CETYPING  Ids Op OpAux Cks CESyn)
       (Import Syn   : NLSYNTAX  Ids Op OpAux Cks CESyn)
       (Import Ord   : NLORDERED Ids Op OpAux Cks CESyn Syn)
       (Import Typ   : NLTYPING  Ids Op OpAux Cks CESyn Syn Ord CETyp).

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
        Forall2 noops_exp (map (fun '(_, (_, ck)) => ck) n.(n_in)) les ->
        normal_args_eq G (EqApp xs ck f les r)
  | CEqFby:
      forall x ck v0 le r,
        normal_args_eq G (EqFby x ck v0 le r).

  Definition normal_args_node (G: global) (n: node) : Prop :=
    Forall (normal_args_eq G) n.(n_eqs).

  Definition normal_args (G: global) :=
    Forall' (fun ns => normal_args_node (Global G.(types) ns)) G.(nodes).

  Lemma normal_args_node_cons:
    forall node G enums,
      normal_args_node (Global enums (node :: G)) node ->
      ~ Is_node_in node.(n_name) node.(n_eqs) ->
      normal_args_node (Global enums G) node.
  Proof.
    intros node G enums Hnarg Hord.
    apply Forall_forall.
    intros eq Hin.
    destruct eq as [|ys ck f les|]; eauto using normal_args_eq.
    eapply Forall_forall in Hnarg; eauto.
    inversion_clear Hnarg as [|? ? ? ? ? ? Hfind Hnargs|].
    rewrite find_node_other in Hfind; eauto using normal_args_eq.
    rewrite Is_node_in_Forall in Hord.
    eapply Forall_forall in Hord; eauto.
    intro; subst; auto using Is_node_in_eq.
  Qed.

  Lemma normal_args_node_cons':
    forall node G enums,
      normal_args_node (Global enums G) node ->
      ~ Is_node_in node.(n_name) node.(n_eqs) ->
      normal_args_node (Global enums (node :: G)) node.
  Proof.
    intros node G enums Hnarg Hord.
    apply Forall_forall.
    intros eq Hin.
    destruct eq as [|ys ck f les|]; eauto using normal_args_eq.
    eapply Forall_forall in Hnarg; eauto.
    inversion_clear Hnarg as [|? ? ? ? ? ? Hfind Hnargs|].
    erewrite <-find_node_other in Hfind; eauto using normal_args_eq.
    rewrite Is_node_in_Forall in Hord.
    eapply Forall_forall in Hord; eauto.
    intro; subst; auto using Is_node_in_eq.
  Qed.

  Lemma normal_args_node_cons'':
    forall n G enums,
      normal_args_node (Global enums G) n ->
      wt_node (Global enums G) n ->
      Forall (fun n' => ~(n.(n_name) = n'.(n_name))) G ->
      normal_args_node (Global enums (n :: G)) n.
  Proof.
    intros n G enums Hnarg (WTn&?) FA.
    eapply Forall_not_find_node_None in FA.
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

  Lemma normal_args_eq_types_cons:
    forall ns enums e eq,
      normal_args_eq (Global enums ns) eq ->
      normal_args_eq (Global (e :: enums) ns) eq.
  Proof.
    induction 1; eauto using normal_args_eq.
    econstructor; eauto.
    now rewrite find_node_types_cons.
  Qed.

  Corollary normal_args_node_types_cons:
    forall ns enums e n,
      normal_args_node (Global enums ns) n ->
      normal_args_node (Global (e :: enums) ns) n.
  Proof.
    unfold normal_args_node; intros * NA.
    apply Forall_forall; intros; eapply Forall_forall in NA; eauto.
    now apply normal_args_eq_types_cons.
  Qed.

  Corollary normal_args_types_cons:
    forall enums ns e,
      normal_args (Global enums ns) ->
      normal_args (Global (e :: enums) ns).
  Proof.
    unfold normal_args.
    induction ns; simpl; intros * NA; inv NA; constructor.
    - now apply normal_args_node_types_cons.
    - apply IHns; auto.
  Qed.

  Lemma global_iface_eq_normal_args_eq : forall G1 G2 eq,
      global_iface_eq G1 G2 ->
      normal_args_eq G1 eq ->
      normal_args_eq G2 eq.
  Proof.
    intros * Heq Hnormed.
    inv Hnormed; try constructor.
    destruct Heq as (_&Heq).
    specialize (Heq f). rewrite H in Heq. inv Heq.
    symmetry in H2. econstructor; eauto.
    destruct H3 as (?&?&?). congruence.
  Qed.

End NLNORMALARGS.

Module NLNormalArgsFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS    Ids Op OpAux)
       (CESyn : CESYNTAX  Ids Op OpAux Cks)
       (CETyp : CETYPING  Ids Op OpAux Cks CESyn)
       (Syn   : NLSYNTAX  Ids Op OpAux Cks CESyn)
       (Ord   : NLORDERED Ids Op OpAux Cks CESyn Syn)
       (Typ   : NLTYPING  Ids Op OpAux Cks CESyn Syn Ord CETyp)
<: NLNORMALARGS Ids Op OpAux Cks CESyn CETyp Syn Ord Typ.
  Include NLNORMALARGS Ids Op OpAux Cks CESyn CETyp Syn Ord Typ.
End NLNormalArgsFun.
