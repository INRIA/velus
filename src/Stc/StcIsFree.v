From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import FunctionalEnvironment.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Clocks.

From Velus Require Export CoreExpr.CEIsFree.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type STCISFREE
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS    Ids Op OpAux)
       (Import CESyn : CESYNTAX  Ids Op OpAux Cks)
       (Import Syn   : STCSYNTAX Ids Op OpAux Cks CESyn)
       (Import CEIsF : CEISFREE  Ids Op OpAux Cks CESyn).

  Inductive Is_free_in_tc: var_last -> trconstr -> Prop :=
  | FreeTcDef:
      forall x ck e y,
        Is_free_in_arhs y ck e ->
        Is_free_in_tc y (TcDef ck x e)
  | FreeTcReset:
      forall ckr rsconstr y,
        Is_free_in_clock y ckr ->
        Is_free_in_tc (Var y) (TcReset ckr rsconstr)
  | FreeTcUpdLast:
      forall ck ckrs x e y,
        Is_free_in_acexp y ck e ->
        Is_free_in_tc y (TcUpdate ck ckrs (UpdLast x e))
  | FreeTcUpdNext:
    forall ck ckrs x e y,
      Is_free_in_aexp y ck e ->
      Is_free_in_tc y (TcUpdate ck ckrs (UpdNext x e))
  | FreeTcUpdInst:
      forall ck ckrs s xs b es y,
        Is_free_in_aexps y ck es ->
        Is_free_in_tc y (TcUpdate ck ckrs (UpdInst s xs b es)).

  Definition Is_free_in (x: var_last) (tcs: list trconstr) : Prop :=
    Exists (Is_free_in_tc x) tcs.

  Definition free_in_tc (tc: trconstr) (fvs: (PS.t * PS.t)) : (PS.t * PS.t) :=
    match tc with
    | TcDef ck _ e => free_in_arhs ck e fvs
    | TcReset ckr _ => (free_in_clock ckr (fst fvs), (snd fvs))
    | TcUpdate ck _ (UpdLast _ e) => free_in_acexp ck e fvs
    | TcUpdate ck _ (UpdNext _ e) => free_in_aexp ck e fvs
    | TcUpdate ck _ (UpdInst _ _ _ es) => free_in_aexps ck es fvs
    end.

  Global Hint Constructors Is_free_in_tc : stcfree.

  Lemma free_in_tc_spec1:
    forall x tc m,
      PS.In x (fst (free_in_tc tc m))
      <-> (Is_free_in_tc (Var x) tc \/ PS.In x (fst m)).
  Proof.
    intros. unfold free_in_tc. cases; simpl.
    all:rewrite ?free_in_aexp_spec1, ?free_in_aexps_spec1, ?free_in_acexp_spec1, ?free_in_arhs_spec1, ?free_in_clock_spec.
    all:split; intros [|]; auto with stcfree.
    all:take (Is_free_in_tc _ _) and inv it; auto.
  Qed.

  Corollary free_in_tc_spec1':
    forall x tc,
      PS.In x (fst (free_in_tc tc (PS.empty, PS.empty)))
      <-> Is_free_in_tc (Var x) tc.
  Proof.
    intros; rewrite free_in_tc_spec1.
    split.
    - intros [ H | H ]; auto with *.
    - intros. auto with *.
  Qed.

  Lemma free_in_tc_spec2:
    forall x tc m,
      PS.In x (snd (free_in_tc tc m))
      <-> (Is_free_in_tc (Last x) tc \/ PS.In x (snd m)).
  Proof.
    intros. unfold free_in_tc. cases; simpl.
    all:rewrite ?free_in_aexp_spec2, ?free_in_aexps_spec2, ?free_in_acexp_spec2, ?free_in_arhs_spec2, ?free_in_clock_spec.
    all:split; intros; try take (_ \/ _) and destruct it; auto with stcfree.
    all:try take (Is_free_in_tc _ _) and inv it; auto. auto.
  Qed.

  Corollary free_in_tc_spec2':
    forall x tc,
      PS.In x (snd (free_in_tc tc (PS.empty, PS.empty)))
      <-> Is_free_in_tc (Last x) tc.
  Proof.
    intros; rewrite free_in_tc_spec2.
    split.
    - intros [ H | H ]; auto with *.
    - intros. left. assumption.
  Qed.

End STCISFREE.

Module StcIsFreeFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS    Ids Op OpAux)
       (CESyn : CESYNTAX  Ids Op OpAux Cks)
       (Syn   : STCSYNTAX Ids Op OpAux Cks CESyn)
       (CEIsF : CEISFREE  Ids Op OpAux Cks CESyn)
<: STCISFREE Ids Op OpAux Cks CESyn Syn CEIsF.
  Include STCISFREE Ids Op OpAux Cks CESyn Syn CEIsF.
End StcIsFreeFun.
