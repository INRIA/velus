From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import SyBloc.SBSyntax.
From Velus Require Import Clocks.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type SBISVARIABLE
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import CESyn : CESYNTAX     Op)
       (Import Syn   : SBSYNTAX Ids Op CESyn).

  Inductive Is_variable_in_eq: ident -> equation -> Prop :=
  | VarEqDef:
      forall x ck e,
        Is_variable_in_eq x (EqDef x ck e)
  | VarEqCall:
      forall x s xs ck rst b es,
        In x xs ->
        Is_variable_in_eq x (EqCall s xs ck rst b es).

  Definition Is_variable_in (x: ident) (eqs: list equation) : Prop :=
    Exists (Is_variable_in_eq x) eqs.

  Lemma Is_variable_in_variables:
    forall eqs x,
      Is_variable_in x eqs <-> In x (variables eqs).
  Proof.
    unfold variables.
    induction eqs as [|[]]; simpl.
    - split; try contradiction; inversion 1.
    - split.
      + inversion_clear 1 as [?? Var|]; try inv Var; auto.
        right; apply IHeqs; auto.
      + intros [E|].
        * subst; left; constructor.
        * right; apply IHeqs; auto.
    - setoid_rewrite <-IHeqs; split.
      + inversion_clear 1 as [?? Var|]; auto; inv Var.
      + right; auto.
    - setoid_rewrite <-IHeqs; split.
      + inversion_clear 1 as [?? Var|]; auto; inv Var.
      + right; auto.
    - split.
      + inversion_clear 1 as [?? Var|]; try inv Var.
        * apply in_app; auto.
        * apply in_app; right; apply IHeqs; auto.
      + rewrite in_app; intros [?|?].
        * left; constructor; auto.
        * right; apply IHeqs; auto.
  Qed.

  Definition is_variable_in_eq_b (x: ident) (eq: equation) : bool :=
    match eq with
    | EqDef x' _ _ => ident_eqb x x'
    | EqCall _ xs _ _ _ _ => existsb (ident_eqb x) xs
    | _ => false
    end.

  Fact Is_variable_in_eq_reflect:
    forall x eq,
      Is_variable_in_eq x eq <-> is_variable_in_eq_b x eq = true.
  Proof.
    destruct eq; simpl; split;
      try discriminate; try now inversion 1.
    - inversion_clear 1; apply ident_eqb_refl.
    - rewrite ident_eqb_eq; intro; subst; constructor.
    - inversion_clear 1.
      apply existsb_exists; eexists; split; eauto.
      apply ident_eqb_refl.
    - rewrite existsb_exists; intros (?&?& E).
      apply ident_eqb_eq in E; subst.
      constructor; auto.
  Qed.

  Lemma Is_variable_in_eq_dec:
    forall x eq,
      { Is_variable_in_eq x eq } + { ~ Is_variable_in_eq x eq }.
  Proof.
    intros;
      eapply Bool.reflect_dec, Bool.iff_reflect, Is_variable_in_eq_reflect.
  Qed.

  Definition variables_eq (vars: PS.t) (eq: equation) : PS.t :=
    match eq with
    | EqDef x _ _ => PS.add x vars
    | EqCall _ xs _ _ _ _ => ps_adds xs vars
    | _ => vars
    end.

  Lemma variables_eq_empty:
    forall x eq vars,
      PS.In x (variables_eq vars eq)
      <-> PS.In x (variables_eq PS.empty eq) \/ PS.In x vars.
  Proof.
    split; intro Hin.
    - destruct eq; simpl in *; auto.
      + apply PSE.MP.Dec.F.add_iff in Hin as [|]; subst; intuition.
      + rewrite ps_adds_spec in *; tauto.
    - destruct eq; simpl in *; destruct Hin as [Hin|Hin]; auto.
      + rewrite PSE.MP.Dec.F.add_iff in *; intuition; pose proof (not_In_empty x); contradiction.
      + rewrite PSE.MP.Dec.F.add_iff; auto.
      + pose proof (not_In_empty x); contradiction.
      + pose proof (not_In_empty x); contradiction.
      + rewrite ps_adds_spec in *; intuition; pose proof (not_In_empty x); contradiction.
      + rewrite ps_adds_spec; tauto.
  Qed.

End SBISVARIABLE.

Module SBIsVariableFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (CESyn : CESYNTAX     Op)
       (Syn   : SBSYNTAX Ids Op CESyn)
<: SBISVARIABLE Ids Op CESyn Syn.
  Include SBISVARIABLE Ids Op CESyn Syn.
End SBIsVariableFun.
