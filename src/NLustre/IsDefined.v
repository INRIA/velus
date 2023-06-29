From Coq Require Import PArith.
From Coq Require Import List.

Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import FunctionalEnvironment.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.Memories.

(** * Defined variables *)

(**

  The [Is_defined_in] predicate identifies the variables defined by a
  set of equations.

 *)

Module Type ISDEFINED
       (Ids          : IDS)
       (Op           : OPERATORS)
       (OpAux        : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import CESyn : CESYNTAX      Ids Op OpAux Cks)
       (Import Syn   : NLSYNTAX Ids  Op OpAux Cks CESyn)
       (Import Mem   : MEMORIES Ids  Op OpAux Cks CESyn Syn).

  (** ** Logical predicates: *)

  Inductive Is_defined_in_eq : var_last -> equation -> Prop :=
  | DefEqDef:
      forall x ck e,
        Is_defined_in_eq (Var x) (EqDef x ck e)
  | DefEqLast:
      forall x ty ck c0 ckrs,
        Is_defined_in_eq (Last x) (EqLast x ty ck c0 ckrs)
  | DefEqApp:
      forall x xs ck f e r,
        In x xs ->
        Is_defined_in_eq (Var x) (EqApp xs ck f e r)
  | DefEqFby:
      forall x ck v e r,
        Is_defined_in_eq (Var x) (EqFby x ck v e r).

  (* definition is needed in signature *)
  Definition Is_defined_in x (eqs: list equation) : Prop :=
    List.Exists (Is_defined_in_eq x) eqs.

  (** ** Properties *)

  Global Hint Constructors Is_defined_in_eq : nldef.

  Lemma not_Is_defined_in_eq_EqDef:
    forall x i ck ce,
      ~ Is_defined_in_eq x (EqDef i ck ce) -> x <> Var i.
  Proof.
    intros x i ck ce H0 xeqi.
    rewrite xeqi in H0.
    assert (Is_defined_in_eq (Var i) (EqDef i ck ce)) by auto with nldef.
    contradiction.
  Qed.

  Lemma not_Is_defined_in_eq_EqApp:
    forall x ys ck f le r,
      ~ Is_defined_in_eq (Var x) (EqApp ys ck f le r) -> ~ List.In x ys.
  Proof.
    intros * H. intro.
    exfalso. apply H; auto with nldef.
  Qed.

  Lemma Is_defined_in_EqApp:
    forall xs ck f es r d,
      0 < length xs ->
      Is_defined_in_eq (Var (hd d xs)) (EqApp xs ck f es r).
  Proof.
    intros * Length.
    constructor.
    destruct xs; simpl in *; auto; lia.
  Qed.

  Lemma not_Is_defined_in_eq_EqFby:
    forall x i ck v0 le r,
      ~ Is_defined_in_eq x (EqFby i ck v0 le r) -> x <> Var i.
  Proof.
    intros x i ck v0 le r H0 xeqi.
    rewrite xeqi in H0.
    assert (Is_defined_in_eq (Var i) (EqFby i ck v0 le r)) by auto with nldef.
    contradiction.
  Qed.

  Lemma not_Is_defined_in_eq_EqLast:
    forall x i ty ck v0 r,
      ~ Is_defined_in_eq x (EqLast i ty ck v0 r) -> x <> Last i.
  Proof.
    intros * H0 xeqi.
    rewrite xeqi in H0.
    assert (Is_defined_in_eq (Last i) (EqLast i ty ck v0 r)) by auto with nldef.
    contradiction.
  Qed.

  Lemma not_Is_defined_in_cons:
    forall x eq eqs,
      ~Is_defined_in x (eq :: eqs)
      <-> ~Is_defined_in_eq x eq /\ ~Is_defined_in x eqs.
  Proof.
    intros x eq eqs. split.
    - (* ==> *)
      intro Hndef; split; intro His_def;
        eapply Hndef. now constructor. now constructor 2.
    - (* <== *)
      intros [Hdef_eq Hdef_eqs] Hdef_all.
      inv Hdef_all; eauto.
  Qed.

  Lemma In_memory_eq_In_defined_eq_gen:
    forall x eq S,
      PS.In x (fst (memory_eq S eq))
      -> Is_defined_in_eq (Var x) eq \/ PS.In x (fst S).
  Proof.
    intros x eq S HH.
    destruct eq; simpl in *; auto.
    apply PS.add_spec in HH as [|]; subst; auto with nldef.
  Qed.

  Corollary In_memory_eq_Is_defined_eq:
    forall x eq,
      PS.In x (fst (memory_eq (PS.empty, PS.empty) eq))
      -> Is_defined_in_eq (Var x) eq.
  Proof.
    intros.
    apply In_memory_eq_In_defined_eq_gen in H as [|]; auto.
    apply not_In_empty in H as [].
  Qed.

  Lemma In_EqFby_Is_defined_in:
    forall x ck c0 e r eqs,
      In (EqFby x ck c0 e r) eqs ->
      Is_defined_in (Var x) eqs.
  Proof.
    induction eqs; inversion_clear 1; subst.
    now repeat constructor.
    constructor 2; intuition.
  Qed.

  Lemma Is_fby_in_Is_defined_in: forall x eqs,
      Is_fby_in x eqs ->
      Is_defined_in (Var x) eqs.
  Proof.
    unfold Is_fby_in, Is_defined_in.
    intros * L. solve_Exists. inv L; auto with nldef.
  Qed.

  Lemma Is_last_in_Is_defined_in: forall x eqs,
      Is_last_in x eqs ->
      Is_defined_in (Last x) eqs.
  Proof.
    unfold Is_last_in, Is_defined_in.
    intros * L. solve_Exists. inv L; auto with nldef.
  Qed.

  Global Hint Resolve Is_fby_in_Is_defined_in Is_last_in_Is_defined_in : nldef.

  (** ** Decision procedures: *)

  Definition defined_eq (defs: (PS.t * PS.t)) (eq: equation) : (PS.t * PS.t) :=
    match eq with
    | EqDef x _ _   => (PS.add x (fst defs), snd defs)
    | EqLast x _ _ _ _ => (fst defs, PS.add x (snd defs))
    | EqApp xs _ _ _ _ => (ps_adds xs (fst defs), snd defs)
    | EqFby x _ _ _ _ => (PS.add x (fst defs), snd defs)
    end.

  Definition defined (eqs: list equation) : (PS.t * PS.t) :=
    List.fold_left defined_eq eqs (PS.empty, PS.empty).

  (** ** Silly unfolding property: *)

  Lemma defined_eq1 : forall x m eq,
      PS.In x (fst (defined_eq m eq))
      <-> PS.In x (fst (defined_eq (PS.empty, PS.empty) eq)) \/ PS.In x (fst m).
  Proof.
    intros ?? []; simpl; rewrite ?PS.add_spec, ?ps_adds_spec, ?PSF.empty_iff.
    all:split; auto; intros; repeat (take (_ \/ _) and destruct it); auto; try now exfalso.
  Qed.

  Lemma defined_eq2 : forall x m eq,
      PS.In x (snd (defined_eq m eq))
      <-> PS.In x (snd (defined_eq (PS.empty, PS.empty) eq)) \/ PS.In x (snd m).
  Proof.
    intros ?? []; simpl; rewrite ?PS.add_spec, ?PSF.empty_iff.
    all:split; auto; intros; repeat (take (_ \/ _) and destruct it); auto; try now exfalso.
  Qed.

  Lemma In_fold_left_defined_eq1:
    forall x eqs m,
      PS.In x (fst (List.fold_left defined_eq eqs m))
      <-> Exists (fun eq => PS.In x (fst (defined_eq (PS.empty, PS.empty) eq))) eqs \/ PS.In x (fst m).
  Proof.
    induction eqs as [|eq]; simpl.
    - split; auto.
      intros [Ex|]; auto. inv Ex.
    - intros ?. rewrite IHeqs, defined_eq1.
      split; intros; repeat (take (_ \/ _) and destruct it); auto.
      inv H; auto.
  Qed.

  Lemma In_fold_left_defined_eq2:
    forall x eqs m,
      PS.In x (snd (List.fold_left defined_eq eqs m))
      <-> Exists (fun eq => PS.In x (snd (defined_eq (PS.empty, PS.empty) eq))) eqs \/ PS.In x (snd m).
  Proof.
    induction eqs as [|eq]; simpl.
    - split; auto.
      intros [Ex|]; auto. inv Ex.
    - intros ?. rewrite IHeqs, defined_eq2.
      split; intros; repeat (take (_ \/ _) and destruct it); auto.
      inv H; auto.
  Qed.

  (** ** Reflection lemmas: *)

  Lemma defined_eq_spec1:
    forall x eq, Is_defined_in_eq (Var x) eq <-> PS.In x (fst (defined_eq (PS.empty, PS.empty) eq)).
  Proof.
    intros x []; simpl; rewrite ?PS.add_spec, ?ps_adds_spec, ?PSF.empty_iff.
    all:split; [intros Is; inv Is
               |intros; repeat take (_ \/ _) and destruct it; subst];
      auto with nldef; try now exfalso.
  Qed.

  Lemma defined_eq_spec2:
    forall x eq, Is_defined_in_eq (Last x) eq <-> PS.In x (snd (defined_eq (PS.empty, PS.empty) eq)).
  Proof.
    intros x []; simpl; rewrite ?PS.add_spec, ?ps_adds_spec, ?PSF.empty_iff.
    all:split; [intros Is; inv Is
               |intros; repeat take (_ \/ _) and destruct it; subst];
      auto with nldef; try now exfalso.
  Qed.

  Lemma defined_spec1:
    forall x eqs, Is_defined_in (Var x) eqs <-> PS.In x (fst (defined eqs)).
  Proof.
    intros. unfold defined, Is_defined_in.
    rewrite In_fold_left_defined_eq1, PSF.empty_iff.
    split; [intros In; left|intros [|[]]]; solve_Exists.
    1,2:now apply defined_eq_spec1.
  Qed.

  Lemma defined_spec2:
    forall x eqs, Is_defined_in (Last x) eqs <-> PS.In x (snd (defined eqs)).
  Proof.
    intros. unfold defined, Is_defined_in.
    rewrite In_fold_left_defined_eq2, PSF.empty_iff.
    split; [intros In; left|intros [|[]]]; solve_Exists.
    1,2:now apply defined_eq_spec2.
  Qed.

  Lemma Is_defined_in_eq_dec:
    forall x eq, {Is_defined_in_eq x eq}+{~Is_defined_in_eq x eq}.
  Proof.
    intros [] *; eapply Bool.reflect_dec, Bool.iff_reflect.
    - eapply defined_eq_spec1.
    - eapply defined_eq_spec2.
  Qed.

  Lemma Is_defined_in_dec:
    forall x eqs, {Is_defined_in x eqs}+{~Is_defined_in x eqs}.
  Proof.
    intros [] *; eapply Bool.reflect_dec, Bool.iff_reflect.
    - eapply defined_spec1.
    - eapply defined_spec2.
  Qed.

  Lemma decidable_Is_defined_in:
    forall x eqs,
      Decidable.decidable (Is_defined_in x eqs).
  Proof.
    intros. apply decidable_Exists.
    intros eq Hin.
    destruct (Is_defined_in_eq_dec x eq); [left|right]; auto.
  Qed.

  (** ** Properties *)

  Lemma Is_defined_in_var_defined:
    forall x eq,
      Is_defined_in_eq (Var x) eq <-> List.In x (var_defined eq).
  Proof.
    intros; rewrite defined_eq_spec1.
    destruct eq; simpl;
      rewrite ?PSF.add_iff, ?ps_adds_spec, PSF.empty_iff;
      intuition.
  Qed.

  Corollary Is_defined_in_vars_defined:
    forall x eqs,
      Is_defined_in (Var x) eqs
      <-> In x (vars_defined eqs).
  Proof.
    intros. unfold Is_defined_in, vars_defined.
    split; intros.
    - simpl_Exists. solve_In. now apply Is_defined_in_var_defined.
    - simpl_In. solve_Exists. now apply Is_defined_in_var_defined.
  Qed.

  Lemma Is_defined_in_last_defined:
    forall x eq,
      Is_defined_in_eq (Last x) eq <-> List.In x (last_defined eq).
  Proof.
    intros; rewrite defined_eq_spec2.
    destruct eq; simpl;
      rewrite ?PSF.add_iff, ?ps_adds_spec, PSF.empty_iff;
      intuition.
  Qed.

  Corollary Is_defined_in_lasts_defined:
    forall x eqs,
      Is_defined_in (Last x) eqs
      <-> In x (lasts_defined eqs).
  Proof.
    intros. unfold Is_defined_in, lasts_defined.
    split; intros.
    - simpl_Exists. solve_In. now apply Is_defined_in_last_defined.
    - simpl_In. solve_Exists. now apply Is_defined_in_last_defined.
  Qed.

  Lemma Is_defined_in_cons:
    forall x eq eqs,
      Is_defined_in x (eq :: eqs) ->
      Is_defined_in_eq x eq
      \/ (~Is_defined_in_eq x eq /\ Is_defined_in x eqs).
  Proof.
    intros x eq eqs Hdef.
    apply List.Exists_cons in Hdef.
    destruct (Is_defined_in_eq_dec x eq); intuition.
  Qed.

  (* TODO *)
  (* Lemma In_memory_eq_In_defined_eq: *)
  (*   forall x eq S, *)
  (*     PS.In x (memory_eq S eq) *)
  (*     -> PS.In x (defined_eq S eq). *)
  (* Proof. *)
  (*   intros x eq S HH. *)
  (*   destruct eq; *)
  (*     match goal with *)
  (*     | |- context[ EqApp _ _ _ _ _ ] => *)
  (*       generalize ps_adds_spec; intro add_spec *)
  (*     | _ => *)
  (*       generalize PS.add_spec; intro add_spec *)
  (*     end; *)
  (*     try (apply add_spec; now intuition). *)
  (*   apply add_spec in HH. *)
  (*   destruct HH as [HH|HH]. *)
  (*   - rewrite HH; apply add_spec; left; reflexivity. *)
  (*   - apply add_spec; right; exact HH. *)
  (* Qed. *)

  (* Lemma In_fold_left_memory_eq_defined_eq: *)
  (*   forall x eqs S, *)
  (*     PS.In x (List.fold_left memory_eq eqs S) *)
  (*     -> PS.In x (List.fold_left defined_eq eqs S). *)
  (* Proof. *)
  (*   intros x eqs. *)
  (*   induction eqs as [|eq eqs IH]; [now intuition|]. *)
  (*   intros S HH. *)
  (*   apply IH in HH; clear IH. *)
  (*   apply In_fold_left_defined_eq in HH. *)
  (*   simpl. apply In_fold_left_defined_eq. *)
  (*   destruct HH as [HH|HH]. *)
  (*   - left; exact HH. *)
  (*   - right; now apply In_memory_eq_In_defined_eq with (1:=HH). *)
  (* Qed. *)

  Lemma Is_defined_in_In:
    forall x eqs,
      Is_defined_in x eqs ->
      exists eq, In eq eqs /\ Is_defined_in_eq x eq.
  Proof.
    intros * Def.
    apply Exists_exists in Def; auto.
  Qed.

  Lemma node_output_defined_in_eqs:
    forall n x,
      In x (map fst n.(n_out)) ->
      Is_defined_in (Var x) n.(n_eqs).
  Proof.
    intros * Ho.
    apply Is_defined_in_vars_defined.
    rewrite n_defd. apply in_or_app; auto.
  Qed.

End ISDEFINED.

Module IsDefinedFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS        Ids Op OpAux)
       (CESyn : CESYNTAX      Ids Op OpAux Cks)
       (Syn   : NLSYNTAX Ids  Op OpAux Cks CESyn)
       (Mem   : MEMORIES Ids  Op OpAux Cks CESyn Syn)
       <: ISDEFINED Ids Op OpAux Cks CESyn Syn Mem.
  Include ISDEFINED Ids Op OpAux Cks CESyn Syn Mem.
End IsDefinedFun.
