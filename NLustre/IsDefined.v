Require Import PArith.
Require Import Omega.
Require Import List.

Import List.ListNotations.
Open Scope list_scope.

Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.CoreExpr.CESyntax.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.Memories.

(** * Defined variables *)

(**

  The [Is_defined_in] predicate identifies the variables defined by a
  set of equations.

 *)

Module Type ISDEFINED
       (Ids            : IDS)
       (Op             : OPERATORS)
       (Import CESyn   : CESYNTAX     Op)
       (Import Syn     : NLSYNTAX Ids Op CESyn)
       (Import Mem     : MEMORIES Ids Op CESyn Syn).

  (** ** Logical predicates: *)

  Inductive Is_defined_in_eq : ident -> equation -> Prop :=
  | DefEqDef:
      forall x ck e,
        Is_defined_in_eq x (EqDef x ck e)
  | DefEqApp:
      forall x xs ck f e r,
        In x xs ->
        Is_defined_in_eq x (EqApp xs ck f e r)
  | DefEqFby:
      forall x ck v e,
        Is_defined_in_eq x (EqFby x ck v e).

  (* definition is needed in signature *)
  Definition Is_defined_in_eqs (x: ident) (eqs: list equation) : Prop :=
    List.Exists (Is_defined_in_eq x) eqs.


  (** ** Properties *)

  Hint Constructors Is_defined_in_eq.

  Lemma not_Is_defined_in_eq_EqDef:
    forall x i ck ce,
      ~ Is_defined_in_eq x (EqDef i ck ce) -> x <> i.
  Proof.
    intros x i ck ce H0 xeqi.
    rewrite xeqi in H0.
    assert (Is_defined_in_eq i (EqDef i ck ce)) by auto.
    contradiction.
  Qed.

  Lemma not_Is_defined_in_eq_EqApp:
    forall x ys ck f le r,
      ~ Is_defined_in_eq x (EqApp ys ck f le r) -> ~ List.In x ys.
  Proof.
    intros * H. intro.
    exfalso. apply H. auto.
  Qed.

  Lemma Is_defined_in_EqApp:
    forall xs ck f es r d,
      0 < length xs ->
      Is_defined_in_eq (hd d xs) (EqApp xs ck f es r).
  Proof.
    intros * Length.
    constructor.
    destruct xs; simpl in *; auto; omega.
  Qed.

  Lemma not_Is_defined_in_eq_EqFby:
    forall x i ck v0 le,
      ~ Is_defined_in_eq x (EqFby i ck v0 le) -> x <> i.
  Proof.
    intros x i ck v0 le H0 xeqi.
    rewrite xeqi in H0.
    assert (Is_defined_in_eq i (EqFby i ck v0 le)) by auto.
    contradiction.
  Qed.

  Lemma not_Is_defined_in_cons:
    forall x eq eqs,
      ~Is_defined_in_eqs x (eq :: eqs)
      <-> ~Is_defined_in_eq x eq /\ ~Is_defined_in_eqs x eqs.
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
      PS.In x (memory_eq S eq)
      -> Is_defined_in_eq x eq \/ PS.In x S.
  Proof.
    intros x eq S.
    destruct eq; simpl; intro HH; try intuition.
    apply PS.add_spec in HH; intuition.
    subst; left; constructor.
  Qed.

  Corollary In_memory_eq_Is_defined_eq:
    forall x eq,
      PS.In x (memory_eq PS.empty eq)
      -> Is_defined_in_eq x eq.
  Proof.
    intros.
    cut (Is_defined_in_eq x eq \/ PS.In x PS.empty).
    intro His_def; destruct His_def; auto; not_In_empty.
    apply In_memory_eq_In_defined_eq_gen; auto.
  Qed.

  Lemma Is_defined_in_memories:
    forall x eqs,
      PS.In x (memories eqs) -> Is_defined_in_eqs x eqs.
  Proof.
    unfold memories, Is_defined_in_eqs.
    induction eqs.
    - simpl; intro; not_In_empty.
    - intro HH; simpl in HH.
      apply In_fold_left_memory_eq in HH.
      rewrite List.Exists_cons.
      destruct HH as [HH|HH].
      + right; now apply IHeqs with (1:=HH).
      + left.
        apply In_memory_eq_Is_defined_eq in HH; auto.
  Qed.

  Lemma In_EqFby_Is_defined_in_eqs:
    forall x ck c0 e eqs,
      In (EqFby x ck c0 e) eqs ->
      Is_defined_in_eqs x eqs.
  Proof.
    induction eqs; inversion_clear 1; subst.
    now repeat constructor.
    constructor 2; intuition.
  Qed.

  Lemma Is_defined_in_vars_defined:
    forall x eqs,
      Is_defined_in_eqs x eqs ->
      In x (vars_defined eqs).
  Proof.
    induction eqs as [|eq eqs]; inversion_clear 1;
      unfold vars_defined; simpl; apply in_app.
    - left. inv H0; simpl; auto.
    - intuition.
  Qed.

  (** ** Decision procedures: *)

  Fixpoint defined_eq (defs: PS.t) (eq: equation) {struct eq} : PS.t :=
    match eq with
    | EqDef x _ _   => PS.add x defs
    | EqApp xs _ _ _ _ => ps_adds xs defs
    | EqFby x _ _ _ => PS.add x defs
    end.

  Definition defined (eqs: list equation) : PS.t :=
    List.fold_left defined_eq eqs PS.empty.

  (** ** Silly unfolding property: *)

  Lemma Subset_defined_eq:
    forall eq m1 m2,
      PS.Subset m1 m2 ->
      PS.Subset (defined_eq m1 eq) (defined_eq m2 eq).
  Proof.
    intros * Hsub.
    destruct eq; simpl.
    - apply PSP.subset_add_3, PSP.subset_add_2; try apply PS.add_spec; auto.
    - now apply Subset_ps_adds.
    - apply PSP.subset_add_3, PSP.subset_add_2; try apply PS.add_spec; auto.
  Qed.
  
  Lemma In_fold_left_defined_eq:
    forall x eqs m,
      PS.mem x (List.fold_left defined_eq eqs m) = true
      <-> PS.mem x (List.fold_left defined_eq eqs PS.empty) = true \/ PS.In x m.
  Proof.
    induction eqs as [|eq].
    - split; auto.
      destruct 1 as [H|]; auto.
      now apply not_In_empty in H; contradiction.
    - split.
      + intro H.
        simpl; rewrite IHeqs. setoid_rewrite IHeqs in H. clear IHeqs.
        destruct H as [H|H]; auto.
        destruct eq; simpl in *; try rewrite PS.add_spec in *;
          try rewrite ps_adds_spec in *; destruct H; auto.
      + simpl. setoid_rewrite IHeqs.
        destruct 1 as [[H|H]|H]; auto.
        rewrite <-Subset_defined_eq with (m1:=PS.empty);
          auto using PSP.subset_empty.
        right. destruct eq; simpl;
                 try apply PS.add_spec; try apply ps_adds_spec; auto.
  Qed.

  (** ** Reflection lemmas: *)

  Lemma Is_defined_in_eqP :
    forall x eq, Is_defined_in_eq x eq <-> PS.mem x (defined_eq PS.empty eq) = true.
  Proof.
  intros x eq; split; [ intro Hdef | intro Hmem].
  - (* ==> *)
    destruct Hdef; simpl;
    match goal with
    | |- context[ PS.mem ?x (PS.add ?x _) ] =>
      now rewrite PSE.add_mem_1
    | |- context[ PS.mem _ (ps_adds _ _) ] =>
      now apply PS.mem_spec, ps_adds_spec; auto
    end.
  - (* <== *)
    destruct eq; simpl in *;
    match goal with
    | |- context[ EqApp _ _ _ _ _ ] =>
      edestruct (in_dec ident_eq_dec) as [Hin_xys | Hnin_xys];
        [ eauto using Is_defined_in_eq
        | exfalso;
          apply ps_adds_spec in Hmem as [Hmem | Hmem]; auto;
          eapply not_In_empty; eauto ]
    | _ =>
      destruct (ident_eq_dec i x) eqn:Hxi;
        [ subst; auto using Is_defined_in_eq
        | exfalso;
          rewrite PSP.Dec.F.add_neq_b, PSF.empty_b in Hmem; auto;
          discriminate ]
    end.
  Qed.

  Lemma Is_defined_inP:
    forall x eqs,
      Is_defined_in_eqs x eqs <-> PS.mem x (defined eqs) = true.
  Proof.
    unfold defined, Is_defined_in_eqs.
    induction eqs as [ | eq ].
    - rewrite List.Exists_nil; split; intro H;
      try apply not_In_empty in H; contradiction.
    - simpl;
        rewrite In_fold_left_defined_eq, PS.mem_spec.
      split.
      + (* ==> *)
        intro H; apply List.Exists_cons in H; destruct H.
        inversion H; destruct eq;
          match goal with
          | |- context[ EqApp _ _ _ _ _ ] =>
            generalize ps_adds_spec; intro add_spec
          | _ =>
            generalize PS.add_spec; intro add_spec
          end;
          (right; apply add_spec; intuition).
        left; apply IHeqs; apply H.
      + (* <== *)
        rewrite List.Exists_cons.
        destruct 1.
        * now intuition.
        * destruct eq;
            match goal with
            | |- context[ EqApp _ _ _ _ _ ] =>
              generalize ps_adds_spec; intro add_spec
            | _ =>
              generalize PS.add_spec; intro add_spec
            end;
          (simpl in H; apply add_spec in H; destruct H;
           [ try rewrite H; left; constructor; auto
           | apply not_In_empty in H; contradiction]).

  Qed.

  Lemma Is_defined_in_eq_dec:
    forall x eq, {Is_defined_in_eq x eq}+{~Is_defined_in_eq x eq}.
  Proof.
    intros;
      eapply Bool.reflect_dec,
             Bool.iff_reflect,
             Is_defined_in_eqP.
  Qed.

  Lemma Is_defined_in_dec:
    forall x eqs, {Is_defined_in_eqs x eqs}+{~Is_defined_in_eqs x eqs}.
  Proof.
    intros;
      eapply Bool.reflect_dec,
             Bool.iff_reflect,
             Is_defined_inP.
  Qed.


  Lemma decidable_Is_defined_in_eqs:
    forall x eqs,
      Decidable.decidable (Is_defined_in_eqs x eqs).
  Proof.
    intros. apply decidable_Exists.
    intros eq Hin.
    destruct (Is_defined_in_eq_dec x eq); [left|right]; auto.
  Qed.

  (** ** Properties *)

  Lemma Is_defined_in_eqs_var_defined:
    forall x eq,
      Is_defined_in_eq x eq <-> List.In x (var_defined eq).
  Proof.
  intros; rewrite Is_defined_in_eqP, PS.mem_spec.

  destruct eq; simpl;
    rewrite ?PSF.add_iff, ?ps_adds_spec, PSF.empty_iff;
    intuition.
  Qed.

  Lemma Is_defined_in_var_defined:
    forall x eqs,
      Is_defined_in_eqs x eqs
      <-> In x (vars_defined eqs).
  Proof.
  intros; rewrite Is_defined_inP, PS.mem_spec.
  induction eqs as [ | eq eqs IHeqs ]; simpl.
  - now rewrite PSF.empty_iff.
  - destruct eq; rewrite <- PS.mem_spec; unfold defined; simpl.
    + rewrite In_fold_left_defined_eq, PSF.add_iff, PSF.empty_iff, IHeqs; tauto.
    + unfold vars_defined; simpl;
        rewrite in_app, In_fold_left_defined_eq, ps_adds_spec,
        PSF.empty_iff, IHeqs; tauto.
    + rewrite In_fold_left_defined_eq, PSF.add_iff, PSF.empty_iff, IHeqs; tauto.
  Qed.

  Lemma Is_defined_in_cons:
    forall x eq eqs,
      Is_defined_in_eqs x (eq :: eqs) ->
      Is_defined_in_eq x eq
      \/ (~Is_defined_in_eq x eq /\ Is_defined_in_eqs x eqs).
  Proof.
    intros x eq eqs Hdef.
    apply List.Exists_cons in Hdef.
    destruct (Is_defined_in_eq_dec x eq); intuition.
  Qed.

  Lemma In_memory_eq_In_defined_eq:
    forall x eq S,
      PS.In x (memory_eq S eq)
      -> PS.In x (defined_eq S eq).
  Proof.
    intros x eq S HH.
    destruct eq;
      match goal with
      | |- context[ EqApp _ _ _ _ _ ] =>
        generalize ps_adds_spec; intro add_spec
      | _ =>
        generalize PS.add_spec; intro add_spec
      end;
      try (apply add_spec; now intuition).
    apply add_spec in HH.
    destruct HH as [HH|HH].
    - rewrite HH; apply add_spec; left; reflexivity.
    - apply add_spec; right; exact HH.
  Qed.

  Lemma In_fold_left_memory_eq_defined_eq:
    forall x eqs S,
      PS.In x (List.fold_left memory_eq eqs S)
      -> PS.In x (List.fold_left defined_eq eqs S).
  Proof.
    intros x eqs.
    induction eqs as [|eq eqs IH]; [now intuition|].
    intros S HH.
    apply IH in HH; clear IH.
    apply In_fold_left_defined_eq in HH.
    simpl. apply In_fold_left_defined_eq.
    destruct HH as [HH|HH].
    - left; exact HH.
    - right; now apply In_memory_eq_In_defined_eq with (1:=HH).
  Qed.

  Lemma not_Exists_Is_defined_in_eqs_n_in:
    forall n,
      ~Exists (fun ni=>Is_defined_in_eqs ni n.(n_eqs)) (map fst n.(n_in)).
  Proof.
    intros n HH.
    rewrite Exists_map in HH.
    apply decidable_Exists_not_Forall in HH.
    2:(intros; apply decidable_Is_defined_in_eqs).
    apply HH. clear HH.
    apply Forall_forall.
    intros x Hin.
    rewrite Is_defined_in_var_defined.
    rewrite n.(n_defd).
    destruct x as [x xty].
    apply In_InMembers in Hin.
    rewrite <-fst_InMembers. simpl.
    apply (NoDupMembers_app_InMembers _ _ _ n.(n_nodup) Hin).
  Qed.

  Lemma Is_defined_in_eqs_In:
    forall x eqs,
      Is_defined_in_eqs x eqs ->
      exists eq, In eq eqs /\ Is_defined_in_eq x eq.
  Proof.
    induction eqs as [|eq]. now inversion 1.
    inversion_clear 1 as [? ? Hdef|? ? Hex].
    - exists eq; split; auto with datatypes.
    - apply Exists_exists in Hex as (eq' & Hin & Hdef).
      exists eq'; split; auto with datatypes.
  Qed.


  Lemma node_output_defined_in_eqs:
    forall n x,
      In x (map fst n.(n_out)) ->
      Is_defined_in_eqs x n.(n_eqs).
  Proof.
    intros n x Ho.
    cut (In x (map fst (n.(n_vars) ++ n.(n_out)))).
    - intro Hvo. rewrite <-n_defd in Hvo.
      now apply Is_defined_in_var_defined.
    - rewrite map_app. apply in_or_app. now right.
  Qed.

  Lemma node_variable_defined_in_eqs:
    forall n x,
      In x (map fst n.(n_vars)) ->
      Is_defined_in_eqs x n.(n_eqs).
  Proof.
    intros n x Ho.
    cut (In x (map fst (n.(n_vars) ++ n.(n_out)))).
    - intro Hvo. rewrite <-n_defd in Hvo.
      now apply Is_defined_in_var_defined.
    - rewrite map_app. apply in_or_app. now left.
  Qed.

End ISDEFINED.

Module IsDefinedFun
       (Ids     : IDS)
       (Op      : OPERATORS)
       (CESyn   : CESYNTAX     Op)
       (Syn     : NLSYNTAX Ids Op CESyn)
       (Mem     : MEMORIES Ids Op CESyn Syn)
       <: ISDEFINED Ids Op CESyn Syn Mem.
  Include ISDEFINED Ids Op CESyn Syn Mem.
End IsDefinedFun.
