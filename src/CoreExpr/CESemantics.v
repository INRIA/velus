From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Setoid.
From Coq Require Import Morphisms.

From Velus Require Import Common.
From Velus Require Import FunctionalEnvironment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import VelusMemory.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import IndexedStreams.


Module Type CESEMANTICS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX  Ids Op)
       (Import Cks   : CLOCKS         Ids Op OpAux)
       (Import Syn   : CESYNTAX       Ids Op OpAux Cks)
       (Import Str   : INDEXEDSTREAMS Ids Op OpAux Cks).

  (** ** FEnvironment and history *)

  (**

An history maps variables to streams of values (the variables'
histories). Taking a snapshot of the history at a given time yields an
environment.

   *)

  Definition env := FEnv.t svalue.
  Definition history := stream env.

  (** ** Instantaneous semantics *)

  Section InstantSemantics.

    Variable base: bool.
    Variable R: env.

    Definition sem_vars_instant (xs: list ident) (vs: list svalue) : Prop :=
      Forall2 (sem_var_instant R) xs vs.

    Definition sem_clocked_var_instant (x: ident) (ck: clock) : Prop :=
      (sem_clock_instant base R ck true <-> exists c, sem_var_instant R x (present c))
      /\ (sem_clock_instant base R ck false <-> sem_var_instant R x absent).

    Definition sem_clocked_vars_instant (xs: list (ident * clock)) : Prop :=
      Forall (fun xc => sem_clocked_var_instant (fst xc) (snd xc)) xs.

    Inductive sem_exp_instant: exp -> svalue -> Prop:=
    | Sconst:
        forall c v,
          v = (if base then present (Vscalar (sem_cconst c)) else absent) ->
          sem_exp_instant (Econst c) v
    | Senum:
        forall x v ty,
          v = (if base then present (Venum x) else absent) ->
          sem_exp_instant (Eenum x ty) v
    | Svar:
        forall x v ty,
          sem_var_instant R x v ->
          sem_exp_instant (Evar x ty) v
    | Swhen_eq:
        forall s x tx sc b,
          sem_var_instant R x (present (Venum b)) ->
          sem_exp_instant s (present sc) ->
          sem_exp_instant (Ewhen s (x, tx) b) (present sc)
    | Swhen_abs1:
        forall s x tx sc b b',
          sem_var_instant R x (present (Venum b')) ->
          b <> b' ->
          sem_exp_instant s (present sc) ->
          sem_exp_instant (Ewhen s (x, tx) b) absent
    | Swhen_abs:
        forall s x tx b,
          sem_var_instant R x absent ->
          sem_exp_instant s absent ->
          sem_exp_instant (Ewhen s (x, tx) b) absent
    | Sunop_eq:
        forall le op v v' ty,
          sem_exp_instant le (present v) ->
          sem_unop op v (typeof le) = Some v' ->
          sem_exp_instant (Eunop op le ty) (present v')
    | Sunop_abs:
        forall le op ty,
          sem_exp_instant le absent ->
          sem_exp_instant (Eunop op le ty) absent
    | Sbinop_eq:
        forall le1 le2 op v1 v2 v' ty,
          sem_exp_instant le1 (present v1) ->
          sem_exp_instant le2 (present v2) ->
          sem_binop op v1 (typeof le1) v2 (typeof le2) = Some v' ->
          sem_exp_instant (Ebinop op le1 le2 ty) (present v')
    | Sbinop_abs:
        forall le1 le2 op ty,
          sem_exp_instant le1 absent ->
          sem_exp_instant le2 absent ->
          sem_exp_instant (Ebinop op le1 le2 ty) absent.

    Definition sem_exps_instant (les: list exp) (vs: list svalue) :=
      Forall2 sem_exp_instant les vs.

    Inductive sem_cexp_instant: cexp -> svalue -> Prop :=
    | Smerge_pres:
        forall x tx es ty b es1 e es2 c,
          sem_var_instant R x (present (Venum b)) ->
          es = es1 ++ e :: es2 ->
          length es1 = b ->
          sem_cexp_instant e (present c) ->
          Forall (fun e => sem_cexp_instant e absent) (es1 ++ es2) ->
          sem_cexp_instant (Emerge (x, tx) es ty) (present c)
    | Smerge_abs:
        forall x tx es ty,
          sem_var_instant R x absent ->
          Forall (fun e => sem_cexp_instant e absent) es ->
          sem_cexp_instant (Emerge (x, tx) es ty) absent
    | Scase_pres:
        forall e es d b vs c,
          sem_exp_instant e (present (Venum b)) ->
          Forall2 (fun e v => sem_cexp_instant (or_default d e) (present v)) es vs ->
          nth_error vs b = Some c ->
          sem_cexp_instant (Ecase e es d) (present c)
    | Scase_abs:
        forall e es d,
          sem_exp_instant e absent ->
          Forall (fun e => sem_cexp_instant (or_default d e) absent) es ->
          sem_cexp_instant (Ecase e es d) absent
    | Sexp:
        forall e v,
          sem_exp_instant e v ->
          sem_cexp_instant (Eexp e) v.

    Inductive sem_rhs_instant: rhs -> svalue -> Prop :=
    | Sextcall_pres:
      forall f es tyout tyins vs v,
        Forall2 (fun e ty => typeof e = Tprimitive ty) es tyins ->
        Forall2 (fun e v => sem_exp_instant e (present (Vscalar v))) es vs ->
        sem_extern f tyins vs tyout v ->
        sem_rhs_instant (Eextcall f es tyout) (present (Vscalar v))
    | Sextcall_abs:
      forall f es tyout tyins,
        Forall2 (fun e ty => typeof e = Tprimitive ty) es tyins ->
        Forall (fun e => sem_exp_instant e absent) es ->
        sem_rhs_instant (Eextcall f es tyout) absent
    | Scexp:
      forall e v,
        sem_cexp_instant e v ->
        sem_rhs_instant (Ecexp e) v.

  End InstantSemantics.

  Global Hint Constructors sem_exp_instant sem_cexp_instant : nlsem stcsem.

  Section sem_cexp_instant_ind_2.

    Variable base: bool.
    Variable R: env.

    Variable P : cexp -> svalue -> Prop.

    Hypothesis merge_presCase:
      forall x tx es ty b es1 e es2 c,
        sem_var_instant R x (present (Venum b)) ->
        es = es1 ++ e :: es2 ->
        length es1 = b ->
        sem_cexp_instant base R e (present c) ->
        P e (present c) ->
        Forall (fun e => sem_cexp_instant base R e absent) (es1 ++ es2) ->
        Forall (fun e => P e absent) (es1 ++ es2) ->
        P (Emerge (x, tx) es ty) (present c).

    Hypothesis merge_absCase:
      forall x tx es ty,
        sem_var_instant R x absent ->
        Forall (fun e => sem_cexp_instant base R e absent) es ->
        Forall (fun e => P e absent) es ->
        P (Emerge (x, tx) es ty) absent.

    Hypothesis case_presCase:
      forall e es d b vs c,
        sem_exp_instant base R e (present (Venum b)) ->
        Forall2 (fun e v => sem_cexp_instant base R (or_default d e) (present v)) es vs ->
        Forall2 (fun e v => P (or_default d e) (present v)) es vs ->
        nth_error vs b = Some c ->
        P (Ecase e es d) (present c).

    Hypothesis case_absCase:
      forall e es d,
        sem_exp_instant base R e absent ->
        Forall (fun e => sem_cexp_instant base R (or_default d e) absent) es ->
        Forall (fun e => P (or_default d e) absent) es ->
        P (Ecase e es d) absent.

    Hypothesis expCase:
      forall e v,
        sem_exp_instant base R e v ->
        P (Eexp e) v.

    Fixpoint sem_cexp_instant_ind_2
             (ce: cexp) (v: svalue)
             (Sem: sem_cexp_instant base R ce v) {struct Sem}
      : P ce v.
    Proof.
      inv Sem.
      - eapply merge_presCase; eauto.
        clear - H3 sem_cexp_instant_ind_2.
        induction H3; constructor; auto.
      - apply merge_absCase; auto.
        induction H0; constructor; auto.
      - eapply case_presCase; eauto.
        take (nth_error _ _ = _) and clear it.
        induction H0; constructor; auto.
      - apply case_absCase; auto.
        induction H0; constructor; auto.
      - apply expCase; auto.
    Defined.

  End sem_cexp_instant_ind_2.

  Global Hint Extern 4 (sem_exps_instant _ _ nil nil) => apply Forall2_nil : nlsem stcsem.

  Section InstantAnnotatedSemantics.

    Variable base : bool.
    Variable R: env.

    Inductive sem_annotated_instant {A}
              (sem_instant: bool -> env -> A -> svalue -> Prop)
      : clock -> A -> svalue -> Prop :=
    | Stick:
        forall ck a c,
          sem_instant base R a (present c) ->
          sem_clock_instant base R ck true ->
          sem_annotated_instant sem_instant ck a (present c)
    | Sabs:
        forall ck a,
          sem_instant base R a absent ->
          sem_clock_instant base R ck false ->
          sem_annotated_instant sem_instant ck a absent.

    Definition sem_aexp_instant := sem_annotated_instant sem_exp_instant.
    Definition sem_caexp_instant := sem_annotated_instant sem_cexp_instant.
    Definition sem_arhs_instant := sem_annotated_instant sem_rhs_instant.

  End InstantAnnotatedSemantics.

  (** ** Liftings of instantaneous semantics *)

  Section LiftSemantics.

    Variable bk : stream bool.
    Variable H : history.

    Definition sem_vars (x: list ident) (xs: stream (list svalue)): Prop :=
      lift' H sem_vars_instant x xs.

    Definition sem_clocked_var (x: ident) (ck: clock): Prop :=
      forall n, sem_clocked_var_instant (bk n) (H n) x ck.

    Definition sem_clocked_vars (xs: list (ident * clock)) : Prop :=
      forall n, sem_clocked_vars_instant (bk n) (H n) xs.

    Definition sem_aexp ck (e: exp) (xs: stream svalue): Prop :=
      lift bk H (fun base R => sem_aexp_instant base R ck) e xs.

    Definition sem_exp (e: exp) (xs: stream svalue): Prop :=
      lift bk H sem_exp_instant e xs.

    Definition sem_exps (e: list exp) (xs: stream (list svalue)): Prop :=
      lift bk H sem_exps_instant e xs.

    Definition sem_caexp ck (c: cexp) (xs: stream svalue): Prop :=
      lift bk H (fun base R => sem_caexp_instant base R ck) c xs.

    Definition sem_cexp (c: cexp) (xs: stream svalue): Prop :=
      lift bk H sem_cexp_instant c xs.

    Definition sem_arhs ck (c: rhs) (xs: stream svalue) : Prop :=
      lift bk H (fun base R => sem_arhs_instant base R ck) c xs.

    Definition sem_rhs (c: rhs) (xs: stream svalue): Prop :=
      lift bk H sem_rhs_instant c xs.

  End LiftSemantics.

  (** ** Time-dependent semantics *)

  Definition clock_of_instant (vs: list svalue) : bool :=
    existsb (fun v => v <>b absent) vs.

  Lemma clock_of_instant_false:
    forall xs,
      clock_of_instant xs = false <-> absent_list xs.
  Proof.
    unfold absent_list.
    induction xs; simpl.
    - constructor; constructor.
    - rewrite Bool.orb_false_iff, Forall_cons2, IHxs, nequiv_decb_false, equiv_decb_equiv;
        intuition.
  Qed.

  Lemma clock_of_instant_true:
    forall xs,
      clock_of_instant xs = true <-> Exists (fun v => v <> absent) xs.
  Proof.
    induction xs; simpl.
    - split; inversion 1.
    - rewrite Bool.orb_true_iff, Exists_cons, IHxs, <-not_absent_bool; reflexivity.
  Qed.

  Definition clock_of (xss: stream (list svalue)): stream bool :=
    fun n => clock_of_instant (xss n).

  (* Definition bools_of (vs: stream svalue) (rs: stream bool) := *)
  (*   forall n, svalue_to_bool (vs n) = Some (rs n). *)

  (** Morphisms properties *)

  Add Parametric Morphism : sem_exp_instant
      with signature @eq _ ==> FEnv.Equiv eq ==> @eq _ ==> @eq _ ==> Basics.impl
        as sem_exp_instant_morph.
  Proof.
    intros b H H' EH x.
    induction x; intros * Hsem; inv Hsem.
    4:eapply Swhen_eq; eauto.
    6:eapply Swhen_abs1; eauto.
    8:eapply Swhen_abs; eauto.
    1-3,10-13:econstructor; eauto.
    1,8,10,12:rewrite <-EH; eauto.
    1-9:try eapply IHx; eauto.
    1-4:try eapply IHx1; eauto.
    1-2:eapply IHx2; eauto.
  Qed.

  Add Parametric Morphism : sem_cexp_instant
      with signature @eq _ ==> FEnv.Equiv eq ==> @eq _ ==> @eq _ ==> Basics.impl
        as sem_cexp_instant_morph.
  Proof.
    intros b H H' EH x.
    induction x using cexp_ind2; intros * Hsem; inv Hsem.
    1:eapply Smerge_pres; eauto.
    4:eapply Smerge_abs; eauto.
    6:eapply Scase_pres; eauto.
    8:eapply Scase_abs; eauto.
    10:econstructor.
    1,4,6,8,10:erewrite <-EH; eauto.
    - eapply Forall_forall in H0. eapply H0; eauto.
      auto with datatypes.
    - eapply Forall_impl_In; [|eauto]. intros ? Hin Hsem.
      eapply Forall_forall in H0. eapply H0; eauto.
      apply in_app in Hin as [?|?]; auto with datatypes.
    - rewrite Forall_forall in *. intros ? Hin.
      eapply H0; eauto.
    - eapply Forall2_impl_In; [|eauto]. intros.
      eapply Forall_forall in H0; eauto. eapply H0; eauto.
    - rewrite Forall_forall in *. intros. eapply H0; eauto.
  Qed.

  Add Parametric Morphism : sem_rhs_instant
      with signature @eq _ ==> FEnv.Equiv eq ==> @eq _ ==> @eq _ ==> Basics.impl
        as sem_rhs_instant_morph.
  Proof.
    intros b H H' EH xs xs' Sem; inv Sem; econstructor; eauto; simpl_Forall.
    all:rewrite <-EH; auto.
  Qed.

  Add Parametric Morphism A sem
    (sem_compat: Proper (eq ==> FEnv.Equiv eq ==> eq ==> eq ==> Basics.impl) sem)
    : (fun b e => @sem_annotated_instant b e A sem)
      with signature eq ==> FEnv.Equiv eq ==> eq ==> eq ==> eq ==> Basics.impl
        as sem_annotated_instant_morph.
  Proof.
    intros b H H' EH ck e v Sem.
    inv Sem; constructor; auto.
    1,3:rewrite <-EH; auto.
    1,2:rewrite <-EH; auto.
  Qed.

  Add Parametric Morphism : sem_aexp_instant
      with signature eq ==> FEnv.Equiv eq ==> eq ==> eq ==> eq ==> Basics.impl
        as sem_aexp_instant_morph.
  Proof.
    intros; eapply sem_annotated_instant_morph; eauto.
    solve_proper.
  Qed.

  Add Parametric Morphism : sem_caexp_instant
      with signature eq ==> FEnv.Equiv eq ==> eq ==> eq ==> eq ==> Basics.impl
        as sem_caexp_morph.
  Proof.
    intros; eapply sem_annotated_instant_morph; eauto.
    solve_proper.
  Qed.

  Add Parametric Morphism A B H sem e: (fun b xs => @lift b H A B sem e xs)
      with signature eq_str ==> @eq_str B ==> Basics.impl
        as lift_eq_str.
  Proof.
    intros ?? E ?? E' Lift n.
    rewrite <-E, <-E'; auto.
  Qed.

  Add Parametric Morphism A B sem H e: (@lift' H A B sem e)
      with signature @eq_str B ==> Basics.impl
        as lift'_eq_str.
  Proof.
    intros * E Lift n.
    rewrite <-E; auto.
  Qed.

  (* Add Parametric Morphism : (sem_aexp) *)
  Add Parametric Morphism : clock_of
      with signature eq_str ==> eq_str
        as clock_of_eq_str.
  Proof.
    unfold clock_of. intros * E n.
    rewrite E; auto.
  Qed.

  Add Parametric Morphism : (sem_clocked_var)
      with signature eq_str ==> eq ==> eq ==> eq ==> Basics.impl
        as sem_clocked_var_eq_str.
  Proof.
    intros * E ??? Sem n.
    rewrite <-E; auto.
  Qed.

  Add Parametric Morphism : (sem_clocked_vars)
      with signature eq_str ==> eq ==> eq ==> Basics.impl
        as sem_clocked_vars_eq_str.
  Proof.
    intros * E ?? Sem n.
    rewrite <-E; auto.
  Qed.

  Lemma not_subrate_clock:
    forall R ck,
      ~ sem_clock_instant false R ck true.
  Proof.
    intros * Sem; induction ck; inv Sem.
    now apply IHck.
  Qed.

  Corollary not_subrate_clock_impl:
    forall R ck b,
      sem_clock_instant false R ck b ->
      b = false.
  Proof.
    intros * Sem.
    destruct b; auto.
    contradict Sem; apply not_subrate_clock.
  Qed.

  Lemma sem_vars_gt0:
    forall H (xs: list (ident * type)) ls,
      0 < length xs ->
      sem_vars H (map fst xs) ls ->
      forall n, 0 < length (ls n).
  Proof.
    intros * Hgt0 Hsem n.
    specialize (Hsem n).
    apply Forall2_length in Hsem.
    rewrite map_length in Hsem.
    now rewrite Hsem in Hgt0.
  Qed.

  Lemma sem_arhs_instant_absent:
    forall R ck e v,
      sem_arhs_instant false R ck e v ->
      v = absent.
  Proof.
    inversion_clear 1; auto.
    exfalso; eapply not_subrate_clock; eauto.
  Qed.

  Ltac assert_const_length xss :=
    match goal with
      H: sem_vars _ _ xss |- _ =>
      let H' := fresh in
      let k := fresh in
      let k' := fresh in
      assert (wf_streams xss)
        by (intros k k'; pose proof H as H';
            unfold sem_vars, lift in *;
            specialize (H k); specialize (H' k');
            apply Forall2_length in H; apply Forall2_length in H';
            now rewrite H in H')
    end.

  Lemma sem_exps_instant_cons:
    forall b R e es v vs,
      sem_exps_instant b R (e :: es) (v :: vs)
      <-> (sem_exp_instant b R e v /\ sem_exps_instant b R es vs).
  Proof.
    intros. unfold sem_exps_instant. now setoid_rewrite Forall2_cons'.
  Qed.

  (** ** Determinism of the semantics *)

  (** *** Instantaneous semantics *)

  Section InstantDeterminism.

    Variable base: bool.
    Variable R: env.

    Lemma sem_exp_instant_det:
      forall e v1 v2,
        sem_exp_instant base R e v1
        -> sem_exp_instant base R e v2
        -> v1 = v2.
    Proof.
      induction e (* using exp_ind2 *);
        try now (do 2 inversion_clear 1);
        match goal with
        | H1:sem_var_instant ?R ?e (present ?b1),
             H2:sem_var_instant ?R ?e (present ?b2),
                H3: ?b1 <> ?b2 |- _ =>
          exfalso; apply H3;
            cut (present (Vbool b1) = present (Vbool b2)); [now injection 1|];
              eapply sem_var_instant_det; eassumption
        | H1:sem_var_instant ?R ?e ?v1,
             H2:sem_var_instant ?R ?e ?v2 |- ?v1 = ?v2 =>
          eapply sem_var_instant_det; eassumption
        | H1:sem_var_instant ?R ?e (present _),
             H2:sem_var_instant ?R ?e absent |- _ =>
          apply (sem_var_instant_det _ _ _ _ H1) in H2;
            discriminate
        | _ => auto
        end.
      - (* Econst *)
        do 2 inversion_clear 1; destruct base; congruence.
      - (* Eenum *)
        do 2 inversion_clear 1; destruct base; congruence.
      - (* Ewhen *)
        intros v1 v2 Hsem1 Hsem2. destruct_conjs.
        inversion Hsem1; inversion Hsem2; subst;
          repeat match goal with
                 | H1:sem_exp_instant ?b ?R ?e ?v1,
                      H2:sem_exp_instant ?b ?R ?e ?v2 |- _ =>
                   apply IHe with (1:=H1) in H2
                 | H1:sem_var_instant ?R ?i ?v1,
                      H2:sem_var_instant ?R ?i ?v2 |- _ =>
                   apply sem_var_instant_det with (1:=H1) in H2
                 | H1:sem_unop _ _ _ = Some ?v1,
                      H2:sem_unop _ _ _ = Some ?v2 |- _ =>
                   rewrite H1 in H2; injection H2; intro; subst
                 | Hp:present _ = present _ |- _ =>
                   injection Hp; intro; subst
                 end; subst; try easy.
      - (* Eunop *)
        intros v1 v2 Hsem1 Hsem2.
        inversion_clear Hsem1; inversion_clear Hsem2;
          repeat match goal with
                 | H1:sem_exp_instant _ _ e _, H2:sem_exp_instant _ _ e _ |- _ =>
                   apply IHe with (1:=H1) in H2; inversion H2; subst
                 | H1:sem_unop _ _ _ = _, H2:sem_unop _ _ _ = _ |- _ =>
                   rewrite H1 in H2; injection H2; intro; subst
                 | H1:sem_exp_instant _ _ _ (present _),
                      H2:sem_exp_instant _ _ _ absent |- _ =>
                   apply IHe with (1:=H1) in H2
                 | H1: typeof ?e = _, H2: typeof ?e = _ |- _ => rewrite H1 in H2; inv H2
                 end; congruence.
      - (* Ebinop *)
        intros v1 v2 Hsem1 Hsem2.
        inversion_clear Hsem1; inversion_clear Hsem2;
          repeat match goal with
                 | H1:sem_exp_instant _ _ e1 _, H2:sem_exp_instant _ _ e1 _ |- _ =>
                   apply IHe1 with (1:=H1) in H2
                 | H1:sem_exp_instant _ _ e2 _, H2:sem_exp_instant _ _ e2 _ |- _ =>
                   apply IHe2 with (1:=H1) in H2
                 | H1:sem_binop _ _ _ _ _ = Some ?v1,
                      H2:sem_binop _ _ _ _ _ = Some ?v2 |- _ =>
                   rewrite H1 in H2; injection H2; intro; subst
                 | H:present _ = present _ |- _ => inv H
                 | H1: typeof ?e = _, H2: typeof ?e = _ |- _ => rewrite H1 in H2; inv H2
                 end; subst; congruence.
    Qed.

    Lemma sem_aexp_instant_det:
      forall ck e v1 v2,
        sem_aexp_instant base R ck e v1
        -> sem_aexp_instant base R ck e v2
        -> v1 = v2.
    Proof.
      intros ck e v1 v2.
      do 2 inversion_clear 1;
        match goal with
        | H1:sem_exp_instant _ _ _ _, H2:sem_exp_instant _ _ _ _ |- _ =>
          eapply sem_exp_instant_det; eassumption
        | H1:sem_clock_instant _ _ _ ?T, H2:sem_clock_instant _ _ _ ?F |- _ =>
          assert (T = F) by (eapply sem_clock_instant_det; eassumption);
            try discriminate
        end; auto.
    Qed.

    Lemma sem_exps_instant_det:
      forall les cs1 cs2,
        sem_exps_instant base R les cs1 ->
        sem_exps_instant base R les cs2 ->
        cs1 = cs2.
    Proof.
      intros les cs1 cs2. apply Forall2_det. apply sem_exp_instant_det.
    Qed.

  End InstantDeterminism.

  (* Strangely, the below lemma proof does not typecheck in the section... *)
  Lemma sem_cexp_instant_det:
    forall base R e v1,
      sem_cexp_instant base R e v1 ->
      forall v2,
        sem_cexp_instant base R e v2 ->
        v1 = v2.
  Proof.
    induction 1 using sem_cexp_instant_ind_2;
      inversion_clear 1;
      try repeat progress match goal with
                          | H1: sem_cexp_instant ?bk ?R ?e ?l,
                                H2: sem_cexp_instant ?bk ?R ?e ?r |- _ =>
                            assert (l = r) as E by auto; inv E; clear H1 H2
                          | H1: sem_var_instant ?R ?i (present _),
                                H2: sem_var_instant ?R ?i (present _) |- _ =>
                            apply sem_var_instant_det with (1:=H1) in H2; inv H2
                          | H1: sem_exp_instant ?bk ?R ?l ?v1,
                                H2: sem_exp_instant ?bk ?R ?l ?v2 |- _ =>
                            apply sem_exp_instant_det with (1:=H1) in H2;
                              discriminate || injection H2; intro; subst
                          | H1: sem_var_instant ?R ?i (present _),
                                H2: sem_var_instant ?R ?i absent |- _ =>
                            apply sem_var_instant_det with (1:=H1) in H2; discriminate
                          | H: ?l ++ _ :: _ = ?l' ++ _ :: _, H': length ?l = length ?l' |- _ =>
                            apply app_inv with (2 := H') in H as (?&E); inv E
                          end; auto.
    - assert (vs0 = vs).
      { repeat (take (nth_error _ _ = _) and clear it).
        revert dependent vs0.
        induction H0; intros; inv H1; inv H5; auto.
        f_equal; auto.
        assert (present y = present y0) as E by auto; inv E; auto.
      }
      subst.
      match goal with H: nth_error _ _ = _, H': nth_error _ _ = _ |- _ => rewrite H in H'; inv H' end.
      auto.
    - eapply sem_exp_instant_det; eassumption.
  Qed.

  Lemma sem_caexp_instant_det:
    forall base R ck e v1 v2,
      sem_caexp_instant base R ck e v1
      -> sem_caexp_instant base R ck e v2
      -> v1 = v2.
  Proof.
    intros until v2.
    do 2 inversion_clear 1;
         match goal with
         | H1: sem_cexp_instant _ _ _ _,
               H2: sem_cexp_instant _ _ _ _ |- _ =>
           eapply sem_cexp_instant_det; eassumption
         | H1:sem_clock_instant _ _ _ ?T,
              H2:sem_clock_instant _ _ _ ?F |- _ =>
           let H := fresh in
           assert (H: T = F) by (eapply sem_clock_instant_det; eassumption);
             try discriminate H
         end; congruence.
  Qed.

  (** *** Lifted semantics *)

  Section LiftDeterminism.

    Variable bk : stream bool.
    Variable H : history.

    Ltac apply_lift sem_det :=
      intros; eapply lift_det; try eassumption;
      compute; intros; eapply sem_det; eauto.

    Ltac apply_lift' sem_det :=
      intros; eapply lift'_det; try eassumption;
      compute; intros; eapply sem_det; eauto.

    Lemma sem_exp_det:
      forall e xs1 xs2,
        sem_exp bk H e xs1 -> sem_exp bk H e xs2 -> xs1 = xs2.
    Proof.
      apply_lift sem_exp_instant_det.
    Qed.

    Lemma sem_exps_det:
      forall les cs1 cs2,
        sem_exps bk H les cs1 ->
        sem_exps bk H les cs2 ->
        cs1 = cs2.
    Proof.
      apply_lift sem_exps_instant_det.
    Qed.

    Lemma sem_aexp_det:
      forall ck e xs1 xs2,
        sem_aexp bk H ck e xs1 -> sem_aexp bk H ck e xs2 -> xs1 = xs2.
    Proof.
      apply_lift sem_aexp_instant_det.
    Qed.

    Lemma sem_cexp_det:
      forall c xs1 xs2,
        sem_cexp bk H c xs1 -> sem_cexp bk H c xs2 -> xs1 = xs2.
    Proof.
      apply_lift sem_cexp_instant_det.
    Qed.

    Lemma sem_caexp_det:
      forall ck c xs1 xs2,
        sem_caexp bk H ck c xs1 -> sem_caexp bk H ck c xs2 -> xs1 = xs2.
    Proof.
      apply_lift sem_caexp_instant_det.
    Qed.

  End LiftDeterminism.

  (* Lemma clock_of_det: *)
  (*   forall xss ck1 ck2, *)
  (*     clock_of xss ck1 -> *)
  (*     clock_of xss ck2 -> *)
  (*     ck2 ≈ ck1. *)
  (* Proof. *)
  (*   intros * Hck1 Hck2 n. *)
  (*   specialize (Hck1 n); specialize (Hck2 n). *)
  (*   congruence. *)
  (* Qed. *)

  Ltac sem_det :=
    match goal with
    | H1: sem_clock_instant ?bk ?H ?C ?X,
          H2: sem_clock_instant ?bk ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_clock_instant_det; eexact H1 || eexact H2
    | H1: sem_clock ?bk ?H ?C ?X,
          H2: sem_clock ?bk ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_clock_det; eexact H1 || eexact H2
    | H1: sem_cexp_instant ?bk ?H ?C ?X,
          H2: sem_cexp_instant ?bk ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_cexp_instant_det; eexact H1 || eexact H2
    | H1: sem_cexp ?bk ?H ?C ?X,
          H2: sem_cexp ?bk ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_cexp_det; eexact H1 || eexact H2
    | H1: sem_exps_instant ?bk ?H ?C ?X,
          H2: sem_exps_instant ?bk ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_exps_instant_det; eexact H1 || eexact H2
    | H1: sem_exps ?bk ?H ?C ?X,
          H2: sem_exps ?bk ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_exps_det; eexact H1 || eexact H2
    | H1: sem_exp_instant ?bk ?H ?C ?X,
          H2: sem_exp_instant ?bk ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_exp_instant_det; eexact H1 || eexact H2
    | H1: sem_exp ?bk ?H ?C ?X,
          H2: sem_exp ?bk ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_exp_det; eexact H1 || eexact H2
    | H1: sem_aexp_instant ?bk ?H ?CK ?C ?X,
          H2: sem_aexp_instant ?bk ?H ?CK ?C ?Y |- ?X = ?Y =>
      eapply sem_aexp_instant_det; eexact H1 || eexact H2
    | H1: sem_aexp ?bk ?H ?CK ?C ?X,
          H2: sem_aexp ?bk ?H ?CK ?C ?Y |- ?X = ?Y =>
      eapply sem_aexp_det; eexact H1 || eexact H2
    | H1: sem_var_instant ?H ?C ?X,
          H2: sem_var_instant ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_var_instant_det; eexact H1 || eexact H2
    | H1: sem_var ?H ?C ?X,
          H2: sem_var ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_var_det; eexact H1 || eexact H2
    end.

  Ltac by_sem_det :=
    repeat match goal with
           | H: exists _, _ |- _ => destruct H
           end;
    match goal with
    | H1: sem_clock_instant ?bk ?H ?C ?X,
          H2: sem_clock_instant ?bk ?H ?C ?Y |- _ =>
      assert (X = Y) by (eapply sem_clock_instant_det; eexact H1 || eexact H2)
    | H1: sem_cexp_instant ?bk ?H ?C ?X,
          H2: sem_cexp_instant ?bk ?H ?C ?Y |- _ =>
      assert (X = Y) by (eapply sem_cexp_instant_det; eexact H1 || eexact H2)
    | H1: sem_exps_instant ?bk ?H ?C ?X,
          H2: sem_exps_instant ?bk ?H ?C ?Y |- _ =>
      assert (X = Y) by (eapply sem_exps_instant_det; eexact H1 || eexact H2)
    | H1: sem_exp_instant ?bk ?H ?C ?X,
          H2: sem_exp_instant ?bk ?H ?C ?Y |- _ =>
     assert (X = Y) by (eapply sem_exp_instant_det; eexact H1 || eexact H2)
    | H1: sem_aexp_instant ?bk ?H ?CK ?C ?X,
          H2: sem_aexp_instant ?bk ?H ?CK ?C ?Y |- _ =>
      assert (X = Y) by (eapply sem_aexp_instant_det; eexact H1 || eexact H2)
    | H1: sem_var_instant ?H ?C ?X,
          H2: sem_var_instant ?H ?C ?Y |- _ =>
      assert (X = Y) by (eapply sem_var_instant_det; eexact H1 || eexact H2)
    end; discriminate.

End CESEMANTICS.

Module CESemanticsFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX  Ids Op)
       (Cks   : CLOCKS         Ids Op OpAux)
       (Syn   : CESYNTAX       Ids Op OpAux Cks)
       (Str   : INDEXEDSTREAMS Ids Op OpAux Cks)
  <: CESEMANTICS Ids Op OpAux Cks Syn Str.
  Include CESEMANTICS Ids Op OpAux Cks Syn Str.
End CESemanticsFun.
