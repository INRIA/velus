From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Sorting.Permutation.

From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import IndexedStreams.
From Velus Require Import CoreExpr.CESemantics.

(** * Interpreter for Core Expresssions *)

Module Type CEINTERPRETER
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Ids Op)
       (Import Cks   : CLOCKS          Ids Op OpAux)
       (Import CESyn : CESYNTAX        Ids Op OpAux Cks)
       (Import Str   : INDEXEDSTREAMS  Ids Op OpAux Cks)
       (Import CESem : CESEMANTICS Ids Op OpAux Cks CESyn Str).

  (** ** Instantaneous semantics *)

  Section InstantInterpreter.

    Variable base : bool.
    Variable R: env.

    Definition interp_vars_instant (xs: list ident): list svalue :=
      map (interp_var_instant R) xs.

     Fixpoint interp_exp_instant (e: exp): svalue :=
      match e with
      | Econst c =>
        if base then present (Vscalar (sem_cconst c)) else absent
      | Eenum x _ =>
        if base then present (Venum x) else absent
      | Evar x _ =>
        interp_var_instant R x
      | Ewhen e (x, _) b =>
        match interp_var_instant R x, interp_exp_instant e with
        | present (Venum b'), present ev =>
          if b ==b b' then present ev else absent
        | _, _ => absent
        end
      | Eunop op e _ =>
        match interp_exp_instant e with
        | present v =>
          match sem_unop op v (typeof e) with
          | Some v' => present v'
          | None => absent
          end
        | absent => absent
        end
      | Ebinop op e1 e2 _ =>
        match interp_exp_instant e1, interp_exp_instant e2 with
        | present v1, present v2 =>
          match sem_binop op v1 (typeof e1) v2 (typeof e2) with
          | Some v => present v
          | None => absent
          end
        | _, _ => absent
        end
      end.

    Definition interp_exps_instant (les: list exp): list svalue :=
      map interp_exp_instant les.

    Fixpoint interp_cexp_instant (e: cexp): svalue :=
      match e with
      | Emerge (x, _) es _ =>
        match interp_var_instant R x with
        | present (Venum c) =>
          or_default absent (nth_error (map interp_cexp_instant es) c)
        | _ => absent
        end

      | Ecase b es d =>
        match interp_exp_instant b with
        | present (Venum c) =>
          or_default_with absent (or_default (interp_cexp_instant d))
                          (nth_error (map (option_map interp_cexp_instant) es) c)
        | _ => absent
        end

      | Eexp e =>
        interp_exp_instant e
      end.

    Definition interp_cexps_instant (ces: list cexp): list svalue :=
      map interp_cexp_instant ces.

    Definition interp_ocexps_instant (e: cexp) (oces: list (option cexp)): list svalue :=
      map (fun oe => interp_cexp_instant (or_default e oe)) oces.

    Ltac rw_exp_helper :=
      repeat match goal with
             | _: sem_var_instant R ?x ?v |- context[interp_var_instant R ?x] =>
               erewrite <-interp_var_instant_complete; eauto; simpl
             | H: sem_unop ?op ?c ?t = _ |- context[sem_unop ?op ?c ?t] =>
               rewrite H
             | H: sem_binop ?op ?c1 ?t1 ?c2 ?t2 = _ |- context[sem_binop ?op ?c1 ?t1 ?c2 ?t2] =>
               rewrite H
          end.

    Lemma interp_vars_instant_complete:
      forall xs vs,
        sem_vars_instant R xs vs ->
        vs = interp_vars_instant xs.
    Proof.
      unfold sem_vars_instant, interp_vars_instant.
      induction 1; auto; simpl; rw_exp_helper; f_equal; auto.
    Qed.

    Lemma interp_exp_instant_complete:
      forall e v,
        sem_exp_instant base R e v ->
        v = interp_exp_instant e.
    Proof.
      induction 1; simpl;
        try rewrite <-IHsem_exp_instant;
        try rewrite <-IHsem_exp_instant1;
        try rewrite <-IHsem_exp_instant2;
        rw_exp_helper; auto.
      - now rewrite equiv_decb_refl.
      - take (_ <> _) and apply not_equiv_decb_equiv in it; now setoid_rewrite it.
    Qed.

    Lemma interp_exps_instant_complete:
      forall es vs,
        sem_exps_instant base R es vs ->
        vs = interp_exps_instant es.
    Proof.
      induction 1; simpl; auto.
      f_equal; auto.
      now apply interp_exp_instant_complete.
    Qed.

    Ltac rw_cexp_helper :=
      repeat (rw_exp_helper;
              repeat match goal with
                     | _: sem_exp_instant base R ?e ?v |- context[interp_exp_instant ?e] =>
                       erewrite <-(interp_exp_instant_complete e v); eauto; simpl
                     end).


    Lemma interp_cexp_instant_complete:
      forall e v,
        sem_cexp_instant base R e v ->
        v = interp_cexp_instant e.
    Proof.
      induction 1 using sem_cexp_instant_ind_2; simpl;
        try rewrite <-IHsem_cexp_instant;
        try rewrite <-IHsem_cexp_instant1;
        try rewrite <-IHsem_cexp_instant2;
        rw_cexp_helper;
        try rewrite equiv_decb_refl; auto.
      - subst.
        rewrite map_app; simpl.
        rewrite nth_error_app2; try rewrite map_length; auto.
        rewrite Nat.sub_diag; auto.
      - clear H0.
        rewrite map_nth_error'.
        take (nth_error _ _ = _) and apply nth_error_split in it as (vs1 & vs2 & ? & ?); subst.
        take (Forall2 _ _ _) and apply Forall2_app_inv_r in it as (es1 & es2' & Hes1 & Hes2' & ?); subst.
        inversion_clear Hes2' as [|???? Hc Hes2].
        erewrite <-Forall2_length; eauto.
        rewrite nth_error_app2; eauto.
        rewrite Nat.sub_diag; simpl.
        destruct x; simpl in *; auto.
    Qed.

    Lemma interp_cexps_instant_complete:
      forall es vs,
        Forall2 (sem_cexp_instant base R) es vs ->
        vs = interp_cexps_instant es.
    Proof.
      induction 1; simpl; auto.
      f_equal; auto.
      now apply interp_cexp_instant_complete.
    Qed.

    Lemma interp_ocexps_instant_complete:
      forall es vs e,
        Forall2 (fun oe => sem_cexp_instant base R (or_default e oe)) es vs ->
        vs = interp_ocexps_instant e es.
    Proof.
      induction 1; simpl; auto.
      f_equal; auto.
      now apply interp_cexp_instant_complete.
    Qed.

    Definition interp_annotated_instant {A} (interp: A -> svalue) (ck: clock) (a: A): svalue :=
      if interp_clock_instant base R ck then
        interp a
      else
        absent.

    Definition interp_caexp_instant (ck: clock) (ce: cexp) : svalue :=
      interp_annotated_instant (interp_cexp_instant) ck ce.

    Lemma interp_caexp_instant_complete:
      forall ck e v,
        sem_caexp_instant base R ck e v ->
        v = interp_caexp_instant ck e.
    Proof.
      unfold interp_caexp_instant, interp_annotated_instant.
      induction 1; erewrite <-interp_clock_instant_complete; eauto; simpl; auto.
      apply interp_cexp_instant_complete; auto.
    Qed.

    Definition interp_aexp_instant (ck: clock) (e: exp) : svalue :=
      interp_annotated_instant (interp_exp_instant) ck e.

    Lemma interp_aexp_instant_complete:
      forall ck e v,
        sem_aexp_instant base R ck e v ->
        v = interp_aexp_instant ck e.
    Proof.
      unfold interp_aexp_instant, interp_annotated_instant.
      induction 1; erewrite <-interp_clock_instant_complete; eauto; simpl; auto.
      apply interp_exp_instant_complete; auto.
    Qed.

  End InstantInterpreter.

  (** ** Liftings of instantaneous semantics *)

  Section LiftInterpreter.

    Variable bk : stream bool.
    Variable H: history.

    Definition interp_vars (xs: list ident): stream (list svalue) :=
      lift_interp' H interp_vars_instant xs.

    Definition interp_exp (e: exp): stream svalue :=
      lift_interp bk H interp_exp_instant e.

    Definition interp_exps (e: list exp): stream (list svalue) :=
      lift_interp bk H interp_exps_instant e.

    Definition interp_exps' (e: list exp): list (stream svalue) :=
      map interp_exp e.

    Lemma interp_exps'_complete:
      forall es ess,
        sem_exps bk H es ess ->
        Forall2 (sem_exp bk H) es (interp_exps' es).
    Proof.
      induction es; intros * Sem; simpl; auto.
      constructor.
      - intro n; specialize (Sem n); inv Sem.
        unfold interp_exp, lift_interp.
        erewrite <-interp_exp_instant_complete; eauto.
      - eapply IHes.
        intro n; specialize (Sem n); inv Sem.
        instantiate (1 := fun n => tl (ess n)).
        simpl.
        rewrite <-H2; simpl; auto.
    Qed.

    Definition interp_cexp (e: cexp): stream svalue :=
      lift_interp bk H interp_cexp_instant e.

    Definition interp_cexps (e: list cexp): stream (list svalue) :=
      lift_interp bk H interp_cexps_instant e.

    Definition interp_cexps' (e: list cexp): list (stream svalue) :=
      map interp_cexp e.

    Lemma interp_cexps'_complete:
      forall es ess,
        (forall n, Forall2 (sem_cexp_instant (bk n) (H n)) es (ess n)) ->
        Forall2 (sem_cexp bk H) es (interp_cexps' es).
    Proof.
      induction es; intros * Sem; simpl; auto.
      constructor.
      - intro n; specialize (Sem n); inv Sem.
        unfold interp_cexp, lift_interp.
        erewrite <-interp_cexp_instant_complete; eauto.
      - eapply IHes.
        intro n; specialize (Sem n); inv Sem.
        instantiate (1 := fun n => tl (ess n)).
        simpl.
        rewrite <-H2; simpl; auto.
    Qed.

    Definition interp_ocexp (e: cexp) (oe: option cexp): stream svalue :=
      lift_interp bk H (fun b R oe => interp_cexp_instant b R (or_default e oe)) oe.

    Definition interp_ocexps (e: cexp) (es: list (option cexp)): stream (list svalue) :=
      lift_interp bk H (fun b R => interp_ocexps_instant b R e) es.

    Definition interp_ocexps' (e: cexp) (es: list (option cexp)): list (stream svalue) :=
      map (interp_ocexp e) es.

    Lemma interp_ocexps'_complete:
      forall es ess e,
        (forall n, Forall2 (fun oe => sem_cexp_instant (bk n) (H n) (or_default e oe)) es (ess n)) ->
        Forall2 (fun oe => sem_cexp bk H (or_default e oe)) es (interp_ocexps' e es).
    Proof.
      induction es; intros * Sem; simpl; auto.
      constructor.
      - intro n; specialize (Sem n); inv Sem.
        unfold interp_ocexp, lift_interp.
        erewrite <-interp_cexp_instant_complete; eauto.
      - eapply IHes.
        intro n; specialize (Sem n); inv Sem.
        instantiate (1 := fun n => tl (ess n)).
        simpl.
        rewrite <-H2; simpl; auto.
    Qed.

    Definition interp_caexp (ck: clock) (e: cexp): stream svalue :=
      lift_interp bk H (fun base R => interp_caexp_instant base R ck) e.

    Definition interp_aexp (ck: clock) (e: exp): stream svalue :=
      lift_interp bk H (fun base R => interp_aexp_instant base R ck) e.

    Corollary interp_vars_complete:
      forall xs vss,
        sem_vars H xs vss ->
        vss ≈ interp_vars xs.
    Proof.
      intros; eapply lift'_complete; eauto;
        apply interp_vars_instant_complete.
    Qed.

    Corollary interp_exp_complete:
      forall e vs,
        sem_exp bk H e vs ->
        vs ≈ interp_exp e.
    Proof.
      intros; eapply lift_complete; eauto;
        apply interp_exp_instant_complete.
    Qed.

    Corollary interp_exps_complete:
      forall es vss,
        sem_exps bk H es vss ->
        vss ≈ interp_exps es.
    Proof.
      intros; eapply lift_complete; eauto;
        apply interp_exps_instant_complete.
    Qed.

    Corollary interp_cexp_complete:
      forall e vs,
        sem_cexp bk H e vs ->
        vs ≈ interp_cexp e.
    Proof.
      intros; eapply lift_complete; eauto;
        apply interp_cexp_instant_complete.
    Qed.

    Corollary interp_aexp_complete:
      forall e ck vs,
        sem_aexp bk H ck e vs ->
        vs ≈ interp_aexp ck e.
    Proof.
      intros; eapply lift_complete; eauto.
      intros; apply interp_aexp_instant_complete; auto.
    Qed.

    Corollary interp_caexp_complete:
      forall e ck vs,
        sem_caexp bk H ck e vs ->
        vs ≈ interp_caexp ck e.
    Proof.
      intros; eapply lift_complete; eauto.
      intros; apply interp_caexp_instant_complete; auto.
    Qed.
    (* Definition interp_annotated {A} (interp_instant: bool -> env -> A -> svalue) (ck: clock) (a: A): stream svalue := *)
    (*   lift (fun base R => interp_annotated_instant base R interp_instant ck) a. *)

  End LiftInterpreter.

End CEINTERPRETER.

Module CEInterpreterFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Ids Op)
       (Cks   : CLOCKS          Ids Op OpAux)
       (CESyn : CESYNTAX        Ids Op OpAux Cks)
       (Str   : INDEXEDSTREAMS  Ids Op OpAux Cks)
       (CESem : CESEMANTICS Ids Op OpAux Cks CESyn Str)
       <: CEINTERPRETER Ids Op OpAux Cks CESyn Str CESem.
  Include CEINTERPRETER Ids Op OpAux Cks CESyn Str CESem.
End CEInterpreterFun.
