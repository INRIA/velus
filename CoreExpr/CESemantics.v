Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Setoid.
Require Import Morphisms.

Require Import Velus.Common.
Require Import Velus.Environment.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.RMemory.
Require Import Velus.CoreExpr.CESyntax.
Require Import Velus.CoreExpr.Stream.

(* Used in Lift Determinism *)
Require Import Logic.FunctionalExtensionality.

Module Type CESEMANTICS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Syn   : CESYNTAX      Op)
       (Import Str   : STREAM        Op OpAux).

  (** ** Environment and history *)

  (**

An history maps variables to streams of values (the variables'
histories). Taking a snapshot of the history at a given time yields an
environment.

   *)

  Definition env := Env.t value.
  Definition history := Env.t (stream value).

  (** ** Instantaneous semantics *)

  Section InstantSemantics.

    Variable base: bool.
    Variable R: env.

    Definition sem_var_instant (x: ident) (v: value) : Prop :=
      Env.find x R = Some v.

    Definition sem_vars_instant (xs: list ident) (vs: list value) : Prop :=
      Forall2 sem_var_instant xs vs.

    Inductive sem_clock_instant: clock -> bool -> Prop :=
    | Sbase:
        sem_clock_instant Cbase base
    | Son:
        forall ck x c b,
          sem_clock_instant ck true ->
          sem_var_instant x (present c) ->
          val_to_bool c = Some b ->
          sem_clock_instant (Con ck x b) true
    | Son_abs1:
        forall ck x c,
          sem_clock_instant ck false ->
          sem_var_instant x absent ->
          sem_clock_instant (Con ck x c) false
    | Son_abs2:
        forall ck x c b,
          sem_clock_instant ck true ->
          sem_var_instant x (present c) ->
          val_to_bool c = Some b ->
          sem_clock_instant (Con ck x (negb b)) false.

    Definition sem_clocked_var_instant (x: ident) (ck: clock) : Prop :=
      (sem_clock_instant ck true <-> exists c, sem_var_instant x (present c))
      /\ (sem_clock_instant ck false <-> sem_var_instant x absent).

    Definition sem_clocked_vars_instant (xs: list (ident * clock)) : Prop :=
      Forall (fun xc => sem_clocked_var_instant (fst xc) (snd xc)) xs.

    Inductive sem_lexp_instant: lexp -> value -> Prop:=
    | Sconst:
        forall c v,
          v = (if base then present (sem_const c) else absent) ->
          sem_lexp_instant (Econst c) v
    | Svar:
        forall x v ty,
          sem_var_instant x v ->
          sem_lexp_instant (Evar x ty) v
    | Swhen_eq:
        forall s x sc xc b,
          sem_var_instant x (present xc) ->
          sem_lexp_instant s (present sc) ->
          val_to_bool xc = Some b ->
          sem_lexp_instant (Ewhen s x b) (present sc)
    | Swhen_abs1:
        forall s x sc xc b,
          sem_var_instant x (present xc) ->
          val_to_bool xc = Some b ->
          sem_lexp_instant s (present sc) ->
          sem_lexp_instant (Ewhen s x (negb b)) absent
    | Swhen_abs:
        forall s x b,
          sem_var_instant x absent ->
          sem_lexp_instant s absent ->
          sem_lexp_instant (Ewhen s x b) absent
    | Sunop_eq:
        forall le op c c' ty,
          sem_lexp_instant le (present c) ->
          sem_unop op c (typeof le) = Some c' ->
          sem_lexp_instant (Eunop op le ty) (present c')
    | Sunop_abs:
        forall le op ty,
          sem_lexp_instant le absent ->
          sem_lexp_instant (Eunop op le ty) absent
    | Sbinop_eq:
        forall le1 le2 op c1 c2 c' ty,
          sem_lexp_instant le1 (present c1) ->
          sem_lexp_instant le2 (present c2) ->
          sem_binop op c1 (typeof le1) c2 (typeof le2) = Some c' ->
          sem_lexp_instant (Ebinop op le1 le2 ty) (present c')
    | Sbinop_abs:
        forall le1 le2 op ty,
          sem_lexp_instant le1 absent ->
          sem_lexp_instant le2 absent ->
          sem_lexp_instant (Ebinop op le1 le2 ty) absent.

    Definition sem_lexps_instant (les: list lexp) (vs: list value) :=
      Forall2 sem_lexp_instant les vs.

    Inductive sem_cexp_instant: cexp -> value -> Prop :=
    | Smerge_true:
        forall x t f c,
          sem_var_instant x (present true_val) ->
          sem_cexp_instant t (present c) ->
          sem_cexp_instant f absent ->
          sem_cexp_instant (Emerge x t f) (present c)
    | Smerge_false:
        forall x t f c,
          sem_var_instant x (present false_val) ->
          sem_cexp_instant t absent ->
          sem_cexp_instant f (present c) ->
          sem_cexp_instant (Emerge x t f) (present c)
    | Smerge_abs:
        forall x t f,
          sem_var_instant x absent ->
          sem_cexp_instant t absent ->
          sem_cexp_instant f absent ->
          sem_cexp_instant (Emerge x t f) absent
    | Site_eq:
        forall x t f c b ct cf,
          sem_lexp_instant x (present c) ->
          sem_cexp_instant t (present ct) ->
          sem_cexp_instant f (present cf) ->
          val_to_bool c = Some b ->
          sem_cexp_instant (Eite x t f) (if b then present ct else present cf)
    | Site_abs:
        forall b t f,
          sem_lexp_instant b absent ->
          sem_cexp_instant t absent ->
          sem_cexp_instant f absent ->
          sem_cexp_instant (Eite b t f) absent
    | Sexp:
        forall e v,
          sem_lexp_instant e v ->
          sem_cexp_instant (Eexp e) v.

  End InstantSemantics.

  Section InstantAnnotatedSemantics.

    Variable base : bool.
    Variable R: env.

    Inductive sem_annotated_instant {A}
              (sem_instant: bool -> env -> A -> value -> Prop)
      : clock -> A -> value -> Prop :=
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

    Definition sem_laexp_instant := sem_annotated_instant sem_lexp_instant.
    Definition sem_caexp_instant := sem_annotated_instant sem_cexp_instant.

  End InstantAnnotatedSemantics.

  (** ** Liftings of instantaneous semantics *)

  Section LiftSemantics.

    Variable bk : stream bool.
    Variable H : history.

    Definition restr_hist (n: nat): env :=
      Env.map (fun xs => xs n) H.
    Hint Unfold restr_hist.

    Definition lift {A B} (sem: bool -> env -> A -> B -> Prop)
               x (ys: stream B): Prop :=
      forall n, sem (bk n) (restr_hist n) x (ys n).
    Hint Unfold lift.

    Definition lift' {A B} (sem: env -> A -> B -> Prop) x (ys: stream B): Prop :=
      forall n, sem (restr_hist n) x (ys n).
    Hint Unfold lift'.

    Definition sem_clock (ck: clock) (xs: stream bool): Prop :=
      lift sem_clock_instant ck xs.

    Definition sem_var (x: ident) (xs: stream value): Prop :=
      lift' sem_var_instant x xs.

    Definition sem_vars (x: idents) (xs: stream (list value)): Prop :=
      lift' sem_vars_instant x xs.

    Definition sem_clocked_var (x: ident) (ck: clock): Prop :=
      forall n, sem_clocked_var_instant (bk n) (restr_hist n) x ck.

    Definition sem_clocked_vars (xs: list (ident * clock)) : Prop :=
      forall n, sem_clocked_vars_instant (bk n) (restr_hist n) xs.

    Definition sem_laexp ck (e: lexp) (xs: stream value): Prop :=
      lift (fun base R => sem_laexp_instant base R ck) e xs.

    Definition sem_lexp (e: lexp) (xs: stream value): Prop :=
      lift sem_lexp_instant e xs.

    Definition sem_lexps (e: list lexp) (xs: stream (list value)): Prop :=
      lift sem_lexps_instant e xs.

    Definition sem_caexp ck (c: cexp) (xs: stream value): Prop :=
      lift (fun base R => sem_caexp_instant base R ck) c xs.

    Definition sem_cexp (c: cexp) (xs: stream value): Prop :=
      lift sem_cexp_instant c xs.

  End LiftSemantics.

  (** ** Time-dependent semantics *)

  Definition clock_of_instant (vs: list value) : bool :=
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

  Definition clock_of (xss: stream (list value)): stream bool :=
    fun n => clock_of_instant (xss n).

  Definition reset_of (vs: stream value) (rs: stream bool) :=
    forall n, value_to_bool (vs n) = Some (rs n).

  (** Morphisms properties *)

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

  (* Add Parametric Morphism : (sem_laexp) *)
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

  Lemma sem_caexp_instant_absent:
    forall R ck e v,
      sem_caexp_instant false R ck e v ->
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

  (** ** Determinism of the semantics *)

  (** *** Instantaneous semantics *)

  Section InstantDeterminism.

    Variable base: bool.
    Variable R: env.

    Lemma sem_var_instant_det:
      forall x v1 v2,
        sem_var_instant R x v1
        -> sem_var_instant R x v2
        -> v1 = v2.
    Proof.
      congruence.
    Qed.

    Lemma sem_clock_instant_det:
      forall ck v1 v2,
        sem_clock_instant base R ck v1
        -> sem_clock_instant base R ck v2
        -> v1 = v2.
    Proof.
      induction ck; repeat inversion 1; subst; intuition;
        try repeat progress match goal with
                            | H1: sem_clock_instant ?bk ?R ?ck ?l,
                                  H2: sem_clock_instant ?bk ?R ?ck ?r |- _ =>
                              apply IHck with (1:=H1) in H2; discriminate
                            | H1: sem_var_instant ?R ?i (present ?l),
                                  H2: sem_var_instant ?R ?i (present ?r) |- _ =>
                              apply sem_var_instant_det with (1:=H1) in H2;
                                injection H2; intro; subst
                            | H1: val_to_bool _ = Some ?b, H2: val_to_bool _ = _ |- _ =>
                              rewrite H1 in H2; destruct b; discriminate
                            end.
    Qed.

    Lemma sem_lexp_instant_det:
      forall e v1 v2,
        sem_lexp_instant base R e v1
        -> sem_lexp_instant base R e v2
        -> v1 = v2.
    Proof.
      induction e (* using lexp_ind2 *);
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
      - (* Ewhen *)
        intros v1 v2 Hsem1 Hsem2.
        inversion Hsem1; inversion Hsem2; subst;
          repeat progress match goal with
                          | H1:sem_lexp_instant ?b ?R ?e ?v1,
                               H2:sem_lexp_instant ?b ?R ?e ?v2 |- _ =>
                            apply IHe with (1:=H1) in H2
                          | H1:sem_var_instant ?R ?i ?v1,
                               H2:sem_var_instant ?R ?i ?v2 |- _ =>
                            apply sem_var_instant_det with (1:=H1) in H2
                          | H1:sem_unop _ _ _ = Some ?v1,
                               H2:sem_unop _ _ _ = Some ?v2 |- _ =>
                            rewrite H1 in H2; injection H2; intro; subst
                          | Hp:present _ = present _ |- _ =>
                            injection Hp; intro; subst
                          | H1:val_to_bool _ = Some _,
                               H2:val_to_bool _ = Some (negb _) |- _ =>
                            rewrite H2 in H1; exfalso; injection H1;
                              now apply Bool.no_fixpoint_negb
                          end; subst; try easy.
      - (* Eunop *)
        intros v1 v2 Hsem1 Hsem2.
        inversion_clear Hsem1; inversion_clear Hsem2;
          repeat progress match goal with
                          | H1:sem_lexp_instant _ _ e _, H2:sem_lexp_instant _ _ e _ |- _ =>
                            apply IHe with (1:=H1) in H2; inversion H2; subst
                          | H1:sem_unop _ _ _ = _, H2:sem_unop _ _ _ = _ |- _ =>
                            rewrite H1 in H2; injection H2; intro; subst
                          | H1:sem_lexp_instant _ _ _ (present _),
                               H2:sem_lexp_instant _ _ _ absent |- _ =>
                            apply IHe with (1:=H1) in H2
                          end; try easy.
      - (* Ebinop *)
        intros v1 v2 Hsem1 Hsem2.
        inversion_clear Hsem1; inversion_clear Hsem2;
          repeat progress match goal with
                          | H1:sem_lexp_instant _ _ e1 _, H2:sem_lexp_instant _ _ e1 _ |- _ =>
                            apply IHe1 with (1:=H1) in H2
                          | H1:sem_lexp_instant _ _ e2 _, H2:sem_lexp_instant _ _ e2 _ |- _ =>
                            apply IHe2 with (1:=H1) in H2
                          | H1:sem_binop _ _ _ _ _ = Some ?v1,
                               H2:sem_binop _ _ _ _ _ = Some ?v2 |- _ =>
                            rewrite H1 in H2; injection H2; intro; subst
                          | H:present _ = present _ |- _ => injection H; intro; subst
                          end; subst; try easy.
    Qed.

    Lemma sem_laexp_instant_det:
      forall ck e v1 v2,
        sem_laexp_instant base R ck e v1
        -> sem_laexp_instant base R ck e v2
        -> v1 = v2.
    Proof.
      intros ck e v1 v2.
      do 2 inversion_clear 1;
        match goal with
        | H1:sem_lexp_instant _ _ _ _, H2:sem_lexp_instant _ _ _ _ |- _ =>
          eapply sem_lexp_instant_det; eassumption
        | H1:sem_clock_instant _ _ _ ?T, H2:sem_clock_instant _ _ _ ?F |- _ =>
          assert (T = F) by (eapply sem_clock_instant_det; eassumption);
            try discriminate
        end; auto.
    Qed.

    Lemma sem_lexps_instant_det:
      forall les cs1 cs2,
        sem_lexps_instant base R les cs1 ->
        sem_lexps_instant base R les cs2 ->
        cs1 = cs2.
    Proof.
      intros les cs1 cs2. apply Forall2_det. apply sem_lexp_instant_det.
    Qed.

    Lemma sem_cexp_instant_det:
      forall e v1 v2,
        sem_cexp_instant base R e v1
        -> sem_cexp_instant base R e v2
        -> v1 = v2.
    Proof.
      induction e;
        do 2 inversion_clear 1;
        try repeat progress match goal with
                            | H1: sem_cexp_instant ?bk ?R ?e ?l,
                                  H2: sem_cexp_instant ?bk ?R ?e ?r |- _ =>
                              apply IHe1 with (1:=H1) in H2
                                                         || apply IHe2 with (1:=H1) in H2;
                                injection H2; intro; subst
                            | H1: sem_var_instant ?R ?i (present true_val),
                                  H2: sem_var_instant ?R ?i (present false_val) |- _ =>
                              apply sem_var_instant_det with (1:=H1) in H2;
                                exfalso; injection H2; now apply true_not_false_val
                            | H1: sem_lexp_instant ?bk ?R ?l ?v1,
                                  H2: sem_lexp_instant ?bk ?R ?l ?v2 |- _ =>
                              apply sem_lexp_instant_det with (1:=H1) in H2;
                                discriminate || injection H2; intro; subst
                            | H1: sem_var_instant ?R ?i (present _),
                                  H2: sem_var_instant ?R ?i absent |- _ =>
                              apply sem_var_instant_det with (1:=H1) in H2; discriminate
                            | H1: val_to_bool _ = Some _,
                                  H2:val_to_bool _ = Some _ |- _ =>
                              rewrite H1 in H2; injection H2; intro; subst
                            end; auto.
      eapply sem_lexp_instant_det; eassumption.
    Qed.

    Lemma sem_caexp_instant_det:
      forall ck e v1 v2,
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

  End InstantDeterminism.

  (** *** Lifted semantics *)

  Section LiftDeterminism.

    Variable bk : stream bool.
    Variable H : history.

    Lemma lift_det:
      forall {A B} (P: bool -> env -> A -> B -> Prop) (bk: stream bool)
        x (xs1 xs2 : stream B),
        (forall b R v1 v2, P b R x v1 -> P b R x v2 -> v1 = v2) ->
        lift bk H P x xs1 -> lift bk H P x xs2 -> xs1 = xs2.
    Proof.
      intros * Hpoint H1 H2.
      extensionality n. specialize (H1 n). specialize (H2 n).
      eapply Hpoint; eassumption.
    Qed.

    Lemma lift'_det:
      forall {A B} (P: env -> A -> B -> Prop)
        x (xs1 xs2 : stream B),
        (forall R v1 v2, P R x v1 -> P R x v2 -> v1 = v2) ->
        lift' H P x xs1 -> lift' H P x xs2 -> xs1 = xs2.
    Proof.
      intros * Hpoint H1 H2.
      extensionality n. specialize (H1 n). specialize (H2 n).
      eapply Hpoint; eassumption.
    Qed.

    Ltac apply_lift sem_det :=
      intros; eapply lift_det; try eassumption;
      compute; intros; eapply sem_det; eauto.

    Ltac apply_lift' sem_det :=
      intros; eapply lift'_det; try eassumption;
      compute; intros; eapply sem_det; eauto.

    Lemma sem_var_det:
      forall x xs1 xs2,
        sem_var H x xs1 -> sem_var H x xs2 -> xs1 = xs2.
    Proof.
      apply_lift' sem_var_instant_det.
    Qed.

    Lemma sem_clock_det:
      forall ck bs1 bs2,
        sem_clock bk H ck bs1 -> sem_clock bk H ck bs2 -> bs1 = bs2.
    Proof.
      apply_lift sem_clock_instant_det.
    Qed.

    Lemma sem_lexp_det:
      forall e xs1 xs2,
        sem_lexp bk H e xs1 -> sem_lexp bk H e xs2 -> xs1 = xs2.
    Proof.
      apply_lift sem_lexp_instant_det.
    Qed.

    Lemma sem_lexps_det:
      forall les cs1 cs2,
        sem_lexps bk H les cs1 ->
        sem_lexps bk H les cs2 ->
        cs1 = cs2.
    Proof.
      apply_lift sem_lexps_instant_det.
    Qed.

    Lemma sem_laexp_det:
      forall ck e xs1 xs2,
        sem_laexp bk H ck e xs1 -> sem_laexp bk H ck e xs2 -> xs1 = xs2.
    Proof.
      apply_lift sem_laexp_instant_det.
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

  (* XXX: every semantics definition, including [sem_var] which doesn't
need it, takes a base clock value or base clock stream, except
[sem_var_instant]. For uniformity, we may want to pass a (useless)
clock to [sem_var_instant] too. *)

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
    | H1: sem_lexps_instant ?bk ?H ?C ?X,
          H2: sem_lexps_instant ?bk ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_lexps_instant_det; eexact H1 || eexact H2
    | H1: sem_lexps ?bk ?H ?C ?X,
          H2: sem_lexps ?bk ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_lexps_det; eexact H1 || eexact H2
    | H1: sem_lexp_instant ?bk ?H ?C ?X,
          H2: sem_lexp_instant ?bk ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_lexp_instant_det; eexact H1 || eexact H2
    | H1: sem_lexp ?bk ?H ?C ?X,
          H2: sem_lexp ?bk ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_lexp_det; eexact H1 || eexact H2
    | H1: sem_laexp_instant ?bk ?H ?CK ?C ?X,
          H2: sem_laexp_instant ?bk ?H ?CK ?C ?Y |- ?X = ?Y =>
      eapply sem_laexp_instant_det; eexact H1 || eexact H2
    | H1: sem_laexp ?bk ?H ?CK ?C ?X,
          H2: sem_laexp ?bk ?H ?CK ?C ?Y |- ?X = ?Y =>
      eapply sem_laexp_det; eexact H1 || eexact H2
    | H1: sem_var_instant ?H ?C ?X,
          H2: sem_var_instant ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_var_instant_det; eexact H1 || eexact H2
    | H1: sem_var ?H ?C ?X,
          H2: sem_var ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_var_det; eexact H1 || eexact H2
    end.

End CESEMANTICS.

Module CESemanticsFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Syn   : CESYNTAX      Op)
       (Str   : STREAM        Op OpAux)
  <: CESEMANTICS Ids Op OpAux Syn Str.
  Include CESEMANTICS Ids Op OpAux Syn Str.
End CESemanticsFun.
