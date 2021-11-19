From Coq Require Import List.
Import List.ListNotations.
From Coq Require Export Lists.Streams.
From Coq Require Import Setoid.
From Coq Require Import Morphisms.
From Coq Require Import Arith.EqNat.

From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Environment.
From Velus Require Import Clocks.

(* for Theorem consolidate_mask *)
From Coq Require Import Logic.IndefiniteDescription.

Module Type COINDSTREAMS
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Clocks : CLOCKS Ids Op OpAux).

  Open Scope stream_scope.

  Lemma const_nth:
    forall {A} n (c: A),
      (Streams.const c) # n = c.
  Proof.
    induction n; simpl; auto.
  Qed.

  Ltac unfold_Stv xs :=
    rewrite (unfold_Stream xs);
    destruct xs as [[|]];
    simpl.

  Ltac unfold_St xs :=
    rewrite (unfold_Stream xs);
    destruct xs;
    simpl.

  Lemma eq_EqSt:
    forall {A}, inclusion (Stream A) eq (@EqSt A).
  Proof.
    intros ? xs xs' E.
    now rewrite E.
  Qed.

  Add Parametric Morphism A : (@Cons A)
      with signature eq ==> @EqSt A ==> @EqSt A
        as Cons_EqSt.
  Proof.
    cofix Cofix.
    intros x xs xs' Exs.
    constructor; simpl; auto.
  Qed.

  Add Parametric Morphism A : (@hd A)
      with signature @EqSt A ==> eq
        as hd_EqSt.
  Proof.
    intros xs xs' Exs.
    destruct xs, xs'; inv Exs; simpl; auto.
  Qed.

  Add Parametric Morphism A : (@tl A)
      with signature @EqSt A ==> @EqSt A
        as tl_EqSt.
  Proof.
    intros xs xs' Exs.
    destruct xs, xs'; inv Exs; simpl; auto.
  Qed.

  Add Parametric Morphism A (n: nat) : (@Str_nth A n)
      with signature @EqSt A ==> eq
        as Str_nth_EqSt.
  Proof.
    intros xs xs' Exs.
    apply eqst_ntheq; auto.
  Qed.

  Section EqSts.
    Context {A: Type}.

    Definition EqSts (xss yss: list (Stream A)) :=
      Forall2 (@EqSt A) xss yss.

    Theorem EqSts_reflex: forall xss, EqSts xss xss.
    Proof.
      induction xss; constructor; auto.
      reflexivity.
    Qed.

    Theorem EqSts_sym: forall xss yss, EqSts xss yss -> EqSts yss xss.
    Proof.
      induction xss, yss; intros * H; auto; try inv H.
      constructor.
      - now symmetry.
      - now apply IHxss.
    Qed.

    Theorem EqSts_trans: forall xss yss zss, EqSts xss yss -> EqSts yss zss -> EqSts xss zss.
    Proof.
      induction xss, yss, zss; intros * Hx Hy; auto; try inv Hx; try inv Hy.
      constructor.
      - now transitivity s.
      - eapply IHxss; eauto.
    Qed.

  End EqSts.

  Add Parametric Relation A : (list (Stream A)) (@EqSts A)
      reflexivity proved by (@EqSts_reflex A)
      symmetry proved by (@EqSts_sym A)
      transitivity proved by (@EqSts_trans A)
        as EqStsrel.

  Add Parametric Morphism A : (@List.cons (Stream A))
      with signature @EqSt A ==> @EqSts A ==> @EqSts A
        as cons_EqSt.
  Proof. constructor; auto. Qed.

  Add Parametric Morphism A : (@List.app (Stream A))
      with signature @EqSts A ==> @EqSts A ==> @EqSts A
        as app_EqSts.
  Proof.
    intros xss xss' Exss yss yss' Eyss.
    revert dependent yss; revert dependent xss'.
    induction xss; induction yss; intros; inv Exss; inv Eyss;
      simpl; try constructor; auto.
    - now rewrite 2 app_nil_r.
    - apply IHxss; auto.
      constructor; auto.
  Qed.

  Add Parametric Morphism
      A B (P: A -> Stream B -> Prop) xs
      (P_compat: Proper (eq ==> @EqSt B ==> Basics.impl) P)
    : (@Forall2 A (Stream B) P xs)
      with signature @EqSts B ==> Basics.impl
        as Forall2_EqSt.
  Proof.
    intros ys ys' Eys.
    revert xs ys ys' Eys;
      induction xs, ys; intros ** H; inv H; inv Eys; auto.
    constructor; eauto.
    - eapply P_compat; eauto.
    - eapply IHxs; eauto.
  Qed.

  Add Parametric Morphism
      A B (P: A -> Stream B -> Prop) xs
      (P_compat: Proper (eq ==> @EqSt B ==> iff) P)
    : (@Forall2 A (Stream B) P xs)
      with signature @EqSts B ==> iff
        as Forall2_EqSt_iff.
  Proof.
    intros ys ys' Eys.
    split; revert xs ys ys' Eys;
      induction xs, ys; intros * Eys H; inv H; inv Eys; auto;
        constructor; eauto.
    now take (_ ≡ _) and rewrite <- it.
    now take (_ ≡ _) and rewrite it.
  Qed.

  Add Parametric Morphism
      A B (P: Stream A -> B -> Prop)
      (P_compat: Proper (@EqSt A ==> eq ==> Basics.impl) P)
    : (@Forall2 (Stream A) B P)
      with signature @EqSts A ==> eq ==> Basics.impl
        as Forall2_EqSt'.
  Proof.
    intros ys ys' Eys xs.
    revert xs ys ys' Eys;
      induction xs, ys; intros ** H; inv H; inv Eys; auto.
    constructor; eauto.
    - eapply P_compat; eauto.
    - eapply IHxs; eauto.
  Qed.

  Add Parametric Morphism
      A B (P: A -> Stream B -> Prop) xs
      (P_compat: Proper (eq ==> @EqSt B ==>  Basics.flip Basics.impl) P)
    : (@Forall2 A (Stream B) P xs)
      with signature @EqSts B ==> Basics.flip Basics.impl
        as Forall2_EqSt_flip.
  Proof.
    intros ys ys' Eys.
    revert xs ys ys' Eys.
    induction xs, ys; intros ** H; inv H; inv Eys; auto.
    constructor; eauto.
    - eapply P_compat; eauto.
    - eapply IHxs; eauto.
  Qed.

  Add Parametric Morphism
      A B C (P: A -> B -> Stream C -> Prop) xs ys
      (P_compat: Proper (eq ==> eq ==> @EqSt C ==> Basics.impl) P)
    : (@Forall3 A B (Stream C) P xs ys)
      with signature @EqSts C ==> Basics.impl
        as Forall3_EqSt.
  Proof.
    intros x y Exy Hxy.
    revert xs ys x y Exy Hxy;
      induction xs, ys; intros * Exy H; inv H; inv Exy; auto;
        constructor; eauto.
    now take (_ ≡ _) and rewrite <- it.
  Qed.

  Add Parametric Morphism
      A B
    : (@List.map (Stream A) (Stream B))
      with signature (fun (f f': Stream A -> Stream B) => forall xs xs', xs ≡ xs' -> f xs ≡ f' xs') ==> @EqSts A ==> @EqSts B
        as map_st_EqSt.
  Proof.
    intros f f' Ef xs xs' Exs.
    revert xs xs' Exs; induction xs, xs'; intros * H; inv H; constructor.
    - now apply Ef.
    - now apply IHxs.
  Qed.

  Add Parametric Morphism
      A B
    : (@List.map (Stream A) B)
      with signature (fun (f f': Stream A -> B) => forall xs xs', xs ≡ xs' -> f xs = f' xs') ==> @EqSts A ==> eq
        as map_EqSt.
  Proof.
    intros f f' Ef xs xs' Exs.
    revert xs xs' Exs; induction xs, xs'; intros * H; inv H; auto.
    simpl; f_equal.
    - now apply Ef.
    - now apply IHxs.
  Qed.

  Add Parametric Morphism
      A P
      (P_compat: Proper (@EqSt A ==> Basics.impl) P)
    : (@Forall (Stream A) P)
      with signature @EqSts A ==> Basics.impl
        as Forall_EqSt.
  Proof.
    induction x; intros * E H; inversion E; subst; auto.
    constructor; inv H.
    - eapply P_compat; eauto.
    - apply IHx; auto.
  Qed.

  Add Parametric Morphism
      A
      : (@length (Stream A))
      with signature @EqSts A ==> eq
        as length_EqSt.
  Proof.
    induction x; inversion_clear 1; simpl; auto.
  Qed.

  (* TODO: generalize *)
  Lemma map_nth_error_orel:
    forall {A B} (l : list (Stream A)) (f: Stream A -> Stream B) n x,
      (forall x y, x ≡ y -> f x ≡ f y) ->
      orel (@EqSt _) (nth_error l n) (Some x) ->
      orel (@EqSt _) (nth_error (List.map f l) n) (Some (f x)).
  Proof.
    induction l; simpl; intros * ? E.
    - rewrite nth_error_nil in E; inv E.
    - destruct n; simpl in *; eauto.
      inv E; constructor; auto.
  Qed.

  Lemma map_nth_error_orel':
    forall {A B} (l: list (Stream A)) (f: Stream A -> Stream B) n x,
      orel (@EqSt _) (nth_error (List.map f l) n) (Some x) ->
      exists y,
        orel (@EqSt _) (nth_error l n) (Some y)
        /\ x ≡ f y.
  Proof.
    induction l; simpl; intros * E.
    - rewrite nth_error_nil in E; inv E.
    - destruct n; simpl in *; eauto.
      inv E; exists a; split; auto.
      symmetry; auto.
  Qed.

  Add Parametric Morphism
      A
      : (@List.nth_error (Stream A))
      with signature @EqSts A ==> eq ==> orel (@EqSt A)
        as nth_error_EqSt.
  Proof.
    induction x; inversion_clear 1; simpl.
    - setoid_rewrite nth_error_nil; reflexivity.
    - destruct y1; simpl; auto.
      constructor; auto.
  Qed.

  Lemma EqSts_nil:
    forall {A} (l: list (Stream A)),
      EqSts l [] <-> l = [].
  Proof.
    induction l; split; try reflexivity.
    - inversion_clear 1.
    - discriminate.
  Qed.

  (* Equivalence of streams "up to" n *)
  Section EqStN.
    Context {A : Type}.

    Inductive EqStN : nat -> Stream A -> Stream A -> Prop :=
    | EqSt0 : forall xs1 xs2, EqStN 0 xs1 xs2
    | EqStS : forall n x1 xs1 x2 xs2,
        x1 = x2 ->
        EqStN n xs1 xs2 ->
        EqStN (S n) (x1 ⋅ xs1) (x2 ⋅ xs2).

    Hint Constructors EqStN.

    Lemma EqStN_spec : forall n xs1 xs2,
        (EqStN n xs1 xs2) <->
        (forall k, k < n -> xs1 # k = xs2 # k).
    Proof.
      split; intros Heq.
      - intros k Hlt. revert xs1 xs2 n Heq Hlt.
        induction k; intros ?? [|] Heq Hlt; try lia.
        + now inv Heq.
        + repeat rewrite Str_nth_S_tl. inv Heq; simpl.
          eapply IHk; eauto. lia.
      - revert xs1 xs2 Heq.
        induction n; intros; auto.
        unfold_St xs1. unfold_St xs2. constructor.
        + specialize (Heq 0). apply Heq; lia.
        + apply IHn; intros.
          apply (Heq (S k)); lia.
    Qed.

    Lemma EqStN_EqSt : forall xs1 xs2,
        (forall n, EqStN n xs1 xs2) <-> xs1 ≡ xs2.
    Proof.
      intros.
      setoid_rewrite EqStN_spec.
      split; intros Heq.
      - apply ntheq_eqst; intros.
        eapply Heq; auto.
      - intros ?? Hk.
        eapply eqst_ntheq; eauto.
    Qed.

    Corollary EqStN_EqSts : forall xs1 xs2,
        (forall n, Forall2 (EqStN n) xs1 xs2) <-> EqSts xs1 xs2.
    Proof.
      split; intros * Heq.
      - eapply Forall2_forall2; split.
        + specialize (Heq 0). now apply Forall2_length in Heq.
        + intros * Hlen ??; subst.
          eapply EqStN_EqSt; intros n0.
          specialize (Heq n0). eapply Forall2_forall2 in Heq as (_&Heq); eauto.
      - intros n.
        eapply Forall2_impl_In; [|eauto]; intros ?? _ _ Heq'.
        eapply EqStN_EqSt; eauto.
    Qed.

    Lemma EqStN_weaken : forall n xs1 xs2,
        EqStN (S n) xs1 xs2 ->
        EqStN n xs1 xs2.
    Proof.
      induction n; intros * Heq; inv Heq; eauto.
    Qed.
  End EqStN.

  Hint Constructors EqStN.

  Instance EqStN_refl {A} n : Reflexive (@EqStN A n).
  Proof.
    intros ?. apply EqStN_EqSt.
    reflexivity.
  Qed.

  Instance EqStN_sym {A} n : Symmetric (@EqStN A n).
  Proof.
    induction n; intros ?? Heq; inv Heq; auto.
  Qed.

  Instance EqStN_trans {A} n : Transitive (@EqStN A n).
  Proof.
    induction n; intros ??? Heq1 Heq2; inv Heq1; inv Heq2; eauto.
  Qed.

  Add Parametric Morphism A n : (@EqStN A n)
      with signature @EqSt _ ==> @EqSt _ ==> Basics.impl
        as EqStN_morph.
  Proof.
    induction n; intros (?&?) (?&?) Heq1 (?&?) (?&?) Heq2 Heq;
      inv Heq1; inv Heq2; inv Heq; simpl in *; constructor; subst; eauto.
    eapply IHn; eauto.
  Qed.

  (** A generic function to build a coinductive Stream. *)
  CoFixpoint init_from {A} (n: nat) (f: nat -> A) : Stream A :=
    f n ⋅ init_from (S n) f.

  (** A basic definition-rewriting lemma.  *)
  Lemma init_from_n:
    forall {A} (f: nat -> A) n,
      init_from n f = f n ⋅ init_from (S n) f.
  Proof.
    intros; now rewrite unfold_Stream at 1.
  Qed.

  (** The [m]th element of the built stream, starting from [n],
        is the result of the application of [f] at [(m+n)]. *)
  Lemma init_from_nth:
    forall {A} m n (f: nat -> A),
      (init_from n f) # m = f (m + n).
  Proof.
    unfold Str_nth; induction m; intros; simpl; auto.
    now rewrite IHm, <-plus_n_Sm.
  Qed.

  (** Taking the tail of a built Stream from [n] is building it from [S n]. *)
  Lemma init_from_tl:
    forall {A} n (f: nat -> A),
      tl (init_from n f) = init_from (S n) f.
  Proof.
    intros; rewrite init_from_n; auto.
  Qed.

  (** A generalization for multiple tails. *)
  Lemma init_from_nth_tl:
    forall {A} n m (f: nat -> A),
      Str_nth_tl n (init_from m f) = init_from (n + m) f.
  Proof.
    induction n; intros; simpl; auto.
    now rewrite IHn, Nat.add_succ_r.
  Qed.

  (** ** Typing of streams *)

  Definition wt_stream (sv : Stream svalue) (ty : type) : Prop :=
    SForall (fun v => wt_svalue v ty) sv.

  Definition wt_streams: list (Stream svalue) -> list type -> Prop :=
    Forall2 wt_stream.

  (** ** Synchronous operators *)

  CoFixpoint const (b: Stream bool) (c: cconst): Stream svalue :=
    (if hd b then present (Vscalar (sem_cconst c)) else absent) ⋅ const (tl b) c.

  CoFixpoint enum (b: Stream bool) (c: enumtag): Stream svalue :=
    (if hd b then present (Venum c) else absent) ⋅ enum (tl b) c.

  CoInductive lift1 (op: unop) (ty: type)
    : Stream svalue -> Stream svalue -> Prop :=
  | Lift1A:
      forall xs rs,
        lift1 op ty xs rs ->
        lift1 op ty (absent ⋅ xs) (absent ⋅ rs)
  | Lift1P:
      forall x r xs rs,
        sem_unop op x ty = Some r ->
        lift1 op ty xs rs ->
        lift1 op ty (present x ⋅ xs) (present r ⋅ rs).

  CoInductive lift2 (op: binop) (ty1 ty2: type)
    : Stream svalue -> Stream svalue -> Stream svalue -> Prop :=
  | Lift2A:
      forall xs ys rs,
        lift2 op ty1 ty2 xs ys rs ->
        lift2 op ty1 ty2 (absent ⋅ xs) (absent ⋅ ys) (absent ⋅ rs)
  | Lift2ScalarP:
      forall x y r xs ys rs,
        sem_binop op x ty1 y ty2 = Some r ->
        lift2 op ty1 ty2 xs ys rs ->
        lift2 op ty1 ty2 (present x ⋅ xs) (present y ⋅ ys) (present r ⋅ rs).

  CoInductive when (c: enumtag)
    : Stream svalue -> Stream svalue -> Stream svalue -> Prop :=
  | WhenA:
      forall xs cs rs,
        when c xs cs rs ->
        when c (absent ⋅ xs) (absent ⋅ cs) (absent ⋅ rs)
  | WhenPA:
      forall x c' xs cs rs,
        when c xs cs rs ->
        c <> c' ->
        when c (present x ⋅ xs) (present (Venum c') ⋅ cs) (absent ⋅ rs)
  | WhenPP:
      forall x xs cs rs,
        when c xs cs rs ->
        when c (present x ⋅ xs) (present (Venum c) ⋅ cs) (present x ⋅ rs).

  CoInductive merge
    : Stream svalue -> list (enumtag * Stream svalue) -> Stream svalue -> Prop :=
  | MergeA:
      forall xs ess rs,
        merge xs (List.map (fun '(i, es) => (i, tl es)) ess) rs ->
        Forall (fun es => hd (snd es) = absent) ess ->
        merge (absent ⋅ xs) ess (absent ⋅ rs)
  | MergeP:
      forall c xs ess rs v,
        merge xs (List.map (fun '(i, es) => (i, tl es)) ess) rs ->
        List.Exists (fun '(i, es) => i = c /\ hd es = present v) ess ->
        Forall (fun '(i, es) => i <> c -> hd es = absent) ess ->
        merge (present (Venum c) ⋅ xs) ess (present v ⋅ rs).

  CoInductive case
    : Stream svalue -> list (enumtag * Stream svalue) -> option (Stream svalue) -> Stream svalue -> Prop :=
  | CaseA:
      forall xs ess d rs,
        case xs (List.map (fun '(i, es) => (i, tl es)) ess) (option_map (@tl _) d) rs ->
        Forall (fun es => hd (snd es) = absent) ess ->
        LiftO True (fun d => hd d = absent) d ->
        case (absent ⋅ xs) ess d (absent ⋅ rs)
  | CaseP:
      forall c xs ess d rs v,
        case xs (List.map (fun '(i, es) => (i, tl es)) ess) (option_map (@tl _) d) rs ->
        Forall (fun es => hd (snd es) <> absent) ess ->
        LiftO True (fun d => hd d <> absent) d ->
        List.Exists (fun '(i, es) => i = c /\ hd es = present v) ess ->
        case (present (Venum c) ⋅ xs) ess d (present v ⋅ rs)
  | CasePDef:
      forall c xs ess d rs vd,
        case xs (List.map (fun '(i, es) => (i, tl es)) ess) (Some d) rs ->
        Forall (fun es => hd (snd es) <> absent) ess ->
        Forall (fun es => (fst es) <> c) ess ->
        case (present (Venum c) ⋅ xs) ess (Some (present vd ⋅ d)) (present vd ⋅ rs).

  Add Parametric Morphism : merge
      with signature @EqSt svalue ==> eq ==> @EqSt svalue ==> Basics.impl
        as merge_EqSt.
  Proof.
    cofix Cofix.
    intros cs cs' Ecs xs ys ys' Eys H.
    destruct cs' as [[]], ys' as [[]];
      inv H; inv Ecs; inv Eys; simpl in *;
        try discriminate.
    - constructor; auto.
      eapply Cofix; eauto.
    - repeat take (_ = _) and inv it.
      econstructor; eauto.
      eapply Cofix; eauto.
  Qed.

  Add Parametric Morphism : case
      with signature @EqSt svalue ==> eq ==> eq ==> @EqSt svalue ==> Basics.impl
        as case_EqSt.
  Proof.
    cofix Cofix.
    intros cs cs' Ecs xs d ys ys' Eys H.
    destruct cs' as [[]], ys' as [[]];
      inv H; inv Ecs; inv Eys; simpl in *;
        try discriminate.
    - constructor; auto.
      eapply Cofix; eauto.
    - repeat take (_ = _) and inv it.
      econstructor; eauto.
      eapply Cofix; eauto.
    - repeat take (_ = _) and inv it.
      eapply CasePDef; eauto.
      eapply Cofix; eauto.
  Qed.

  Add Parametric Morphism : case
      with signature eq ==> Forall2 (fun xs1 xs2 => eq (fst xs1) (fst xs2) /\ EqSt (snd xs1) (snd xs2)) ==> eq ==> eq ==> Basics.impl
        as case_EqStS.
  Proof.
    cofix Cofix.
    intros cs xs1 xs2 Exs d ys H.
    inv H; simpl in *; try discriminate.
    - constructor; auto.
      eapply Cofix; eauto.
      + rewrite Forall2_map_1, Forall2_map_2.
        eapply Forall2_impl_In; [|eauto];
          intros (?&?&?) (?&?&?) _ _ (?&?&?); simpl in *; subst; auto.
      + clear - Exs H1. induction Exs; inv H1; constructor; eauto.
        destruct x as (?&?&?), y as (?&?&?); simpl in *.
        destruct H as (?&?&?); simpl in *; congruence.
    - econstructor; eauto.
      eapply Cofix; eauto.
      + rewrite Forall2_map_1, Forall2_map_2.
        eapply Forall2_impl_In; [|eauto];
          intros (?&?&?) (?&?&?) _ _ (?&?&?); simpl in *; subst; auto.
      + clear - Exs H1. induction Exs; inv H1; constructor; eauto.
        destruct x as (?&?&?), y as (?&?&?); simpl in *.
        destruct H as (?&?&?); simpl in *; congruence.
      + clear - Exs H3. induction Exs; inv H3; destruct x as (?&?&?), y as (?&?&?).
        destruct H as (?&?&?), H1 as (?&?); simpl in *; subst; auto. right; eauto.
    - eapply CasePDef; eauto.
      eapply Cofix; eauto.
      + rewrite Forall2_map_1, Forall2_map_2.
        eapply Forall2_impl_In; [|eauto];
          intros (?&?&?) (?&?&?) _ _ (?&?&?); simpl in *; subst; auto.
      + clear - Exs H1. induction Exs; inv H1; constructor; eauto.
        destruct x as (?&?&?), y as (?&?&?); simpl in *.
        destruct H as (?&?&?); simpl in *; congruence.
      + clear - Exs H2. induction Exs; inv H2; constructor; eauto.
        destruct x as (?&?&?), y as (?&?&?); simpl in *.
        destruct H as (?&?&?); simpl in *; congruence.
  Qed.

  (** ** exp level synchronous operators specifications

        To ease the use of coinductive hypotheses to prove non-coinductive
        goals, we give for each coinductive predicate an indexed specification,
        reflecting the shapes of the involved streams pointwise speaking.
        In general this specification is a disjunction with a factor for each
        case of the predicate.
        The corresponding lemmas simply go by induction on [n] and by inversion
        of the coinductive hypothesis for the direct direction, and by coinduction
        on the converse.
   *)

  Lemma const_spec:
    forall xs c b,
      xs ≡ const b c <->
      forall n, xs # n = if b # n then present (Vscalar (sem_cconst c)) else absent.
  Proof.
    split.
    - intros E n; revert dependent xs; revert c b; induction n; intros;
        unfold_Stv b; unfold_Stv xs; inv E; simpl in *; try discriminate;
          repeat rewrite Str_nth_S; auto.
    - revert xs c b.
      cofix COFIX.
      intros * E.
      unfold_Stv b; unfold_Stv xs; constructor; simpl; auto;
        try (specialize (E 0); now inv E);
        apply COFIX; intro n; specialize (E (S n)); rewrite 2 Str_nth_S in E; auto.
  Qed.

  Corollary const_true: forall bs c n,
      bs # n = true ->
      (const bs c) # n = present (Vscalar (sem_cconst c)).
  Proof.
    intros.
    specialize (EqSt_reflex (const bs c)) as Hconst.
    eapply const_spec with (n:=n) in Hconst.
    rewrite Hconst, H; auto.
  Qed.

  Corollary const_false : forall bs c n,
      bs # n = false ->
      (const bs c) # n = absent.
  Proof.
    intros.
    specialize (EqSt_reflex (const bs c)) as Hconst.
    eapply const_spec with (n:=n) in Hconst.
    rewrite Hconst, H; auto.
  Qed.

  Corollary const_nth' : forall bs c n,
      (const bs c) # n = if (bs # n) then present (Vscalar (sem_cconst c)) else absent.
  Proof.
    intros bs c n.
    destruct (bs # n) eqn:Hb.
    - apply const_true; auto.
    - apply const_false; auto.
  Qed.

  Lemma const_inv1 :
    forall c b s,
      const b c ≡ absent ⋅ s ->
      exists b', s ≡ const b' c /\ b ≡ false ⋅ b'.
  Proof.
    intros * H.
    unfold_Stv b; inv H; simpl in *; inv H0.
    exists b. split; symmetry; auto. reflexivity.
  Qed.

  Lemma const_inv2 :
    forall c c' b s,
      const b c ≡ present c' ⋅ s ->
      exists b', s ≡ const b' c
            /\ b ≡ true ⋅ b'
            /\ c' = Vscalar (sem_cconst c).
  Proof.
    intros * H.
    unfold_Stv b; inv H; simpl in *; inv H0.
    exists b. split. symmetry. assumption. split; reflexivity.
  Qed.

  Lemma const_tl :
    forall c b v tl,
      const b c ≡ v ⋅ tl ->
      const (Streams.tl b) c ≡ tl.
  Proof.
    intros * H.
    unfold_Stv b; inv H; simpl in *; inv H0; assumption.
  Qed.

  Lemma const_Cons : forall c b bs,
      const (b ⋅ bs) c ≡
      (if b then present (Vscalar (sem_cconst c)) else absent) ⋅ (const bs c).
  Proof.
    intros.
    rewrite unfold_Stream at 1; reflexivity.
  Qed.

  Lemma enum_spec:
    forall xs c b,
      xs ≡ enum b c <->
      forall n, xs # n = if b # n then present (Venum c) else absent.
  Proof.
    split.
    - intros E n; revert dependent xs; revert c b; induction n; intros;
        unfold_Stv b; unfold_Stv xs; inv E; simpl in *; try discriminate;
          repeat rewrite Str_nth_S; auto.
    - revert xs c b.
      cofix COFIX.
      intros * E.
      unfold_Stv b; unfold_Stv xs; constructor; simpl; auto;
        try (specialize (E 0); now inv E);
        apply COFIX; intro n; specialize (E (S n)); rewrite 2 Str_nth_S in E; auto.
  Qed.

  Corollary enum_true: forall bs c n,
      bs # n = true ->
      (enum bs c) # n = present (Venum c).
  Proof.
    intros.
    specialize (EqSt_reflex (enum bs c)) as Henum.
    eapply enum_spec with (n:=n) in Henum.
    rewrite Henum, H; auto.
  Qed.

  Corollary enum_false : forall bs c n,
      bs # n = false ->
      (enum bs c) # n = absent.
  Proof.
    intros.
    specialize (EqSt_reflex (enum bs c)) as Henum.
    eapply enum_spec with (n:=n) in Henum.
    rewrite Henum, H; auto.
  Qed.

  Corollary enum_nth' : forall bs c n,
      (enum bs c) # n = if (bs # n) then present (Venum c) else absent.
  Proof.
    intros bs c n.
    destruct (bs # n) eqn:Hb.
    - apply enum_true; auto.
    - apply enum_false; auto.
  Qed.

  Ltac cofix_step CoFix H :=
    let n := fresh "n" in
    apply CoFix; intro n; specialize (H (S n));
    repeat rewrite Str_nth_S in H; auto.

  Lemma when_spec:
    forall c xs cs rs,
      when c xs cs rs <->
      (forall n,
          (xs # n = absent
           /\ cs # n = absent
           /\ rs # n = absent)
          \/
          (exists x c',
              xs # n = present x
              /\ cs # n = present (Venum c')
              /\ c <> c'
              /\ rs # n = absent)
          \/
          (exists x,
              xs # n = present x
              /\ cs # n = present (Venum c)
              /\ rs # n = present x)).
  Proof.
    split.
    - intros H n; revert dependent xs; revert cs rs c.
      induction n; intros.
      + inv H; intuition.
        * right; left. do 2 eexists; intuition.
        * right; right. do 2 eexists; intuition.
      + inv H; repeat rewrite Str_nth_S; auto.
    - revert xs cs rs c.
      cofix CoFix; intros * H.
      unfold_Stv xs; unfold_Stv cs; unfold_Stv rs;
        try (specialize (H 0); repeat rewrite Str_nth_0 in H;
             destruct H as [(?&?&?)|[(?&?&?&?&?&?)|(?&?&?&?)]];
             discriminate).
      + constructor; cofix_step CoFix H.
      + destruct v0.
        all: try (specialize (H 0); repeat rewrite Str_nth_0 in H;
                  destruct H as [(?&?&?)|[(?&?&?&?&?&?)|(?&?&?&?)]];
                  discriminate).
        constructor.
        * cofix_step CoFix H.
        * specialize (H 0); repeat rewrite Str_nth_0 in H;
            destruct H as [(?&?&?)|[(?&?&?&?&?&?)|(?&?&?&?)]];
            try discriminate.
             congruence.
      + destruct (H 0) as [(?&?&?)|[(?&?&?&?&?&?)|(?& E & E' & E'')]];
          try discriminate.
        rewrite Str_nth_0 in E, E', E''.
        rewrite E, E', E''.
        constructor; try congruence.
        cofix_step CoFix H.
  Qed.

  Lemma lift1_spec:
    forall op ty xs ys,
      lift1 op ty xs ys <->
      (forall n,
          (xs # n = absent /\ ys # n = absent)
          \/
          (exists x y,
              xs # n = present x
              /\ sem_unop op x ty = Some y
              /\ ys # n = present y)).
  Proof.
    split.
    - intros H n; revert dependent xs; revert ys ty op.
      induction n; intros.
      + inv H; intuition.
        right. do 2 eexists; intuition; auto.
      + inv H; repeat rewrite Str_nth_S;auto.
    - revert xs ys ty op.
      cofix CoFix; intros * H.
      unfold_Stv xs; unfold_Stv ys;
        try (specialize (H 0); repeat rewrite Str_nth_0 in H;
             destruct H as [(?&?)|(?&?&?&?&?)]; discriminate).
      + constructor; cofix_step CoFix H.
      + destruct (H 0) as [(?&?)|(?&?& E &?& E')]; try discriminate;
          rewrite Str_nth_0 in E, E'; inv E; inv E'.
        constructor; auto.
        cofix_step CoFix H.
  Qed.

  Lemma lift2_spec:
    forall op ty1 ty2 xs ys zs,
      lift2 op ty1 ty2 xs ys zs <->
      (forall n,
          (xs # n = absent
           /\ ys # n = absent
           /\ zs # n = absent)
          \/
          (exists x y z,
              xs # n = present x
              /\ ys # n = present y
              /\ sem_binop op x ty1 y ty2 = Some z
              /\ zs # n = present z)).
  Proof.
    split.
    - intros H n; revert dependent xs; revert ys zs ty1 ty2 op.
      induction n; intros.
      + inv H; intuition.
        right. do 3 eexists; intuition; auto.
      + inv H; repeat rewrite Str_nth_S; auto.
    - revert xs ys zs ty1 ty2 op.
      cofix CoFix; intros * H.
      unfold_Stv xs; unfold_Stv ys; unfold_Stv zs;
        try (specialize (H 0); repeat rewrite Str_nth_0 in H;
             destruct H as [(?&?&?)|(?&?&?&?&?&?&?)]; discriminate).
      + constructor; cofix_step CoFix H.
      + destruct (H 0) as [(?&?&?)|(?&?&?& E & E' &?& E'')]; try discriminate;
          rewrite Str_nth_0 in E, E', E''; inv E; inv E'; inv E''.
        constructor; auto.
        cofix_step CoFix H.
  Qed.

  (** ** cexp level synchronous operators specifications *)

  Lemma merge_spec:
    forall xs ess rs,
      merge xs ess rs <->
      (forall n,
          (xs # n = absent
           /\ Forall (fun es => (snd es) # n = absent) ess
           /\ rs # n = absent)
          \/
          (exists c v,
              xs # n = present (Venum c)
              /\ List.Exists (fun '(i, es) => i = c /\ es # n = present v) ess
              /\ Forall (fun '(i, es) => i <> c -> es # n = absent) ess
              /\ rs # n = present v)).
  Proof.
    split.
    - intros * H n.
      revert dependent xs; revert ess rs.
      induction n; intros.
      + inv H; intuition.
        right; do 2 eexists; intuition; eauto.
      + inv H; repeat rewrite Str_nth_S.
        * take (Forall _ _) and clear it.
          take (merge _ _ _) and apply IHn in it as [(?&?&?)|(?&?&?&?&?&?)].
          -- left; intuition.
             take (Forall _ _) and apply Forall_map in it.
             apply Forall_forall; intros (?&?) Hin; eapply Forall_forall in Hin; eauto.
             simpl in Hin; auto.
          -- right. repeat esplit; eauto.
             ++ rewrite Exists_map in H0. eapply Exists_exists in H0 as ((?&?)&?&?&?); subst.
                eapply Exists_exists; repeat (esplit; eauto).
             ++ rewrite Forall_map in H1. eapply Forall_impl; [|eauto]; intros (?&?) ??.
                rewrite Str_nth_S_tl; auto.
        * take (merge _ _ _) and apply IHn in it as [(?&?&?)|(?&?&?&?&?&?)].
          -- left; intuition.
             rewrite Forall_map in H0. eapply Forall_impl; [|eapply H0]; intros (?&?) ?.
             rewrite Str_nth_S_tl; auto.
          -- right. repeat esplit; eauto.
             ++ rewrite Exists_map in H0. eapply Exists_exists in H0 as ((?&?)&?&?&?); subst.
                eapply Exists_exists; repeat (esplit; eauto).
             ++ rewrite Forall_map in H3. eapply Forall_impl; [|eapply H3]; intros (?&?) ??.
                rewrite Str_nth_S_tl; auto.
    - revert xs ess rs; cofix CoFix; intros * H.
      unfold_Stv xs; unfold_Stv rs;
        try (specialize (H 0); repeat rewrite Str_nth_0 in H;
             destruct H as [(?&?&?)|(?&?&?&?&?&?)];
             discriminate).
      + constructor.
        * cofix_step CoFix H.
          destruct H as [(?&?&?)|(?&?&?&?&?&?)].
          -- left; intuition.
             apply Forall_map, Forall_forall; intros (?&?) Hin;
               eapply Forall_forall in Hin; eauto; simpl in Hin; auto.
          -- subst; right; do 2 eexists. repeat split; eauto.
             ++ rewrite Exists_map. eapply Exists_exists in H0 as ((?&?)&?&?&?); subst.
                eapply Exists_exists; repeat (esplit; eauto).
             ++ rewrite Forall_map. eapply Forall_impl; [|eapply H1]; intros (?&?) ??.
                rewrite <-Str_nth_S_tl; auto.
        * destruct (H 0) as [(?&?&?)|(?&?&?&?&?&?)]; try discriminate.
          apply Forall_forall; intros (?&?) Hin;
            eapply Forall_forall in Hin; eauto; simpl in *; auto.
      + destruct (H 0) as [(?&?&?)|(?&?& Hc & E & E' & Hr)]; try discriminate.
        inv Hc. inv Hr.
        econstructor; eauto.
        cofix_step CoFix H.
        destruct H as [(?&?&?)|(?&?&?&?&?&?)].
        -- left; intuition.
           apply Forall_map, Forall_forall; intros (?&?) Hin.
           eapply Forall_forall in H0; eauto; simpl in Hin; auto.
        -- right; do 2 eexists. repeat split; eauto.
             ++ rewrite Exists_map. eapply Exists_exists in H0 as ((?&?)&?&?&?); subst.
                eapply Exists_exists; repeat (esplit; eauto).
             ++ rewrite Forall_map. eapply Forall_impl; [|eapply H1]; intros (?&?) ??.
                rewrite <-Str_nth_S_tl; auto.
  Qed.

  Lemma case_spec:
    forall xs ess d rs,
      case xs ess d rs <->
      (forall n,
          (xs # n = absent
           /\ Forall (fun es => (snd es) # n = absent) ess
           /\ LiftO True (fun d => d # n = absent) d
           /\ rs # n = absent)
          \/
          (exists c v,
              xs # n = present (Venum c)
              /\ Forall (fun es => (snd es) # n <> absent) ess
              /\ List.Exists (fun '(i, es) => i = c /\ es # n = present v) ess
              /\ LiftO True (fun d => d # n <> absent) d
              /\ rs # n = present v
          )
          \/
          (exists c v,
              xs # n = present (Venum c)
              /\ Forall (fun es => (snd es) # n <> absent) ess
              /\ Forall (fun es => (fst es) <> c) ess
              /\ LiftO False (fun d => d # n = present v) d
              /\ rs # n = present v)).
  Proof.
    split.
    - intros * H n.
      revert dependent xs; revert ess d rs.
      induction n; intros.
      + inv H; intuition.
        * right; left. repeat esplit; eauto.
        * right; right. repeat esplit; eauto.
      + inv H; repeat rewrite Str_nth_S.
        * take (case _ _ _ _) and apply IHn in it as [(?&?&?&?)|[(?&?&?&?&?&?&?)|(?&?&?&?&?&?&?)]].
          -- left; intuition.
             rewrite Forall_map in H0. eapply Forall_impl; [|eapply H0]; intros (?&?) ?.
             rewrite Str_nth_S_tl; auto.
             destruct d; simpl in *; auto.
          -- right; left. repeat esplit; eauto.
             ++ rewrite Forall_map in H0. eapply Forall_impl; [|eapply H0]; intros (?&?) ?.
                rewrite Str_nth_S_tl; auto.
             ++ rewrite Exists_map in H3. eapply Exists_exists in H3 as ((?&?)&?&?&?); subst.
                eapply Exists_exists; repeat (esplit; eauto).
             ++ destruct d; simpl in *; auto.
          -- right; right. repeat esplit; eauto.
             ++ rewrite Forall_map in H0. eapply Forall_impl; [|eapply H0]; intros (?&?) ?.
                rewrite Str_nth_S_tl; auto.
             ++ rewrite Forall_map in H3. eapply Forall_impl; [|eapply H3]; intros (?&?) ?.
                auto.
             ++ destruct d; simpl in *; eauto.
        * take (case _ _ _ _) and apply IHn in it as [(?&?&?&?)|[(?&?&?&?&?&?&?)|(?&?&?&?&?&?&?)]].
          -- left; intuition.
             rewrite Forall_map in H0. eapply Forall_impl; [|eapply H0]; intros (?&?) ?.
             rewrite Str_nth_S_tl; auto.
             destruct d; simpl in *; auto.
          -- right; left. repeat esplit; eauto.
             ++ rewrite Forall_map in H0. eapply Forall_impl; [|eapply H0]; intros (?&?) ?.
                rewrite Str_nth_S_tl; auto.
             ++ rewrite Exists_map in H4. eapply Exists_exists in H4 as ((?&?)&?&?&?); subst.
                eapply Exists_exists; repeat (esplit; eauto).
             ++ destruct d; simpl in *; auto.
          -- right; right. repeat esplit; eauto.
             ++ rewrite Forall_map in H0. eapply Forall_impl; [|eapply H0]; intros (?&?) ?.
                rewrite Str_nth_S_tl; auto.
             ++ rewrite Forall_map in H4. eapply Forall_impl; [|eapply H4]; intros (?&?) ?.
                auto.
             ++ destruct d; simpl in *; eauto.
        * take (case _ _ _ _) and apply IHn in it as [(?&?&?&?)|[(?&?&?&?&?&?&?)|(?&?&?&?&?&?&?)]].
          -- left; intuition.
             rewrite Forall_map in H0. eapply Forall_impl; [|eapply H0]; intros (?&?) ?.
             rewrite Str_nth_S_tl; auto.
          -- right; left. repeat esplit; eauto.
             ++ rewrite Forall_map in H0. eapply Forall_impl; [|eapply H0]; intros (?&?) ?; simpl.
                rewrite Str_nth_S_tl; auto.
             ++ rewrite Exists_map in H3. eapply Exists_exists in H3 as ((?&?)&?&?&?); subst.
                eapply Exists_exists; repeat (esplit; eauto).
          -- right; right. repeat esplit; eauto.
             ++ rewrite Forall_map in H0. eapply Forall_impl; [|eapply H0]; intros (?&?) ?.
                rewrite Str_nth_S_tl; auto.
             ++ rewrite Forall_map in H3. eapply Forall_impl; [|eapply H3]; intros (?&?) ?.
                auto.
    - revert xs ess d rs; cofix CoFix; intros * H.
      unfold_Stv xs; unfold_Stv rs;
        try (specialize (H 0); repeat rewrite Str_nth_0 in H;
             destruct H as [(?&?&?&?)|[(?&?&?&?&?&?&?)|(?&?&?&?&?&?&?)]];
             discriminate).
      + constructor.
        * cofix_step CoFix H.
          destruct H as [(?&?&?&?)|[(?&?&?&?&?&?&?)|(?&?&?&?&?&?&?)]].
          -- left; intuition.
             apply Forall_map, Forall_forall; intros (?&?) Hin;
               eapply Forall_forall in Hin; eauto; simpl in Hin; auto.
             destruct d; auto.
          -- subst; right; left. repeat esplit; eauto.
             ++ rewrite Forall_map. eapply Forall_impl; [|eapply H0]; intros (?&?) ?; simpl.
                rewrite <-Str_nth_S_tl; auto.
             ++ rewrite Exists_map. eapply Exists_exists in H1 as ((?&?)&?&?&?); subst.
                eapply Exists_exists; repeat (esplit; eauto).
             ++ destruct d; simpl in *; auto.
          -- subst; right; right. repeat esplit; eauto.
             ++ rewrite Forall_map. eapply Forall_impl; [|eapply H0]; intros (?&?) ?; simpl.
                rewrite <-Str_nth_S_tl; auto.
             ++ rewrite Forall_map. eapply Forall_impl; [|eapply H1]; intros (?&?) ?; simpl.
                auto.
             ++ destruct d; simpl in *; eauto.
        * destruct (H 0) as [(?&?&?&?)|[(?&?&?&?&?&?&?)|(?&?&?&?&?&?&?)]]; try discriminate.
          apply Forall_forall; intros (?&?) Hin;
            eapply Forall_forall in Hin; eauto; simpl in *; auto.
        * destruct (H 0) as [(?&?&?&?)|[(?&?&?&?&?&?&?)|(?&?&?&?&?&?&?)]]; try discriminate.
          destruct d; auto.
      + destruct (H 0) as [(?&?&?&?)|[(?&?&Hc&?&?&?&Hr)|(?&?&Hc&?&?&Hd&Hr)]]; try discriminate.
        1,2:inv Hc; inv Hr.
        * econstructor; eauto.
          cofix_step CoFix H.
          destruct H as [(?&?&?&?)|[(?&?&?&?&?&?&?)|(?&?&?&?&?&?&?)]].
          -- left; intuition.
             eapply Forall_map, Forall_impl; [|eapply H3]; intros (?&?) ?; auto.
             destruct d; auto.
          -- subst; right; left. repeat esplit; eauto.
             ++ rewrite Forall_map. eapply Forall_impl; [|eapply H3]; intros (?&?) ?; simpl.
                rewrite <-Str_nth_S_tl; auto.
             ++ rewrite Exists_map. eapply Exists_exists in H4 as ((?&?)&?&?&?); subst.
                eapply Exists_exists; repeat (esplit; eauto).
             ++ destruct d; simpl in *; auto.
          -- subst; right; right. repeat esplit; eauto.
             ++ rewrite Forall_map. eapply Forall_impl; [|eapply H3]; intros (?&?) ?; simpl.
                rewrite <-Str_nth_S_tl; auto.
             ++ rewrite Forall_map. eapply Forall_impl; [|eapply H4]; intros (?&?) ?; simpl.
                auto.
             ++ destruct d; simpl in *; eauto.
        * destruct d as [(?&?)|]; simpl in *; try rewrite Str_nth_0_hd in Hd; simpl in *; inv Hd.
          eapply CasePDef; eauto.
          cofix_step CoFix H.
          destruct H as [(?&?&?&?)|[(?&?&?&?&?&?&?)|(?&?&?&?&?&?&?)]].
          -- left; intuition.
             eapply Forall_map, Forall_impl; [|eapply H2]; intros (?&?) ?; auto.
          -- subst; right; left. repeat esplit; eauto.
             ++ rewrite Forall_map. eapply Forall_impl; [|eapply H2]; intros (?&?) ?; simpl.
                rewrite <-Str_nth_S_tl; auto.
             ++ rewrite Exists_map. eapply Exists_exists in H3 as ((?&?)&?&?&?); subst.
                eapply Exists_exists; repeat (esplit; eauto).
          -- subst; right; right. repeat esplit; eauto.
             ++ rewrite Forall_map. eapply Forall_impl; [|eapply H2]; intros (?&?) ?; simpl.
                rewrite <-Str_nth_S_tl; auto.
             ++ rewrite Forall_map. eapply Forall_impl; [|eapply H3]; intros (?&?) ?; simpl.
                auto.
  Qed.

  CoFixpoint clocks_of (ss: list (Stream svalue)) : Stream bool :=
    existsb (fun s => hd s <>b absent) ss ⋅ clocks_of (List.map (@tl svalue) ss).

  (** *** bools_of : extract boolean from an svalue stream *)

  CoInductive bools_of : Stream svalue -> Stream bool -> Prop :=
  | bools_of_P:
      forall c' vs bs,
        bools_of vs bs ->
        bools_of (present (Venum c') ⋅ vs) ((c' ==b true_tag) ⋅ bs)
  | bools_of_A:
      forall vs bs,
        bools_of vs bs ->
        bools_of (absent ⋅ vs) (false ⋅ bs).

  Instance bools_of_Proper:
    Proper (@EqSt svalue ==> @EqSt bool ==> Basics.impl)
           bools_of.
  Proof.
    cofix CoFix.
    intros [x xs] [x' xs'] Heq1 [y ys] [y' ys'] Heq2 Hsem; subst.
    inv Hsem; inv Heq1; inv Heq2;
      simpl in *; subst; econstructor; eauto.
    1,2:eapply CoFix; eauto.
  Qed.

  Corollary bools_of_det : forall xs ys ys',
      bools_of xs ys ->
      bools_of xs ys' ->
      ys ≡ ys'.
  Proof.
    cofix CoFix.
    intros * Hb1 Hb2. inv Hb1; inv Hb2.
    1,2:constructor; eauto.
  Qed.

  Lemma bools_of_absent :
    bools_of (Streams.const absent) (Streams.const false).
  Proof.
    cofix CoFix.
    rewrite (CommonStreams.const_Cons absent), (CommonStreams.const_Cons false).
    constructor; auto.
  Qed.

  Lemma bools_of_nth : forall xs bs,
      bools_of xs bs <->
      (forall n, (exists c, xs # n = present (Venum c) /\ bs # n = (c ==b true_tag)) \/
            (xs # n = absent /\ bs # n = false)).
  Proof.
    split; intros Hbools.
    - intros n. revert xs bs Hbools.
      induction n; intros; unfold_Stv xs; unfold_St bs;
        repeat rewrite Str_nth_0_hd; repeat rewrite Str_nth_S_tl; simpl;
          inv Hbools; eauto.
    - revert xs bs Hbools. cofix CoFix.
      intros; unfold_Stv xs; unfold_St bs.
      + assert (Hb0 := Hbools 0).
        repeat rewrite Str_nth_0_hd in Hb0; simpl in Hb0.
        destruct Hb0 as [(?&?&?)|(?&?)]; subst; try congruence.
        constructor. eapply CoFix; intros.
        specialize (Hbools (S n)). repeat rewrite Str_nth_S_hd in Hbools; simpl in Hbools; auto.
      + assert (Hb0 := Hbools 0).
        repeat rewrite Str_nth_0_hd in Hb0; simpl in Hb0.
        destruct Hb0 as [(?&?&?)|(?&?)]; subst; try congruence. inv H.
        constructor. eapply CoFix; intros.
        specialize (Hbools (S n)). repeat rewrite Str_nth_S_hd in Hbools; simpl in Hbools; auto.
  Qed.

  CoFixpoint disj_str (rss : list (Stream bool)) : Stream bool :=
    (existsb (fun rs => hd rs) rss) ⋅ (disj_str (List.map (@tl _) rss)).

  Lemma disj_str_spec:
    forall n rss,
      (disj_str rss) # n = existsb (fun rs => rs # n) rss.
  Proof.
    induction n; intros *; rewrite unfold_Stream at 1; simpl.
    + induction rss; simpl; auto.
    + rewrite Str_nth_S. induction rss; simpl; eauto.
      rewrite IHn; simpl.
      rewrite Str_nth_S_tl. f_equal.
      rewrite existsb_map. apply existsb_ext.
      intros ?. apply Str_nth_S_tl.
  Qed.

  Corollary disj_str_cons: forall r rs,
      disj_str (r::rs) ≡ disj_str [r;disj_str rs].
  Proof.
    intros.
    eapply ntheq_eqst; intros n.
    repeat (rewrite disj_str_spec; simpl).
    rewrite Bool.orb_false_r. reflexivity.
  Qed.

  Corollary disj_str_app : forall rs1 rs2,
      disj_str (rs1++rs2) ≡ disj_str [disj_str rs1;disj_str rs2].
  Proof.
    intros.
    eapply ntheq_eqst; intros n.
    repeat (rewrite disj_str_spec; simpl).
    rewrite Bool.orb_false_r, existsb_app. reflexivity.
  Qed.

  Definition bools_ofs (vs : list (Stream svalue)) (rs : Stream bool) :=
    exists rss, Forall2 bools_of vs rss /\
           rs ≡ disj_str rss.

  Lemma bools_ofs_empty :
    bools_ofs nil (Streams.const false).
  Proof.
    exists nil. split; auto.
    apply ntheq_eqst. intros n.
    rewrite disj_str_spec; simpl.
    setoid_rewrite const_nth. reflexivity.
  Qed.

  Lemma bools_ofs_absent {A} : forall (xs : list A),
      bools_ofs (List.map (fun _ => Streams.const absent) xs) (Streams.const false).
  Proof.
    intros *.
    unfold bools_ofs. exists (List.map (fun _ => Streams.const false) xs).
    split.
    - rewrite Forall2_map_1, Forall2_map_2.
      eapply Forall2_same, Forall_forall. intros ? _. apply bools_of_absent.
    - apply ntheq_eqst. intros n.
      rewrite disj_str_spec.
      rewrite existsb_map, const_nth.
      induction xs; simpl; auto.
  Qed.

  Instance bools_ofs_Proper:
    Proper (@EqSts svalue ==> @EqSt bool ==> Basics.impl)
           bools_ofs.
  Proof.
    intros xs xs' Eq1 bs bs' Eq2 (rs&Bools&Disj).
    rewrite Eq2 in Disj.
    exists rs; split; auto.
    unfold EqSts in Eq1. symmetry in Eq1.
    eapply Forall2_trans_ex in Bools; eauto.
    eapply Forall2_impl_In; [|eauto]. intros ? ? _ _ (?&?&Eq&?).
    rewrite Eq; auto.
  Qed.

  Lemma bools_ofs_det : forall xs r r',
      bools_ofs xs r ->
      bools_ofs xs r' ->
      r ≡ r'.
  Proof.
    intros * (?&Bools1&Disj1) (?&Bools2&Disj2).
    rewrite Disj1, Disj2. clear Disj1 Disj2.
    eapply ntheq_eqst. intros n.
    repeat rewrite disj_str_spec in *.
    revert x x0 Bools1 Bools2.
    induction xs; intros; simpl in *; inv Bools1; inv Bools2; simpl in *; auto.
    eapply bools_of_det in H1; eauto. erewrite H1, IHxs; eauto.
  Qed.

  Instance disj_str_SameElements_Proper:
    Proper (SameElements (@EqSt bool) ==> @EqSt bool) disj_str.
  Proof.
    intros ?? Eq.
    eapply ntheq_eqst. intros n.
    repeat rewrite disj_str_spec.
    induction Eq; simpl; auto.
    - rewrite H, IHEq; auto.
    - destruct (x # n) eqn:Hxn; simpl; auto.
      symmetry. rewrite <- Exists_existsb with (P:=fun x' => x' # n = x # n).
      2:{ intros x0. split; intros; congruence. }
      eapply SetoidList.InA_altdef in H.
      eapply Exists_Exists; [|eauto]. intros ? Eq. rewrite Eq; auto.
    - destruct (x # n) eqn:Hxn; simpl; auto.
      rewrite <- Exists_existsb with (P:=fun x' => x' # n = x # n).
      2:{ intros x0. split; intros; congruence. }
      eapply SetoidList.InA_altdef in H.
      eapply Exists_Exists; [|eauto]. intros ? Eq. rewrite Eq; auto.
    - destruct (existsb _ l') eqn:Ex.
      + rewrite <-Exists_existsb with (P:=fun x => x # n = true) in *. 2,3:reflexivity.
        rewrite H; auto.
      + rewrite existsb_Forall, forallb_Forall in *. rewrite H; auto.
    - congruence.
  Qed.

  Instance bools_ofs_SameElements_Proper:
    Proper (SameElements (@EqSt svalue) ==> eq ==> Basics.impl)
           bools_ofs.
  Proof.
    intros xs xs' Eq bs bs' ? (rs&Bools&Disj); subst.
    eapply Forall2_SameElements_1 in Bools as (rs'&Perm'&Bools'); eauto.
    econstructor; esplit. eauto.
    rewrite Disj, Perm'. 1-3:eauto using EqStrel_Reflexive, EqStrel_Symmetric.
    - reflexivity.
    - intros * Eq1 Eq2 Bools'. rewrite <-Eq1, <-Eq2; auto.
    - eauto using bools_of_det.
  Qed.

  (** ** fby stream *)

  CoFixpoint sfby (v : value) (str : Stream svalue) :=
    match str with
    | (present v') ⋅ str' => (present v) ⋅ (sfby v' str')
    | absent ⋅ str' => absent ⋅ (sfby v str')
    end.

  Fact sfby_Cons : forall v y ys,
      sfby v (y ⋅ ys) =
      match y with
      | present v' => (present v) ⋅ (sfby v' ys)
      | absent => absent ⋅ (sfby v ys)
      end.
  Proof.
    intros v y ys.
    rewrite unfold_Stream at 1; simpl.
    destruct y; reflexivity.
  Qed.

  Add Parametric Morphism : sfby
      with signature eq ==> @EqSt svalue ==> @EqSt svalue
    as sfby_EqSt.
  Proof.
    cofix CoFix.
    intros v [x xs] [y ys] Heq.
    inv Heq; simpl in *; subst.
    constructor; simpl.
    + destruct y; auto.
    + destruct y; auto.
  Qed.

  (** ** Properties of history *)

  Definition history := Env.t (Stream svalue).
  Definition history_tl (H: history) : history := Env.map (@tl svalue) H.

  Fact history_tl_find_Some : forall (H: history) id vs,
      Env.find id H = Some vs ->
      Env.find id (history_tl H) = Some (tl vs).
  Proof.
    intros H id vs Hfind.
    unfold history_tl.
    rewrite Env.Props.P.F.map_o.
    rewrite Hfind. reflexivity.
  Qed.

  Fact history_tl_find_Some' : forall (H: history) id vs,
      Env.find id (history_tl H) = Some vs ->
      exists v, Env.find id H = Some (v ⋅ vs).
  Proof.
    intros H id vs Hfind.
    unfold history_tl in Hfind.
    rewrite Env.Props.P.F.map_o in Hfind.
    apply option_map_inv_Some in Hfind as [vs' [Hfind Htl]]; subst.
    exists (hd vs'). destruct vs'; auto.
  Qed.

  Fact history_tl_find_None : forall (H: history) id,
      Env.find id H = None ->
      Env.find id (history_tl H) = None.
  Proof.
    intros H id Hfind.
    unfold history_tl.
    rewrite Env.Props.P.F.map_o.
    rewrite Hfind. reflexivity.
  Qed.

  Fact history_tl_find_None' : forall (H: history) id,
      Env.find id (history_tl H) = None ->
      Env.find id H = None.
  Proof.
    intros H id Hfind.
    unfold history_tl in Hfind.
    rewrite Env.Props.P.F.map_o in Hfind.
    apply option_map_inv_None in Hfind; auto.
  Qed.

  Definition env := Env.t svalue.

  Definition history_nth (n : nat) (H: history) : env :=
    Env.map (Str_nth n) H.

  Definition history_hd (H: history) : env := history_nth 0 H.

  Lemma history_nth_tl : forall H n,
      history_nth (S n) H = history_nth n (history_tl H).
  Proof.
    intros H n.
    unfold history_nth, history_tl.
    rewrite Env.map_map. eapply Env.map_ext.
    intros [x xs]. rewrite Str_nth_S; auto.
  Qed.

  Fact history_nth_find_None : forall n (H: history) id,
      Env.find id H = None ->
      Env.find id (history_nth n H) = None.
  Proof.
   induction n; intros H id Hfind.
   - unfold history_nth.
     rewrite Env.Props.P.F.map_o, Hfind. reflexivity.
   - rewrite history_nth_tl.
     rewrite IHn; auto.
     erewrite history_tl_find_None; auto.
  Qed.

  Fact history_nth_find_None' : forall n (H: history) id,
      Env.find id (history_nth n H) = None ->
      Env.find id H = None.
  Proof.
   induction n; intros H id Hfind.
   - unfold history_nth in Hfind.
     rewrite Env.Props.P.F.map_o in Hfind.
     apply option_map_inv_None in Hfind; auto.
   - rewrite history_nth_tl in Hfind.
     apply IHn in Hfind.
     apply history_tl_find_None' in Hfind; auto.
  Qed.

  Fact history_nth_find_Some : forall n (H: history) id vs,
      Env.find id H = Some vs ->
      Env.find id (history_nth n H) = Some (Str_nth n vs).
  Proof.
   induction n; intros H id vs Hfind.
   - unfold history_nth.
     rewrite Env.Props.P.F.map_o, Hfind. reflexivity.
   - rewrite history_nth_tl.
     rewrite IHn with (vs:=(tl vs)); auto.
     erewrite history_tl_find_Some; auto.
  Qed.

  Fact history_nth_find_Some' : forall n (H: history) id v,
      Env.find id (history_nth n H) = Some v ->
      exists vs, Env.find id H = Some vs /\ vs # n = v.
  Proof.
   induction n; intros H id v Hfind.
   - unfold history_nth in Hfind.
     rewrite Env.Props.P.F.map_o in Hfind.
     apply option_map_inv_Some in Hfind as [vs' [Hfind Heq]].
     exists vs'; auto.
   - rewrite history_nth_tl in Hfind.
     apply IHn in Hfind as [vs' [Hfind Heq]].
     apply history_tl_find_Some' in Hfind as [v' Hfind].
     exists (v' ⋅ vs'); split; auto.
  Qed.

  Fact history_nth_find_Some'' : forall (H: history) vs id,
      (forall n, Env.find id (history_nth n H) = Some (vs # n)) ->
      exists vs', Env.find id H = Some vs' /\ vs' ≡ vs.
  Proof.
    intros * Hfind.
    destruct (Env.find id H) as [vs'|] eqn:Hfind'.
    - exists vs'. split; auto.
      apply ntheq_eqst. intros n.
      specialize (Hfind n).
      apply history_nth_find_Some' in Hfind as [vs'' [? ?]].
      rewrite H0 in Hfind'. inv Hfind'; auto.
    - apply history_nth_find_None with (n:=0) in Hfind'.
      congruence.
  Qed.

  Fact history_hd_refines : forall H H',
      Env.refines eq H H' ->
      Env.refines eq (history_hd H) (history_hd H').
  Proof.
    intros H H' Href x v Hfind.
    eapply history_nth_find_Some' in Hfind as [vs' [Hfind Heq]].
    exists v; split; auto.
    eapply Href in Hfind as [vs'' [? Hfind]]; subst.
    eapply history_nth_find_Some in Hfind; eauto.
  Qed.

  Fact history_tl_refines : forall H H',
      Env.refines (@EqSt _) H H' ->
      Env.refines (@EqSt _) (history_tl H) (history_tl H').
  Proof.
    intros H H' Href x vs Hfind.
    eapply history_tl_find_Some' in Hfind as [v' Hfind].
    eapply Href in Hfind as [vs' [Heq' Hfind']].
    exists (tl vs').
    apply history_tl_find_Some in Hfind'.
    split; auto.
    destruct vs'; simpl. inv Heq'; auto.
  Qed.

  Lemma env_find_tl : forall x x' H H',
      orel (@EqSt svalue) (Env.find x H) (Env.find x' H') ->
      orel (@EqSt svalue)
           (Env.find x (history_tl H))
           (Env.find x' (history_tl H')).
  Proof.
    intros * Hfind. unfold history_tl.
    do 2 rewrite Env.Props.P.F.map_o.
    inversion Hfind as [|?? Hs]; eauto; econstructor; now rewrite Hs.
  Qed.

  (** * sem_var
        This is common to Lustre and NLustre Semantics *)

  Inductive sem_var: history -> ident -> Stream svalue -> Prop :=
    sem_var_intro:
      forall H x xs xs',
        Env.MapsTo x xs' H ->
        xs ≡ xs' ->
        sem_var H x xs.

  Add Parametric Morphism : sem_var
    with signature Env.Equiv (@EqSt _) ==> @eq ident ==> @EqSt svalue ==> Basics.impl
      as sem_var_morph.
  Proof.
    intros H H' ? x xs xs' Heq; subst.
    intros Hsem; inv Hsem.
    eapply Env.Equiv_orel in H0. rewrite H2 in H0. inv H0.
    econstructor.
    - symmetry in H4. eapply H4.
    - rewrite <-H5, <-H3, Heq. reflexivity.
  Qed.

  Lemma sem_var_det : forall H x s1 s2,
      sem_var H x s1 ->
      sem_var H x s2 ->
      s1 ≡ s2.
  Proof.
    intros * Hsem1 Hsem2.
    inv Hsem1. inv Hsem2.
    rewrite H2, H4.
    apply Env.find_1 in H1. apply Env.find_1 in H3.
    rewrite H1 in H3. inv H3. reflexivity.
  Qed.

  Lemma env_maps_hd :
    forall i v s H,
      Env.MapsTo i (v ⋅ s) H -> Env.MapsTo i v (history_hd H).
  Proof.
    intros * Hmap.
    unfold history_hd.
    assert (v = Streams.hd (v ⋅ s)) as Hv by auto.
    rewrite Hv. eapply Env.map_1. assumption.
  Qed.

  Lemma env_maps_tl :
    forall i v s H,
      Env.MapsTo i (v ⋅ s) H -> Env.MapsTo i s (history_tl H).
  Proof.
    intros * Hmap.
    unfold history_tl.
    assert (s = Streams.tl (v ⋅ s)) as Hs by auto.
    rewrite Hs. eapply Env.map_1. assumption.
  Qed.

  Lemma sem_var_step :
    forall H x v s,
      sem_var H x (v ⋅ s) -> sem_var (history_tl H) x s.
  Proof.
    intros * Hsem.
    inv Hsem.
    destruct xs'.
    econstructor.
    eapply env_maps_tl; eauto. now inv H2.
  Qed.

  Lemma sem_var_step_inv :
    forall H x s,
      sem_var (history_tl H) x s ->
      exists v, sem_var H x (v ⋅ s).
  Proof.
    intros * Hsem.
    inv Hsem. unfold Env.MapsTo, history_tl in *.
    rewrite Env.Props.P.F.map_o in H1. eapply option_map_inv in H1 as ((v&s')&Hfind&Heq); subst; simpl in *.
    exists v. econstructor; eauto. constructor; auto.
  Qed.

  Lemma sem_var_step_nl :
    forall H x v s,
      sem_var H x (v ⋅ s) -> sem_var (history_tl H) x s.
  Proof.
    intros * Hsem.
    inv Hsem.
    destruct xs'.
    econstructor.
    eapply env_maps_tl; eauto. now inv H2.
  Qed.

  Lemma sem_var_switch_env:
    forall H H' x v,
      orel (@EqSt svalue) (Env.find x H) (Env.find x H') ->
      sem_var H x v <-> sem_var H' x v.
  Proof.
    intros * Hfind; split; intro Hsem; inversion_clear Hsem as [???? Hr];
      rewrite Hr in Hfind; inv Hfind;
        eapply Env.find_1 in Hr; rewrite H1; [rewrite H3|rewrite <- H3];
          econstructor; eauto using Env.find_2; reflexivity.
  Qed.

  Lemma sem_var_env_eq :
    forall H H' xs ss,
      Forall2 (sem_var H) xs ss ->
      Forall2 (sem_var H') xs ss ->
      Forall (fun x => orel (EqSt (A:=svalue)) (Env.find x H) (Env.find x H')) xs.
  Proof.
    induction 1; auto. intros Hf. inv Hf. constructor; auto.
    do 2 take (sem_var _ _ _) and inv it.
    do 2 take (Env.MapsTo _ _ _) and apply Env.find_1 in it as ->.
    now rewrite <- H4, <- H5.
  Qed.

  (** ** clocks_of and its properties *)

  Add Parametric Morphism : clocks_of
      with signature @EqSts svalue ==> @EqSt bool
        as clocks_of_EqSt.
  Proof.
    cofix Cofix.
    intros xs xs' Exs.
    constructor; simpl.
    - clear Cofix.
      revert dependent xs'.
      induction xs; intros; try inv Exs; simpl; auto.
      f_equal; auto.
      now rewrite H1.
    - apply Cofix.
      clear Cofix.
      revert dependent xs'.
      induction xs; intros; try inv Exs; simpl; constructor.
      + now rewrite H1.
      + now apply IHxs.
  Qed.

  Lemma clocks_of_EqStN : forall n xs1 xs2,
      Forall2 (EqStN n) xs1 xs2 ->
      EqStN n (clocks_of xs1) (clocks_of xs2).
  Proof.
    induction n; intros * Heq; auto.
    rewrite (unfold_Stream (clocks_of xs1)), (unfold_Stream (clocks_of xs2)); simpl.
    constructor; auto.
    - clear - Heq. induction Heq; simpl; auto.
      f_equal; auto. now inv H.
    - eapply IHn.
      rewrite Forall2_map_1, Forall2_map_2. eapply Forall2_impl_In; [|eauto]; intros.
      inv H1; auto.
  Qed.

  Lemma clocks_of_nth : forall n xs,
      (clocks_of xs) # n = existsb (fun s => s <>b absent) (List.map (Str_nth n) xs).
  Proof.
    induction n; intros x.
    - cbn. rewrite existsb_map; auto.
    - rewrite Str_nth_S_tl; simpl.
      rewrite IHn, map_map.
      repeat rewrite existsb_map.
      reflexivity.
  Qed.

  (** ** sem_clock and its properties *)

  CoInductive sem_clock: history -> Stream bool -> clock -> Stream bool -> Prop :=
  | Sbase:
      forall H b b',
        b ≡ b' ->
        sem_clock H b Cbase b'
  | Son:
      forall H b bk bs ck x t k xs,
        sem_clock H b ck (true ⋅ bk) ->
        sem_var H x (present (Venum k) ⋅ xs) ->
        sem_clock (history_tl H) (tl b) (Con ck x (t, k)) bs ->
        sem_clock H b (Con ck x (t, k)) (true ⋅ bs)
  | Son_abs1:
      forall H b bk bs ck x k xs,
        sem_clock H b ck (false ⋅ bk) ->
        sem_var H x (absent ⋅ xs) ->
        sem_clock (history_tl H) (tl b) (Con ck x k) bs ->
        sem_clock H b (Con ck x k) (false ⋅ bs)
  | Son_abs2:
      forall H b bk bs ck x t k k' xs,
        sem_clock H b ck (true ⋅ bk) ->
        sem_var H x (present (Venum k') ⋅ xs) ->
        k <> k' ->
        sem_clock (history_tl H) (tl b) (Con ck x (t, k)) bs ->
        sem_clock H b (Con ck x (t, k)) (false ⋅ bs).

  Fact history_tl_Equiv : forall H H',
      Env.Equiv (@EqSt _) H H' ->
      Env.Equiv (@EqSt _) (history_tl H) (history_tl H').
  Proof.
    intros * [Heq1 Heq2].
    unfold history_tl. constructor.
    - intros k.
      repeat rewrite Env.Props.P.F.map_in_iff; auto.
    - intros * Hm1 Hm2.
      rewrite Env.Props.P.F.map_mapsto_iff in Hm1, Hm2.
      destruct Hm1 as [e1 [Htl1 Hm1]]. destruct Hm2 as [e2 [Htl2 Hm2]]. subst.
      apply tl_EqSt; eauto.
  Qed.

  Add Parametric Morphism : sem_clock
      with signature Env.Equiv (@EqSt _) ==> @EqSt bool ==> eq ==> @EqSt bool ==> Basics.impl
        as sem_clock_morph.
  Proof.
    cofix CoFix.
    intros H H' Hequiv b b' Eb ck bk bk' Ebk Sem.
    inv Sem.
    1:constructor; now rewrite <-Ebk, <-Eb.
    1-3:(destruct bk' as [[]]; inv Ebk; simpl in *; try discriminate).
    1,2,3:(assert (Hequiv':=Hequiv); destruct Hequiv' as [Heq1 Heq2]; inv H2;
           take (Env.MapsTo _ _ _) and (apply Env.find_In in it as HIn);
           rewrite Heq1, Env.In_find in HIn; destruct HIn as [xs'' Hfind];
           assert (Heq:=Hfind); eapply Heq2 in Heq; eauto).
    1,2:(econstructor; eauto). 7:eapply Son_abs2; eauto.
    1,3,4,6,7,9:(eapply CoFix; eauto; try reflexivity; inv Eb; auto).
    1-3:apply history_tl_Equiv; auto.
    1-3:econstructor; [eauto|etransitivity; eauto].
  Qed.

  Lemma sc_step :
    forall H b ck s ss,
      sem_clock H b ck (s ⋅ ss) ->
      sem_clock (history_tl H) (Streams.tl b) ck ss.
  Proof.
    intros * Hsem.
    inv Hsem; auto. econstructor. rewrite H1. simpl. reflexivity.
  Qed.

  Ltac discriminate_stream :=
    let H := fresh in
    match goal with
    | H1: ?b ≡ true ⋅ _, H2 : ?b ≡ false ⋅ _ |- _ =>
      rewrite H1 in H2; inversion H2 as [? H]; simpl in H; discriminate
    end.

  Ltac discriminate_var :=
    repeat match goal with
           | H: sem_var _ _ _ |- _ => auto
           end;
    match goal with
    | H1: sem_var ?H ?x (present _ ⋅ _),
          H2 : sem_var ?H ?x (absent ⋅ _)
      |- _ => eapply sem_var_det with (2 := H2) in H1;
            inv H1; simpl in *; discriminate
    end.

  Lemma sem_clock_det :
    forall (ck : clock) (H : history)
      (b xs xs' : Stream bool),
      sem_clock H b ck xs ->
      sem_clock H b ck xs' ->
      xs ≡ xs'.
  Proof.
    cofix Cofix. intros * Hsc Hsc'.
    unfold_Stv xs; unfold_Stv xs'.
    - inv Hsc; inv Hsc'.
      rewrite H1 in H2. inv H2. constructor; auto.
      constructor; simpl; auto. eapply Cofix; eauto.
    - inv Hsc; inv Hsc'; try discriminate_stream;
        try discriminate_var.
      take (sem_var _ x (present (Venum k) ⋅ _)) and
           eapply sem_var_det in it; eauto.
      inversion it as [Hit]. simpl in Hit. inv Hit.
      exfalso; auto.
    - inv Hsc; inv Hsc'; try discriminate_stream;
        try discriminate_var.
      take (sem_var _ x (present (Venum k') ⋅ _)) and
           eapply sem_var_det in it; eauto.
      inversion it as [Hit]. simpl in Hit. inv Hit.
      exfalso; auto.
    - inv Hsc; inv Hsc'; constructor; simpl; auto;
        try (now eapply Cofix; eauto).
      rewrite H1 in H2. inv H2. now simpl in H3.
  Qed.

  Fact sem_clock_true_inv : forall H ck b bs bs',
      sem_clock H (b ⋅ bs) ck (true ⋅ bs') ->
      b = true.
  Proof.
    induction ck; intros * Hsem; inv Hsem.
    - inv H1; auto.
    - eapply IHck in H7; auto.
  Qed.

  Ltac discriminate_clock :=
    let HH := fresh in
    match goal with
    | H1: sem_clock ?H ?b ?ck (true ⋅ _),
          H2 : sem_clock ?H ?b ?ck (false ⋅ _) |- _ =>
      eapply sem_clock_det with (2 := H2) in H1; eauto;
      inversion H1 as [HH ?]; simpl in HH; discriminate
    end.

  (** *** sub_clock *)

  CoInductive sub_clock : relation (Stream bool) :=
  | SubP1 : forall s s',
      sub_clock s s' -> sub_clock (true ⋅ s) (true ⋅ s')
  | SubP2 : forall s s',
      sub_clock s s' -> sub_clock (true ⋅ s) (false ⋅ s')
  | SubA : forall s s',
      sub_clock s s' -> sub_clock (false ⋅ s) (false ⋅ s').

  Global Instance sub_clock_trans : Transitive sub_clock.
  Proof.
    cofix Cofix. intros x y z XY YZ.
    unfold_Stv x; unfold_Stv z; inv XY; inv YZ; constructor;
      eapply Cofix; eauto.
  Qed.

  Global Instance sub_clock_refl : Reflexive sub_clock.
  Proof.
    cofix Cofix. intro x.
    unfold_Stv x; constructor; auto.
  Qed.

  Add Parametric Morphism : (sub_clock)
      with signature @EqSt bool ==> @EqSt bool ==> Basics.impl
        as sub_clock_EqSt.
  Proof.
    cofix Cofix. intros b b' Eb c c' Ec Hsub.
    unfold_Stv b'; unfold_Stv c'; try constructor; inv Eb; inv Ec; inv Hsub;
      simpl in *; try discriminate; eapply Cofix; eauto.
  Qed.

  Lemma sub_clock_step :
    forall b b', sub_clock b b' -> sub_clock (Streams.tl b) (Streams.tl b').
  Proof.
    intros * Hs. unfold_Stv b; unfold_Stv b'; inv Hs; eauto.
  Qed.

  Lemma sub_clock_Con :
    forall H b ck x b0 s s',
      sem_clock H b ck s ->
      sem_clock H b (Con ck x b0) s' ->
      sub_clock s s'.
  Proof.
    intros * Hsc Hsc'.
    - destruct ck.
      + inv Hsc. revert Hsc' H1. revert H b x b0 s s'. cofix Cofix; intros.
        unfold_Stv s'; unfold_Stv s.
        * constructor. inv Hsc'. inv H1. eapply Cofix; eauto.
        * inversion_clear Hsc' as [|????????? Hb'| |]. inv Hb'.
        discriminate_stream.
        * constructor. inv Hsc'; inv H1; eapply Cofix; eauto.
        * constructor. inv Hsc'; inv H1; eapply Cofix; eauto.
      + revert Hsc Hsc'. revert H b ck i s s' x b0.
        cofix Cofix; intros.
        unfold_Stv s'; unfold_Stv s.
        * constructor. apply sc_step in Hsc.
          apply sc_step in Hsc'.
          eapply Cofix; eauto.
        * inv Hsc'. discriminate_clock.
        * inv Hsc'. discriminate_clock.
          constructor. apply sc_step in Hsc. eapply Cofix; eauto.
        * constructor. apply sc_step in Hsc.
          apply sc_step in Hsc'. eapply Cofix; eauto.
  Qed.

  Lemma sub_clock_parent :
    forall H b ck ck' s s',
      sem_clock H b ck s ->
      sem_clock H b ck' s' ->
      clock_parent ck ck' ->
      sub_clock s s'.
  Proof.
    intros * Hsc Hsc' Hparent.
    revert dependent s'. induction Hparent; intros.
    - eapply sub_clock_Con; eauto.
    - inversion Hsc' as [|????????? Hck'|???????? Hck' |?????????? Hck'];
        subst; pose proof (sub_clock_Con _ _ _ _ _ _ _ Hck' Hsc');
          apply IHHparent in Hck'; etransitivity; eauto.
  Qed.

  (** ** Aligned and its properties *)

  CoInductive aligned: Stream svalue -> Stream bool -> Prop :=
  | synchro_present:
      forall v vs bs,
        aligned vs bs ->
        aligned (present v ⋅ vs) (true ⋅ bs)
  | synchro_absent:
      forall vs bs,
        aligned vs bs ->
        aligned (absent ⋅ vs) (false ⋅ bs).

  Instance aligned_Proper:
    Proper (@EqSt _ ==> @EqSt bool ==> iff)
           aligned.
  Proof.
    intros vs vs' Heq1 bs bs' Heq2.
    split; revert vs vs' Heq1 bs bs' Heq2;
      cofix aligned_Proper;
      intros [v vs] [v' vs'] Heq1 [b bs] [b' bs'] Heq2 H;
      inv Heq1; inv Heq2; simpl in *; subst; inv H;
        constructor; eauto.
  Qed.

  Lemma aligned_spec : forall vs bs,
      aligned vs bs <->
      (forall n, (exists v, bs # n = true /\ vs # n = present v)
            \/ (bs # n = false /\ vs # n = absent)).
  Proof with eauto.
    split.
    - intros H n. revert vs bs H.
      induction n; intros.
      + inv H; repeat rewrite Str_nth_0.
        * left. exists v...
        * right...
      + inv H; repeat rewrite Str_nth_S...
    - revert vs bs.
      cofix CoFix; intros * H.
      unfold_Stv vs; unfold_Stv bs.
      1,4:(specialize (H 0); repeat rewrite Str_nth_0 in H;
           destruct H as [[? [? ?]]|[? ?]]; try congruence).
      1,2:(constructor; cofix_step CoFix H).
  Qed.

  Lemma aligned_EqSt : forall vs bs1 bs2,
      aligned vs bs1 ->
      aligned vs bs2 ->
      bs1 ≡ bs2.
  Proof.
    cofix CoFix.
    intros [v vs] [b1 bs1] [b2 bs2] Hsync1 Hsync2.
    inv Hsync1; inv Hsync2; constructor; simpl; eauto.
  Qed.

  Lemma const_aligned : forall bs c,
      aligned (const bs c) bs.
  Proof with eauto.
    intros bs c.
    remember (const bs c) as vs.
    rewrite aligned_spec. intros n.
    eapply eq_EqSt, const_spec with (n:=n) in Heqvs.
    rewrite Heqvs; clear Heqvs.
    destruct (bs # n).
    - left. eexists...
    - right...
  Qed.

  Lemma enum_aligned : forall bs c,
      aligned (enum bs c) bs.
  Proof with eauto.
    intros bs c.
    remember (enum bs c) as vs.
    rewrite aligned_spec. intros n.
    eapply eq_EqSt, enum_spec with (n:=n) in Heqvs.
    rewrite Heqvs; clear Heqvs.
    destruct (bs # n).
    - left. eexists...
    - right...
  Qed.

  CoFixpoint abstract_clock (xs: Stream svalue) : Stream bool:=
    match xs with
    | absent ⋅ xs => false ⋅ abstract_clock xs
    | present _ ⋅ xs => true ⋅ abstract_clock xs
    end.

  Add Parametric Morphism : abstract_clock
      with signature @EqSt _ ==> @EqSt bool
        as ac_EqSt.
  Proof.
    cofix Cofix; intros b b' Eb.
    unfold_Stv b; unfold_Stv b';
      constructor; inv Eb; simpl in *; try discriminate; auto.
  Qed.

  Lemma ac_Cons : forall x xs,
      abstract_clock (x ⋅ xs) ≡
      (match x with absent => false | _ => true end) ⋅ (abstract_clock xs).
  Proof.
    intros *. constructor; simpl.
    1,2:destruct x; reflexivity.
  Qed.

  Lemma ac_tl :
    forall s, abstract_clock (Streams.tl s) ≡ Streams.tl (abstract_clock s).
  Proof.
    intros. unfold_Stv s; reflexivity.
  Qed.

  Lemma ac_nth : forall xs n,
      (abstract_clock xs) # n = (match xs # n with absent => false | _ => true end).
  Proof.
    intros xs n. revert xs.
    induction n; intros; unfold_Stv xs; rewrite ac_Cons.
    1,2:rewrite Str_nth_0; auto.
    1,2:repeat rewrite Str_nth_S; eauto.
  Qed.

  Lemma ac_when :
    forall k cs xs rs,
      when k cs xs rs -> abstract_clock cs ≡ abstract_clock xs.
  Proof.
    cofix Cofix.
    intros * Hwhen. inv Hwhen; econstructor; simpl; eauto.
  Qed.

  Lemma ac_const:
    forall c b,
      abstract_clock (const b c) ≡ b.
  Proof.
    cofix Cofix.
    intros *.
    unfold_Stv b; constructor; simpl; auto.
  Qed.

  Lemma ac_enum:
    forall b k,
      abstract_clock (enum b k) ≡ b.
  Proof.
    cofix Cofix.
    intros *.
    unfold_Stv b; constructor; simpl; auto.
  Qed.

  Lemma ac_case:
    forall cs vs d ss,
      case cs vs d ss ->
      abstract_clock cs ≡ abstract_clock ss.
  Proof.
    cofix Cofix.
    intros * Hcase.
    unfold_Stv cs;
      inv Hcase; simpl in *; constructor; simpl; auto.
    1,2,3:eapply Cofix; eauto.
  Qed.

  Lemma ac_lift1 :
    forall op ty s o,
      lift1 op ty s o -> abstract_clock s ≡ abstract_clock o.
  Proof.
    cofix Cofix.
    intros * Hlift.
    unfold_Stv s; inv Hlift; econstructor; simpl; eauto.
  Qed.

  Lemma ac_lift2 :
    forall op ty1 ty2 s1 s2 o,
      lift2 op ty1 ty2 s1 s2 o -> abstract_clock s1 ≡ abstract_clock o.
  Proof.
    cofix Cofix.
    intros * Hlift.
    unfold_Stv s1; inv Hlift; econstructor; simpl; eauto.
  Qed.

  Lemma ac_aligned :
    forall s, aligned s (abstract_clock s).
  Proof.
    cofix Cofix. intro.
    unfold_Stv s; rewrite unfold_Stream; simpl; constructor; auto.
  Qed.

  Lemma sub_clock_sclocksof :
    forall s ss,
      In s ss ->
      Forall (fun s' => sub_clock (abstract_clock s) (abstract_clock s')) ss ->
      clocks_of ss ≡ abstract_clock s.
  Proof.
    intros * Hin Hsub.
    remember (abstract_clock s) as acs eqn: Hacs. apply eq_EqSt in Hacs.
    revert Hin Hacs Hsub. revert s ss acs.
    cofix Cofix. intros.
    rewrite (unfold_Stream s) in *; destruct s as [[|]]; simpl in *;
    rewrite unfold_Stream in Hacs; simpl in Hacs; inversion Hacs as [Hac ?].
    - constructor; simpl in *. rewrite Hac.
      apply existsb_Forall, forallb_Forall, Forall_forall; intros * Hin'.
      pose proof Hin' as Hs; eapply Forall_forall in Hs; eauto; simpl in Hs.
      rewrite Hacs in Hs. inversion Hs as [| |??? HH Hx ]. unfold_Stv x; auto.
      rewrite unfold_Stream in Hx. simpl in Hx. discriminate.
      eapply in_map in Hin. eapply Cofix; eauto. rewrite Forall_map.
      eapply Forall_impl; eauto. intros * HH. simpl in HH.
      rewrite ac_tl. now apply sub_clock_step.
    - constructor; simpl in *. rewrite Hac. rewrite existsb_exists; eauto.
      eapply in_map in Hin. eapply Cofix; eauto. rewrite Forall_map.
      eapply Forall_impl; eauto. intros * HH. simpl in HH.
      rewrite ac_tl. now apply sub_clock_step.
  Qed.

  Fact ac_Streams_const :
    abstract_clock (Streams.const absent) ≡ Streams.const false.
  Proof.
    cofix CoFix.
    constructor; simpl; auto.
  Qed.

  (** *** count and mask *)

  CoFixpoint count_acc (s: nat) (rs: Stream bool): Stream nat :=
    let s := if hd rs then S s else s in
    s ⋅ count_acc s (tl rs).

  Definition count := count_acc 0.

  Lemma count_acc_grow_trans:
    forall s s' rs,
      s' <= s ->
      ForAll (fun x => s' <= hd x) (count_acc s rs).
  Proof.
    cofix Cofix; intros.
    constructor; simpl; destruct (hd rs); auto.
  Qed.

  Corollary count_acc_grow:
    forall s rs,
      ForAll (fun x => s <= hd x) (count_acc s rs).
  Proof.
    intros; apply count_acc_grow_trans; auto.
  Qed.

  Lemma count_S_nth:
    forall n s rs,
      hd (Str_nth_tl n (count_acc (S s) rs)) =
      S (hd (Str_nth_tl n (count_acc s rs))).
  Proof.
    unfold Str_nth.
    induction n; simpl; intros; destruct (hd rs); auto.
  Qed.

  Corollary count_S_nth':
    forall n s rs,
      (count_acc (S s) rs) # n =
      S ((count_acc s rs) # n).
  Proof.
    intros *.
    do 2 (rewrite <-(Nat.add_0_l n), <-Str_nth_plus; symmetry); simpl.
    apply count_S_nth.
  Qed.

  Lemma count_0: forall n r,
      (forall m, m <= n -> r # m = false) <->
      (count r) # n = 0.
  Proof.
    split. revert r.
    - induction n; intros * Hr; unfold_Stv r;
      try rewrite Str_nth_0_hd; try rewrite Str_nth_S_tl; simpl; auto.
      + specialize (Hr 0 (Nat.le_0_l _)). inv Hr.
      + specialize (Hr 0 (Nat.le_0_l _)). inv Hr.
      + apply IHn. intros m Hle.
        specialize (Hr _ (le_n_S _ _ Hle)).
        apply Hr.
    - revert r.
      induction n;
        (intros * Hcount * Hle; destruct m; try lia;
         unfold_Stv r; simpl in *;
         try rewrite Str_nth_0_hd in Hcount; try rewrite Str_nth_0_hd;
         try rewrite Str_nth_S_tl in Hcount; try rewrite Str_nth_S_tl;
         simpl in *; try rewrite count_S_nth' in Hcount; auto; try congruence).
      eapply IHn; eauto. lia.
  Qed.

  Lemma count_not_0: forall n r,
      (exists m, m <= n /\ r # m = true) ->
      (count r) # n > 0.
  Proof.
    induction n; intros * Hr; unfold_Stv r;
      try rewrite Str_nth_0_hd; try rewrite Str_nth_S_tl;
        destruct Hr as (m&Hle&Hr);
        simpl; auto.
    - inv Hle. inv Hr.
    - rewrite count_S_nth'. lia.
    - apply IHn. destruct m.
      + inv Hr.
      + exists m. split; try lia.
        apply Hr.
  Qed.

  Add Parametric Morphism : count
      with signature @EqSt _ ==> @EqSt _
        as count_morph.
  Proof.
    intros ?? Heq. eapply ntheq_eqst; intros n.
    revert x y Heq.
    induction n; intros; unfold_Stv x; unfold_Stv y;
      inv Heq; simpl in *; auto; try congruence.
    1-2:repeat rewrite Str_nth_S_tl in *; simpl in *;
      repeat rewrite count_S_nth'.
    f_equal.
    1,2:apply IHn; auto.
  Qed.

  Lemma count_increasing : forall n1 n2 r,
      n1 <= n2 ->
      (count r) # n1 <= (count r) # n2.
  Proof.
    intros n1 n2. revert n1.
    induction n2; intros * Hle.
    - destruct n1; lia.
    - destruct n1; unfold_Stv r; try rewrite Str_nth_0_hd; repeat rewrite Str_nth_S_tl; simpl;
        repeat rewrite count_S_nth'; try lia.
      + eapply le_n_S, IHn2. lia.
      + eapply IHn2. lia.
  Qed.

  Corollary count_0_inv : forall n r,
      (count r) # n = 0 ->
      r # 0 = false.
  Proof.
    intros * Hcount.
    specialize (count_increasing 0 n r) as Hle.
    rewrite Hcount in Hle. eapply Nat.le_0_r in Hle; try lia.
    rewrite Str_nth_0_hd in Hle.
    unfold_Stv r; simpl in *; auto.
    congruence.
  Qed.

  Fact count_disj_le2 : forall n r1 r2,
      (count r2) # n <= (count (disj_str [r1;r2])) # n.
  Proof.
    induction n; intros;
      repeat rewrite Str_nth_0_hd; repeat rewrite Str_nth_S_tl.
    1,2:unfold_Stv r1; unfold_Stv r2; simpl;
      repeat rewrite count_S_nth'; auto using le_n_S.
  Qed.

  Lemma count_shift : forall n1 n2 r,
      n1 < n2 ->
      (count r) # n2 = (count r) # n1 + (count (Str_nth_tl (S n1) r)) # (n2 - S n1).
  Proof.
    intros n1 n2. revert n1.
    induction n2; intros * Hlt; destruct n1; simpl; try lia;
      repeat rewrite Str_nth_0_hd; repeat rewrite Str_nth_S_tl; simpl.
    - rewrite Nat.sub_0_r. unfold_Stv r; auto.
      rewrite count_S_nth'; auto.
    - unfold_Stv r; auto.
      repeat rewrite count_S_nth'.
      1,2:(erewrite IHn2; [reflexivity|lia]).
  Qed.

  Lemma count_eq_false : forall n1 n2 r,
      n1 < n2 ->
      (count r) # n1 = (count r) # n2 <->
      (forall k, n1 < k -> k <= n2 -> r # k = false).
  Proof.
    intros * Hlt; split.
    - intros * Hcount * Hl1 Hl2.
      erewrite count_shift with (n2:=n2) in Hcount; eauto.
      destruct ((count (Str_nth_tl _ _)) # _) eqn:Hcount'. 2:lia.
      clear Hcount.
      eapply Lt.lt_le_S, Nat.le_exists_sub in Hl1 as (k'&?&Hl1); subst.
      eapply (count_0 _ _) with (m:=k') in Hcount'. 2:lia.
      rewrite Str_nth_plus in Hcount'; auto.
    - intros * Hcount.
      erewrite count_shift with (n2:=n2); eauto.
      rewrite (proj1 (count_0 (_ - _) _)); auto.
      intros ? ?. rewrite Str_nth_plus. apply Hcount; lia.
  Qed.

  Lemma count_between : forall r n1 n2,
      n1 <= n2 ->
      (count r) # n1 = (count r) # n2 ->
      (forall k, n1 <= k -> k <= n2 -> (count r) # k = (count r) # n1).
  Proof.
    intros * Hle Hc ? Hle1 Hle2.
    eapply Nat.le_antisymm.
    - rewrite Hc.
      eapply count_increasing; auto.
    - eapply count_increasing; eauto.
  Qed.

  (** ** mask and friends *)

  CoFixpoint mask {A : Type} (absent: A) (k: nat) (rs: Stream bool) (xs: Stream A) : Stream A :=
    let mask' k' := mask absent k' (tl rs) (tl xs) in
    match k, hd rs with
    | 0, true    => Streams.const absent
    | 0, false   => hd xs  ⋅ mask' 0
    | 1, true    => hd xs  ⋅ mask' 0
    | S k', true => absent ⋅ mask' k'
    | S _, false => absent ⋅ mask' k
    end.

  (** Synchronous value mask *)
  Definition maskv := mask absent.

  (** Masking an history *)
  Definition mask_hist k rs := Env.map (maskv k rs).

  (** Boolean mask *)
  Definition maskb := mask false.

  Lemma mask_nth {A} (absent: A) :
    forall n k rs xs,
      (mask absent k rs xs) # n = if (count rs) # n  =? k then xs # n else absent.
  Proof.
    unfold Str_nth.
    induction n, k as [|[|k]]; intros;
      unfold_Stv rs; simpl; auto.
    - pose proof (count_acc_grow 1 rs) as H.
      apply (ForAll_Str_nth_tl n) in H; inv H.
      assert (hd (Str_nth_tl n (count_acc 1 rs)) <> 0) as E by lia;
        apply beq_nat_false_iff in E; rewrite E.
      pose proof (const_nth n absent); auto.
    - rewrite IHn; unfold count.
      destruct (hd (Str_nth_tl n (count_acc 1 rs)) =? 1) eqn: E;
        rewrite count_S_nth in E.
      + apply beq_nat_true_iff, eq_add_S, beq_nat_true_iff in E; rewrite E; auto.
      + rewrite beq_nat_false_iff, Nat.succ_inj_wd_neg, <-beq_nat_false_iff in E;
          rewrite E; auto.
    - rewrite IHn; unfold count.
      destruct (hd (Str_nth_tl n (count_acc 1 rs)) =? S (S k)) eqn: E;
        rewrite count_S_nth in E.
      + apply beq_nat_true_iff, eq_add_S, beq_nat_true_iff in E; rewrite E; auto.
      + rewrite beq_nat_false_iff, Nat.succ_inj_wd_neg, <-beq_nat_false_iff in E;
          rewrite E; auto.
  Qed.

  Corollary maskv_nth:
    forall n k rs xs,
      (maskv k rs xs) # n = if (count rs) # n =? k then xs # n else absent.
  Proof.
    intros. setoid_rewrite mask_nth; auto.
  Qed.

  Corollary maskb_nth:
    forall n k rs xs,
      (maskb k rs xs) # n = if (count rs) # n  =? k then xs # n else false.
  Proof.
    intros. setoid_rewrite mask_nth; auto.
  Qed.

  Lemma mask_Cons {A} (absent: A) :
    forall k r rs x xs,
      (mask absent k (r ⋅ rs) (x ⋅ xs))
        ≡ (match k with
           | 0 => if r then (Streams.const absent) else (x ⋅ (mask absent 0 rs xs))
           | 1 => if r then (x ⋅ (mask absent 0 rs xs)) else (absent ⋅ mask absent 1 rs xs)
           | S (S _ as k') => if r then (absent ⋅ mask absent k' rs xs) else (absent ⋅ mask absent k rs xs)
           end).
  Proof.
    intros *.
    constructor; simpl.
    1,2:destruct k; [|destruct k]; destruct r; try reflexivity.
  Qed.

  Corollary maskv_Cons :
    forall k r rs x xs,
      (maskv k (r ⋅ rs) (x ⋅ xs))
        ≡ (match k with
           | 0 => if r then (Streams.const absent) else (x ⋅ (maskv 0 rs xs))
           | 1 => if r then (x ⋅ (maskv 0 rs xs)) else (absent ⋅ maskv 1 rs xs)
           | S (S _ as k') => if r then (absent ⋅ maskv k' rs xs) else (absent ⋅ maskv k rs xs)
           end).
  Proof.
    eapply mask_Cons.
  Qed.

  Corollary maskb_Cons :
    forall k r rs x xs,
      (maskb k (r ⋅ rs) (x ⋅ xs))
        ≡ (match k with
           | 0 => if r then (Streams.const false) else (x ⋅ (maskb 0 rs xs))
           | 1 => if r then (x ⋅ (maskb 0 rs xs)) else (false ⋅ maskb 1 rs xs)
           | S (S _ as k') => if r then (false ⋅ maskb k' rs xs) else (false ⋅ maskb k rs xs)
           end).
  Proof.
    eapply mask_Cons.
  Qed.

  Lemma EqSt_unmask {A} (absent: A) : forall b x y,
    (forall (k : nat), mask absent k b x ≡ mask absent k b y) ->
    x ≡ y.
  Proof.
    intros * Heq.
    apply ntheq_eqst. intros n.
    specialize (Heq ((count b) # n)).
    apply Str_nth_EqSt with (n:=n) in Heq.
    repeat rewrite mask_nth in Heq.
    rewrite Nat.eqb_refl in Heq; auto.
  Qed.

  Hint Constructors EqStN.

  Lemma EqStN_mask {A} (absent : A) : forall n rs1 rs2 xs1 xs2,
      EqStN n rs1 rs2 ->
      EqStN n xs1 xs2 ->
      forall k, EqStN n (mask absent k rs1 xs1) (mask absent k rs2 xs2).
  Proof.
    induction n; intros * Heq1 Heq2 k; auto.
    inv Heq1; inv Heq2; repeat rewrite mask_Cons.
    destruct k as [|[|]], x2; try (solve [constructor; auto]).
    reflexivity.
  Qed.

  Corollary EqStNs_mask {A} (absent : A) : forall n rs1 rs2 xs1 xs2,
      EqStN n rs1 rs2 ->
      Forall2 (EqStN n) xs1 xs2 ->
      forall k, Forall2 (EqStN n) (List.map (mask absent k rs1) xs1) (List.map (mask absent k rs2) xs2).
  Proof.
    intros * Heq1 Heq2 ?.
    rewrite Forall2_map_1, Forall2_map_2.
    eapply Forall2_impl_In; [|eauto]; intros.
    eapply EqStN_mask; eauto.
  Qed.

  Lemma EqStN_unmask {A} (absent : A) : forall n rs1 rs2 xs1 xs2,
      EqStN n rs1 rs2 ->
      (forall k, EqStN n (mask absent k rs1 xs1) (mask absent k rs2 xs2)) ->
      EqStN n xs1 xs2.
  Proof.
    induction n; intros * Heq1 Heq2; auto.
    inv Heq1. unfold_St xs1; unfold_St xs2.
    repeat setoid_rewrite mask_Cons in Heq2.
    constructor.
    - destruct x2.
      + specialize (Heq2 1). inv Heq2; auto.
      + specialize (Heq2 0). inv Heq2; auto.
    - eapply IHn; eauto.
      intros k. destruct x2.
      + specialize (Heq2 (S k)). destruct k; inv Heq2; auto.
      + specialize (Heq2 k). destruct k as [|[|]]; inv Heq2; auto.
  Qed.

  Corollary EqStNs_unmask {A} (absent : A) : forall n rs1 rs2 xs1 xs2,
      EqStN n rs1 rs2 ->
      (forall k, Forall2 (EqStN n) (List.map (mask absent k rs1) xs1) (List.map (mask absent k rs2) xs2)) ->
      Forall2 (EqStN n) xs1 xs2.
  Proof.
    intros * Heq1 Heq2.
    setoid_rewrite Forall2_map_1 in Heq2. setoid_rewrite Forall2_map_2 in Heq2.
    eapply Forall2_forall2; split; intros.
    - specialize (Heq2 0). now eapply Forall2_length in Heq2.
    - eapply EqStN_unmask; eauto.
      intros k. specialize (Heq2 k).
      eapply Forall2_forall2 in Heq2 as (_&Heq2); eauto.
  Qed.

  Lemma mask_false_0 {A} (absent: A) : forall xs,
      mask absent 0 (Streams.const false) xs ≡ xs.
  Proof.
    intros *.
    assert (forall k, (count (Streams.const false)) # k = 0) as Count.
    { induction k; simpl; auto. }
    eapply ntheq_eqst. intros k.
    rewrite mask_nth, Count; auto.
  Qed.

  Corollary masks_false_0 {A} (absent: A) : forall xs,
      EqSts (List.map (mask absent 0 (Streams.const false)) xs) xs.
  Proof.
    intros *. unfold EqSts.
    rewrite Forall2_map_1. apply Forall2_same.
    eapply Forall_forall. intros ? _. apply mask_false_0.
  Qed.

  Corollary maskb_false_0 : forall bs,
      maskb 0 (Streams.const false) bs ≡ bs.
  Proof.
    intros *.
    setoid_rewrite mask_false_0. reflexivity.
  Qed.

  Lemma mask_false_S {A} (absent: A) : forall n xs,
      mask absent (S n) (Streams.const false) xs ≡ Streams.const absent.
  Proof.
    intros *.
    assert (forall k, (count (Streams.const false)) # k = 0) as Count.
    { induction k; simpl; auto. }
    eapply ntheq_eqst. intros k.
    rewrite mask_nth, Count, const_nth; auto.
  Qed.

  Corollary masks_false_S {A} (absent: A) : forall n xs,
      EqSts (List.map (mask absent (S n) (Streams.const false)) xs) (List.map (fun _ => Streams.const absent) xs).
  Proof.
    intros *. unfold EqSts.
    rewrite Forall2_map_1, Forall2_map_2. apply Forall2_same.
    eapply Forall_forall. intros ? _. apply mask_false_S.
  Qed.

  Corollary maskb_false_S : forall n bs,
      maskb (S n) (Streams.const false) bs ≡ Streams.const false.
  Proof.
    intros *.
    setoid_rewrite mask_false_S. reflexivity.
  Qed.

  Lemma mask_hist_false_0 : forall H,
      Env.Equiv (@EqSt _) (mask_hist 0 (Streams.const false) H) H.
  Proof.
    intros *.
    eapply Env.Equiv_orel. intros ?.
    setoid_rewrite Env.Props.P.F.map_o.
    destruct (Env.find x H) eqn:Hfind; simpl; constructor.
    eapply mask_false_0.
  Qed.

  Lemma mask_hist_false_S : forall n H,
      Env.Equiv (@EqSt _) (mask_hist (S n) (Streams.const false) H) (Env.map (fun _ => Streams.const absent) H).
  Proof.
    intros *.
    eapply Env.Equiv_orel. intros ?.
    setoid_rewrite Env.Props.P.F.map_o.
    destruct (Env.find x H) eqn:Hfind; simpl; constructor.
    eapply mask_false_S.
  Qed.

  Lemma consolidate_mask {A} (absent: A) : forall P r,
      (Proper (eq ==> (@EqSt _) ==> Basics.impl) P) ->
      (forall k, exists v, P k (mask absent k r v)) ->
      exists v, forall k, P k (mask absent k r v).
  Proof.
    intros * HP Hmask.
    eapply functional_choice in Hmask as (f&?).
    exists (init_from 0 (fun n => (f ((count r) # n)) # n)).
    intros k. specialize (H k).
    eapply HP; eauto.
    eapply ntheq_eqst. intros n.
    repeat rewrite mask_nth.
    destruct (_ =? _) eqn:Hcount; auto.
    apply Nat.eqb_eq in Hcount; subst.
    rewrite init_from_nth, Nat.add_0_r; auto.
  Qed.

  Lemma consolidate_mask_hist : forall P r,
      (Proper (eq ==> (Env.Equiv (@EqSt _)) ==> Basics.impl) P) ->
      (forall k1 k2 H1 H2 d, P k1 H1 -> P k2 H2 -> Env.dom H1 d -> Env.dom H2 d) ->
      (forall k, exists H, P k (mask_hist k r H)) ->
      exists H, forall k, P k (mask_hist k r H).
  Proof.
    intros * HP Hdom Hmask.
    eapply functional_choice in Hmask as (f&?).
    exists (Env.mapi (fun x _ => init_from 0 (fun n => or_default_with absent (fun v => v # n)
                                                            (Env.find x (f ((count r) # n))))) (f 0)).
    assert (forall k1 k2 x, Env.In x (f k1) -> Env.In x (f k2)) as Hdomf.
    { intros * Hin. specialize (H k1) as H1. specialize (H k2) as H2.
      eapply Hdom in H2; try eapply H1. 2:eapply Env.dom_map, Env.dom_elements.
      apply Env.dom_map in H2.
      eapply Env.dom_use; eauto. eapply Env.dom_use; [|eauto]. eapply Env.dom_elements.
    }
    intros k. specialize (H k).
    eapply HP; eauto.
    eapply Env.Equiv_orel; intros.
    unfold mask_hist. rewrite 2 Env.Props.P.F.map_o, Env.gmapi.
    destruct (Env.find x (f 0)) eqn:H0, (Env.find x (f k)) eqn:Hk; simpl; auto.
    - constructor.
      eapply ntheq_eqst. intros n.
      repeat rewrite maskv_nth.
      destruct (_ =? _) eqn:Hcount; auto.
      apply Nat.eqb_eq in Hcount; subst.
      rewrite init_from_nth, Nat.add_0_r; auto.
      rewrite Hk; simpl; auto.
    - exfalso. eapply Env.find_In, Hdomf, Env.Props.P.F.not_find_in_iff in H0; eauto.
    - exfalso. eapply Env.find_In, Hdomf, Env.Props.P.F.not_find_in_iff in Hk; eauto.
  Qed.

  Add Parametric Morphism {A} (absent: A) k : (mask absent k)
      with signature @EqSt _ ==> @EqSt _ ==> @EqSt _
        as mask_morph.
  Proof.
    intros rs rs' Ers xs xs' Exs.
    eapply ntheq_eqst; intros n.
    eapply eqst_ntheq with (n:=n) in Exs.
    rewrite 2 mask_nth, Exs, Ers. reflexivity.
  Qed.

  Add Parametric Morphism k : (maskv k)
      with signature @EqSt _ ==> @EqSt _ ==> @EqSt _
        as maskv_morph.
  Proof.
    intros rs rs' Ers xs xs' Exs.
    apply mask_morph; auto.
  Qed.

  Add Parametric Morphism k : (mask_hist k)
      with signature @EqSt _ ==> Env.Equiv (@EqSt _) ==> Env.Equiv (@EqSt _)
        as mask_hist_morph.
  Proof.
    intros r r' Er H H' EH.
    unfold mask_hist. rewrite Env.Equiv_orel in *; intros x.
    specialize (EH x). repeat rewrite Env.Props.P.F.map_o.
    destruct (Env.find x H); inv EH; simpl; constructor; auto.
    rewrite H2, Er. reflexivity.
  Qed.

  Add Parametric Morphism k : (maskb k)
      with signature @EqSt _ ==> @EqSt _ ==> @EqSt _
        as maskb_morph.
  Proof.
    intros rs rs' Ers xs xs' Exs.
    apply mask_morph; auto.
  Qed.

  Lemma maskb_EqSt' : forall b x y,
    (forall (k : nat), maskb k b x ≡ maskb k b y) ->
    x ≡ y.
  Proof.
    intros * Heq.
    apply ntheq_eqst. intros n.
    specialize (Heq ((count b) # n)).
    apply Str_nth_EqSt with (n:=n) in Heq.
    repeat rewrite maskb_nth in Heq.
    rewrite Nat.eqb_refl in Heq; auto.
  Qed.

  Lemma maskb_idem : forall k b x,
      maskb k b (maskb k b x) ≡ maskb k b x.
  Proof.
    intros.
    eapply ntheq_eqst; intros n.
    repeat rewrite maskb_nth.
    destruct (_ =? k); auto.
  Qed.

  Lemma mask_absent {A} (absent: A) : forall k rs,
      mask absent k rs (Streams.const absent) ≡ Streams.const absent.
  Proof.
    intros *.
    eapply ntheq_eqst. intros n.
    rewrite mask_nth, const_nth.
    destruct (_ =? k); auto.
  Qed.

  Corollary mask_hist_absent: forall k rs (H: Env.t (Stream svalue)),
      Env.Equiv (@EqSt _) (mask_hist k rs (Env.map (fun _ => Streams.const absent) H))
                (Env.map (fun _ => Streams.const absent) H).
  Proof.
    intros *.
    rewrite Env.Equiv_orel. intros x.
    repeat setoid_rewrite Env.Props.P.F.map_o.
    destruct (Env.find _ _); simpl; constructor.
    eapply mask_absent.
  Qed.

  Corollary mask_hist_absent': forall k rs (H: Env.t (Stream svalue)),
      Env.Equiv (@EqSt _) (Env.map (fun _ => Streams.const absent) (mask_hist k rs H))
                (Env.map (fun _ => Streams.const absent) H).
  Proof.
    intros *.
    rewrite Env.Equiv_orel. intros x.
    repeat setoid_rewrite Env.Props.P.F.map_o.
    destruct (Env.find _ _); simpl; constructor.
    reflexivity.
  Qed.

  Corollary maskb_absent: forall k rs,
      maskb k rs (Streams.const false) ≡ Streams.const false.
  Proof.
    intros *.
    eapply ntheq_eqst. intros n.
    rewrite maskb_nth, const_nth.
    destruct (_ =? k); auto.
  Qed.

  Lemma refines_mask : forall r H H' k,
      Env.refines (@EqSt _) H H' ->
      Env.refines (@EqSt _) (mask_hist k r H) (mask_hist k r H').
  Proof.
    unfold mask_hist.
    intros * Href ?? Hfind.
    rewrite Env.Props.P.F.map_o in *.
    apply option_map_inv in Hfind as (?&Hfind&?); subst.
    eapply Href in Hfind as (?&Heq&Hfind).
    rewrite Hfind; simpl.
    do 2 esplit; eauto. now rewrite Heq.
  Qed.

  Lemma refines_unmask : forall r H H',
      (forall k, Env.refines (@EqSt _) (mask_hist k r H) (mask_hist k r H')) ->
      Env.refines (@EqSt _) H H'.
  Proof.
    unfold mask_hist.
    intros ??? Href ?? Hfind.
    specialize (Href 0 x (maskv 0 r v)) as Href0.
    rewrite Env.Props.P.F.map_o, Hfind in Href0; simpl in Href0.
    specialize (Href0 eq_refl) as (?&?&Hfind0).
    rewrite Env.Props.P.F.map_o in Hfind0. apply option_map_inv in Hfind0 as (v'&Hfind'&?); subst.
    exists v'. split; auto.
    eapply ntheq_eqst; intros n.
    specialize (Href ((count r) #n) x).
    repeat rewrite Env.Props.P.F.map_o in Href.
    rewrite Hfind, Hfind' in Href; simpl in Href.
    specialize (Href _ eq_refl) as (?&Heq1&Heq2). inv Heq2.
    eapply eqst_ntheq with (n:=n) in Heq1.
    repeat rewrite maskv_nth, Nat.eqb_refl in Heq1; auto.
  Qed.

  (* Remark mask_const_absent: *)
  (*   forall n rs, *)
  (*     mask n rs (Streams.const absent) ≡ Streams.const absent. *)
  (* Proof. *)
  (*   cofix Cofix; intros. *)
  (*   unfold_Stv rs; rewrite (unfold_Stream (Streams.const absent)); *)
  (*     constructor; destruct n as [|[]]; simpl; auto; try apply Cofix. *)
  (*   reflexivity. *)
  (* Qed. *)

  Lemma clocks_of_mask : forall xs k rs,
      clocks_of (List.map (maskv k rs) xs) ≡ (maskb k rs (clocks_of xs)).
  Proof.
    intros.
    apply ntheq_eqst; intros.
    rewrite maskb_nth. repeat rewrite clocks_of_nth.
    repeat rewrite existsb_map.
    destruct (_ =? k) eqn:Hcount.
    - apply existsb_ext; intros x.
      rewrite maskv_nth, Hcount; auto.
    - rewrite existsb_Forall, forallb_forall.
      intros ? _.
      rewrite maskv_nth, Hcount, neg_eq_svalue.
      apply equiv_decb_refl.
  Qed.

  Lemma ac_mask : forall k rs xs,
      abstract_clock (maskv k rs xs) ≡ maskb k rs (abstract_clock xs).
  Proof.
    cofix CoFix.
    intros.
    unfold_Stv xs; unfold_Stv rs;
      constructor; simpl; destruct k as [|[|?]]; eauto.
    1,2:unfold Streams.const; apply ac_Streams_const.
  Qed.

  Lemma bools_of_mask : forall rs xs bs,
      (forall k, bools_of (maskv k rs xs) (maskb k rs bs)) <->
      bools_of xs bs.
  Proof.
    intros.
    setoid_rewrite bools_of_nth. setoid_rewrite mask_nth.
    split; intros.
    - specialize (H ((count rs) # n) n).
      rewrite Nat.eqb_refl in H; auto.
    - destruct (_ =? _); auto.
  Qed.

  Lemma bools_of_mask_inv : forall rs k xs bs,
      bools_of (maskv k rs xs) bs ->
      exists bs', bs ≡ maskb k rs bs'.
  Proof.
    intros. exists bs.
    eapply ntheq_eqst. intros n.
    eapply bools_of_nth with (n:=n) in H as [(?&?&?)|(?&?)].
    1,2:rewrite maskb_nth, maskv_nth in *; destruct (_ =? _); auto.
    inv H.
  Qed.

  Lemma bools_of_mask_det : forall xs rs k bs1 bs2,
      bools_of xs bs1 ->
      bools_of (maskv k rs xs) bs2 ->
      bs2 ≡ maskb k rs bs1.
  Proof.
    intros * Hb1 Hb2.
    eapply ntheq_eqst; intros n.
    rewrite bools_of_nth in *. setoid_rewrite mask_nth in Hb2. rewrite maskb_nth.
    specialize (Hb1 n) as [(?&?&?)|(?&?)]; specialize (Hb2 n) as [(?&?&?)|(?&?)]; subst.
    1-4:destruct (_ =? _); try congruence.
  Qed.

  Lemma sem_var_mask: forall k r H x v,
      sem_var H x v ->
      sem_var (mask_hist k r H) x (maskv k r v).
  Proof.
    intros * Hvar. inv Hvar.
    econstructor.
    eapply Env.map_1; eauto.
    rewrite H2. reflexivity.
  Qed.

  Lemma sem_var_mask_inv: forall k r H x v,
      sem_var (mask_hist k r H) x v ->
      exists v', sem_var H x v' /\ v ≡ (maskv k r v').
  Proof.
    intros * Hvar. inv Hvar.
    eapply Env.Props.P.F.map_mapsto_iff in H1 as (v'&?&Hmap); subst.
    exists v'. split; auto.
    econstructor; eauto. reflexivity.
  Qed.

  (** *** Caracterizing a stream that is slower than a clock stream *)

  CoInductive slower : Stream svalue -> Stream bool -> Prop :=
  | slowerF : forall vs bs,
      slower vs bs ->
      slower (absent ⋅ vs) (false ⋅ bs)
  | slowerT : forall v vs bs,
      slower vs bs ->
      slower (v ⋅ vs) (true ⋅ bs).

  Definition slower_hist H bs :=
    forall x vs, Env.MapsTo x vs H -> slower vs bs.

  Definition slower_subhist (dom : ident -> Prop) H bs :=
    forall x vs, dom x -> Env.MapsTo x vs H -> slower vs bs.

  Lemma slower_nth : forall bs vs,
      slower vs bs <->
      (forall n, bs # n = false -> vs # n = absent).
  Proof with eauto.
    split.
    - intros H n. revert vs bs H.
      induction n; intros.
      + inv H; repeat rewrite Str_nth_0 in *; auto. inv H0.
      + inv H; repeat rewrite Str_nth_S...
    - revert vs bs.
      cofix CoFix; intros * H.
      unfold_Stv vs; unfold_Stv bs.
      1-3:(constructor; cofix_step CoFix H).
      specialize (H 0) as H0; repeat rewrite Str_nth_0 in H0.
      rewrite H0; auto. constructor; cofix_step CoFix H.
  Qed.

  Add Parametric Morphism : slower
      with signature @EqSt _ ==> @EqSt _ ==> Basics.impl
        as slower_morph.
  Proof.
    intros xs xs' Exs bs bs' Ebs Hs.
    eapply slower_nth; intros.
    eapply slower_nth with (n:=n) in Hs.
    rewrite <-Exs; auto. rewrite Ebs; auto.
  Qed.

  Add Parametric Morphism dom : (slower_subhist dom)
      with signature Env.Equiv (@EqSt _) ==> @EqSt _ ==> Basics.impl
        as slower_subhist_morph.
  Proof.
    intros H H' EH bs bs' Ebs Hs ?? Hdom Hmaps.
    rewrite Env.Equiv_orel in EH. specialize (EH x). rewrite Hmaps in EH. inv EH.
    rewrite <-Ebs, <-H2. eapply Hs; unfold Env.MapsTo; eauto.
  Qed.

  Lemma aligned_slower : forall bs vs,
      aligned vs bs ->
      slower vs bs.
  Proof.
    cofix CoFix; intros.
    inv H; constructor; apply CoFix; auto.
  Qed.

  Lemma sc_slower : forall H bs ck bs' vs,
      sem_clock H bs ck bs' ->
      aligned vs bs' ->
      slower vs bs.
  Proof.
    cofix CoFix.
    destruct ck; intros * Hsem Hal; inv Hsem. 2-4:inv Hal.
    - rewrite <-H1 in Hal.
      apply aligned_slower; auto.
    - unfold_St bs. eapply sem_clock_true_inv in H6; subst.
      constructor. eapply CoFix; eauto.
    - unfold_Stv bs; constructor; eapply CoFix; eauto.
    - unfold_Stv bs; constructor; eapply CoFix; eauto.
  Qed.

  Lemma slower_mask : forall vs bs k r,
      slower vs (maskb k r bs) ->
      vs ≡ maskv k r vs.
  Proof.
    intros * Hslow.
    eapply ntheq_eqst; intros.
    rewrite maskv_nth.
    1-2:destruct (_ =? _) eqn:Hcount; try congruence.
    eapply slower_nth with (n:=n) in Hslow; auto.
    rewrite maskb_nth, Hcount; auto.
  Qed.

  Corollary slower_mask_hist : forall H bs k r,
      slower_hist H (maskb k r bs) ->
      Env.Equiv (@EqSt _) H (mask_hist k r H).
  Proof.
    intros * Hslow.
    eapply Env.Equiv_orel. intros.
    setoid_rewrite Env.Props.P.F.map_o.
    destruct (Env.find _ _) eqn:Hfind; constructor.
    eapply Hslow in Hfind.
    eapply slower_mask; eauto.
  Qed.

  Lemma ac_slower : forall vs,
      slower vs (abstract_clock vs).
  Proof.
    intros.
    rewrite slower_nth. intros n Hac. rewrite ac_nth in Hac.
    destruct (vs # n); auto.
    congruence.
  Qed.

  (** *** filter and friends *)

  (* does not constrain the input history enough in the case of an absence *)
  CoFixpoint filter {A} (abs : A) (sel : enumtag) (es : Stream svalue) (vs : Stream A) : Stream A :=
    (if hd es ==b present (Venum sel) then hd vs else abs) ⋅ (filter abs sel (tl es) (tl vs)).

  (** Synchronous value filter *)
  Definition filterv := filter absent.

  (** Filtering an history *)
  Definition filter_hist sel es := Env.map (filterv sel es).

  (** Boolean filter *)
  Definition filterb := filter false.

  Lemma filter_nth {A} (abs : A) :
    forall n sel es xs,
      (filter abs sel es xs) # n = if es # n ==b present (Venum sel) then xs # n else abs.
  Proof.
    unfold Str_nth.
    induction n; intros; unfold_St es; unfold_St xs; auto.
  Qed.

  Corollary filterv_nth:
    forall n e es xs,
      (filterv e es xs) # n = if es # n ==b present (Venum e) then xs # n else absent.
  Proof.
    intros. setoid_rewrite filter_nth; auto.
  Qed.

  Corollary filterb_nth:
    forall n e es xs,
      (filterb e es xs) # n = if es # n ==b present (Venum e) then xs # n else false.
  Proof.
    intros. setoid_rewrite filter_nth; auto.
  Qed.

  Lemma filter_Cons {A} (absent: A) :
    forall sel e es x xs,
      (filter absent sel (e ⋅ es) (x ⋅ xs))
        ≡ (if e ==b present (Venum sel) then x else absent) ⋅ (filter absent sel es xs).
  Proof.
    intros *.
    constructor; simpl; reflexivity.
  Qed.

  Add Parametric Morphism {A} (absent: A) k : (filter absent k)
      with signature @EqSt _ ==> @EqSt _ ==> @EqSt _
        as filter_morph.
  Proof.
    intros rs rs' Ers xs xs' Exs.
    eapply ntheq_eqst; intros n.
    eapply eqst_ntheq with (n:=n) in Exs.
    rewrite 2 filter_nth, Exs, Ers. reflexivity.
  Qed.

  Add Parametric Morphism k : (filterv k)
      with signature @EqSt _ ==> @EqSt _ ==> @EqSt _
        as filterv_morph.
  Proof.
    intros rs rs' Ers xs xs' Exs.
    apply filter_morph; auto.
  Qed.

  Add Parametric Morphism k : (filter_hist k)
      with signature @EqSt _ ==> Env.Equiv (@EqSt _) ==> Env.Equiv (@EqSt _)
        as filter_hist_morph.
  Proof.
    intros r r' Er H H' EH.
    unfold filter_hist. rewrite Env.Equiv_orel in *; intros x.
    specialize (EH x). repeat rewrite Env.Props.P.F.map_o.
    destruct (Env.find x H); inv EH; simpl; constructor; auto.
    rewrite H2, Er. reflexivity.
  Qed.

  Add Parametric Morphism k : (filterb k)
      with signature @EqSt _ ==> @EqSt _ ==> @EqSt _
        as filterb_morph.
  Proof.
    intros rs rs' Ers xs xs' Exs.
    apply filter_morph; auto.
  Qed.

  Lemma EqSt_unfilter : forall tn es xs ys,
      wt_stream es (Tenum tn) ->
      (forall sel, In sel (seq 0 (snd tn)) -> filterv sel es xs ≡ filterv sel es ys) ->
      slower xs (abstract_clock es) ->
      slower ys (abstract_clock es) ->
      xs ≡ ys.
  Proof.
    intros * Hwt Heq Hcs1 Hcs2.
    eapply ntheq_eqst. intros ?.
    eapply SForall_forall in Hwt. instantiate (1:=n) in Hwt.
    destruct (es # n) eqn:Hes; simpl in *.
    - eapply slower_nth in Hcs1. 2:rewrite ac_nth, Hes; eauto.
      eapply slower_nth in Hcs2. 2:rewrite ac_nth, Hes; eauto.
      congruence.
    - inv Hwt.
      assert (In v0 (seq 0 (snd tn))) as Hin by (apply in_seq; lia).
      specialize (Heq _ Hin). eapply Str_nth_EqSt with (n:=n) in Heq.
      setoid_rewrite filter_nth in Heq; rewrite Hes in Heq; simpl in *.
      repeat rewrite equiv_decb_refl in Heq; auto.
  Qed.

  Lemma EqStN_filter {A} (absent : A) : forall n sc1 sc2 xs1 xs2,
      EqStN n sc1 sc2 ->
      EqStN n xs1 xs2 ->
      forall c, EqStN n (filter absent c sc1 xs1) (filter absent c sc2 xs2).
  Proof.
    induction n; intros * Heq1 Heq2 k; auto.
    inv Heq1; inv Heq2; repeat rewrite filter_Cons.
    destruct k as [|[|]], x2; try (solve [constructor; auto]).
  Qed.

  Lemma EqStN_unfilter : forall n tn sc1 sc2 xs1 xs2,
      wt_stream sc1 (Tenum tn) ->
      wt_stream sc2 (Tenum tn) ->
      EqStN n sc1 sc2 ->
      (forall sel, In sel (seq 0 (snd tn)) -> EqStN n (filterv sel sc1 xs1) (filterv sel sc2 xs2)) ->
      slower xs1 (abstract_clock sc1) ->
      slower xs2 (abstract_clock sc2) ->
      EqStN n xs1 xs2.
  Proof.
    intros * Hwt1 Hwt2 Heq1 Heq2 Hcs1 Hcs2.
    eapply EqStN_spec. intros ? Hlt.
    eapply EqStN_spec in Heq1; [|eauto].
    eapply SForall_forall in Hwt1; instantiate (1:=k) in Hwt1.
    eapply SForall_forall in Hwt2; instantiate (1:=k) in Hwt2.
    destruct (sc2 # k) eqn:Heq3; simpl in *.
    - eapply slower_nth in Hcs1. 2:rewrite ac_nth, Heq1; eauto.
      eapply slower_nth in Hcs2. 2:rewrite ac_nth, Heq3; eauto.
      congruence.
    - inv Hwt2.
      assert (In v0 (seq 0 (snd tn))) as Hin by (apply in_seq; lia).
      specialize (Heq2 _ Hin). eapply EqStN_spec in Heq2; [|eauto].
      setoid_rewrite filter_nth in Heq2. rewrite Heq1, Heq3 in Heq2; simpl in *.
      repeat rewrite equiv_decb_refl in Heq2; auto.
  Qed.

  Lemma ac_filter : forall k sc xs,
      abstract_clock (filterv k sc xs) ≡ filterb k sc (abstract_clock xs).
  Proof.
    intros. apply ntheq_eqst; intros n.
    rewrite ac_nth. setoid_rewrite filter_nth. rewrite ac_nth.
    destruct (_ ==b _); auto.
  Qed.

  Lemma sem_var_filter: forall k r H x v,
      sem_var H x v ->
      sem_var (filter_hist k r H) x (filterv k r v).
  Proof.
    intros * Hvar. inv Hvar.
    econstructor.
    eapply Env.map_1; eauto.
    rewrite H2. reflexivity.
  Qed.

  Lemma sem_var_filter_inv: forall k r H x v,
      sem_var (filter_hist k r H) x v ->
      exists v', sem_var H x v' /\ v ≡ (filterv k r v').
  Proof.
    intros * Hvar. inv Hvar.
    eapply Env.Props.P.F.map_mapsto_iff in H1 as (v'&?&Hmap); subst.
    exists v'. split; auto.
    econstructor; eauto. reflexivity.
  Qed.

  Lemma refines_filter : forall e sc H H',
      Env.refines (@EqSt _) H H' ->
      Env.refines (@EqSt _) (filter_hist e sc H) (filter_hist e sc H').
  Proof.
    unfold filter_hist.
    intros * Href ?? Hfind.
    rewrite Env.Props.P.F.map_o in *.
    apply option_map_inv in Hfind as (?&Hfind&?); subst.
    eapply Href in Hfind as (?&Heq&Hfind).
    rewrite Hfind; simpl.
    do 2 esplit; eauto. now rewrite Heq.
  Qed.

  Lemma filter_absent {A} (absent: A) : forall k sc,
      filter absent k sc (Streams.const absent) ≡ Streams.const absent.
  Proof.
    intros *.
    eapply ntheq_eqst. intros n.
    rewrite filter_nth, const_nth.
    destruct (_ ==b _); auto.
  Qed.

  Corollary filter_hist_absent: forall k sc (H: Env.t (Stream svalue)),
      Env.Equiv (@EqSt _) (filter_hist k sc (Env.map (fun _ => Streams.const absent) H))
                (Env.map (fun _ => Streams.const absent) H).
  Proof.
    intros *.
    rewrite Env.Equiv_orel. intros x.
    repeat setoid_rewrite Env.Props.P.F.map_o.
    destruct (Env.find _ _); simpl; constructor.
    eapply filter_absent.
  Qed.

  Corollary filter_hist_absent': forall k sc (H: Env.t (Stream svalue)),
      Env.Equiv (@EqSt _) (Env.map (fun _ => Streams.const absent) (filter_hist k sc H))
                (Env.map (fun _ => Streams.const absent) H).
  Proof.
    intros *.
    rewrite Env.Equiv_orel. intros x.
    repeat setoid_rewrite Env.Props.P.F.map_o.
    destruct (Env.find _ _); simpl; constructor.
    reflexivity.
  Qed.

  Corollary filterb_absent: forall k sc,
      filterb k sc (Streams.const false) ≡ Streams.const false.
  Proof.
    intros *.
    eapply ntheq_eqst. intros n.
    rewrite filterb_nth, const_nth.
    destruct (_ ==b _); auto.
  Qed.

  Lemma filterb_both_slower : forall k sc bs bs',
      slower sc bs ->
      slower sc bs' ->
      filterb k sc bs ≡ filterb k sc bs'.
  Proof.
    intros * Hslow1 Hslow2.
    apply ntheq_eqst; intros n.
    rewrite slower_nth in *. repeat rewrite filterb_nth.
    specialize (Hslow1 n). specialize (Hslow2 n).
    destruct (sc # n); auto.
    destruct (_ ==b _); auto.
    destruct (bs # n), (bs' # n); auto.
    - specialize (Hslow2 eq_refl); congruence.
    - specialize (Hslow1 eq_refl); congruence.
  Qed.

End COINDSTREAMS.

Module CoindStreamsFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Clocks : CLOCKS Ids Op OpAux)
<: COINDSTREAMS Ids Op OpAux Clocks.
  Include COINDSTREAMS Ids Op OpAux Clocks.
End CoindStreamsFun.
