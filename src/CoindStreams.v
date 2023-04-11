From Coq Require Import List.
Import List.ListNotations.
From Coq Require Export Lists.Streams.
From Coq Require Import Setoid.
From Coq Require Import Morphisms.
From Coq Require Import Arith.EqNat.

From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import FunctionalEnvironment.
From Velus Require Import Clocks.

(* for Theorem consolidate_mask *)
From Coq Require Import Logic.IndefiniteDescription.

Infix "⊑" := (@FEnv.refines _ _ (@EqSt _)) (at level 70, no associativity) : fenv_scope.

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
      inv E; exists a; split; auto with datatypes.
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
        induction n; intros; auto using EqStN.
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

    Lemma EqStN_weaken : forall k n xs1 xs2,
        k < n ->
        EqStN n xs1 xs2 ->
        EqStN k xs1 xs2.
    Proof.
      intros * Hlt Heq.
      apply EqStN_spec; intros.
      eapply EqStN_spec in Heq; eauto. lia.
    Qed.

    Corollary EqStN_weaken_S : forall n xs1 xs2,
        EqStN (S n) xs1 xs2 ->
        EqStN n xs1 xs2.
    Proof.
      intros. eapply EqStN_weaken; eauto.
    Qed.
  End EqStN.

  Global Hint Constructors EqStN : coindstreams.

  Global Instance EqStN_refl {A} n : Reflexive (@EqStN A n).
  Proof.
    intros ?. apply EqStN_EqSt.
    reflexivity.
  Qed.

  Global Instance EqStN_sym {A} n : Symmetric (@EqStN A n).
  Proof.
    induction n; intros ?? Heq; inv Heq; auto with coindstreams.
  Qed.

  Global Instance EqStN_trans {A} n : Transitive (@EqStN A n).
  Proof.
    induction n; intros ??? Heq1 Heq2; inv Heq1; inv Heq2; eauto with coindstreams.
  Qed.

  Add Parametric Morphism A n : (@EqStN A n)
      with signature @EqSt _ ==> @EqSt _ ==> Basics.impl
        as EqStN_morph.
  Proof.
    induction n; intros (?&?) (?&?) Heq1 (?&?) (?&?) Heq2 Heq;
      inv Heq1; inv Heq2; inv Heq; simpl in *; constructor; subst; eauto.
    eapply IHn; eauto.
  Qed.

  Add Parametric Morphism {A B} (f : A -> B) n : (map f)
      with signature @EqStN _ n ==> @EqStN _ n
        as map_EqStN.
  Proof.
    intros * Heq.
    apply EqStN_spec; intros.
    rewrite EqStN_spec in Heq.
    rewrite 2 Str_nth_map, Heq; auto.
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

  Fact wt_stream_enum : forall xs tx tn,
      wt_stream xs (Tenum tx tn) ->
      SForall (fun v => match v with
                     | present (Vscalar _) => False
                     | _ => True
                     end) xs.
    Proof.
      intros * Hwt.
      apply SForall_forall; intros n. apply SForall_forall with (n:=n) in Hwt.
      cases_eqn Hxs. setoid_rewrite Hxs in Hwt.
      inv Hwt.
    Qed.

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

  CoInductive liftn (sem_extern : list cvalue -> cvalue -> Prop)
    : list (Stream svalue) -> Stream svalue -> Prop :=
  | LiftNA:
      forall xss ys,
        Forall (fun xs => hd xs = absent) xss ->
        liftn sem_extern (List.map (@tl _) xss) ys ->
        liftn sem_extern xss (absent ⋅ ys)
  | LiftNScalarP:
      forall xs xss y ys,
        Forall2 (fun xs x => hd xs = present (Vscalar x)) xss xs ->
        sem_extern xs y ->
        liftn sem_extern (List.map (@tl _) xss) ys ->
        liftn sem_extern xss (present (Vscalar y) ⋅ ys).

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

  Add Parametric Morphism op t : (lift1 op t)
      with signature @EqSt svalue ==> @EqSt svalue ==> Basics.impl
        as lift1_EqSt.
  Proof.
    cofix Cofix.
    intros es es' Ees ys ys' Eys Lift.
    destruct es' as [[]], ys' as [[]];
      inv Lift; inv Eys; inv Ees; simpl in *; try discriminate.
    - constructor; eapply Cofix; eauto.
    - constructor.
      + now inv H1; inv H3.
      + eapply Cofix; eauto.
  Qed.

  Add Parametric Morphism op t1 t2 : (lift2 op t1 t2)
      with signature @EqSt svalue ==> @EqSt svalue ==> @EqSt svalue ==> Basics.impl
        as lift2_EqSt.
  Proof.
    cofix Cofix.
    intros e1s e1s' Ee1s e2s e2s' Ee2s ys ys' Eys Lift.
    destruct e1s' as [[]], e2s' as [[]], ys' as [[]];
      inv Lift; inv Eys; inv Ee1s; inv Ee2s; simpl in *; try discriminate.
    - constructor; eapply Cofix; eauto.
    - constructor.
      + now inv H1; inv H3; inv H5.
      + eapply Cofix; eauto.
  Qed.

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

  Lemma liftn_spec:
    forall sem_extern xss ys,
      liftn sem_extern xss ys <->
      (forall n,
          (Forall (fun xs => xs # n = absent) xss
           /\ ys # n = absent)
          \/
          (exists xs y,
             Forall2 (fun xs x => xs # n = present (Vscalar x)) xss xs
             /\ sem_extern xs y
             /\ ys # n = present (Vscalar y))).
  Proof.
    split.
    - intros H n; revert dependent xss; revert ys.
      induction n; intros.
      + inv H; intuition.
        right. do 3 eexists; intuition; eauto.
      + inv H; repeat rewrite Str_nth_S; eauto.
        1,2:edestruct IHn as [(?&?)|(?&?&?&?&?)]; eauto.
        1,3:left; split; simpl_Forall; auto.
        1,2:right; do 2 esplit; repeat split; eauto; simpl_Forall; auto.
    - revert xss ys.
      cofix CoFix; intros * H.
      unfold_Stv ys;
        try (specialize (H 0); repeat rewrite Str_nth_0 in H;
             destruct H as [(?&?)|(?&?&?&?&?)]; discriminate).
      + econstructor.
        * destruct (H 0) as [(?&?)|(?&?&?& E & E')]; try discriminate.
          simpl_Forall; auto.
        * cofix_step CoFix H.
          destruct H as [(?&?)|(?&?&?&?&?)]; [left|right]; repeat esplit; simpl_Forall; eauto.
      + destruct (H 0) as [(?&?)|(?&?&?& E & E')]; try discriminate.
        inv E'.
        econstructor; eauto.
        cofix_step CoFix H.
        destruct H as [(?&?)|(?&?&?&?&?)]; [left|right]; repeat esplit; simpl_Forall; eauto.
  Qed.

  Add Parametric Morphism sem_extern : (liftn sem_extern)
      with signature @EqSts svalue ==> @EqSt svalue ==> Basics.impl
        as liftn_EqSt.
  Proof.
    intros * Heq1 * Heq2 Hlift.
    apply liftn_spec; intros. apply liftn_spec with (n:=n) in Hlift.
    apply eqst_ntheq with (n:=n) in Heq2.
    destruct Hlift as [(?&?)|(?&?&?&?&?)]; [left|right]; repeat esplit; eauto; try congruence.
    - eapply Forall2_ignore1 in Heq1; simpl_Forall.
      take (_ ≡ _) and apply eqst_ntheq with (n:=n) in it; setoid_rewrite <-it; auto.
    - apply Forall2_swap_args in Heq1. eapply Forall2_trans_ex in H; [|eauto].
      simpl_Forall.
      take (_ ≡ _) and apply eqst_ntheq with (n:=n) in it; setoid_rewrite <-it; auto.
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
        * take (merge _ _ _) and apply IHn in it as [(?&?&?)|(?&?&?&?&?&?)].
          -- left; intuition.
             simpl_Forall; eauto.
          -- right. repeat esplit; eauto.
             ++ solve_Exists.
             ++ simpl_Forall; eauto.
        * take (merge _ _ _) and apply IHn in it as [(?&?&?)|(?&?&?&?&?&?)].
          -- left; intuition.
             simpl_Forall; eauto.
          -- right. repeat esplit; eauto.
             ++ clear H1. solve_Exists.
             ++ simpl_Forall; eauto.
    - revert xs ess rs; cofix CoFix; intros * H.
      unfold_Stv xs; unfold_Stv rs;
        try (specialize (H 0); repeat rewrite Str_nth_0 in H;
             destruct H as [(?&?&?)|(?&?&?&?&?&?)];
             discriminate).
      + constructor.
        * cofix_step CoFix H.
          destruct H as [(?&?&?)|(?&?&?&?&?&?)].
          -- left; intuition.
             simpl_Forall; eauto.
          -- subst; right; do 2 eexists. repeat split; eauto.
             ++ solve_Exists.
             ++ simpl_Forall; eauto.
        * destruct (H 0) as [(?&?&?)|(?&?&?&?&?&?)]; try discriminate.
          simpl_Forall; eauto.
      + destruct (H 0) as [(?&?&?)|(?&?& Hc & E & E' & Hr)]; try discriminate.
        inv Hc. inv Hr.
        econstructor; eauto.
        cofix_step CoFix H.
        destruct H as [(?&?&?)|(?&?&?&?&?&?)].
        -- left; intuition.
           simpl_Forall; eauto.
        -- right; do 2 eexists. repeat split; eauto.
           ++ clear E. solve_Exists.
           ++ simpl_Forall; eauto.
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
             simpl_Forall. rewrite Str_nth_S_tl; auto.
             destruct d; simpl in *; auto.
          -- right; left. repeat esplit; eauto; simpl_Forall.
             ++ rewrite Str_nth_S_tl; auto.
             ++ solve_Exists.
             ++ destruct d; simpl in *; auto.
          -- right; right. repeat esplit; eauto; simpl_Forall; eauto.
             destruct d; simpl in *; eauto.
        * take (case _ _ _ _) and apply IHn in it as [(?&?&?&?)|[(?&?&?&?&?&?&?)|(?&?&?&?&?&?&?)]].
          -- left; intuition.
             simpl_Forall; eauto.
             destruct d; simpl in *; auto.
          -- right; left. repeat esplit; eauto; simpl_Forall; eauto.
             ++ clear H3. solve_Exists.
             ++ destruct d; simpl in *; auto.
          -- right; right. repeat esplit; eauto; simpl_Forall; eauto.
             destruct d; simpl in *; eauto.
        * take (case _ _ _ _) and apply IHn in it as [(?&?&?&?)|[(?&?&?&?&?&?&?)|(?&?&?&?&?&?&?)]].
          -- left; intuition.
             simpl_Forall.
             rewrite Str_nth_S_tl; auto.
          -- right; left. repeat esplit; eauto; simpl_Forall; eauto.
             solve_Exists.
          -- right; right. repeat esplit; eauto; simpl_Forall; eauto.
    - revert xs ess d rs; cofix CoFix; intros * H.
      unfold_Stv xs; unfold_Stv rs;
        try (specialize (H 0); repeat rewrite Str_nth_0 in H;
             destruct H as [(?&?&?&?)|[(?&?&?&?&?&?&?)|(?&?&?&?&?&?&?)]];
             discriminate).
      + constructor.
        * cofix_step CoFix H.
          destruct H as [(?&?&?&?)|[(?&?&?&?&?&?&?)|(?&?&?&?&?&?&?)]].
          -- left; intuition; simpl_Forall; eauto.
             destruct d; auto.
          -- subst; right; left. repeat esplit; eauto; simpl_Forall; eauto.
             ++ solve_Exists.
             ++ destruct d; simpl in *; auto.
          -- subst; right; right. repeat esplit; eauto.
             ++ simpl_Forall; auto.
             ++ rewrite Forall_map. eapply Forall_impl; [|eapply H1]; intros (?&?) ?; simpl.
                auto.
             ++ destruct d; simpl in *; eauto.
        * destruct (H 0) as [(?&?&?&?)|[(?&?&?&?&?&?&?)|(?&?&?&?&?&?&?)]]; try discriminate.
          simpl_Forall; eauto.
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
             ++ simpl_Forall; eauto.
             ++ clear H1. solve_Exists.
             ++ destruct d; simpl in *; auto.
          -- subst; right; right. repeat esplit; eauto.
             ++ simpl_Forall; eauto.
             ++ rewrite Forall_map. eapply Forall_impl; [|eapply H4]; intros (?&?) ?; simpl.
                auto.
             ++ destruct d; simpl in *; eauto.
        * destruct d as [(?&?)|]; simpl in *; try rewrite Str_nth_0_hd in Hd; simpl in *; inv Hd.
          eapply CasePDef; eauto.
          cofix_step CoFix H.
          destruct H as [(?&?&?&?)|[(?&?&?&?&?&?&?)|(?&?&?&?&?&?&?)]].
          -- left; intuition.
             simpl_Forall; eauto.
          -- subst; right; left. repeat esplit; eauto.
             ++ simpl_Forall; eauto.
             ++ solve_Exists.
          -- subst; right; right. repeat esplit; eauto.
             ++ simpl_Forall; eauto.
             ++ rewrite Forall_map. eapply Forall_impl; [|eapply H3]; intros (?&?) ?; simpl.
                auto.
  Qed.

  CoFixpoint clocks_of (ss: list (Stream svalue)) : Stream bool :=
    existsb (fun s => hd s <>b absent) ss ⋅ clocks_of (List.map (@tl svalue) ss).

  (** *** bools_of : extract boolean from an svalue stream *)

  CoInductive bools_of : Stream svalue -> Stream bool -> Prop :=
  | bools_of_T:
      forall vs bs,
        bools_of vs bs ->
        bools_of (present (Venum true_tag) ⋅ vs) (true ⋅ bs)
  | bools_of_F:
      forall vs bs,
        bools_of vs bs ->
        bools_of (present (Venum false_tag) ⋅ vs) (false ⋅ bs)
  | bools_of_A:
      forall vs bs,
        bools_of vs bs ->
        bools_of (absent ⋅ vs) (false ⋅ bs).

  Global Instance bools_of_Proper:
    Proper (@EqSt svalue ==> @EqSt bool ==> Basics.impl)
           bools_of.
  Proof.
    cofix CoFix.
    intros [x xs] [x' xs'] Heq1 [y ys] [y' ys'] Heq2 Hsem; subst.
    inv Hsem; inv Heq1; inv Heq2;
      simpl in *; subst; econstructor; eauto.
    1-3:eapply CoFix; eauto.
  Qed.

  Corollary bools_of_det : forall xs ys ys',
      bools_of xs ys ->
      bools_of xs ys' ->
      ys ≡ ys'.
  Proof.
    cofix CoFix.
    intros * Hb1 Hb2. inv Hb1; inv Hb2.
    1-3:constructor; eauto.
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
      (forall n, (xs # n = present (Venum true_tag) /\ bs # n = true) \/
            (xs # n = present (Venum false_tag) /\ bs # n = false) \/
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
        destruct Hb0 as [(?&?)|[(?&?)|(?&?)]]; subst; try congruence.
        constructor. eapply CoFix; intros.
        specialize (Hbools (S n)). repeat rewrite Str_nth_S_hd in Hbools; simpl in Hbools; auto.
      + assert (Hb0 := Hbools 0).
        repeat rewrite Str_nth_0_hd in Hb0; simpl in Hb0.
        destruct Hb0 as [(?&?)|[(?&?)|(?&?)]]; subst; try congruence; inv H.
        1,2:(constructor; eapply CoFix; intros;
             specialize (Hbools (S n)); repeat rewrite Str_nth_S_hd in Hbools; simpl in Hbools; auto).
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

  Global Instance bools_ofs_Proper:
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

  Global Instance disj_str_SameElements_Proper:
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
      eapply Exists_impl; [|eauto]. intros ? Eq. rewrite Eq; auto.
    - destruct (x # n) eqn:Hxn; simpl; auto.
      rewrite <- Exists_existsb with (P:=fun x' => x' # n = x # n).
      2:{ intros x0. split; intros; congruence. }
      eapply SetoidList.InA_altdef in H.
      eapply Exists_impl; [|eauto]. intros ? Eq. rewrite Eq; auto.
    - destruct (existsb _ l') eqn:Ex.
      + rewrite <-Exists_existsb with (P:=fun x => x # n = true) in *. 2,3:reflexivity.
        rewrite H; auto.
      + rewrite existsb_Forall, forallb_Forall in *. rewrite H; auto.
    - congruence.
  Qed.

  Global Instance bools_ofs_SameElements_Proper:
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

  Section history.
    Context {K : Type}.

    Definition history := @FEnv.t K (Stream svalue).
    Definition history_tl (H: history) : history := FEnv.map (@tl svalue) H.

    Fact history_tl_find_Some : forall (H: history) id vs,
        H id = Some vs ->
        (history_tl H) id = Some (tl vs).
    Proof.
      intros H id vs Hfind.
      unfold history_tl, FEnv.map.
      rewrite Hfind. reflexivity.
    Qed.

    Fact history_tl_find_Some' : forall (H: history) id vs,
        (history_tl H) id = Some vs ->
        exists v, H id = Some (v ⋅ vs).
    Proof.
      intros H id vs Hfind.
      unfold history_tl, FEnv.map in Hfind.
      inv_equalities.
      exists (hd x). now destruct x.
    Qed.

    Fact history_tl_find_None : forall (H: history) id,
        H id = None ->
        (history_tl H) id = None.
    Proof.
      intros H id Hfind.
      unfold history_tl, FEnv.map.
      now rewrite Hfind.
    Qed.

    Fact history_tl_find_None' : forall (H: history) id,
        (history_tl H) id = None ->
        H id = None.
    Proof.
      intros H id Hfind.
      unfold history_tl, FEnv.map in Hfind.
      now inv_equalities.
    Qed.

    Definition env := @FEnv.t K svalue.

    Definition history_nth (n : nat) (H: history) : env :=
      FEnv.map (Str_nth n) H.

    Fact history_nth_find_None : forall n (H: history) id,
        H id = None ->
        (history_nth n H) id = None.
    Proof.
      intros * Hfind.
      unfold history_nth, FEnv.map. now rewrite Hfind.
    Qed.

    Fact history_nth_find_None' : forall n (H: history) id,
        (history_nth n H) id = None ->
        H id = None.
    Proof.
      intros * Hfind.
      unfold history_nth, FEnv.map in Hfind.
      now inv_equalities.
    Qed.

    Fact history_nth_find_Some : forall n (H: history) id vs,
        H id = Some vs ->
        (history_nth n H) id = Some (Str_nth n vs).
    Proof.
      intros * Hfind.
      unfold history_nth, FEnv.map. now rewrite Hfind.
    Qed.

    Fact history_nth_find_Some' : forall n (H: history) id v,
        (history_nth n H) id = Some v ->
        exists vs, H id = Some vs /\ vs # n = v.
    Proof.
      intros * Hfind.
      unfold history_nth, FEnv.map in Hfind. inv_equalities.
      eauto.
    Qed.

    Fact history_nth_find_Some'' : forall (H: history) vs id,
        (forall n, (history_nth n H) id = Some (vs # n)) ->
        exists vs', H id = Some vs' /\ vs' ≡ vs.
    Proof.
      intros * Hfind.
      destruct (H id) as [vs'|] eqn:Hfind'.
      - exists vs'. split; auto.
        apply ntheq_eqst. intros n.
        specialize (Hfind n).
        unfold history_nth, FEnv.map in Hfind. inv_equalities.
        rewrite Hf in Hfind'. inv Hfind'; auto.
      - specialize (Hfind 0). unfold history_nth, FEnv.map in Hfind. inv_equalities.
        congruence.
    Qed.

    Open Scope fenv_scope.

    Fact history_tl_refines : forall H H',
        H ⊑ H' ->
        (history_tl H) ⊑ (history_tl H').
    Proof.
      intros H H' Href x vs Hfind.
      eapply history_tl_find_Some' in Hfind as [v' Hfind].
      eapply Href in Hfind as [vs' [Heq' Hfind']].
      exists (tl vs').
      apply history_tl_find_Some in Hfind'.
      split; auto.
      destruct vs'; simpl. inv Heq'; auto.
    Qed.

    Fact history_tl_Equiv : forall H H',
        FEnv.Equiv (@EqSt _) H H' ->
        FEnv.Equiv (@EqSt _) (history_tl H) (history_tl H').
    Proof.
      unfold history_tl, FEnv.map.
      intros * Heq x.
      specialize (Heq x); inv Heq; simpl; constructor.
      now rewrite H2.
    Qed.

  End history.

  Global Hint Unfold history_tl : fenv.

  (** * sem_var
        This is common to Lustre and NLustre Semantics *)

  Section sem_var.
    Context {K : Type}.

    Inductive sem_var: history -> K -> Stream svalue -> Prop :=
      sem_var_intro:
        forall H x xs xs',
          H x = Some xs' ->
          xs ≡ xs' ->
          sem_var H x xs.

    Global Add Parametric Morphism : sem_var
        with signature FEnv.Equiv (@EqSt _) ==> @eq _ ==> @EqSt svalue ==> Basics.impl
          as sem_var_morph.
    Proof.
      intros H H' ? x xs xs' Heq; subst.
      intros Hsem; inv Hsem.
      specialize (H0 x). rewrite H2 in H0. inv H0.
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
      rewrite H1 in H3. inv H3. reflexivity.
    Qed.

    Lemma env_maps_tl :
      forall i v s H,
        H i = Some (v ⋅ s) -> (@history_tl K H) i = Some s.
    Proof.
      intros * Hmap.
      unfold history_tl, FEnv.map.
      rewrite Hmap. reflexivity.
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
      inv Hsem. unfold history_tl, FEnv.map in *. inv_equalities.
      exists (hd x0). econstructor; eauto. constructor; auto.
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
        orel (@EqSt svalue) (H x) (H' x) ->
        sem_var H x v <-> sem_var H' x v.
    Proof.
      intros * Hfind; split; intro Hsem; inversion_clear Hsem as [???? Hr];
        rewrite Hr in Hfind; inv Hfind;
        econstructor; eauto; rewrite H1; auto.
      now symmetry.
    Qed.

    Open Scope fenv_scope.

    Lemma sem_var_union : forall Hi1 Hi2 x vs,
        sem_var (Hi1 + Hi2) x vs ->
        sem_var Hi1 x vs \/ sem_var Hi2 x vs.
    Proof.
      intros * Hv. inv Hv.
      eapply FEnv.union4 in H0 as [Hfind|Hfind]; eauto using sem_var.
    Qed.

    Lemma sem_var_union' : forall Hi1 Hi2 x vs,
        sem_var (Hi1 + Hi2) x vs ->
        (~FEnv.In x Hi2 /\ sem_var Hi1 x vs) \/ sem_var Hi2 x vs.
    Proof.
      intros * Hv. inv Hv.
      eapply FEnv.union4' in H0 as [Hfind|(Hnone&Hfind)]; eauto using sem_var.
      left. split; eauto using sem_var.
      now apply FEnv.not_find_In.
    Qed.

    Lemma sem_var_disj_union : forall Hi1 Hi2 x vs,
        (forall x, FEnv.In x Hi1 -> ~FEnv.In x Hi2) ->
        sem_var (Hi1 + Hi2) x vs <-> sem_var Hi1 x vs \/ sem_var Hi2 x vs.
    Proof.
      intros * Hdisj; split.
      - eapply sem_var_union.
      - intros [Hv|Hv]; inv Hv; econstructor; eauto.
        + erewrite FEnv.union2; eauto.
          destruct (Hi2 x) eqn:Hhi; auto.
          exfalso. eapply Hdisj; econstructor; eauto.
        + erewrite FEnv.union3'; eauto.
    Qed.

    Context `{FEnv.fenv_key K}.

    Lemma sem_var_of_list : forall xs x vs,
        NoDupMembers xs ->
        In (x, vs) xs ->
        sem_var (FEnv.of_list xs) x vs.
    Proof.
      intros * Hnd Hin.
      econstructor; eauto using FEnv.of_list_In_find.
      reflexivity.
    Qed.

    Lemma sem_var_of_list' : forall xs x vs,
        sem_var (FEnv.of_list xs) x vs ->
        exists vs', vs ≡ vs' /\ In (x, vs') xs.
    Proof.
      intros * Hvar. inv Hvar; eauto using FEnv.of_list_find_In.
    Qed.

    Lemma sem_var_union2 : forall Hi1 Hi2 x vs,
        sem_var Hi1 x vs ->
        ~FEnv.In x Hi2 ->
        sem_var (Hi1 + Hi2) x vs.
    Proof.
      intros * Hvar Hnin. inv Hvar.
      econstructor; eauto.
      apply FEnv.union2; eauto. now apply FEnv.not_find_In.
    Qed.

    Lemma sem_var_union3' : forall Hi1 Hi2 x vs,
        sem_var Hi2 x vs ->
        sem_var (Hi1 + Hi2) x vs.
    Proof.
      intros * Hvar.
      inv Hvar. econstructor; eauto using FEnv.union3'.
    Qed.

  End sem_var.

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
    induction n; intros * Heq; auto with coindstreams.
    rewrite (unfold_Stream (clocks_of xs1)), (unfold_Stream (clocks_of xs2)); simpl.
    constructor; auto.
    - clear - Heq. induction Heq; simpl; auto.
      f_equal; auto. inv H; auto.
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

  (** ** abstract_clock and some properties *)

  CoFixpoint abstract_clock {A} (xs: Stream (synchronous A)) : Stream bool:=
    match xs with
    | absent ⋅ xs => false ⋅ abstract_clock xs
    | present _ ⋅ xs => true ⋅ abstract_clock xs
    end.

  Add Parametric Morphism {A} : (@abstract_clock A)
      with signature @EqSt _ ==> @EqSt bool
        as ac_EqSt.
  Proof.
    cofix Cofix; intros b b' Eb.
    unfold_Stv b; unfold_Stv b';
      constructor; inv Eb; simpl in *; try discriminate; auto.
  Qed.

  Lemma ac_Cons {A} : forall x xs,
      @abstract_clock A (x ⋅ xs) ≡
      (match x with absent => false | _ => true end) ⋅ (abstract_clock xs).
  Proof.
    intros *. constructor; simpl.
    1,2:destruct x; reflexivity.
  Qed.

  Lemma ac_tl {A} :
    forall s, @abstract_clock A (Streams.tl s) ≡ Streams.tl (abstract_clock s).
  Proof.
    intros. unfold_Stv s; reflexivity.
  Qed.

  Lemma ac_nth {A} : forall xs n,
      (@abstract_clock A xs) # n = (match xs # n with absent => false | _ => true end).
  Proof.
    intros xs n. revert xs.
    induction n; intros; unfold_Stv xs; rewrite ac_Cons.
    1,2:rewrite Str_nth_0; auto.
    1,2:repeat rewrite Str_nth_S; eauto.
  Qed.

  (** ** sem_clock and its properties *)

  CoInductive enums_of (e : enumtag) : Stream svalue -> Stream bool -> Prop :=
  | enums_of_abs : forall xs ys,
      enums_of e xs ys ->
      enums_of e (absent ⋅ xs) (false ⋅ ys)
  | enums_of_eq : forall xs ys,
      enums_of e xs ys ->
      enums_of e (present (Venum e) ⋅ xs) (true ⋅ ys)
  | enums_of_neq : forall e' xs ys,
      enums_of e xs ys ->
      e' <> e ->
      enums_of e (present (Venum e') ⋅ xs) (false ⋅ ys).

  Lemma enums_of_nth e : forall xs bs,
      enums_of e xs bs
      <-> (forall n, (xs # n = absent /\ bs # n = false)
              \/ (xs # n = present (Venum e) /\ bs # n = true)
              \/ (exists e', xs # n = present (Venum e') /\ e' <> e /\ bs # n = false)).
  Proof.
    split.
    - intros Henum n. revert dependent xs; revert bs.
      induction n; intros.
      + inv Henum; intuition.
        right; right. eexists; intuition; auto.
      + inv Henum; repeat rewrite Str_nth_S; auto.
    - revert xs bs.
      cofix CoFix; intros * Henum.
      unfold_Stv xs; unfold_Stv bs;
        try (specialize (Henum 0) as H0; repeat rewrite Str_nth_0 in H0;
             destruct H0 as [(?&?)|[(?&?)|(?&?&?&?)]]; try discriminate).
      + constructor; cofix_step CoFix Henum.
      + rewrite H. constructor; cofix_step CoFix Henum.
      + rewrite H. econstructor; eauto. cofix_step CoFix Henum.
  Qed.

  Inductive sem_clock: history -> Stream bool -> clock -> Stream bool -> Prop :=
  | Sbase:
      forall H b b',
        b ≡ b' ->
        sem_clock H b Cbase b'
  | Son:
      forall H b bs ck x t k xs bs',
        sem_clock H b ck bs ->
        sem_var H x xs ->
        abstract_clock xs ≡ bs -> (* Otherwise would be weaker than previous definition *)
        enums_of k xs bs' ->
        sem_clock H b (Con ck x (t, k)) bs'.

  Add Parametric Morphism e : (enums_of e)
      with signature @EqSt _ ==> @EqSt _ ==> Basics.impl
        as enums_of_EqSt.
  Proof.
    cofix CoFix.
    intros (?&?) (?&?) Hvs (?&?) (?&?) Hbs Henums.
    inv Henums; inv Hvs; inv Hbs; simpl in *; subst.
    all:constructor; eauto; eapply CoFix; eauto.
  Qed.

  Lemma enums_of_detn e n : forall xs1 xs2 bs1 bs2,
      EqStN n xs1 xs2 ->
      enums_of e xs1 bs1 ->
      enums_of e xs2 bs2 ->
      EqStN n bs1 bs2.
  Proof.
    intros * Heq Henums1 Henums2.
    apply EqStN_spec. intros k Hlt. rewrite enums_of_nth in *.
    eapply EqStN_spec in Heq; eauto.
    edestruct (Henums1 k) as [(?&?)|[(?&?)|(?&?&?&?)]];
      edestruct (Henums2 k) as [(?&?)|[(?&?)|(?&?&?&?)]]; congruence.
  Qed.

  Add Parametric Morphism : sem_clock
      with signature FEnv.Equiv (@EqSt _) ==> @EqSt bool ==> eq ==> @EqSt bool ==> Basics.impl
        as sem_clock_morph.
  Proof.
    intros H H' Hequiv b b' Eb ck.
    induction ck; intros bk bk' Ebk Sem; inv Sem.
    - constructor. rewrite <-Eb, <-Ebk; auto.
    - econstructor; eauto.
      + eapply IHck in H4; eauto. reflexivity.
      + now rewrite <-Hequiv.
      + now rewrite <-Ebk.
  Qed.

  Lemma sc_step :
    forall H b ck s ss,
      sem_clock H b ck (s ⋅ ss) ->
      sem_clock (history_tl H) (Streams.tl b) ck ss.
  Proof.
    induction ck; intros * Hsem; inv Hsem.
    - inv H1. constructor; auto.
    - destruct bs, xs; simpl in *. econstructor; eauto using sem_var_step.
      + inv H9; simpl in *; auto.
        destruct s0; simpl in *; auto.
      + inv H10; auto.
  Qed.

  Lemma enums_of_det e : forall xs bs1 bs2,
      enums_of e xs bs1 ->
      enums_of e xs bs2 ->
      bs1 ≡ bs2.
  Proof.
    intros * Henum1 Henum2.
    apply ntheq_eqst; intros n.
    rewrite enums_of_nth in *.
    specialize (Henum1 n) as [(?&?)|[(?&?)|(?&?&?&?)]]; specialize (Henum2 n) as [(?&?)|[(?&?)|(?&?&?&?)]];
      try congruence.
  Qed.

  Lemma sem_clock_det :
    forall (ck : clock) (H : history)
      (b xs xs' : Stream bool),
      sem_clock H b ck xs ->
      sem_clock H b ck xs' ->
      xs ≡ xs'.
  Proof.
    induction ck; intros * Hsem1 Hsem2; inv Hsem1; inv Hsem2.
    - rewrite <-H1, <-H2. reflexivity.
    - eapply sem_var_det in H7; eauto. rewrite H7 in H15.
      eapply enums_of_det; eauto.
  Qed.

  Fact sem_clock_true_inv : forall H ck b bs bs',
      sem_clock H (b ⋅ bs) ck (true ⋅ bs') ->
      b = true.
  Proof.
    induction ck; intros * Hsem; inv Hsem.
    - inv H1; auto.
    - destruct bs0. inv H10. inv H9; simpl in *; subst.
      eapply IHck in H4; eauto.
  Qed.

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
    inv Hsc'. eapply sem_clock_det in Hsc; eauto. rewrite <-Hsc.
    clear - H9 H10.
    revert xs s' bs H9 H10.
    cofix CoFix; intros (?&?) (?&?) (?&?) Hac Henums;
      inv Hac; inv Henums; simpl in *; subst.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
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
    - inversion Hsc' as [|????????? Hck']; subst.
      subst; pose proof (sub_clock_Con _ _ _ _ _ _ _ Hck' Hsc');
        apply IHHparent in Hck'; etransitivity; eauto.
  Qed.

  (** ** Aligned and its properties *)

  CoInductive aligned {A} : Stream (synchronous A) -> Stream bool -> Prop :=
  | synchro_present:
      forall v vs bs,
        aligned vs bs ->
        aligned (present v ⋅ vs) (true ⋅ bs)
  | synchro_absent:
      forall vs bs,
        aligned vs bs ->
        aligned (absent ⋅ vs) (false ⋅ bs).

  Global Instance aligned_Proper {A} :
    Proper (@EqSt (synchronous A) ==> @EqSt bool ==> iff)
           aligned.
  Proof.
    intros vs vs' Heq1 bs bs' Heq2.
    split; revert vs vs' Heq1 bs bs' Heq2;
      cofix aligned_Proper;
      intros [v vs] [v' vs'] Heq1 [b bs] [b' bs'] Heq2 H;
      inv Heq1; inv Heq2; simpl in *; subst; inv H;
        constructor; eauto.
  Qed.

  Lemma aligned_spec {A} : forall (vs: Stream (synchronous A)) bs,
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

  Lemma aligned_EqSt {A} : forall (vs: Stream (synchronous A)) bs1 bs2,
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
    setoid_rewrite Heqvs; clear Heqvs.
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
    setoid_rewrite Heqvs; clear Heqvs.
    destruct (bs # n).
    - left. eexists...
    - right...
  Qed.

  Lemma ac_when :
    forall k cs xs rs,
      when k cs xs rs -> abstract_clock cs ≡ abstract_clock xs.
  Proof.
    cofix Cofix.
    intros * Hwhen. inv Hwhen; econstructor; simpl; eauto.
  Qed.

  Lemma ac_merge :
    forall cs xs rs,
      merge cs xs rs -> abstract_clock cs ≡ abstract_clock rs.
  Proof.
    cofix Cofix.
    intros * Hmerge. inv Hmerge; econstructor; simpl; eauto.
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

  Lemma ac_liftn :
    forall f ss vs,
      liftn f ss vs ->
      Forall (fun ss => abstract_clock ss ≡ abstract_clock vs) ss.
  Proof.
    intros * Hlift. rewrite liftn_spec in Hlift.
    simpl_Forall.
    apply ntheq_eqst; intros. rewrite 2 ac_nth.
    specialize (Hlift n) as [(?&?)|(?&?&?&?&?)];
      [|take (Forall2 _ _ _) and apply Forall2_ignore2 in it]; simpl_Forall.
    1,2:take (vs # n = _) and setoid_rewrite it.
    1,2:take (x # n = _) and setoid_rewrite it; auto.
  Qed.

  Lemma ac_aligned {A} :
    forall (s: Stream (synchronous A)), aligned s (abstract_clock s).
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

  Fact ac_Streams_const {A} :
    @abstract_clock A (Streams.const absent) ≡ Streams.const false.
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

  Add Parametric Morphism n : count
      with signature @EqStN _ n ==> @EqStN _ n
        as count_EqStN.
  Proof.
    intros ?? Heq. eapply EqStN_spec; intros * Hlt.
    revert x y n Hlt Heq.
    induction k; intros; unfold_Stv x; unfold_Stv y;
      inv Heq; simpl in *; auto; try congruence; try solve [inv Hlt].
    1-2:repeat rewrite Str_nth_S_tl in *; simpl in *;
      repeat rewrite count_S_nth'.
    f_equal.
    1,2:eapply IHk in H5; auto; lia.
  Qed.

  Add Parametric Morphism : count
      with signature @EqSt _ ==> @EqSt _
        as count_EqSt.
  Proof.
    intros ?? Heq. apply EqStN_EqSt; intros.
    apply EqStN_EqSt with (n:=n) in Heq. rewrite Heq. reflexivity.
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
      (count r) # n2 = ((count r) # n1 + (count (Str_nth_tl (S n1) r)) # (n2 - S n1))%nat.
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
      eapply Nat.le_succ_l, Nat.le_exists_sub in Hl1 as (k'&?&Hl1); subst.
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

  CoFixpoint mask' {A : Type} (absent: A) (k k': nat) (rs: Stream bool) (xs: Stream A) : Stream A :=
    let mask' k' := mask' absent k k' (tl rs) (tl xs) in
    match hd rs with
    | false => (if k' =? k then hd xs else absent) ⋅ mask' k'
    | true  => (if S k' =? k then hd xs else absent) ⋅ mask' (S k')
    end.
  Definition mask {A : Type} (absent: A) k rs xs :=
    mask' absent k 0 rs xs.

  (** Synchronous value mask *)
  Definition maskv k rs := @mask svalue absent k rs.

  (** Masking an history *)
  Definition mask_hist {K} k rs := @FEnv.map K _ _ (maskv k rs).
  Global Hint Unfold mask_hist : fenv.

  (** Boolean mask *)
  Definition maskb := mask false.

  Lemma mask_nth {A} (absent: A) :
    forall n k rs xs,
      (mask absent k rs xs) # n = if (count rs) # n =? k then xs # n else absent.
  Proof.
    unfold mask, Str_nth. intros n k rs.
    replace (hd (Str_nth_tl n (count rs))) with (0 + hd (Str_nth_tl n (count rs)))%nat by auto.
    generalize 0 as k'. revert k rs.
    induction n; intros; unfold_Stv rs; simpl; auto.
    - rewrite Nat.add_1_r. reflexivity.
    - rewrite Nat.add_0_r. reflexivity.
    - rewrite IHn; unfold count.
      rewrite count_S_nth, <-plus_n_Sm, plus_Sn_m. reflexivity.
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

  Lemma mask'_Cons {A} (absent: A) :
    forall k r rs x xs k',
      (mask' absent k k' (r ⋅ rs) (x ⋅ xs))
      = (match r with
         | false => (if k' =? k then x else absent) ⋅ mask' absent k k' rs xs
         | true  => (if S k' =? k then x else absent) ⋅ mask' absent k (S k') rs xs
         end).
  Proof.
    intros *.
    rewrite (unfold_Stream (mask' _ _ _ _ _)); simpl.
    destruct r; simpl; reflexivity.
  Qed.

  Lemma mask'_S {A} (absent: A) : forall k k' rs xs,
      mask' absent (S k) (S k') rs xs ≡ mask' absent k k' rs xs.
  Proof.
    cofix CoFix.
    intros. destruct rs as [[]], xs; constructor; simpl; auto.
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

  Lemma mask_hist_false_0 {K} : forall H,
      @FEnv.Equiv K _ (@EqSt _) (mask_hist 0 (Streams.const false) H) H.
  Proof.
    intros * ?. simpl_fenv.
    destruct (H x) eqn:Hfind; simpl; constructor.
    eapply mask_false_0.
  Qed.

  Lemma mask_hist_false_S {K} : forall n H,
      @FEnv.Equiv K _ (@EqSt _) (mask_hist (S n) (Streams.const false) H) (FEnv.map (fun _ => Streams.const absent) H).
  Proof.
    intros * ?. simpl_fenv.
    destruct (H x) eqn:Hfind; simpl; constructor.
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

  Lemma consolidate_mask_hist {K} : forall P r d,
      (Proper (eq ==> (FEnv.Equiv (@EqSt _)) ==> Basics.impl) P) ->
      (forall k H, P k H -> @FEnv.dom K _ H d) ->
      (forall k, exists H, P k (mask_hist k r H)) ->
      exists H, forall k, P k (mask_hist k r H).
  Proof.
    intros * HP Hdom Hmask.
    eapply functional_choice in Hmask as (f&?).
    exists (FEnv.mapi (fun x _ => init_from 0 (fun n => or_default_with absent (fun v => v # n)
                                                             ((f ((count r) # n)) x))) (f 0)).
    assert (forall k1 k2 x, FEnv.In x (f k1) -> FEnv.In x (f k2)) as Hdomf.
    { intros * Hin. specialize (H k1) as H1. specialize (H k2) as H2.
      eapply FEnv.dom_map; eauto.
      eapply Hdom, FEnv.map_in_iff; [|eauto]. eauto.
    }
    intros k. specialize (H k).
    eapply HP; eauto. intros ?.
    unfold mask_hist. simpl_fenv.
    destruct ((f 0) x) eqn:H0, ((f k) x) eqn:Hk; simpl; auto with datatypes.
    - constructor.
      eapply ntheq_eqst. intros n.
      repeat rewrite maskv_nth.
      destruct (_ =? _) eqn:Hcount; auto.
      apply Nat.eqb_eq in Hcount; subst.
      rewrite init_from_nth, Nat.add_0_r; auto.
      rewrite Hk; simpl; auto.
    - exfalso. edestruct Hdomf with (k2:=k); [econstructor; eauto|]. congruence.
    - exfalso. edestruct Hdomf with (k2:=0); [econstructor; eauto|]. congruence.
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

  Add Parametric Morphism {K} k : (@mask_hist K k)
      with signature @EqSt _ ==> FEnv.Equiv (@EqSt _) ==> FEnv.Equiv (@EqSt _)
        as mask_hist_morph.
  Proof.
    intros r r' Er H H' EH x.
    specialize (EH x). simpl_fenv.
    inv EH; simpl; constructor; auto.
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

  Corollary mask_hist_absent {K} : forall k rs (H: @FEnv.t K (Stream svalue)),
      FEnv.Equiv (@EqSt _) (mask_hist k rs (FEnv.map (fun _ => Streams.const absent) H))
                 (FEnv.map (fun _ => Streams.const absent) H).
  Proof.
    intros * x. simpl_fenv.
    destruct (H x); simpl; constructor.
    eapply mask_absent.
  Qed.

  Corollary mask_hist_absent' {K} : forall k rs (H: @FEnv.t K (Stream svalue)),
      FEnv.Equiv (@EqSt _) (FEnv.map (fun _ => Streams.const (@absent value)) (mask_hist k rs H))
                 (FEnv.map (fun _ => Streams.const absent) H).
  Proof.
    intros * x. simpl_fenv.
    destruct (H x); simpl; constructor.
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

  Open Scope fenv_scope.

  Lemma refines_mask {K} : forall r (H H' : @history K) k,
      H ⊑ H' ->
      (mask_hist k r H) ⊑ (mask_hist k r H').
  Proof.
    intros * Href ?? Hfind.
    simpl_fenv.
    eapply Href in Hf as (?&Heq&Hfind).
    rewrite Hfind; simpl.
    do 2 esplit; eauto. now rewrite Heq.
  Qed.

  Lemma refines_unmask {K} : forall r (H H' : @history K),
      (forall k, (mask_hist k r H) ⊑ (mask_hist k r H')) ->
      H ⊑ H'.
  Proof.
    intros ??? Href ?? Hfind.
    specialize (Href 0 x (maskv 0 r v)) as Href0. simpl_fenv.
    rewrite Hfind in Href0; simpl in Href0.
    specialize (Href0 eq_refl) as (?&?&Hfind0). inv_equalities.
    do 2 esplit; eauto.
    eapply ntheq_eqst; intros n.
    specialize (Href ((count r) #n) x); simpl in Href.
    rewrite Hfind, Hf in Href; simpl in Href.
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
    intros. apply ntheq_eqst; intros.
    rewrite ac_nth, maskv_nth, maskb_nth, ac_nth.
    destruct (_ =? _); auto.
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
    eapply bools_of_nth with (n:=n) in H as [(?&?)|[(?&?)|(?&?)]].
    1-3:rewrite maskb_nth, maskv_nth in *; destruct (_ =? _); auto.
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
    specialize (Hb1 n) as [(?&?)|[(?&?)|(?&?)]]; specialize (Hb2 n) as [(?&?)|[(?&?)|(?&?)]]; subst.
    1-9:destruct (_ =? _); try congruence.
    1,2:rewrite H in H1; inv H1.
  Qed.

  Lemma sem_var_mask {K}: forall k r (H : @history K) x v,
      sem_var H x v ->
      sem_var (mask_hist k r H) x (maskv k r v).
  Proof.
    intros * Hvar. inv Hvar.
    econstructor.
    simpl_fenv. now rewrite H1.
    rewrite H2. reflexivity.
  Qed.

  Lemma sem_var_mask_inv {K} : forall k r (H : @history K) x v,
      sem_var (mask_hist k r H) x v ->
      exists v', sem_var H x v' /\ v ≡ (maskv k r v').
  Proof.
    intros * Hvar. inv Hvar.
    simpl_fenv.
    do 2 esplit; eauto. econstructor; eauto. reflexivity.
  Qed.

  (** *** Caracterizing a stream that is slower than a clock stream *)

  CoInductive slower {A} : Stream (synchronous A) -> Stream bool -> Prop :=
  | slowerF : forall vs bs,
      slower vs bs ->
      slower (absent ⋅ vs) (false ⋅ bs)
  | slowerT : forall v vs bs,
      slower vs bs ->
      slower (v ⋅ vs) (true ⋅ bs).

  Definition slower_hist {K} (H : @history K) bs :=
    forall x vs, H x = Some vs -> slower vs bs.

  (* Definition slower_subhist (dom : ident -> Prop) (H : history) bs := *)
  (*   forall x vs, dom x -> H x = Some vs -> slower vs bs. *)

  Lemma slower_nth {A} : forall bs vs,
      @slower A vs bs <->
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

  Add Parametric Morphism {A} : (@slower A)
      with signature @EqSt _ ==> @EqSt _ ==> Basics.impl
        as slower_morph.
  Proof.
    intros xs xs' Exs bs bs' Ebs Hs.
    eapply slower_nth; intros.
    eapply slower_nth with (n:=n) in Hs.
    rewrite <-Exs; auto. rewrite Ebs; auto.
  Qed.

  (* Add Parametric Morphism dom : (slower_subhist dom) *)
  (*     with signature FEnv.Equiv (@EqSt _) ==> @EqSt _ ==> Basics.impl *)
  (*       as slower_subhist_morph. *)
  (* Proof. *)
  (*   intros H H' EH bs bs' Ebs Hs ?? Hdom Hmaps. *)
  (*   specialize (EH x). rewrite Hmaps in EH. inv EH. *)
  (*   rewrite <-Ebs, <-H2. eapply Hs; eauto. *)
  (* Qed. *)

  Lemma aligned_slower {A} : forall bs (vs: Stream (synchronous A)),
      aligned vs bs ->
      slower vs bs.
  Proof.
    cofix CoFix; intros.
    inv H; constructor; apply CoFix; auto.
  Qed.

  Lemma sc_slower : forall H bs ck bs' (vs: Stream (synchronous value)),
      sem_clock H bs ck bs' ->
      aligned vs bs' ->
      slower vs bs.
  Proof.
    induction ck; intros * Hck Hal; inv Hck.
    - rewrite H1; auto using aligned_slower.
    - eapply IHck in H4. 2:rewrite <-H9; apply ac_aligned.
      clear - Hal H10 H4.
      rewrite slower_nth in *. rewrite aligned_spec in Hal. rewrite enums_of_nth in H10.
      intros * Hfalse. specialize (Hal n). specialize (H10 n). specialize (H4 n Hfalse).
      destruct H10 as [(?&?)|[(Hx&?)|(?&Hx&?&?)]].
      + destruct Hal as [(?&?&?)|(?&?)]; try congruence.
      + setoid_rewrite H4 in Hx; congruence.
      + setoid_rewrite H4 in Hx; congruence.
  Qed.

  Lemma slower_mask : forall vs bs k r,
      slower vs (maskb k r bs) ->
      vs ≡ maskv k r vs.
  Proof.
    intros * Hslow.
    eapply ntheq_eqst; intros.
    rewrite maskv_nth.
    destruct (_ =? _) eqn:Hcount; try reflexivity.
    eapply slower_nth with (n:=n) in Hslow; auto.
    rewrite maskb_nth, Hcount; auto.
  Qed.

  Corollary slower_mask_hist {K} : forall (H : @history K) bs k r,
      slower_hist H (maskb k r bs) ->
      FEnv.Equiv (@EqSt _) H (mask_hist k r H).
  Proof.
    intros * Hslow x. simpl_fenv.
    destruct (H x) eqn:Hfind; constructor.
    eapply Hslow in Hfind.
    eapply slower_mask; eauto.
  Qed.

  Lemma ac_slower {A} : forall vs,
      @slower A vs (abstract_clock vs).
  Proof.
    intros.
    rewrite slower_nth. intros n Hac. rewrite ac_nth in Hac.
    destruct (vs # n) eqn:Hv; auto. congruence.
  Qed.

  Global Hint Resolve ac_slower : coindstreams.

  Lemma slower_ac_morph {A B} : forall (vs1 : Stream (synchronous A)) (vs2 : Stream (synchronous B)) bs,
      abstract_clock vs1 ≡ abstract_clock vs2 ->
      slower vs1 bs ->
      slower vs2 bs.
  Proof.
    cofix CoFix.
    intros * Hac Hsc.
    destruct vs1 as ([]&?), vs2 as ([]&?), bs as ([]&?);
      inv Hsc; inv Hac; simpl in *; try congruence.
    1-3:constructor; eapply CoFix; eauto.
  Qed.

  (** ** when relation *)

  (* Whening of histories *)
  Definition when_hist {K} (sel : enumtag) (Hi : @history K) (es : Stream svalue) (Hi' : history) :=
    FEnv.refines (fun vs' vs => when sel vs es vs') Hi' Hi.

  Add Parametric Morphism sel : (when sel)
      with signature @EqSt _ ==> @EqSt _ ==> @EqSt _ ==> Basics.impl
        as when_EqSt.
  Proof.
    intros * Heq1 * Heq2 * Heq3 Hf.
    apply when_spec; intros.
    apply when_spec with (n:=n) in Hf.
    rewrite <-Heq1, <-Heq2, <-Heq3; auto.
    destruct Hf as [|[|]]; destruct_conjs; auto.
    - right; left. do 2 esplit. erewrite <-Heq1, <-Heq2, <-Heq3; eauto.
    - right; right. esplit. erewrite <-Heq1, <-Heq2, <-Heq3; eauto.
  Qed.

  Add Parametric Morphism {K} sel : (@when_hist K sel)
      with signature FEnv.Equiv (@EqSt _) ==> @EqSt _ ==> FEnv.Equiv (@EqSt _) ==> Basics.impl
        as when_hist_EqSt.
  Proof.
    intros * Heq1 * Heq2 * Heq3 Hf.
    unfold when_hist in *.
    intros ?? Hfind. specialize (Heq3 x2). rewrite Hfind in Heq3. inv Heq3.
    symmetry in H. apply Hf in H as (?&Hwhen&Hfind').
    specialize (Heq1 x2). rewrite Hfind' in Heq1. inv Heq1.
    do 2 esplit; [|eauto].
    rewrite <-Heq2, <-H2, <-H1; auto.
  Qed.

  (** when as a function *)

  (* does not constrain the input history enough in the case of an absence *)
  CoFixpoint fwhen {A} (abs : A) (sel : enumtag) (vs : Stream A) (es : Stream svalue) : Stream A :=
    (if hd es ==b present (Venum sel) then hd vs else abs) ⋅ (fwhen abs sel (tl vs) (tl es)).

  Definition fwhenv sel vs es := fwhen (@absent value) sel vs es.
  Definition fwhen_hist {K} sel H es := @FEnv.map K _ _ (fun vs => fwhenv sel vs es) H.
  Definition fwhenb := fwhen false.

  Global Hint Unfold fwhen_hist : fenv.

  Lemma fwhen_nth {A} (abs : A) :
    forall n sel es xs,
      (fwhen abs sel xs es) # n = if es # n ==b present (Venum sel) then xs # n else abs.
  Proof.
    unfold Str_nth.
    induction n; intros; unfold_St es; unfold_St xs; auto.
  Qed.

  Corollary fwhenv_nth:
    forall n e es xs,
      (fwhenv e xs es) # n = if es # n ==b present (Venum e) then xs # n else absent.
  Proof.
    intros. setoid_rewrite fwhen_nth; auto.
  Qed.

  Corollary fwhenb_nth:
    forall n e es xs,
      (fwhenb e xs es) # n = if es # n ==b present (Venum e) then xs # n else false.
  Proof.
    intros. setoid_rewrite fwhen_nth; auto.
  Qed.

  Lemma fwhen_Cons {A} (abs : A) :
    forall sel e es x xs,
      (fwhen abs sel (x ⋅ xs) (e ⋅ es))
        = (if e ==b present (Venum sel) then x else abs) ⋅ (fwhen abs sel xs es).
  Proof.
    intros *.
    rewrite (unfold_Stream (fwhen _ _ _ _)); simpl. reflexivity.
  Qed.

  Lemma when_fwhen sel : forall es vs vs',
      when sel vs es vs' ->
      vs' ≡ fwhenv sel vs es.
  Proof.
    cofix CoFix.
    intros * Hwhen; inv Hwhen; constructor; simpl; auto.
    - destruct (_ ==b _) eqn:Heq; auto.
      rewrite equiv_decb_equiv in Heq. inv Heq. congruence.
    - rewrite equiv_decb_refl; auto.
  Qed.

  Lemma fwhenv_whenv sel : forall es vs,
      SForall (fun v => match v with present (Venum _) | absent => True | _ => False end) es ->
      abstract_clock vs ≡ abstract_clock es ->
      when sel vs es (fwhenv sel vs es).
  Proof.
    cofix CoFix.
    intros ([]&?) ([]&?) Hwt Hac; inv Hwt; inv Hac; simpl in *; try congruence.
    - rewrite (unfold_Stream (fwhenv _ _ _)); simpl.
      constructor. apply CoFix; auto.
    - rewrite (unfold_Stream (fwhenv _ _ _)); simpl. destruct (_ ==b _) eqn:Heq.
      + rewrite equiv_decb_equiv in Heq. inv Heq.
        constructor. apply CoFix; auto.
      + destruct v; try now exfalso.
        constructor. apply CoFix; auto.
        intro contra. subst e. rewrite equiv_decb_refl in Heq. congruence.
  Qed.

  Lemma when_hist_fwhen_hist {K} sel es : forall (Hi Hi' : @history K),
      when_hist sel Hi es Hi' ->
      Hi' ⊑ (fwhen_hist sel Hi es).
  Proof.
    intros * Hwhen.
    intros ?? Hfind.
    eapply Hwhen in Hfind as (?&Hf&Hfind).
    apply when_fwhen in Hf.
    do 2 esplit; eauto.
    simpl_fenv. now rewrite Hfind.
  Qed.

  Lemma when_hist_restrict_ac {K} `{FEnv.fenv_key K} sel es : forall (Hi : @history K) xs,
      SForall (fun v => match v with present (Venum _) | absent => True | _ => False end) es ->
      (forall x vs, List.In x xs -> sem_var Hi x vs -> abstract_clock vs ≡ abstract_clock es) ->
      when_hist sel Hi es (FEnv.restrict (fwhen_hist sel Hi es) xs).
  Proof.
    intros * Hwt Hac.
    intros ?? Hfind. apply FEnv.restrict_find_inv in Hfind as (Hin&Hfind).
    simpl_fenv.
    do 2 esplit; [|eauto].
    eapply fwhenv_whenv; eauto.
    eapply Hac; eauto. econstructor; eauto. reflexivity.
  Qed.

  Add Parametric Morphism {A} (absent: A) k : (fwhen absent k)
      with signature @EqSt _ ==> @EqSt _ ==> @EqSt _
        as fwhen_EqSt.
  Proof.
    intros rs rs' Ers xs xs' Exs.
    eapply ntheq_eqst; intros n.
    eapply eqst_ntheq with (n:=n) in Exs.
    rewrite 2 fwhen_nth, Exs, Ers. reflexivity.
  Qed.

  Add Parametric Morphism k : (fwhenv k)
      with signature @EqSt _ ==> @EqSt _ ==> @EqSt _
        as fwhenv_morph.
  Proof.
    intros rs rs' Ers xs xs' Exs.
    apply fwhen_EqSt; auto.
  Qed.

  Add Parametric Morphism {K} k : (@fwhen_hist K k)
      with signature FEnv.Equiv (@EqSt _) ==> @EqSt _ ==> FEnv.Equiv (@EqSt _)
        as fwhen_hist_EqSt.
  Proof.
    intros H H' EH  r r' Er.
    intros x. specialize (EH x). simpl_fenv.
    inv EH; simpl; constructor.
    rewrite H2, Er. reflexivity.
  Qed.

  Add Parametric Morphism k : (fwhenb k)
      with signature @EqSt _ ==> @EqSt _ ==> @EqSt _
        as fwhenb_EqSt.
  Proof.
    intros rs rs' Ers xs xs' Exs.
    apply fwhen_EqSt; auto.
  Qed.

  Lemma ac_fwhen : forall k sc xs,
      abstract_clock (fwhenv k xs sc) ≡ fwhenb k (abstract_clock xs) sc.
  Proof.
    intros. apply ntheq_eqst; intros n.
    rewrite ac_nth. setoid_rewrite fwhen_nth. rewrite ac_nth.
    destruct (_ ==b _); auto.
  Qed.

  Lemma sem_var_fwhen {K} : forall k r (H: @history K) x v,
      sem_var H x v ->
      sem_var (fwhen_hist k H r) x (fwhenv k v r).
  Proof.
    intros * Hvar. inv Hvar.
    simpl_fenv. econstructor. now rewrite H1.
    now rewrite H2.
  Qed.

  Lemma sem_var_when {K} x : forall sel sc (Hi Hi': @history K) vs,
      when_hist sel Hi sc Hi' ->
      sem_var Hi x vs ->
      FEnv.In x Hi' ->
      when sel vs sc (fwhenv sel vs sc).
  Proof.
    intros * Hwhen Hvar Hin.
    inv Hin. eapply Hwhen in H as (?&Hf&Hv).
    eapply sem_var_det in Hvar; [|econstructor; eauto; reflexivity].
    rewrite Hvar in Hf.
    assert (Hf':=Hf). apply when_fwhen in Hf'. rewrite <-Hf'; auto.
  Qed.

  Lemma sem_var_when_inv {K} : forall k r (Hi Hi' : @history K) x v,
      when_hist k Hi r Hi' ->
      sem_var Hi' x v ->
      exists v', sem_var Hi x v' /\ when k v' r v.
  Proof.
    intros * Hf Hvar. inv Hvar.
    apply Hf in H0 as (?&Hwhen&?).
    do 2 esplit; eauto. 2:rewrite H1; eauto.
    econstructor; eauto. reflexivity.
  Qed.

  Lemma sem_var_fwhen_inv {K} : forall k sc (H: @history K) x v,
      sem_var (fwhen_hist k H sc) x v ->
      exists v', sem_var H x v' /\ v ≡ (fwhenv k v' sc).
  Proof.
    intros * Hvar. inv Hvar.
    simpl_fenv.
    do 2 esplit; eauto.
    econstructor; eauto. reflexivity.
  Qed.

  Lemma refines_fwhen {K} : forall e sc (H H': @history K),
      H ⊑ H' ->
      (fwhen_hist e H sc) ⊑ (fwhen_hist e H' sc).
  Proof.
    intros * Href ?? Hfind.
    simpl_fenv.
    eapply Href in Hf as (?&Heq&Hfind).
    rewrite Hfind; simpl.
    do 2 esplit; eauto. now rewrite Heq.
  Qed.

  Lemma when_absent e :
    when e (Streams.const absent) (Streams.const absent) (Streams.const absent).
  Proof.
    cofix CoFix.
    rewrite (unfold_Stream (Streams.const absent)), (unfold_Stream (Streams.const absent)); simpl.
    constructor; auto.
  Qed.

  Corollary when_hist_absent {K} e sc : forall (Hi Hi': @history K),
    when_hist e Hi sc Hi' ->
    when_hist e (FEnv.map (fun _ => Streams.const absent) Hi) (Streams.const absent) (FEnv.map (fun _ => Streams.const absent) Hi').
  Proof.
    intros * Hwhen.
    intros ?? Hfind. simpl_fenv.
    apply Hwhen in Hf as (?&Hf&Hfind).
    do 2 esplit. 2:now rewrite Hfind.
    apply when_absent.
  Qed.

  Lemma fwhen_absent {A} (absent: A) : forall k sc,
      fwhen absent k (Streams.const absent) sc ≡ Streams.const absent.
  Proof.
    intros *.
    eapply ntheq_eqst. intros n.
    rewrite fwhen_nth, const_nth.
    destruct (_ ==b _); auto.
  Qed.

  Corollary fwhen_hist_absent {K}: forall k sc (H: @history K),
      FEnv.Equiv (@EqSt _) (fwhen_hist k (FEnv.map (fun _ => Streams.const absent) H) sc)
                 (FEnv.map (fun _ => Streams.const absent) H).
  Proof.
    intros * x. simpl_fenv.
    destruct (H x); constructor.
    eapply fwhen_absent.
  Qed.

  Corollary fwhen_hist_absent' {K} : forall k sc (H: @history K),
      FEnv.Equiv (@EqSt _) (FEnv.map (fun _ => Streams.const (@absent value)) (fwhen_hist k H sc))
                 (FEnv.map (fun _ => Streams.const absent) H).
  Proof.
    intros * x. simpl_fenv.
    destruct (H x); constructor.
    reflexivity.
  Qed.

  Corollary fwhenb_absent: forall k sc,
      fwhenb k (Streams.const false) sc ≡ Streams.const false.
  Proof.
    intros *.
    eapply ntheq_eqst. intros n.
    rewrite fwhenb_nth, const_nth.
    destruct (_ ==b _); auto.
  Qed.

  Lemma fwhenb_both_slower : forall k sc bs bs',
      slower sc bs ->
      slower sc bs' ->
      fwhenb k bs sc ≡ fwhenb k bs' sc.
  Proof.
    intros * Hslow1 Hslow2.
    apply ntheq_eqst; intros n.
    setoid_rewrite slower_nth in Hslow1. setoid_rewrite slower_nth in Hslow2.
    repeat rewrite fwhenb_nth.
    specialize (Hslow1 n). specialize (Hslow2 n).
    destruct (sc # n) eqn:Hsc; setoid_rewrite Hsc; auto.
    destruct (_ ==b _); auto.
    destruct (bs # n), (bs' # n); auto.
    - specialize (Hslow2 eq_refl); congruence.
    - specialize (Hslow1 eq_refl); congruence.
  Qed.

  (** ** select and fselect, combining when and mask *)

  Definition stres_st (stres : Stream (synchronous (enumtag * bool))) :=
    Streams.map (fun v => match v with present (e, _) => present (Venum e) | absent => absent end) stres.
  Definition stres_res (stres : Stream (synchronous (enumtag * bool))) :=
    Streams.map (fun v => match v with present (_, b) => b | absent => false end) stres.

  CoInductive select' (sel : enumtag) (k : nat) : nat -> Stream (synchronous (enumtag * bool)) -> Stream svalue -> Stream svalue -> Prop :=
  | select_abs : forall k' stres xs ys,
      select' sel k k' stres xs ys ->
      select' sel k k' (absent ⋅ stres) (absent ⋅ xs) (absent ⋅ ys)
  | select_nsel : forall k' v r stres x xs ys,
      select' sel k k' stres xs ys ->
      v <> sel ->
      select' sel k k' (present (v, r) ⋅ stres) (present x ⋅ xs) (absent ⋅ ys)
  | select_nreset : forall k' stres x xs ys,
      select' sel k k' stres xs ys ->
      select' sel k k' (present (sel, false) ⋅ stres) (present x ⋅ xs) ((if k' =? k then present x else absent) ⋅ ys)
  | select_reset : forall k' stres x xs ys,
      select' sel k (S k') stres xs ys ->
      select' sel k k' (present (sel, true) ⋅ stres) (present x ⋅ xs) ((if S k' =? k then present x else absent) ⋅ ys).
  Definition select sel k := select' sel k 0.

  Definition select_hist {K} sel k stres (Hi Hi': @history K) :=
    FEnv.refines (fun vs' vs => select sel k stres vs vs') Hi' Hi.

  Definition fselect {A} (absent : A) (e : enumtag) (k : nat) (stres : Stream (synchronous (enumtag * bool))) (xs : Stream A) :=
    mask absent k
         (fwhenb e (stres_res stres) (stres_st stres))
         (fwhen absent e xs (stres_st stres)).

  Definition fselectb := fselect false.
  Definition fselectv e k stres xs := fselect (@absent value) e k stres xs.
  Definition fselect_hist {K} e k stres H := @FEnv.map K _ _ (fselectv e k stres) H.
  Global Hint Unfold fselect_hist : fenv.

  Add Parametric Morphism : stres_st
      with signature @EqSt _ ==> @EqSt _
        as stres_st_EqSt.
  Proof.
    intros * Heq. unfold stres_st.
    apply ntheq_eqst; intros n. apply eqst_ntheq with (n:=n) in Heq.
    rewrite 2 Str_nth_map. rewrite Heq; auto.
  Qed.

  Add Parametric Morphism : stres_res
      with signature @EqSt _ ==> @EqSt _
        as stres_res_EqSt.
  Proof.
    intros * Heq. unfold stres_res.
    apply ntheq_eqst; intros n. apply eqst_ntheq with (n:=n) in Heq.
    rewrite 2 Str_nth_map. rewrite Heq; auto.
  Qed.

  Lemma select_mask_when sel k : forall stres xs zs,
      select sel k stres xs zs
      <-> exists ys, when sel xs (stres_st stres) ys
              /\ zs ≡ maskv k (fwhenb sel (stres_res stres) (stres_st stres)) ys.
  Proof.
    intros *. split.
    - intros * Hsel. exists (fwhenv sel xs (stres_st stres)). split.
      + revert Hsel. unfold select. generalize 0 as k'. revert stres xs zs.
        cofix CoFix; intros [] [] [] * Hsel.
        inversion Hsel; clear Hsel; subst k'0 s s0 s1 s2 s3 s4.
        all:unfold stres_st; unfold fwhenv; rewrite map_Cons, fwhen_Cons.
        * constructor; eauto.
        * replace (present (Venum v) ==b present (Venum sel)) with false.
          2:{ destruct (_ ==b _) eqn:Heq; auto.
              rewrite equiv_decb_equiv in Heq. inv Heq. congruence. }
          constructor; eauto.
        * rewrite equiv_decb_refl. constructor; eauto.
        * rewrite equiv_decb_refl. constructor; eauto.

      + revert Hsel. unfold select, maskv, mask. generalize 0 as k'. revert stres xs zs.
        cofix CoFix; intros [] [] [] * Hsel.
        inversion Hsel; clear Hsel; subst k'0 s s0 s1 s2 s3 s4.
        all:unfold stres_st, stres_res, fwhenb; unfold fwhenb, fwhenv;
          repeat rewrite map_Cons; repeat rewrite fwhen_Cons; repeat rewrite mask'_Cons.
        * constructor; simpl; eauto. destruct (_ =? _); auto.
        * replace (present (Venum v) ==b present (Venum sel)) with false.
          2:{ destruct (_ ==b _) eqn:Heq; auto.
              rewrite equiv_decb_equiv in Heq. inv Heq. congruence. }
          constructor; eauto. destruct (_ =? _); auto.
        * rewrite equiv_decb_refl. constructor; eauto.
        * rewrite equiv_decb_refl. constructor; eauto.

    - intros (ys&Hwhen&Hmask).
      revert Hwhen Hmask. unfold maskv, mask, select. generalize 0 as k'.
      revert stres xs ys zs.
      cofix CoFix; intros [] [] [] [] * Hwhen Hmask.
      setoid_rewrite map_Cons in Hwhen. setoid_rewrite map_Cons in Hmask.
      inv Hmask; simpl in *; subst.
      inversion Hwhen; clear Hwhen; subst cs s1 s2 s3 s4.
      + destruct s as [|(?&?)]; simpl in *; try congruence.
        destruct (_ =? _); constructor; eauto.
      + destruct s as [|(?&?)]; simpl in *; take (present _ = _) and inv it.
        destruct (_ ==b _) eqn:Heq; simpl in *.
        { rewrite equiv_decb_equiv in Heq. inv Heq. congruence. }
        destruct (_ =? _); constructor; eauto.
      + destruct s as [|(?&?)]; simpl in *; take (present _ = _) and inversion it; subst e.
        rewrite equiv_decb_refl in *.
        destruct b; simpl; constructor; eauto.
  Qed.

  Add Parametric Morphism e k : (select e k)
      with signature @EqSt _ ==> @EqSt _ ==> @EqSt _ ==> Basics.impl
        as select_EqSt.
  Proof.
    intros * Heq1 * Heq2 * Heq3 Hsel.
    rewrite select_mask_when in *.
    destruct Hsel as (?&?&?). do 2 esplit.
    - rewrite <-Heq2, <-Heq1; eauto.
    - rewrite <-Heq3, <-Heq1; eauto.
  Qed.

  Add Parametric Morphism {K} sel k : (@select_hist K sel k)
      with signature @EqSt _ ==> FEnv.Equiv (@EqSt _) ==> FEnv.Equiv (@EqSt _) ==> Basics.impl
        as select_hist_EqSt.
  Proof.
    intros * Heq1 * Heq2 * Heq3 Hf.
    unfold select_hist in *.
    intros ?? Hfind. specialize (Heq3 x2). rewrite Hfind in Heq3. inv Heq3.
    symmetry in H. apply Hf in H as (?&Hwhen&Hfind').
    specialize (Heq2 x2). rewrite Hfind' in Heq2. inv Heq2.
    do 2 esplit; [|eauto].
    rewrite <-Heq1, <-H2, <-H1; auto.
  Qed.

  Add Parametric Morphism {A} (abs : A) e k : (fselect abs e k)
      with signature @EqSt _ ==> @EqSt _ ==> @EqSt _
        as fselect_EqSt.
  Proof.
    intros * Heq1 * Heq2.
    unfold fselect. now rewrite Heq1, Heq2.
  Qed.

  Add Parametric Morphism e k : (fselectb e k)
      with signature @EqSt _ ==> @EqSt _ ==> @EqSt _
        as fselectb_EqSt.
  Proof.
    intros * ? * ?. apply fselect_EqSt; auto.
  Qed.

  Add Parametric Morphism e k : (fselectv e k)
      with signature @EqSt _ ==> @EqSt _ ==> @EqSt _
        as fselectv_morph.
  Proof.
    intros * ? * ?. apply fselect_EqSt; auto.
  Qed.

  Add Parametric Morphism {K} e k : (@fselect_hist K e k)
      with signature @EqSt _ ==> FEnv.Equiv (@EqSt _) ==> FEnv.Equiv (@EqSt _)
        as fselect_hist_EqSt.
  Proof.
    intros r r' Er H H' EH x.
    specialize (EH x). simpl_fenv.
    inv EH; constructor.
    rewrite H2, Er. reflexivity.
  Qed.

  Lemma ac_fselect : forall e k sc xs,
      abstract_clock (fselectv e k sc xs) ≡ fselectb e k sc (abstract_clock xs).
  Proof.
    intros.
    unfold fselectv, fselectb, fselect.
    rewrite ac_mask, ac_fwhen. reflexivity.
  Qed.

  Lemma select_fselect sel k : forall es vs vs',
      select sel k es vs vs' ->
      vs' ≡ fselectv sel k es vs.
  Proof.
    intros * Hsel. apply select_mask_when in Hsel as (?&Hfil&Hmask).
    apply when_fwhen in Hfil.
    rewrite Hmask, Hfil. reflexivity.
  Qed.

  Lemma sem_var_fselect {K} : forall e k r (H: @history K) x v,
      sem_var H x v ->
      sem_var (fselect_hist e k r H) x (fselectv e k r v).
  Proof.
    intros * Hvar. inv Hvar.
    econstructor. unfold fselect_hist, FEnv.map. now rewrite H1.
    rewrite H2. reflexivity.
  Qed.

  Lemma sem_var_select {K} x : forall sel k sc (Hi Hi': @history K) vs,
      select_hist sel k sc Hi Hi' ->
      sem_var Hi x vs ->
      FEnv.In x Hi' ->
      select sel k sc vs (fselectv sel k sc vs).
  Proof.
    intros * Hselect Hvar Hin.
    inv Hin. eapply Hselect in H as (?&Hf&Hv).
    eapply sem_var_det in Hvar; [|econstructor; eauto; reflexivity].
    rewrite Hvar in Hf.
    assert (Hf':=Hf). apply select_fselect in Hf'. rewrite <-Hf'; auto.
  Qed.

  Lemma sem_var_select_inv {K} : forall sel k r (Hi Hi': @history K) x v,
      select_hist sel k r Hi Hi' ->
      sem_var Hi' x v ->
      exists v', sem_var Hi x v' /\ select sel k r v' v.
  Proof.
    intros * Hf Hvar. inv Hvar.
    apply Hf in H0 as (?&Hwhen&?).
    do 2 esplit; eauto. 2:rewrite H1; eauto.
    econstructor; eauto. reflexivity.
  Qed.

  Lemma sem_var_fselect_inv {K}: forall sel k r (H: @history K) x v,
      sem_var (fselect_hist sel k r H) x v ->
      exists v', sem_var H x v' /\ v ≡ (fselectv sel k r v').
  Proof.
    intros * Hvar. inv Hvar.
    simpl_fenv.
    do 2 esplit; eauto. econstructor; eauto. reflexivity.
  Qed.

  Lemma fselectv_selectv sel k : forall es vs,
      abstract_clock vs ≡ abstract_clock es ->
      select sel k es vs (fselectv sel k es vs).
  Proof.
    intros * Hac. apply select_mask_when. do 2 esplit.
    + eapply fwhenv_whenv.
      1:{ eapply SForall_forall; intros. unfold stres_st. rewrite Str_nth_map.
          destruct (es # n) as [|(?&?)]; auto. }
      rewrite Hac. apply ntheq_eqst; intros.
      rewrite 2 ac_nth. setoid_rewrite Str_nth_map. destruct (es # n) as [|(?&?)]; auto.
    + unfold fselectv, fselect, fwhenv. reflexivity.
  Qed.

  Lemma select_hist_fselect_hist {K} sel k es : forall (Hi Hi': @history K),
      select_hist sel k es Hi Hi' ->
      Hi' ⊑ (fselect_hist sel k es Hi).
  Proof.
    intros * Hselect.
    intros ?? Hfind.
    eapply Hselect in Hfind as (?&Hf&Hfind).
    apply select_fselect in Hf.
    do 2 esplit; eauto.
    unfold fselect_hist, FEnv.map. now rewrite Hfind.
  Qed.

  Lemma select_hist_restrict_ac sel k es : forall Hi xs,
      (forall x vs, List.In x xs -> sem_var Hi x vs -> abstract_clock vs ≡ abstract_clock es) ->
      select_hist sel k es Hi (FEnv.restrict (fselect_hist sel k es Hi) xs).
  Proof.
    intros * Hac.
    intros ?? Hfind. apply FEnv.restrict_find_inv in Hfind as (Hin&Hfind).
    simpl_fenv.
    do 2 esplit; [|eauto].
    eapply fselectv_selectv; eauto.
    eapply Hac; eauto. econstructor; eauto. reflexivity.
  Qed.

  Fact stres_st_ac : forall stres,
      abstract_clock (stres_st stres) ≡ abstract_clock stres.
  Proof.
    intros. unfold stres_st.
    apply ntheq_eqst. intros n. rewrite 2 ac_nth, Str_nth_map.
    destruct (stres # n) as [|(?&?)]; simpl; auto.
  Qed.

  Lemma ac_select :
    forall e k cs xs rs,
      select e k cs xs rs -> abstract_clock cs ≡ abstract_clock xs.
  Proof.
    intros * Hsel.
    apply select_mask_when in Hsel as (?&Hwhen&_).
    apply ac_when in Hwhen. now rewrite Hwhen, stres_st_ac.
  Qed.

  Fact stres_st_absent : stres_st (Streams.const absent) ≡ Streams.const absent.
  Proof.
    apply ntheq_eqst. intros n. setoid_rewrite Str_nth_map.
    rewrite 2 const_nth; auto.
  Qed.

  Fact stres_res_absent : stres_res (Streams.const absent) ≡ Streams.const false.
  Proof.
    apply ntheq_eqst. intros n. setoid_rewrite Str_nth_map.
    rewrite 2 const_nth; auto.
  Qed.

  Lemma select_absent e k :
    select e k (Streams.const absent) (Streams.const absent) (Streams.const absent).
  Proof.
    intros. apply select_mask_when. do 2 esplit.
    rewrite stres_st_absent; eauto using when_absent.
    rewrite stres_st_absent, stres_res_absent.
    apply ntheq_eqst. intros n.
    unfold maskv. rewrite mask_nth, const_nth. destruct (_ =? _); auto.
  Qed.

  Corollary select_hist_absent {K} e k sc : forall (Hi Hi': @history K),
    select_hist e k sc Hi Hi' ->
    select_hist e k (Streams.const absent)
                (FEnv.map (fun _ => Streams.const absent) Hi) (FEnv.map (fun _ => Streams.const absent) Hi').
  Proof.
    intros * Hselect ?? Hfind.
    simpl_fenv.
    apply Hselect in Hf as (?&Hf&Hfind).
    do 2 esplit. 2:now rewrite Hfind.
    apply select_absent.
  Qed.

  Lemma fselect_absent {A} (absent: A) : forall e k sc,
      fselect absent e k sc (Streams.const absent) ≡ Streams.const absent.
  Proof.
    intros *. unfold fselect.
    eapply ntheq_eqst. intros n.
    rewrite mask_nth, fwhen_nth, const_nth.
    destruct (_ =? _); auto. destruct (_ ==b _); auto.
  Qed.

  Corollary fselect_hist_absent {K} : forall e k sc (H: @history K),
      FEnv.Equiv (@EqSt _) (fselect_hist e k sc (FEnv.map (fun _ => Streams.const absent) H))
                (FEnv.map (fun _ => Streams.const absent) H).
  Proof.
    intros * x. simpl_fenv.
    destruct (H x); constructor.
    eapply fselect_absent.
  Qed.

  Corollary fselect_hist_absent' {K} : forall e k sc (H: @history K),
      FEnv.Equiv (@EqSt _) (FEnv.map (fun _ => Streams.const (@absent value)) (fselect_hist e k sc H))
                (FEnv.map (fun _ => Streams.const absent) H).
    intros * x. simpl_fenv.
    destruct (H x); constructor.
    reflexivity.
  Qed.

  Corollary fselectb_absent: forall e k sc,
      fselectb e k sc (Streams.const false) ≡ Streams.const false.
  Proof.
    intros *. unfold fselectb.
    rewrite fselect_absent. reflexivity.
  Qed.

  Lemma fselectb_both_slower : forall e k sc bs bs',
      slower sc bs ->
      slower sc bs' ->
      fselectb e k sc bs ≡ fselectb e k sc bs'.
  Proof.
    intros * Hslow1 Hslow2.
    unfold fselectb, fselect.
    apply mask_morph; [reflexivity|].
    apply fwhenb_both_slower.
    1,2:apply slower_nth; intros n Hbs; setoid_rewrite Str_nth_map.
    - rewrite slower_nth in Hslow1. specialize (Hslow1 _ Hbs). now rewrite Hslow1.
    - rewrite slower_nth in Hslow2. specialize (Hslow2 _ Hbs). now rewrite Hslow2.
  Qed.

  (** ** Additional definitions for state machines *)

  Definition const_stres {A} (b : Stream bool) (v : A) :=
    Streams.map (fun (b : bool) => if b then present v else absent) b.

  Add Parametric Morphism {A} : (@const_stres A)
      with signature @EqSt bool ==> eq ==> @EqSt _
        as const_stres_EqSt.
  Proof.
    intros * Heq ?.
    apply ntheq_eqst. intros n. apply eqst_ntheq with (n:=n) in Heq.
    unfold const_stres. rewrite 2 Str_nth_map, Heq; auto.
  Qed.

  CoFixpoint first_of {A} (v : A) (bs : Stream bool) (ys : Stream (synchronous A)) : Stream (synchronous A) :=
    match bs, ys with
    | true ⋅ bs, _ ⋅ ys => present v ⋅ first_of v bs ys
    | false ⋅ bs, y ⋅ ys => y ⋅ first_of v bs ys
    end.

  Lemma first_of_nth {A} n : forall (v : A) bs ys,
      (first_of v bs ys) # n = if bs # n then present v else ys # n.
  Proof.
    induction n; intros ? (?&?) (?&?).
    - rewrite Str_nth_0, Str_nth_0_hd; simpl.
      destruct b; auto.
    - rewrite Str_nth_S, Str_nth_S_tl; simpl.
      destruct b; eauto.
  Qed.

  Add Parametric Morphism {A} : (@first_of A)
      with signature eq ==> @EqSt _ ==> @EqSt _ ==> @EqSt _
        as first_of_EqSt.
  Proof.
    intros * Heq1 * Heq2.
    apply ntheq_eqst. intros n. apply eqst_ntheq with (n:=n) in Heq1. apply eqst_ntheq with (n:=n) in Heq2.
    rewrite 2 first_of_nth. rewrite Heq1, Heq2. reflexivity.
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
