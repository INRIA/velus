From Coq Require Import List.
From Coq Require Export Lists.Streams.
From Coq Require Import Setoid.
From Coq Require Import Morphisms.
From Coq Require Import Arith.EqNat.
From Coq Require Import Omega.

From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Environment.
From Velus Require Import Clocks.

Module Type COINDSTREAMS
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op).

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

  (** Synchronous operators *)

  CoFixpoint const (b: Stream bool) (c: const): Stream value :=
    (if hd b then present (sem_const c) else absent) ⋅ const (tl b) c.

  CoInductive lift1 (op: unop) (ty: type)
    : Stream value -> Stream value -> Prop :=
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
    : Stream value -> Stream value -> Stream value -> Prop :=
  | Lift2A:
      forall xs ys rs,
        lift2 op ty1 ty2 xs ys rs ->
        lift2 op ty1 ty2 (absent ⋅ xs) (absent ⋅ ys) (absent ⋅ rs)
  | Lift2P:
      forall x y r xs ys rs,
        sem_binop op x ty1 y ty2 = Some r ->
        lift2 op ty1 ty2 xs ys rs ->
        lift2 op ty1 ty2 (present x ⋅ xs) (present y ⋅ ys) (present r ⋅ rs).

  CoInductive when (b: bool)
    : Stream value -> Stream value -> Stream value -> Prop :=
  | WhenA:
      forall xs cs rs,
        when b xs cs rs ->
        when b (absent ⋅ xs) (absent ⋅ cs) (absent ⋅ rs)
  | WhenPA:
      forall x c xs cs rs,
        when b xs cs rs ->
        val_to_bool c = Some (negb b) ->
        when b (present x ⋅ xs) (present c ⋅ cs) (absent ⋅ rs)
  | WhenPP:
      forall x c xs cs rs,
        when b xs cs rs ->
        val_to_bool c = Some b ->
        when b (present x ⋅ xs) (present c ⋅ cs) (present x ⋅ rs).

  CoInductive merge
    : Stream value -> Stream value -> Stream value -> Stream value -> Prop :=
  | MergeA:
      forall xs ts fs rs,
        merge xs ts fs rs ->
        merge (absent ⋅ xs) (absent ⋅ ts) (absent ⋅ fs) (absent ⋅ rs)
  | MergeT:
      forall t xs ts fs rs,
        merge xs ts fs rs ->
        merge (present true_val ⋅ xs)
              (present t ⋅ ts) (absent ⋅ fs) (present t ⋅ rs)
  | MergeF:
      forall f xs ts fs rs,
        merge xs ts fs rs ->
        merge (present false_val ⋅ xs)
              (absent ⋅ ts) (present f ⋅ fs) (present f ⋅ rs).

  CoInductive ite
    : Stream value -> Stream value -> Stream value -> Stream value -> Prop :=
  | IteA:
      forall s ts fs rs,
        ite s ts fs rs ->
        ite (absent ⋅ s) (absent ⋅ ts) (absent ⋅ fs) (absent ⋅ rs)
  | IteT:
      forall t f s ts fs rs,
        ite s ts fs rs ->
        ite (present true_val ⋅ s)
            (present t ⋅ ts) (present f ⋅ fs) (present t ⋅ rs)
  | IteF:
      forall t f s ts fs rs,
        ite s ts fs rs ->
        ite (present false_val ⋅ s)
            (present t ⋅ ts) (present f ⋅ fs) (present f ⋅ rs).

  CoInductive bools_of: Stream value -> Stream bool -> Prop :=
    bools_of_intro:
      forall v vs b bs,
        bools_of vs bs ->
        value_to_bool v = Some b ->
        bools_of (v ⋅ vs) (b ⋅ bs).

  CoFixpoint mask (k: nat) (rs: Stream bool) (xs: Stream value) : Stream value :=
    let mask' k' := mask k' (tl rs) (tl xs) in
    match k, hd rs with
    | 0, true    => Streams.const absent
    | 0, false   => hd xs  ⋅ mask' 0
    | 1, true    => hd xs  ⋅ mask' 0
    | S k', true => absent ⋅ mask' k'
    | S _, false => absent ⋅ mask' k
    end.

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

  Lemma mask_nth:
    forall n k rs xs,
      (mask k rs xs) # n = if (count rs) # n  =? k then xs # n else absent.
  Proof.
    unfold Str_nth.
    induction n, k as [|[|k]]; intros;
      unfold_Stv rs; simpl; auto.
    - pose proof (count_acc_grow 1 rs) as H.
      apply (ForAll_Str_nth_tl n) in H; inv H.
      assert (hd (Str_nth_tl n (count_acc 1 rs)) <> 0) as E by omega;
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
      forall n, xs # n = if b # n then present (sem_const c) else absent.
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
            /\ c' = sem_const c.
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

  Ltac cofix_step CoFix H :=
    let n := fresh "n" in
    apply CoFix; intro n; specialize (H (S n));
    repeat rewrite Str_nth_S in H; auto.

  Lemma when_spec:
    forall k xs cs rs,
      when k xs cs rs <->
      (forall n,
          (xs # n = absent
           /\ cs # n = absent
           /\ rs # n = absent)
          \/
          (exists x c,
              xs # n = present x
              /\ cs # n = present c
              /\ val_to_bool c = Some (negb k)
              /\ rs # n = absent)
          \/
          (exists x c,
              xs # n = present x
              /\ cs # n = present c
              /\ val_to_bool c = Some k
              /\ rs # n = present x)).
  Proof.
    split.
    - intros H n; revert dependent xs; revert cs rs k.
      induction n; intros.
      + inv H; intuition.
        * right; left. do 2 eexists; intuition.
        * right; right. do 2 eexists; intuition.
      + inv H; repeat rewrite Str_nth_S; auto.
    - revert xs cs rs k.
      cofix CoFix; intros * H.
      unfold_Stv xs; unfold_Stv cs; unfold_Stv rs;
        try (specialize (H 0); repeat rewrite Str_nth_0 in H;
             destruct H as [(?&?&?)|[(?&?&?&?&?)|(?&?&?&?&?)]];
             discriminate).
      + constructor; cofix_step CoFix H.
      + constructor.
        * cofix_step CoFix H.
        * specialize (H 0); repeat rewrite Str_nth_0 in H;
            destruct H as [(?&?&?)|[(?&?&?&?&?&?)|(?&?&?&?&?&?)]];
            try discriminate.
          congruence.
      + destruct (H 0) as [(?&?&?)|[(?&?&?&?&?&?)|(?&?& E & E' &?& E'')]];
          try discriminate.
        rewrite Str_nth_0 in E, E', E''.
        rewrite E, E''.
        constructor; try congruence.
        cofix_step CoFix H.
  Qed.

  Lemma lift1_spec:
    forall op t xs ys,
      lift1 op t xs ys <->
      (forall n,
          (xs # n = absent /\ ys # n = absent)
          \/
          (exists x y,
              xs # n = present x
              /\ sem_unop op x t = Some y
              /\ ys # n = present y)).
  Proof.
    split.
    - intros H n; revert dependent xs; revert ys t op.
      induction n; intros.
      + inv H; intuition.
        right. do 2 eexists; intuition; auto.
      + inv H; repeat rewrite Str_nth_S;auto.
    - revert xs ys t op.
      cofix CoFix; intros * H.
      unfold_Stv xs; unfold_Stv ys;
        try (specialize (H 0); repeat rewrite Str_nth_0 in H;
             destruct H as [(?&?)|(?&?&?&?&?)]; discriminate).
      + constructor; cofix_step CoFix H.
      + constructor.
        * destruct (H 0) as [(?&?)|(?&?& E &?& E')]; try discriminate.
          rewrite Str_nth_0 in E, E'.
          inv E; inv E'; auto.
        * cofix_step CoFix H.
  Qed.

  Lemma lift2_spec:
    forall op t1 t2 xs ys zs,
      lift2 op t1 t2 xs ys zs <->
      (forall n,
          (xs # n = absent
           /\ ys # n = absent
           /\ zs # n = absent)
          \/
          (exists x y z,
              xs # n = present x
              /\ ys # n = present y
              /\ sem_binop op x t1 y t2 = Some z
              /\ zs # n = present z)).
  Proof.
    split.
    - intros H n; revert dependent xs; revert ys zs t1 t2 op.
      induction n; intros.
      + inv H; intuition.
        right. do 3 eexists; intuition; auto.
      + inv H; repeat rewrite Str_nth_S; auto.
    - revert xs ys zs t1 t2 op.
      cofix CoFix; intros * H.
      unfold_Stv xs; unfold_Stv ys; unfold_Stv zs;
        try (specialize (H 0); repeat rewrite Str_nth_0 in H;
             destruct H as [(?&?&?)|(?&?&?&?&?&?&?)]; discriminate).
      + constructor; cofix_step CoFix H.
      + constructor.
        * destruct (H 0) as [(?&?&?)|(?&?&?& E & E' &?& E'')]; try discriminate.
          rewrite Str_nth_0 in E, E', E''.
          inv E; inv E'; inv E''; auto.
        * cofix_step CoFix H.
  Qed.

  (** ** cexp level synchronous operators specifications *)

  Lemma merge_spec:
    forall xs ts fs rs,
      merge xs ts fs rs <->
      (forall n,
          (xs # n = absent
           /\ ts # n = absent
           /\ fs # n = absent
           /\ rs # n = absent)
          \/
          (exists t,
              xs # n = present true_val
              /\ ts # n = present t
              /\ fs # n = absent
              /\ rs # n = present t)
          \/
          (exists f,
              xs # n = present false_val
              /\ ts # n = absent
              /\ fs # n = present f
              /\ rs # n = present f)).
  Proof.
    split.
    - intros * H n.
      revert dependent xs; revert ts fs rs.
      induction n; intros.
      + inv H; intuition.
        * right; left. eexists; intuition.
        * right; right. eexists; intuition.
      + inv H; repeat rewrite Str_nth_S; auto.
    - revert xs ts fs rs; cofix CoFix; intros * H.
      unfold_Stv xs; unfold_Stv ts; unfold_Stv fs; unfold_Stv rs;
        try (specialize (H 0); repeat rewrite Str_nth_0 in H;
             destruct H as [(?&?&?&?)|[(?&?&?&?&?)|(?&?&?&?&?)]];
             discriminate).
      + constructor; cofix_step CoFix H.
      + destruct (H 0) as [(?&?&?&?)|[(?&?&?&?&?)|(?& E &?& E' & E'')]];
          try discriminate.
        rewrite Str_nth_0 in E, E', E''; inv E; inv E'; inv E''.
        constructor; cofix_step CoFix H.
      + destruct (H 0) as [(?&?&?&?)|[(?& E & E' &?& E'')|(?&?&?&?&?)]];
          try discriminate.
        rewrite Str_nth_0 in E, E', E''; inv E; inv E'; inv E''.
        constructor; cofix_step CoFix H.
  Qed.

  Lemma ite_spec:
    forall xs ts fs rs,
      ite xs ts fs rs <->
      (forall n,
          (xs # n = absent
           /\ ts # n = absent
           /\ fs # n = absent
           /\ rs # n = absent)
          \/
          (exists t f,
              xs # n = present true_val
              /\ ts # n = present t
              /\ fs # n = present f
              /\ rs # n = present t)
          \/
          (exists t f,
              xs # n = present false_val
              /\ ts # n = present t
              /\ fs # n = present f
              /\ rs # n = present f)).
  Proof.
    split.
    - intros * H n.
      revert dependent xs; revert ts fs rs.
      induction n; intros.
      + inv H; intuition.
        * right; left. do 2 eexists; now intuition.
        * right; right. do 2 eexists; now intuition.
      + inv H; repeat rewrite Str_nth_S; auto.
    - revert xs ts fs rs; cofix CoFix; intros * H.
      unfold_Stv xs; unfold_Stv ts; unfold_Stv fs; unfold_Stv rs;
        try (specialize (H 0); repeat rewrite Str_nth_0 in H;
             destruct H as [(?&?&?&?)|[(?&?&?&?&?&?)|(?&?&?&?&?&?)]];
             discriminate).
      + constructor; cofix_step CoFix H.
      + destruct (H 0) as [(?&?&?&?)|[(?&?& E1 & E2 & E3 & E4)|(?&?& E1 & E2 & E3 & E4)]];
          try discriminate;
          rewrite Str_nth_0 in E1, E2, E3, E4; inv E1; inv E2; inv E3; inv E4;
            constructor; cofix_step CoFix H.
  Qed.

  Add Parametric Morphism k : (mask k)
      with signature @EqSt bool ==> @EqSt value ==> @EqSt value
        as mask_EqSt.
  Proof.
    revert k; cofix Cofix; intros k rs rs' Ers xs xs' Exs.
    unfold_Stv rs; unfold_Stv rs'; unfold_St xs; unfold_St xs';
      constructor; inv Ers; inv Exs;
        simpl in *; try discriminate;
          destruct k as [|[]]; auto; try reflexivity.
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

  Add Parametric Morphism : ite
      with signature @EqSt value ==> @EqSt value ==> @EqSt value ==> @EqSt value ==> Basics.impl
        as ite_EqSt.
  Proof.
    cofix Cofix.
    intros [? ?] [? ?] Heq [? ?] [? ?] Heq0 [? ?] [? ?] Heq1 [? ?] [? ?] Heq2 Hite.
    inv Heq. inv Heq0. inv Heq1. inv Heq2. simpl in *.
    inv Hite; constructor; eapply Cofix; eauto.
  Qed.

  (** ** history and it's properties *)

  Definition history := Env.t (Stream value).
  Definition history_tl (H: history) : history := Env.map (@tl value) H.

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

  Definition env := Env.t value.

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
      Env.refines eq H H' ->
      Env.refines eq (history_tl H) (history_tl H').
  Proof.
    intros H H' Href x vs Hfind.
    eapply history_tl_find_Some' in Hfind as [v' Hfind].
    eapply Href in Hfind as [vs' [Heq' Hfind']].
    exists (tl vs').
    apply history_tl_find_Some in Hfind'.
    split; auto.
    destruct vs'; simpl. inv Heq'; auto.
  Qed.

  Lemma history_nth_refines : forall H H',
      Env.refines eq H H' ->
      forall n, Env.refines eq (history_nth n H) (history_nth n H').
  Proof.
    intros H H' Href n; revert H H' Href.
    induction n; intros.
    - apply history_hd_refines, Href.
    - repeat rewrite history_nth_tl.
      apply IHn, history_tl_refines, Href.
  Qed.

  Lemma env_find_tl : forall x x' H H',
      orel (@EqSt value) (Env.find x H) (Env.find x' H') ->
      orel (@EqSt value)
           (Env.find x (history_tl H))
           (Env.find x' (history_tl H')).
  Proof.
    intros * Hfind. unfold history_tl.
    do 2 rewrite Env.Props.P.F.map_o.
    inversion Hfind as [|?? Hs]; eauto; econstructor; now rewrite Hs.
  Qed.

  (** * sem_var
        This is common to Lustre and NLustre Semantics *)

  Inductive sem_var: history -> ident -> Stream value -> Prop :=
    sem_var_intro:
      forall H x xs xs',
        Env.MapsTo x xs' H ->
        xs ≡ xs' ->
        sem_var H x xs.

  Instance sem_var_Proper:
    Proper (@eq history ==> @eq ident ==> @EqSt value ==> iff)
           sem_var.
  Proof.
    intros H H' ? x x' ? xs xs' Heq; subst.
    split; intros Hsem; inv Hsem; econstructor; eauto.
    - symmetry in Heq. etransitivity; eauto.
    - etransitivity; eauto.
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
      orel (@EqSt value) (Env.find x H) (Env.find x H') ->
      sem_var H x v <-> sem_var H' x v.
  Proof.
    intros * Hfind; split; intro Hsem; inversion_clear Hsem as [???? Hr];
      rewrite Hr in Hfind; inv Hfind;
        eapply Env.find_1 in Hr; rewrite H1; [rewrite H3|rewrite <- H3];
          econstructor; eauto using Env.find_2; reflexivity.
  Qed.

  (** * sem_clock a
        This is also common to Lustre and NLustre **)

  (** ** clocks_of and its properties *)

  CoFixpoint clocks_of (ss: list (Stream value)) : Stream bool :=
    existsb (fun s => hd s <>b absent) ss ⋅ clocks_of (List.map (@tl value) ss).

  Add Parametric Morphism : clocks_of
      with signature @EqSts value ==> @EqSt bool
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


  CoInductive sem_clock: history -> Stream bool -> clock -> Stream bool -> Prop :=
  | Sbase:
      forall H b b',
        b ≡ b' ->
        sem_clock H b Cbase b'
  | Son:
      forall H b bk bs ck x k xs c,
        sem_clock H b ck (true ⋅ bk) ->
        sem_var H x (present c ⋅ xs) ->
        val_to_bool c = Some k ->
        sem_clock (history_tl H) (tl b) (Con ck x k) bs ->
        sem_clock H b (Con ck x k) (true ⋅ bs)
  | Son_abs1:
      forall H b bk bs ck x k xs,
        sem_clock H b ck (false ⋅ bk) ->
        sem_var H x (absent ⋅ xs) ->
        sem_clock (history_tl H) (tl b) (Con ck x k) bs ->
        sem_clock H b (Con ck x k) (false ⋅ bs)
  | Son_abs2:
      forall H b bk bs ck x k c xs,
        sem_clock H b ck (true ⋅ bk) ->
        sem_var H x (present c ⋅ xs) ->
        val_to_bool c = Some k ->
        sem_clock (history_tl H) (tl b) (Con ck x (negb k)) bs ->
        sem_clock H b (Con ck x (negb k)) (false ⋅ bs).

  Add Parametric Morphism H : (sem_clock H)
      with signature @EqSt bool ==> eq ==> @EqSt bool ==> Basics.impl
        as sem_clock_morph.
  Proof.
    revert H; cofix Cofix.
    intros H b b' Eb ck bk bk' Ebk Sem.
    inv Sem.
    - constructor.
      now rewrite <-Ebk, <-Eb.
    - destruct bk' as [[]]; inv Ebk; simpl in *; try discriminate;
        econstructor; eauto; eapply Cofix; eauto; try reflexivity; inv Eb; auto.
    - destruct bk' as [[]]; inv Ebk; simpl in *; try discriminate;
        econstructor; eauto; eapply Cofix; eauto; try reflexivity; inv Eb; auto.
    - destruct bk' as [[]]; inv Ebk; simpl in *; try discriminate;
        eapply Son_abs2; eauto; eapply Cofix; eauto; try reflexivity; inv Eb; auto.
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
      take (sem_var _ x (present c ⋅ _)) and
           eapply sem_var_det in it; eauto.
      inversion it as [Hit]. simpl in Hit. inv Hit.
      destruct k0; simpl in *; congruence.
    - inv Hsc; inv Hsc'; try discriminate_stream;
        try discriminate_var.
      take (sem_var _ x (present c ⋅ _)) and
           eapply sem_var_det in it; eauto.
      inversion it as [Hit]. simpl in Hit. inv Hit.
      destruct k; simpl in *; congruence.
    - inv Hsc; inv Hsc'; constructor; simpl; auto;
        try (now eapply Cofix; eauto).
      rewrite H1 in H2. inv H2. now simpl in H3.
      rewrite H6 in H14. eapply Cofix; eauto.
  Qed.

  Ltac discriminate_clock :=
    let HH := fresh in
    match goal with
    | H1: sem_clock ?H ?b ?ck (true ⋅ _),
          H2 : sem_clock ?H ?b ?ck (false ⋅ _) |- _ =>
      eapply sem_clock_det with (2 := H2) in H1; eauto;
      inversion H1 as [HH ?]; simpl in HH; discriminate
    end.

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
        constructor. inv Hsc'. inv H1. eapply Cofix; eauto.
        inversion_clear Hsc' as [|????????? Hb'| |]. inv Hb'.
        discriminate_stream.
        constructor. inv Hsc'; inv H1; eapply Cofix; eauto.
        constructor. inv Hsc'; inv H1; eapply Cofix; eauto.
      + revert Hsc Hsc'. revert H b ck i b1 s s' x b0.
        cofix Cofix; intros.
        unfold_Stv s'; unfold_Stv s.
        constructor. apply sc_step in Hsc.
        apply sc_step in Hsc'.
        eapply Cofix; eauto.
        inv Hsc'. discriminate_clock.
        inv Hsc'. discriminate_clock.
        constructor. apply sc_step in Hsc. eapply Cofix; eauto.
        constructor. apply sc_step in Hsc.
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
    - inversion Hsc' as [|????????? Hck'|???????? Hck' |????????? Hck'];
        subst; pose proof (sub_clock_Con _ _ _ _ _ _ _ Hck' Hsc');
          apply IHHparent in Hck'; etransitivity; eauto.
  Qed.

  (** ** Synchronized and its properties *)

  CoInductive synchronized: Stream value -> Stream bool -> Prop :=
  | synchro_present:
      forall v vs bs,
        synchronized vs bs ->
        synchronized (present v ⋅ vs) (true ⋅ bs)
  | synchro_absent:
      forall vs bs,
        synchronized vs bs ->
        synchronized (absent ⋅ vs) (false ⋅ bs).

  Instance synchronized_Proper:
    Proper (@EqSt value ==> @EqSt bool ==> iff)
           synchronized.
  Proof.
    intros vs vs' Heq1 bs bs' Heq2.
    split; revert vs vs' Heq1 bs bs' Heq2;
      cofix synchronized_Proper;
      intros [v vs] [v' vs'] Heq1 [b bs] [b' bs'] Heq2 H;
      inv Heq1; inv Heq2; simpl in *; subst; inv H;
        constructor; eauto.
  Qed.

  Lemma synchronized_spec : forall vs bs,
      synchronized vs bs <->
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

  Lemma synchronized_EqSt : forall vs bs1 bs2,
      synchronized vs bs1 ->
      synchronized vs bs2 ->
      bs1 ≡ bs2.
  Proof.
    cofix CoFix.
    intros [v vs] [b1 bs1] [b2 bs2] Hsync1 Hsync2.
    inv Hsync1; inv Hsync2; constructor; simpl; eauto.
  Qed.

  Lemma const_synchronized : forall bs c,
      synchronized (const bs c) bs.
  Proof with eauto.
    intros bs c.
    remember (const bs c) as vs.
    rewrite synchronized_spec. intros n.
    eapply eq_EqSt, const_spec with (n:=n) in Heqvs.
    rewrite Heqvs; clear Heqvs.
    destruct (bs # n).
    - left. eexists...
    - right...
  Qed.

  CoFixpoint abstract_clock (xs: Stream value) : Stream bool:=
    match xs with
    | absent ⋅ xs => false ⋅ abstract_clock xs
    | present _ ⋅ xs => true ⋅ abstract_clock xs
    end.

  Add Parametric Morphism : (abstract_clock)
      with signature @EqSt value ==> @EqSt bool
        as ac_EqSt.
  Proof.
    cofix Cofix; intros b b' Eb.
    unfold_Stv b; unfold_Stv b';
      constructor; inv Eb; simpl in *; try discriminate; auto.
  Qed.

  Lemma ac_tl :
    forall s, abstract_clock (Streams.tl s) ≡ Streams.tl (abstract_clock s).
  Proof.
    intros. unfold_Stv s; reflexivity.
  Qed.

  Lemma ac_when :
    forall k cs xs rs,
      when k cs xs rs -> abstract_clock cs ≡ abstract_clock xs.
  Proof.
    cofix Cofix.
    intros * Hwhen. inv Hwhen; econstructor; simpl; eauto.
  Qed.

  Lemma ac_const:
    forall c b cs,
      const b c ≡ cs -> b ≡ abstract_clock cs.
  Proof.
    cofix Cofix.
    intros * Hconst.
    unfold_Stv b;
      inv Hconst; simpl in *;
      unfold_Stv cs; constructor; simpl; eauto; inv H.
  Qed.

  Lemma ac_ite :
    forall s  ts fs rs,
      ite s ts fs rs -> abstract_clock ts ≡ abstract_clock rs.
  Proof.
    cofix Cofix.
    intros * Hite.
    unfold_Stv ts; inv Hite; econstructor; simpl; eauto.
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

  Lemma ac_synchronized :
    forall s, synchronized s (abstract_clock s).
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

End COINDSTREAMS.

Module CoindStreamsFun
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op) <: COINDSTREAMS Op OpAux.
  Include COINDSTREAMS Op OpAux.
End CoindStreamsFun.
