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

  Definition bools_of' :=
    Streams.map (fun v => match value_to_bool v with Some b => b | None => false end).

  Instance bools_of_Proper:
    Proper (@EqSt value ==> @EqSt bool ==> Basics.impl)
           bools_of.
  Proof.
    cofix CoFix.
    intros [x xs] [x' xs'] Heq1 [y ys] [y' ys'] Heq2 Hsem.
    inv Hsem; inv Heq1; inv Heq2;
      simpl in *; subst; econstructor; eauto.
    eapply CoFix; eauto.
  Qed.

  Lemma bools_of_sound : forall xs ys,
      bools_of xs ys ->
      bools_of' xs ≡ ys.
  Proof.
    cofix CoFix.
    intros [x xs] [y ys] Hbools; inv Hbools.
    constructor; simpl; eauto.
    rewrite H4; auto.
  Qed.

  Corollary bools_of_det : forall xs ys ys',
      bools_of xs ys ->
      bools_of xs ys' ->
      ys ≡ ys'.
  Proof.
    intros * Hb1 Hb2.
    eapply bools_of_sound in Hb1. eapply bools_of_sound in Hb2.
    etransitivity; eauto. symmetry; eauto.
  Qed.

  Lemma bools_of_absent :
    bools_of (Streams.const absent) (Streams.const false).
  Proof.
    cofix CoFix.
    rewrite (const_Cons absent), (const_Cons false).
    constructor; auto.
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

  Definition bools_ofs (vs : list (Stream value)) (rs : Stream bool) :=
    exists rss, Forall2 bools_of vs rss /\
           rs ≡ disj_str rss.

  CoFixpoint mask (k: nat) (rs: Stream bool) (xs: Stream value) : Stream value :=
    let mask' k' := mask k' (tl rs) (tl xs) in
    match k, hd rs with
    | 0, true    => Streams.const absent
    | 0, false   => hd xs  ⋅ mask' 0
    | 1, true    => hd xs  ⋅ mask' 0
    | S k', true => absent ⋅ mask' k'
    | S _, false => absent ⋅ mask' k
    end.

  Lemma bools_ofs_empty:
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
    Proper (@EqSts value ==> @EqSt bool ==> Basics.impl)
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
    Proper (SameElements (@EqSt value) ==> eq ==> Basics.impl)
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

  Lemma mask_EqSt' : forall b x y,
    (forall (k : nat), mask k b x ≡ mask k b y) ->
    x ≡ y.
  Proof.
    intros * Heq.
    apply ntheq_eqst. intros n.
    specialize (Heq ((count b) # n)).
    apply Str_nth_EqSt with (n:=n) in Heq.
    repeat rewrite mask_nth in Heq.
    rewrite Nat.eqb_refl in Heq; auto.
  Qed.

  Lemma mask_false_0 : forall xs,
      mask 0 (Streams.const false) xs ≡ xs.
  Proof.
    intros *.
    assert (forall k, (count (Streams.const false)) # k = 0) as Count.
    { induction k; simpl; auto. }
    eapply ntheq_eqst. intros k.
    rewrite mask_nth, Count; auto.
  Qed.

  Corollary masks_false_0 : forall xs,
      EqSts (List.map (mask 0 (Streams.const false)) xs) xs.
  Proof.
    intros *. unfold EqSts.
    rewrite Forall2_map_1. apply Forall2_same.
    eapply Forall_forall. intros ? _. apply mask_false_0.
  Qed.

  Lemma mask_false_S : forall n xs,
      mask (S n) (Streams.const false) xs ≡ Streams.const absent.
  Proof.
    intros *.
    assert (forall k, (count (Streams.const false)) # k = 0) as Count.
    { induction k; simpl; auto. }
    eapply ntheq_eqst. intros k.
    rewrite mask_nth, Count, const_nth; auto.
  Qed.

  Corollary masks_false_S : forall n xs,
      EqSts (List.map (mask (S n) (Streams.const false)) xs) (List.map (fun _ => Streams.const absent) xs).
  Proof.
    intros *. unfold EqSts.
    rewrite Forall2_map_1, Forall2_map_2. apply Forall2_same.
    eapply Forall_forall. intros ? _. apply mask_false_S.
  Qed.

  (** *** Boolean mask *)

  CoFixpoint maskb (k: nat) (rs: Stream bool) (xs: Stream bool) : Stream bool :=
    let mask' k' := maskb k' (tl rs) (tl xs) in
    match k, hd rs with
    | 0, true    => Streams.const false
    | 0, false   => hd xs  ⋅ mask' 0
    | 1, true    => hd xs  ⋅ mask' 0
    | S k', true => false ⋅ mask' k'
    | S _, false => false ⋅ mask' k
    end.

  Lemma maskb_nth:
    forall n k rs xs,
      (maskb k rs xs) # n = if (count rs) # n  =? k then xs # n else false.
  Proof.
    unfold Str_nth.
    induction n, k as [|[|k]]; intros;
      unfold_Stv rs; simpl; auto.
    - pose proof (count_acc_grow 1 rs) as H.
      apply (ForAll_Str_nth_tl n) in H; inv H.
      assert (hd (Str_nth_tl n (count_acc 1 rs)) <> 0) as E by omega;
        apply beq_nat_false_iff in E; rewrite E.
      pose proof (const_nth n false); auto.
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

  Corollary maskb_Cons:
    forall k r rs x xs,
      (maskb k (r ⋅ rs) (x ⋅ xs))
        ≡ (match k with
           | 0 => if r then (Streams.const false) else (x ⋅ (maskb 0 rs xs))
           | 1 => if r then (x ⋅ (maskb 0 rs xs)) else (false ⋅ maskb 1 rs xs)
           | S (S _ as k') => if r then (false ⋅ maskb k' rs xs) else (false ⋅ maskb k rs xs)
           end).
  Proof.
    intros *.
    constructor; simpl.
    1,2:destruct k; [|destruct k]; destruct r; try reflexivity.
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

  (** ** fby stream *)

  CoFixpoint sfby (v : Op.val) (str : Stream OpAux.value) :=
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
      with signature eq ==> @EqSt value ==> @EqSt value
    as sfby_EqSt.
  Proof.
    cofix CoFix.
    intros v [x xs] [y ys] Heq.
    inv Heq; simpl in *; subst.
    constructor; simpl.
    + destruct y; auto.
    + destruct y; auto.
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

  Corollary const_true: forall bs c n,
      bs # n = true ->
      (const bs c) # n = present (sem_const c).
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
      (const bs c) # n = if (bs # n) then present (sem_const c) else absent.
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

  Lemma const_Cons : forall c b bs,
      const (b ⋅ bs) c ≡
      (if b then present (sem_const c) else absent) ⋅ (const bs c).
  Proof.
    intros.
    rewrite unfold_Stream at 1; reflexivity.
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

  Add Parametric Morphism k : (maskb k)
      with signature @EqSt bool ==> @EqSt bool ==> @EqSt bool
        as maskb_EqSt.
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

  Lemma sem_var_env_eq :
    forall H H' xs ss,
      Forall2 (sem_var H) xs ss ->
      Forall2 (sem_var H') xs ss ->
      Forall (fun x => orel (EqSt (A:=value)) (Env.find x H) (Env.find x H')) xs.
  Proof.
    induction 1; auto. intros Hf. inv Hf. constructor; auto.
    do 2 take (sem_var _ _ _) and inv it.
    do 2 take (Env.MapsTo _ _ _) and apply Env.find_1 in it as ->.
    now rewrite <- H4, <- H5.
  Qed.

  (** * sem_clock
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

  Lemma clocks_of_mask : forall xs k rs,
      clocks_of (List.map (mask k rs) xs) ≡ (maskb k rs (clocks_of xs)).
  Proof.
    intros.
    apply ntheq_eqst; intros.
    rewrite maskb_nth. repeat rewrite clocks_of_nth.
    repeat rewrite existsb_map.
    destruct (_ =? k) eqn:Hcount.
    - apply existsb_ext; intros x.
      rewrite mask_nth, Hcount; auto.
    - rewrite existsb_Forall, forallb_forall.
      intros ? _.
      rewrite mask_nth, Hcount, neg_eq_value.
      apply equiv_decb_refl.
  Qed.

  (** ** sem_clock and its properties *)

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

  Fact history_tl_Equiv : forall H H',
      Env.Equiv (@EqSt value) H H' ->
      Env.Equiv (@EqSt value) (history_tl H) (history_tl H').
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
      with signature Env.Equiv (@EqSt value) ==> @EqSt bool ==> eq ==> @EqSt bool ==> Basics.impl
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

  (** ** Aligned and its properties *)

  CoInductive aligned: Stream value -> Stream bool -> Prop :=
  | synchro_present:
      forall v vs bs,
        aligned vs bs ->
        aligned (present v ⋅ vs) (true ⋅ bs)
  | synchro_absent:
      forall vs bs,
        aligned vs bs ->
        aligned (absent ⋅ vs) (false ⋅ bs).

  Instance aligned_Proper:
    Proper (@EqSt value ==> @EqSt bool ==> iff)
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

  Lemma ac_mask : forall k rs xs,
      abstract_clock (mask k rs xs) ≡ maskb k rs (abstract_clock xs).
  Proof.
    cofix CoFix.
    intros.
    unfold_Stv xs; unfold_Stv rs;
      constructor; simpl; destruct k as [|[|?]]; eauto.
    1,2:unfold Streams.const; apply ac_Streams_const.
  Qed.

End COINDSTREAMS.

Module CoindStreamsFun
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op) <: COINDSTREAMS Op OpAux.
  Include COINDSTREAMS Op OpAux.
End CoindStreamsFun.
