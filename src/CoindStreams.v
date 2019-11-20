(* *********************************************************************)
(*                                                                     *)
(*                 The Vélus verified Lustre compiler                  *)
(*                                                                     *)
(*             (c) 2019 Inria Paris (see the AUTHORS file)             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

From Coq Require Import List.
From Coq Require Export Lists.Streams.
From Coq Require Import Setoid.
From Coq Require Import Morphisms.
From Coq Require Import Arith.EqNat.
From Coq Require Import Omega.

From Velus Require Import Common.
From Velus Require Import Operators.

Module Type COINDSTREAMS
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op).

  Infix "⋅" := Cons (at level 60, right associativity) : stream_scope.
  Infix "≡" := EqSt (at level 70, no associativity) : stream_scope.
  Notation "s # n " := (Str_nth n s) (at level 9) : stream_scope.

  Delimit Scope stream_scope with Stream.
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

  Add Parametric Relation A : (Stream A) (@EqSt A)
      reflexivity proved by (@EqSt_reflex A)
      symmetry proved by (@sym_EqSt A)
      transitivity proved by (@trans_EqSt A)
        as EqStrel.

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

  CoFixpoint clocks_of (ss: list (Stream value)) : Stream bool :=
    existsb (fun s => hd s <>b absent) ss ⋅ clocks_of (List.map (@tl value) ss).

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

  Fact Str_nth_0:
    forall {A} (xs: Stream A) x,
      (x ⋅ xs) # 0 = x.
  Proof. reflexivity. Qed.

  Fact Str_nth_S:
    forall {A} (xs: Stream A) x n,
      (x ⋅ xs) # (S n) = xs # n.
  Proof. reflexivity. Qed.

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

End COINDSTREAMS.

Module CoindStreamsFun
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op) <: COINDSTREAMS Op OpAux.
  Include COINDSTREAMS Op OpAux.
End CoindStreamsFun.
