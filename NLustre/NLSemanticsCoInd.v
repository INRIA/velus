Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Coq.Sorting.Permutation.
Require Import Setoid.

Require Import Coq.FSets.FMapPositive.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.NLSemanticsCommon.
Require Import Velus.NLustre.Ordered.
Require Import Velus.NLustre.Streams.

(** * The NLustre semantics *)

(**

  We provide a "standard" dataflow semantics relating an environment
  of streams to a stream of outputs.

 *)

Module Type NLSEMANTICSCOIND
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Clks  : CLOCKS    Ids)
       (Import Syn   : NLSYNTAX  Ids Op Clks)
       (Import Ord   : ORDERED   Ids Op Clks Syn).

  Definition idents := List.map (@fst ident (type * clock)).

  Definition history := PM.t (Stream value).

  CoFixpoint const (c: const) (b: Stream bool): Stream value :=
    match b with
    | true  ::: b' => present (sem_const c) ::: const c b'
    | false ::: b' => absent ::: const c b'
    end.

  Inductive sem_var: history -> ident -> Stream value -> Prop :=
    sem_var_intro:
      forall H x xs xs',
        PM.MapsTo x xs' H ->
        xs ≡ xs' ->
        sem_var H x xs.

  Remark MapsTo_sem_var:
    forall H x xs,
      PM.MapsTo x xs H ->
      sem_var H x xs.
  Proof. econstructor; eauto; reflexivity. Qed.

  CoInductive when (k: bool): Stream value -> Stream value -> Stream value -> Prop :=
  | WhenA:
      forall xs cs rs,
        when k xs cs rs ->
        when k (absent ::: xs) (absent ::: cs) (absent ::: rs)
  | WhenPA:
      forall x c xs cs rs,
        when k xs cs rs ->
        val_to_bool c = Some (negb k) ->
        when k (present x ::: xs) (present c ::: cs) (absent ::: rs)
  | WhenPP:
      forall x c xs cs rs,
        when k xs cs rs ->
        val_to_bool c = Some k ->
        when k (present x ::: xs) (present c ::: cs) (present x ::: rs).

  CoInductive lift1 (op: unop) (ty: type): Stream value -> Stream value -> Prop :=
  | Lift1A:
      forall xs rs,
        lift1 op ty xs rs ->
        lift1 op ty (absent ::: xs) (absent ::: rs)
  | Lift1P:
      forall x r xs rs,
        sem_unop op x ty = Some r ->
        lift1 op ty xs rs ->
        lift1 op ty (present x ::: xs) (present r ::: rs).

  CoInductive lift2 (op: binop) (ty1 ty2: type): Stream value -> Stream value -> Stream value -> Prop :=
  | Lift2A:
      forall xs ys rs,
        lift2 op ty1 ty2 xs ys rs ->
        lift2 op ty1 ty2 (absent ::: xs) (absent ::: ys) (absent ::: rs)
  | Lift2P:
      forall x y r xs ys rs,
        sem_binop op x ty1 y ty2 = Some r ->
        lift2 op ty1 ty2 xs ys rs ->
        lift2 op ty1 ty2 (present x ::: xs) (present y ::: ys) (present r ::: rs).

  CoInductive merge
    : Stream value -> Stream value -> Stream value -> Stream value -> Prop :=
  | MergeA:
      forall xs ts fs rs,
        merge xs ts fs rs ->
        merge (absent ::: xs) (absent ::: ts) (absent ::: fs) (absent ::: rs)
  | MergeT:
      forall t xs ts fs rs,
        merge xs ts fs rs ->
        merge (present true_val ::: xs)
              (present t ::: ts) (absent ::: fs) (present t ::: rs)
  | MergeF:
      forall f xs ts fs rs,
        merge xs ts fs rs ->
        merge (present false_val ::: xs)
              (absent ::: ts) (present f ::: fs) (present f ::: rs).

  CoInductive ite
    : Stream value -> Stream value -> Stream value -> Stream value -> Prop :=
  | IteA:
      forall s ts fs rs,
        ite s ts fs rs ->
        ite (absent ::: s) (absent ::: ts) (absent ::: fs) (absent ::: rs)
  | IteT:
      forall t f s ts fs rs,
        ite s ts fs rs ->
        ite (present true_val ::: s)
              (present t ::: ts) (present f ::: fs) (present t ::: rs)
  | IteF:
      forall t f s ts fs rs,
        ite s ts fs rs ->
        ite (present false_val ::: s)
              (present t ::: ts) (present f ::: fs) (present f ::: rs).

  Inductive sem_lexp: history -> Stream bool -> lexp -> Stream value -> Prop :=
  | Sconst:
      forall H b c cs,
        cs ≡ const c b ->
        sem_lexp H b (Econst c) cs
  | Svar:
      forall H b x ty xs,
        sem_var H x xs ->
        sem_lexp H b (Evar x ty) xs
  | Swhen:
      forall H b e x k es xs os,
        sem_lexp H b e es ->
        sem_var H x xs ->
        when k es xs os ->
        sem_lexp H b (Ewhen e x k) os
  | Sunop:
      forall H b op e ty es os,
        sem_lexp H b e es ->
        lift1 op (typeof e) es os ->
        sem_lexp H b (Eunop op e ty) os
  | Sbinop:
      forall H b op e1 e2 ty es1 es2 os,
        sem_lexp H b e1 es1 ->
        sem_lexp H b e2 es2 ->
        lift2 op (typeof e1) (typeof e2) es1 es2 os ->
        sem_lexp H b (Ebinop op e1 e2 ty) os.

  Inductive sem_cexp: history -> Stream bool -> cexp -> Stream value -> Prop :=
  | Smerge:
      forall H b x t f xs ts fs os,
        sem_var H x xs ->
        sem_cexp H b t ts ->
        sem_cexp H b f fs ->
        merge xs ts fs os ->
        sem_cexp H b (Emerge x t f) os
  | Site:
      forall H b e t f es ts fs os,
        sem_lexp H b e es ->
        sem_cexp H b t ts ->
        sem_cexp H b f fs ->
        ite es ts fs os ->
        sem_cexp H b (Eite e t f) os
  | Sexp:
      forall H b e es,
        sem_lexp H b e es ->
        sem_cexp H b (Eexp e) es.

  CoFixpoint clocks_of (ss: list (Stream value)) : Stream bool :=
    forallb (fun s => hd s <>b absent) ss ::: clocks_of (List.map (@tl value) ss).

  Definition reset_of : Stream value -> Stream bool :=
    map (fun x => match x with
               | present x => x ==b true_val
               | _ => false
               end).

 (* CoFixpoint fby1 (v: val) (xs: Stream value) : Stream value := *)
  (*   match xs with *)
  (*   | absent ::: xs => absent ::: fby1 v xs *)
  (*   | present x ::: xs => present v ::: fby1 x xs *)
  (*   end. *)

  CoFixpoint fby (c: val) (xs: Stream value) : Stream value :=
    match xs with
    | absent ::: xs => absent ::: fby c xs
    | present x ::: xs => present c ::: fby x xs
    end.

  (* CoInductive fby1' *)
  (*   : val -> val -> Stream value -> Stream value -> Prop := *)
  (* | Fby1A: *)
  (*     forall v c xs ys, *)
  (*       fby1' v c xs ys -> *)
  (*       fby1' v c (absent ::: xs) (absent ::: ys) *)
  (* | Fby1P: *)
  (*     forall v x c xs ys, *)
  (*       fby1' x c xs ys -> *)
  (*       fby1' v c (present x ::: xs) (present v ::: ys). *)

  (* CoInductive fby': val -> Stream value -> Stream value -> Prop := *)
  (* | FbyA: *)
  (*     forall c xs ys, *)
  (*       fby' c xs ys -> *)
  (*       fby' c (absent ::: xs) (absent ::: ys) *)
  (* | FbyP: *)
  (*     forall x c xs ys, *)
  (*       fby1' x c xs ys -> *)
  (*       fby' c (present x ::: xs) (present c ::: ys). *)

  (* Fact fby1_spec: *)
  (*   forall xs ys v c, ys = fby1 v c xs <-> fby1' v c xs ys. *)
  (* Proof.  *)
  (*   split. *)
  (*   - revert xs ys v c; cofix H; intros. *)
  (*     subst. *)
  (*     rewrite unfold_Stream. *)
  (*     destruct xs as [[|w]]; simpl; constructor; auto. *)
  (*   - intros. *)
  (*     rewrite unfold_Stream. *)
  (*     inv H; simpl. *)

  (*     revert xs ys v c; cofix H; intros. *)

  (* Fact foo: *)
  (*   forall xs ys c, ys = fby c xs <-> fby' c xs ys. *)
  (* Proof. *)
  (*   split. *)
  (*   - revert xs ys k; cofix H; intros. *)
  (*     subst. *)
  (*     rewrite unfold_Stream. *)
  (*     destruct xs as [[|v]]; simpl; constructor; auto. *)

  (*   cofix. *)
  (*   destruct xs. *)
  (*   rewrite unfold_Stream. *)
  (*   simpl. *)

  (* CoFixpoint cut (bs: Stream bool) (xs: Stream value) : Stream value := *)
  (*   match bs, xs with *)
  (*     b ::: bs', x ::: xs' => if b then xs else absent ::: cut bs' xs' *)
  (*   end. *)

  (* CoFixpoint cut_bool (bs: Stream bool) : Stream bool := *)
  (*   match bs with *)
  (*     b ::: bs => false ::: if b then bs else cut_bool bs *)
  (*   end. *)

  (* CoFixpoint switch (bs: Stream bool) (xs ys: Stream value) : Stream value := *)
  (*   match bs, xs, ys with *)
  (*     b ::: bs', x ::: xs', y ::: ys' => if b then ys else x ::: switch bs' xs' ys' *)
  (*   end.  *)

  CoFixpoint mask {A} (opaque: A) (n: nat) (rs: Stream bool) (xs: Stream A) : Stream A :=
    match n, rs, xs with
    | 0,  false ::: rs, x ::: xs =>
      x ::: mask opaque 0 rs xs
    | 0, true ::: _, _ ::: _ =>
      Streams.const opaque
    | S 0, true ::: rs, x ::: xs =>
      x ::: mask opaque 0 rs xs
    | S n, false ::: rs, x ::: xs =>
      opaque ::: mask opaque (S n) rs xs
    | S n, true ::: rs, x ::: xs =>
      opaque ::: mask opaque n rs xs
    end.

  Definition mask_v := mask absent.
  Definition mask_b := mask false.

  Remark mask_const_opaque:
    forall {A} n rs (opaque: A),
      mask opaque n rs (Streams.const opaque) ≡ Streams.const opaque.
  Proof.
    cofix Cofix; intros.
    unfold_Stv rs; rewrite (unfold_Stream (Streams.const opaque));
      constructor; destruct n as [|[]]; simpl; auto; try apply Cofix.
    reflexivity.
  Qed.

  Fixpoint take {A} (n: nat) (s: Stream A) : list A :=
    match n with
    | O => nil
    | S n => hd s :: take n (tl s)
    end.

  (* Definition r := *)
  (*   false ::: false ::: false ::: true ::: false ::: false ::: false ::: false ::: false ::: true ::: false ::: false ::: false ::: true ::: Streams.const false. *)

  (* Notation "⊥" := (absent) (at level 50). *)
  (* Notation "⇑" := (present true_val). *)
  (* Notation "⇓" := (present false_val). *)


  (* CoFixpoint x := ⇓ ::: ⇑ ::: x. *)

  (* Eval simpl in (take 16 r, take 16 x, *)
  (*                take 16 (mask_v 0 r x), *)
  (*                take 16 (mask_v 1 r x), *)
  (*                take 16 (mask_v 2 r x), *)
  (*                take 16 (mask_v 3 r x), *)
  (*                take 16 (mask_v 4 r x)). *)

  CoFixpoint flatten_masks (bs: Stream bool) (xss: Stream (Stream value)) : Stream value :=
    let xss := if hd bs then tl xss else xss in
    hd (hd xss) ::: flatten_masks (tl bs) (map (@tl value) xss).

  CoFixpoint masks_from (n: nat) (rs: Stream bool) (xs: Stream value) : Stream (Stream value) :=
    mask_v n rs xs ::: masks_from (n + 1) rs xs.

  Definition masks := masks_from 0.

  (* Eval simpl in take 16 (flatten_masks r (masks r x)). *)

  Definition same_clock (xss: list (Stream value)) : Prop :=
    forall n,
      Forall (fun xs => Str_nth n xs = absent) xss
      \/ Forall (fun xs => Str_nth n xs <> absent) xss.
    (* same_clock_intro: *)
    (*   forall xss, *)
    (*     Forall (fun x => x = absent) (List.map (@hd value) xss) *)
    (*     \/ Forall (fun x => x <> absent) (List.map (@hd value) xss) -> *)
    (*     same_clock (List.map (@tl value) xss) -> *)
    (*     same_clock xss. *)

  Remark same_clock_nil: same_clock [].
  Proof.
    constructor; auto.
  Qed.

  Fact same_clock_app:
    forall xss yss,
      same_clock (xss ++ yss) ->
      same_clock xss /\ same_clock yss.
  Proof.
    intros ** H.
    split; intro; destruct (H n) as [E|Ne];
      try (left; apply Forall_app in E; tauto);
      try (right; apply Forall_app in Ne; tauto).
    (* intros ** H; split; revert xss yss H; cofix Cofix; intros ** H; *)
    (*   inversion_clear H as [? [He | Hne] Same]; constructor; *)
    (*     try (left; rewrite map_app, Forall_app in He; tauto); *)
    (*     try (right; rewrite map_app, Forall_app in Hne; tauto); *)
    (*     try (rewrite map_app in Same; eapply Cofix; eauto). *)
  Qed.

  Corollary same_clock_app_l:
     forall xss yss,
      same_clock (xss ++ yss) ->
      same_clock xss.
  Proof.
    intros ? ? H; apply same_clock_app in H; tauto.
  Qed.

  Corollary same_clock_app_r:
     forall xss yss,
      same_clock (xss ++ yss) ->
      same_clock yss.
  Proof.
    intros ? ? H; apply same_clock_app in H; tauto.
  Qed.

  Corollary same_clock_cons:
    forall xss xs,
      same_clock (xs :: xss) ->
      same_clock xss.
  Proof.
    intros ? ? H; rewrite cons_is_app in H.
    eapply same_clock_app_r; eauto.
  Qed.

  Section NodeSemantics.

    Variable G: global.

    Inductive sem_equation: history -> Stream bool -> equation -> Prop :=
    | SeqDef:
        forall H b x ck e es,
          sem_cexp H b e es ->
          sem_var H x es ->
          sem_equation H b (EqDef x ck e)
    | SeqApp:
        forall H b ys ck f es ess oss,
          Forall2 (sem_lexp H b) es ess ->
          sem_node f ess oss ->
          Forall2 (sem_var H) ys oss ->
          sem_equation H b (EqApp ys ck f es None)
    | SeqReset:
        forall H b ys ck f es x xs ess oss,
          Forall2 (sem_lexp H b) es ess ->
          sem_var H x xs ->
          sem_reset f (reset_of xs) ess oss ->
          Forall2 (sem_var H) ys oss ->
          sem_equation H b (EqApp ys ck f es (Some x))
    | SeqFby:
        forall H b x ck c0 e es os,
          sem_lexp H b e es ->
          os = fby (sem_const c0) es ->
          sem_var H x os ->
          sem_equation H b (EqFby x ck c0 e)

    with sem_reset: ident -> Stream bool -> list (Stream value) -> list (Stream value) -> Prop :=
         | SReset:
             forall f r xss yss,
               (forall n, sem_node f (List.map (mask_v n r) xss) (List.map (mask_v n r) yss)) ->
               sem_reset f r xss yss

    with sem_node: ident -> list (Stream value) -> list (Stream value) -> Prop :=
         | SNode:
             forall H f n xss oss,
               find_node f G = Some n ->
               Forall2 (sem_var H) (idents n.(n_in)) xss ->
               Forall2 (sem_var H) (idents n.(n_out)) oss ->
               same_clock (xss ++ oss) ->
               Forall (sem_equation H (clocks_of xss)) n.(n_eqs) ->
               sem_node f xss oss.

  End NodeSemantics.

  Section SemInd.

    Variable G: global.

    Variable P_equation: history -> Stream bool -> equation -> Prop.
    Variable P_reset: ident -> Stream bool -> list (Stream value) -> list (Stream value) -> Prop.
    Variable P_node: ident -> list (Stream value) -> list (Stream value) -> Prop.

    Hypothesis EqDefCase:
      forall H b x ck e es,
        sem_cexp H b e es ->
        sem_var H x es ->
        P_equation H b (EqDef x ck e).

    Hypothesis EqAppCase:
      forall H b ys ck f es ess oss,
        Forall2 (sem_lexp H b) es ess ->
        sem_node G f ess oss ->
        Forall2 (sem_var H) ys oss ->
        P_node f ess oss ->
        P_equation H b (EqApp ys ck f es None).

    Hypothesis EqResetCase:
      forall H b ys ck f es x xs ess oss,
        Forall2 (sem_lexp H b) es ess ->
        sem_var H x xs ->
        sem_reset G f (reset_of xs) ess oss ->
        Forall2 (sem_var H) ys oss ->
        P_reset f (reset_of xs) ess oss ->
        P_equation H b (EqApp ys ck f es (Some x)).

    Hypothesis EqFbyCase:
      forall H b x ck c0 e es os,
        sem_lexp H b e es ->
        os = fby (sem_const c0) es ->
        sem_var H x os ->
        P_equation H b (EqFby x ck c0 e).

    Hypothesis ResetCase:
      forall f r xss yss,
        (forall n, sem_node G f (List.map (mask_v n r) xss) (List.map (mask_v n r) yss)) ->
        (forall n, P_node f (List.map (mask_v n r) xss) (List.map (mask_v n r) yss)) ->
        P_reset f r xss yss.

    Hypothesis NodeCase:
      forall H f n xss oss,
        find_node f G = Some n ->
        Forall2 (sem_var H) (idents n.(n_in)) xss ->
        Forall2 (sem_var H) (idents n.(n_out)) oss ->
        same_clock (xss ++ oss) ->
        Forall (sem_equation G H (clocks_of xss)) n.(n_eqs) ->
        Forall (P_equation H (clocks_of xss)) n.(n_eqs) ->
        P_node f xss oss.

    Fixpoint sem_equation_mult
             (H: history) (b: Stream bool) (e: equation)
             (Sem: sem_equation G H b e) {struct Sem}
      : P_equation H b e
    with sem_reset_mult
           (f: ident) (r: Stream bool) (xss oss: list (Stream value))
           (Sem: sem_reset G f r xss oss) {struct Sem}
         : P_reset f r xss oss
    with sem_node_mult
           (f: ident) (xss oss: list (Stream value))
           (Sem: sem_node G f xss oss) {struct Sem}
         : P_node f xss oss.
    Proof.
      - destruct Sem; eauto.
      - destruct Sem; eauto.
      - destruct Sem; eauto.
        eapply NodeCase; eauto.
        induction H4; auto.
    Qed.

    Combined Scheme sem_equation_node_ind from sem_equation_mult, sem_node_mult, sem_reset_mult.

  End SemInd.

 Add Parametric Morphism H : (sem_var H)
      with signature eq ==> @EqSt value ==> Basics.impl
        as sem_var_EqSt.
  Proof.
    intros x xs xs' E.
    intros Sem; induction Sem.
    econstructor; eauto.
    transitivity xs; auto; symmetry; auto.
  Qed.

  Add Parametric Morphism : merge
      with signature @EqSt value ==> @EqSt value ==> @EqSt value ==> @EqSt value ==> Basics.impl
        as merge_EqSt.
  Proof.
    cofix Cofix.
    intros cs cs' Ecs xs xs' Exs ys ys' Eys zs zs' Ezs H.
    destruct cs' as [[]], xs' as [[]], ys' as [[]], zs' as [[]];
      inv H; inv Ecs; inv Exs; inv Eys; inv Ezs; simpl in *;
        try discriminate.
      + constructor; eapply Cofix; eauto.
      + rewrite <-H, <-H4, <-H6.
        constructor; eapply Cofix; eauto.
      + rewrite <-H, <-H2, <-H6.
        constructor; eapply Cofix; eauto.
  Qed.

  Add Parametric Morphism : ite
      with signature @EqSt value ==> @EqSt value ==> @EqSt value ==> @EqSt value ==> Basics.impl
        as ite_EqSt.
  Proof.
    cofix Cofix.
    intros es es' Ees ts ts' Ets fs fs' Efs zs zs' Ezs H.
    destruct es' as [[]], ts' as [[]], fs' as [[]], zs' as [[]];
      inv H; inv Ees; inv Ets; inv Efs; inv Ezs; simpl in *;
        try discriminate.
      + constructor; eapply Cofix; eauto.
      + rewrite <-H, <-H2, <-H6.
        constructor; eapply Cofix; eauto.
      + rewrite <-H, <-H4, <-H6.
        constructor; eapply Cofix; eauto.
  Qed.

  Add Parametric Morphism k : (when k)
      with signature @EqSt value ==> @EqSt value ==> @EqSt value ==> Basics.impl
        as when_EqSt.
  Proof.
    cofix Cofix.
    intros cs cs' Ecs xs xs' Exs ys ys' Eys H.
    destruct cs' as [[]], xs' as [[]], ys' as [[]];
      inv H; inv Ecs; inv Exs; inv Eys; simpl in *;
        try discriminate.
      + constructor; eapply Cofix; eauto.
      + constructor.
        * eapply Cofix; eauto.
        * now inv H3.
      + rewrite <-H, <-H5.
        constructor.
        * eapply Cofix; eauto.
        * now inv H3.
  Qed.

  Add Parametric Morphism op t : (lift1 op t)
      with signature @EqSt value ==> @EqSt value ==> Basics.impl
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
      with signature @EqSt value ==> @EqSt value ==> @EqSt value ==> Basics.impl
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
 Add Parametric Morphism c : (const c)
      with signature @EqSt bool ==> @EqSt value
        as const_EqSt.
  Proof.
    cofix; intros b b' Eb.
    unfold_Stv b; unfold_Stv b';
      constructor; inv Eb; simpl in *; try discriminate; auto.
  Qed.

  Add Parametric Morphism H : (sem_lexp H)
      with signature @EqSt bool ==> eq ==> @EqSt value ==> Basics.impl
        as sem_lexp_morph.
  Proof.
    intros ** b b' Eb e xs xs' Exs Sem.
    revert b' xs' Eb Exs; induction Sem.
    - intros. constructor.
      rewrite <-Eb.
      transitivity cs; auto.
      now symmetry.
    - econstructor; eauto.
      eapply sem_var_EqSt; eauto.
    - econstructor; eauto.
      apply IHSem; auto; try reflexivity.
      now rewrite <-Exs.
    - econstructor.
      + apply IHSem; auto; reflexivity.
      + now rewrite <-Exs.
    - econstructor.
      + apply IHSem1; auto; reflexivity.
      + apply IHSem2; auto; reflexivity.
      + now rewrite <-Exs.
  Qed.

  Add Parametric Morphism H : (sem_cexp H)
      with signature @EqSt bool ==> eq ==> @EqSt value ==> Basics.impl
        as sem_cexp_morph.
  Proof.
    intros ** b b' Eb e xs xs' Exs Sem.
    revert b' xs' Eb Exs; induction Sem.
    - econstructor; eauto.
      + apply IHSem1; auto; reflexivity.
      + apply IHSem2; auto; reflexivity.
      + now rewrite <-Exs.
    - econstructor; eauto.
      + rewrite <-Eb; eauto.
      + apply IHSem1; auto; reflexivity.
      + apply IHSem2; auto; reflexivity.
      + now rewrite <-Exs.
    - constructor.
      now rewrite <-Eb, <-Exs.
  Qed.

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
  Add Parametric Morphism A opaque n : (mask opaque n)
      with signature @EqSt bool ==> @EqSt A ==> @EqSt A
        as mask_EqSt.
  Proof.
    revert n; cofix Cofix; intros n rs rs' Ers xs xs' Exs.
    unfold_Stv rs; unfold_Stv rs'; unfold_St xs; unfold_St xs';
      constructor; inv Ers; inv Exs;
        simpl in *; try discriminate;
          destruct n as [|[]]; auto; try reflexivity.
  Qed.

  Add Parametric Morphism G H : (sem_equation G H)
      with signature @EqSt bool ==> eq ==> Basics.impl
        as mod_sem_equation_morph.
  Proof.
    unfold Basics.impl; intros ** b b' Eb e Sem.
    induction Sem.
    - econstructor; eauto.
      now rewrite <-Eb.
    - econstructor; eauto.
      apply Forall2_impl_In with (P:=sem_lexp H b); eauto.
      intros; now rewrite <-Eb.
    - econstructor; eauto.
      apply Forall2_impl_In with (P:=sem_lexp H b); eauto.
      intros; now rewrite <-Eb.
    - econstructor; eauto.
      rewrite <-Eb; eauto.
  Qed.

  Add Parametric Morphism : same_clock
      with signature @EqSts value ==> Basics.impl
    as same_clock_morph.
  Proof.
    unfold Basics.impl.
    intros xss xss' Exss Same.
    intro; specialize (Same n); destruct Same.
    - left. eapply Forall_EqSt; eauto.
      intros xs xs' Exs E; rewrite <-Exs; auto.
    - right. eapply Forall_EqSt; eauto.
      intros xs xs' Exs E; rewrite <-Exs; auto.
    (* cofix Cofix; intros xss xss' Exss Same. *)
    (* constructor; inversion_clear Same as [A [E|Ne]]; inv Exss; try tauto. *)
    (* - left. erewrite <-map_EqSt; eauto. *)
    (*   + apply hd_EqSt. *)
    (*   + constructor; auto. *)
    (* - right. erewrite <-map_EqSt; eauto. *)
    (*   + apply hd_EqSt. *)
    (*   + constructor; auto. *)
    (* - eapply Cofix; eauto. *)
    (*   simpl. *)
    (*   constructor. *)
    (*   + rewrite H0; reflexivity. *)
    (*   + erewrite map_st_EqSt; eauto. *)
    (*     instantiate (1 := @tl value). *)
    (*     * reflexivity. *)
    (*     * apply tl_EqSt. *)
    (* - eapply Cofix; eauto. *)
    (*   simpl. *)
    (*   constructor. *)
    (*   + rewrite H0; reflexivity. *)
    (*   + erewrite map_st_EqSt; eauto. *)
    (*     instantiate (1 := @tl value). *)
    (*     * reflexivity. *)
    (*     * apply tl_EqSt. *)
  Qed.

  Add Parametric Morphism G : (sem_node G)
      with signature eq ==> @EqSts value ==> @EqSts value ==> Basics.impl
        as mod_sem_node_morph.
  Proof.
    unfold Basics.impl; intros f xss xss' Exss yss yss' Eyss Sem.
    induction Sem.
    econstructor; eauto.
    + instantiate (1:=H).
      now rewrite <-Exss.
    + now rewrite <-Eyss.
    + now rewrite <-Eyss, <-Exss.
    + apply Forall_impl with (P:=sem_equation G H (clocks_of xss)); auto.
      intro; now rewrite Exss.
  Qed.

  Add Parametric Morphism G : (sem_reset G)
      with signature eq ==> @EqSt bool ==> @EqSts value ==> @EqSts value ==> Basics.impl
        as mod_sem_reset_morph.
  Proof.
    unfold Basics.impl; intros f r r' Er xss xss' Exss yss yss' Eyss Sem.
    induction Sem as [? ? ? ? Sem].
    constructor.
    intro n; specialize (Sem n).
    eapply mod_sem_node_morph; eauto.
    - apply map_st_EqSt; auto; apply mask_EqSt; auto.
    - apply map_st_EqSt; auto; apply mask_EqSt; auto.
  Qed.

End NLSEMANTICSCOIND.

(* Module NLSemanticsCoIndRecFun *)
(*        (Ids   : IDS) *)
(*        (Op    : OPERATORS) *)
(*        (OpAux : OPERATORS_AUX Op) *)
(*        (Clks  : CLOCKS    Ids) *)
(*        (Syn   : NLSYNTAX  Ids Op Clks) *)
(*        (Ord   : ORDERED   Ids Op Clks Syn) *)
(*        <: NLSEMANTICSCOINDREC Ids Op OpAux Clks Syn Ord. *)
(*   Include NLSEMANTICSCOINDREC Ids Op OpAux Clks Syn Ord. *)
(* End NLSemanticsCoIndRecFun. *)
