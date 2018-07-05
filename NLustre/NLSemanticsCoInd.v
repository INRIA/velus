Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Coq.Sorting.Permutation.
Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Arith.EqNat.

Require Import Coq.FSets.FMapPositive.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.NLustre.NLSyntax.
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

  Definition History := PM.t (Stream value).

  Definition History_tl (H: History) : History := PM.map (@tl value) H.

  CoFixpoint const (c: const) (b: Stream bool): Stream value :=
    (if hd b then present (sem_const c) else absent) ::: const c (tl b).

  Inductive sem_var: History -> ident -> Stream value -> Prop :=
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

  CoInductive lift2 (op: binop) (ty1 ty2: type)
    : Stream value -> Stream value -> Stream value -> Prop :=
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

  CoInductive sem_clock: History -> Stream bool -> clock -> Stream bool -> Prop :=
  | Sbase:
      forall H b b',
        b ≡ b' ->
        sem_clock H b Cbase b'
  | Son:
      forall H b bk bs ck x k xs c,
        sem_clock H b ck (true ::: bk) ->
        sem_var H x (present c ::: xs) ->
        val_to_bool c = Some k ->
        sem_clock (History_tl H) (tl b) (Con ck x k) bs ->
        sem_clock H b (Con ck x k) (true ::: bs)
  | Son_abs1:
      forall H b bk bs ck x k xs,
        sem_clock H b ck (false ::: bk) ->
        sem_var H x (absent ::: xs) ->
        sem_clock (History_tl H) (tl b) (Con ck x k) bs ->
        sem_clock H b (Con ck x k) (false ::: bs)
  | Son_abs2:
      forall H b bk bs ck x k c xs,
        sem_clock H b ck (true ::: bk) ->
        sem_var H x (present c ::: xs) ->
        val_to_bool c = Some k ->
        sem_clock (History_tl H) (tl b) (Con ck x (negb k)) bs ->
        sem_clock H b (Con ck x (negb k)) (false ::: bs).

  Inductive sem_lexp: History -> Stream bool -> lexp -> Stream value -> Prop :=
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

  Inductive sem_cexp: History -> Stream bool -> cexp -> Stream value -> Prop :=
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

  CoInductive sem_avar: History -> Stream bool -> clock -> ident -> Stream value -> Prop :=
  | SVtick:
      forall H b ck x v vs bs,
        sem_var H x (present v ::: vs) ->
        sem_clock H b ck (true ::: bs) ->
        sem_avar (History_tl H) (tl b) ck x vs ->
        sem_avar H b ck x (present v ::: vs)
  | SVabs:
      forall H b ck x vs bs,
        sem_var H x (absent ::: vs) ->
        sem_clock H b ck (false ::: bs) ->
        sem_avar (History_tl H) (tl b) ck x vs ->
        sem_avar H b ck x (absent ::: vs).

  CoInductive sem_aexp {A} (sem: History -> Stream bool -> A -> Stream value -> Prop):
    History -> Stream bool -> clock -> A -> Stream value -> Prop :=
  | Stick:
      forall H b ck a e es bs,
        sem H b a (present e ::: es) ->
        sem_clock H b ck (true ::: bs) ->
        sem_aexp sem (History_tl H) (tl b) ck a es ->
        sem_aexp sem H b ck a (present e ::: es)
  | Sabs:
      forall H b ck a es bs,
        sem H b a (absent ::: es) ->
        sem_clock H b ck (false ::: bs) ->
        sem_aexp sem (History_tl H) (tl b) ck a es ->
        sem_aexp sem H b ck a (absent ::: es).

  Definition sem_laexp := sem_aexp sem_lexp.
  Definition sem_caexp := sem_aexp sem_cexp.

  CoInductive sem_laexps: History -> Stream bool -> clock -> list lexp -> list (Stream value) -> Prop :=
  | SLsTick:
      forall H b ck les ess bs,
        Forall2 (sem_lexp H b) les ess ->
        Forall (fun es => hd es <> absent) ess ->
        sem_clock H b ck (true ::: bs) ->
        sem_laexps (History_tl H) (tl b) ck les (List.map (@tl value) ess) ->
        sem_laexps H b ck les ess
  | SLsAbs:
      forall H b ck les ess bs,
        Forall2 (sem_lexp H b) les ess ->
        Forall (fun es => hd es = absent) ess ->
        sem_clock H b ck (false ::: bs) ->
        sem_laexps (History_tl H) (tl b) ck les (List.map (@tl value) ess) ->
        sem_laexps H b ck les ess.

  Lemma sem_laexps_cons:
     forall H b ck le les es ess,
        sem_laexps H b ck (le :: les) (es :: ess) ->
        sem_laexps H b ck les ess.
  Proof.
    cofix Cofix; intros ** Sem.
    inversion_clear Sem as [? ? ? ? ? ? F2 F1|? ? ? ? ? ? F2 F1]; inv F2; inv F1.
    - eleft; eauto.
    - eright; eauto.
  Qed.

 CoFixpoint clocks_of (ss: list (Stream value)) : Stream bool :=
    forallb (fun s => hd s <>b absent) ss ::: clocks_of (List.map (@tl value) ss).

  Definition reset_of : Stream value -> Stream bool :=
    map (fun x => match x with
               | present x => x ==b true_val
               | _ => false
               end).

  CoFixpoint fby (c: val) (xs: Stream value) : Stream value :=
    match xs with
    | absent ::: xs => absent ::: fby c xs
    | present x ::: xs => present c ::: fby x xs
    end.

  CoFixpoint mask {A} (opaque: A) (k: nat) (rs: Stream bool) (xs: Stream A)
    : Stream A :=
    let mask' k' := mask opaque k' (tl rs) (tl xs) in
    match k, hd rs with
    | 0, true    => Streams.const opaque
    | 0, false   => hd xs  ::: mask' 0
    | 1, true    => hd xs  ::: mask' 0
    | S k', true => opaque ::: mask' k'
    | S _, false => opaque ::: mask' k
    end.

  CoFixpoint count_acc (s: nat) (rs: Stream bool): Stream nat :=
    let s := if hd rs then S s else s in
    s ::: count_acc s (tl rs).

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
    forall {A} n (o: A) k rs xs,
      Str_nth n (mask o k rs xs) =
      if beq_nat (Str_nth n (count rs)) k then Str_nth n xs else o.
  Proof.
    unfold Str_nth.
    induction n, k as [|[|k]]; intros;
    unfold_Stv rs; simpl; auto.
    - pose proof (count_acc_grow 1 rs) as H.
      apply (ForAll_Str_nth_tl n) in H; inv H.
      assert (hd (Str_nth_tl n (count_acc 1 rs)) <> 0) as E by omega;
        apply beq_nat_false_iff in E; rewrite E.
      pose proof (const_nth n o); auto.
    - rewrite IHn; unfold count.
      destruct (beq_nat (hd (Str_nth_tl n (count_acc 1 rs))) 1) eqn: E;
        rewrite count_S_nth in E.
      + apply beq_nat_true_iff, eq_add_S, beq_nat_true_iff in E; rewrite E; auto.
      + rewrite beq_nat_false_iff, NPeano.Nat.succ_inj_wd_neg, <-beq_nat_false_iff in E;
          rewrite E; auto.
    - rewrite IHn; unfold count.
      destruct (beq_nat (hd (Str_nth_tl n (count_acc 1 rs))) (S (S k))) eqn: E;
        rewrite count_S_nth in E.
      + apply beq_nat_true_iff, eq_add_S, beq_nat_true_iff in E; rewrite E; auto.
      + rewrite beq_nat_false_iff, NPeano.Nat.succ_inj_wd_neg, <-beq_nat_false_iff in E;
          rewrite E; auto.
  Qed.

  Definition mask_v := mask absent.

  Remark mask_const_opaque:
    forall {A} n rs (opaque: A),
      mask opaque n rs (Streams.const opaque) ≡ Streams.const opaque.
  Proof.
    cofix Cofix; intros.
    unfold_Stv rs; rewrite (unfold_Stream (Streams.const opaque));
      constructor; destruct n as [|[]]; simpl; auto; try apply Cofix.
    reflexivity.
  Qed.

  (* Definition masked {A} (k: nat) (rs: Stream bool) (xs xs': Stream A) := *)
  (*   forall n, Str_nth n (count rs) = k -> Str_nth n xs' = Str_nth n xs. *)

  CoFixpoint masks_from (n: nat) (rs: Stream bool) (xs: Stream value)
    : Stream (Stream value) :=
    mask_v n rs xs ::: masks_from (n + 1) rs xs.

  Definition masks := masks_from 0.

  Definition same_clock (xss: list (Stream value)) : Prop :=
    forall n,
      Forall (fun xs => Str_nth n xs = absent) xss
      \/ Forall (fun xs => Str_nth n xs <> absent) xss.

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

    Inductive sem_equation: History -> Stream bool -> equation -> Prop :=
    | SeqDef:
        forall H b x ck e es,
          sem_caexp H b ck e es ->
          sem_var H x es ->
          sem_equation H b (EqDef x ck e)
    | SeqApp:
        forall H b ys ck f es ess oss,
          sem_laexps H b ck es ess ->
          sem_node f ess oss ->
          Forall2 (sem_var H) ys oss ->
          sem_equation H b (EqApp ys ck f es None)
    | SeqReset:
        forall H b ys ck f es r ck_r rs ess oss,
          sem_laexps H b ck es ess ->
          sem_avar H b ck_r r rs ->
          sem_reset f (reset_of rs) ess oss ->
          Forall2 (sem_var H) ys oss ->
          sem_equation H b (EqApp ys ck f es (Some (r, ck_r)))
    | SeqFby:
        forall H b x ck c0 e es os,
          sem_laexp H b ck e es ->
          os = fby (sem_const c0) es ->
          sem_var H x os ->
          sem_equation H b (EqFby x ck c0 e)

    with
    sem_reset
    : ident -> Stream bool -> list (Stream value) -> list (Stream value) -> Prop :=
      SReset:
        forall f r xss yss,
          (forall k, sem_node f (List.map (mask_v k r) xss) (List.map (mask_v k r) yss)) ->
          sem_reset f r xss yss

    with
    sem_node: ident -> list (Stream value) -> list (Stream value) -> Prop :=
      SNode:
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

    Variable P_equation: History -> Stream bool -> equation -> Prop.
    Variable P_reset: ident -> Stream bool -> list (Stream value) -> list (Stream value) -> Prop.
    Variable P_node: ident -> list (Stream value) -> list (Stream value) -> Prop.

    Hypothesis EqDefCase:
      forall H b x ck e es,
        sem_caexp H b ck e es ->
        sem_var H x es ->
        P_equation H b (EqDef x ck e).

    Hypothesis EqAppCase:
      forall H b ys ck f es ess oss,
        sem_laexps H b ck es ess ->
        sem_node G f ess oss ->
        Forall2 (sem_var H) ys oss ->
        P_node f ess oss ->
        P_equation H b (EqApp ys ck f es None).

    Hypothesis EqResetCase:
      forall H b ys ck f es r ck_r rs ess oss,
        sem_laexps H b ck es ess ->
        sem_avar H b ck_r r rs ->
        sem_reset G f (reset_of rs) ess oss ->
        Forall2 (sem_var H) ys oss ->
        P_reset f (reset_of rs) ess oss ->
        P_equation H b (EqApp ys ck f es (Some (r, ck_r))).

    Hypothesis EqFbyCase:
      forall H b x ck c0 e es os,
        sem_laexp H b ck e es ->
        os = fby (sem_const c0) es ->
        sem_var H x os ->
        P_equation H b (EqFby x ck c0 e).

    Hypothesis ResetCase:
      forall f r xss yss,
        (forall k, sem_node G f (List.map (mask_v k r) xss) (List.map (mask_v k r) yss)
              /\ P_node f (List.map (mask_v k r) xss) (List.map (mask_v k r) yss)) ->
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
             (H: History) (b: Stream bool) (e: equation)
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
      - destruct Sem as [???? Sem]; eauto.
      - destruct Sem; eauto.
        eapply NodeCase; eauto.
        induction H4; auto.
    Qed.

    Combined Scheme sem_equation_node_ind from
             sem_equation_mult, sem_node_mult, sem_reset_mult.

  End SemInd.

  Add Parametric Morphism H : (sem_var H)
      with signature eq ==> @EqSt value ==> Basics.impl
        as sem_var_EqSt.
  Proof.
    intros x xs xs' E; intro Sem; inv Sem.
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

  Add Parametric Morphism H : (sem_clock H)
      with signature @EqSt bool ==> eq ==> @EqSt bool ==> Basics.impl
        as sem_clock_morph.
  Proof.
    revert H; cofix Cofix.
    intros ** b b' Eb ck bk bk' Ebk Sem.
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

  Add Parametric Morphism H : (sem_avar H)
      with signature @EqSt bool ==> eq ==> eq ==> @EqSt value ==> Basics.impl
        as sem_avar_morph.
  Proof.
    revert H; cofix Cofix.
    intros ** b b' Eb ck e xs xs' Exs Sem.
    inv Sem; unfold_Stv xs'; inversion_clear Exs as [Eh Et];
      try discriminate.
    - econstructor.
      + simpl in *; now rewrite <-Eh, <-Et.
      + rewrite <-Eb; eauto.
      + inv Eb; eapply Cofix; eauto.
    - econstructor.
      + simpl in *; now rewrite <-Et.
      + rewrite <-Eb; eauto.
      + inv Eb; eapply Cofix; eauto.
  Qed.

  Add Parametric Morphism A sem H
    (sem_compat: Proper (eq ==> @EqSt bool ==> eq ==> @EqSt value ==> Basics.impl) sem)
    : (@sem_aexp A sem H)
      with signature @EqSt bool ==> eq ==> eq ==> @EqSt value ==> Basics.impl
        as sem_aexp_morph.
  Proof.
    revert H sem_compat; cofix Cofix.
    intros ** b b' Eb ck e xs xs' Exs Sem.
    inv Sem; unfold_Stv xs'; inversion_clear Exs as [Eh Et];
      try discriminate.
    - econstructor.
      + simpl in *; now rewrite <-Eh, <-Et, <-Eb.
      + rewrite <-Eb; eauto.
      + inv Eb; eapply Cofix; eauto.
    - econstructor.
      + simpl in *; now rewrite <-Et, <-Eb.
      + rewrite <-Eb; eauto.
      + inv Eb; eapply Cofix; eauto.
  Qed.

  Add Parametric Morphism H : (sem_laexp H)
      with signature @EqSt bool ==> eq ==> eq ==> @EqSt value ==> Basics.impl
        as sem_laexp_morph.
  Proof.
    intros; eapply sem_aexp_morph; eauto.
    solve_proper.
  Qed.

  Add Parametric Morphism H : (sem_caexp H)
      with signature @EqSt bool ==> eq ==> eq ==> @EqSt value ==> Basics.impl
        as sem_caexp_morph.
  Proof.
    intros; eapply sem_aexp_morph; eauto.
    solve_proper.
  Qed.

  Add Parametric Morphism H : (sem_laexps H)
      with signature @EqSt bool ==> eq ==> eq ==> @EqSts value ==> Basics.impl
        as sem_laexps_morph.
  Proof.
    revert H; cofix Cofix.
    intros ** b b' Eb ck les ess ess' Eess Sem.
    inversion_clear Sem as [? ? ? ? ? ? F2|].
    - eleft.
      + eapply Forall2_EqSt; eauto.
        * solve_proper.
        * apply Forall2_impl_In with (P:=sem_lexp H b); eauto.
          intros; now rewrite <-Eb.
      + eapply Forall_EqSt; eauto.
        solve_proper.
      + rewrite <-Eb; eauto.
      + inv Eb; eapply Cofix; eauto.
        apply map_st_EqSt; auto.
        inversion 1; auto.
    - eright.
      + eapply Forall2_EqSt; eauto.
        * solve_proper.
        * apply Forall2_impl_In with (P:=sem_lexp H b); eauto.
          intros; now rewrite <-Eb.
      + eapply Forall_EqSt; eauto.
        solve_proper.
      + rewrite <-Eb; eauto.
      + inv Eb; eapply Cofix; eauto.
        apply map_st_EqSt; auto.
        inversion 1; auto.
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

  Add Parametric Morphism A opaque k : (mask opaque k)
      with signature @EqSt bool ==> @EqSt A ==> @EqSt A
        as mask_EqSt.
  Proof.
    revert k; cofix Cofix; intros k rs rs' Ers xs xs' Exs.
    unfold_Stv rs; unfold_Stv rs'; unfold_St xs; unfold_St xs';
      constructor; inv Ers; inv Exs;
        simpl in *; try discriminate;
          destruct k as [|[]]; auto; try reflexivity.
  Qed.

  Add Parametric Morphism : count
      with signature @EqSt bool ==> @EqSt nat
        as count_EqSt.
  Proof.
    unfold count; generalize 0.
    cofix Cofix; intros n xs xs' Exs.
    unfold_Stv xs; unfold_Stv xs'; constructor; inv Exs;
      simpl in *; try discriminate; auto.
  Qed.

  (* Add Parametric Morphism A k : (masked k) *)
  (*     with signature @EqSt bool ==> @EqSt A ==> @EqSt A ==> Basics.impl *)
  (*       as masked_EqSt. *)
  (* Proof. *)
  (*   unfold masked. *)
  (*   intros rs rs' Ers xs xs' Exs ys ys' Eys M n C. *)
  (*   specialize (M n). *)
  (*   rewrite <-Exs, <-Eys. *)
  (*   apply M. *)
  (*   now rewrite Ers. *)
  (* Qed. *)

  Add Parametric Morphism G H : (sem_equation G H)
      with signature @EqSt bool ==> eq ==> Basics.impl
        as mod_sem_equation_morph.
  Proof.
    unfold Basics.impl; intros ** b b' Eb e Sem.
    induction Sem; econstructor; eauto; now rewrite <-Eb.
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
    intro k; specialize (Sem k).
    eapply mod_sem_node_morph; eauto;
     apply map_st_EqSt; auto; apply mask_EqSt; auto.
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
