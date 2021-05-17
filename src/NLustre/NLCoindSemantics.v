From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Setoid.
From Coq Require Import Morphisms.
From Coq Require Import Arith.EqNat.
From Coq Require Import Omega.

From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import CoindStreams.

(** * The NLustre semantics *)

(**

  We provide a "standard" dataflow semantics relating an environment
  of streams to a stream of outputs.

 *)

Module Type NLCOINDSEMANTICS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import CESyn : CESYNTAX      Op)
       (Import Syn   : NLSYNTAX  Ids Op       CESyn)
       (Import Str   : COINDSTREAMS  Op OpAux)
       (Import Ord   : NLORDERED Ids Op CESyn Syn).

  Definition sem_clocked_var (H: history) (b: Stream bool) (x: ident) (ck: clock) : Prop :=
    (forall xs,
        sem_var H x xs ->
        exists bs,
          sem_clock H b ck bs
          /\ aligned xs bs)
    /\ (forall bs,
          sem_clock H b ck bs ->
          exists xs,
            sem_var H x xs).

  Definition sem_clocked_vars (H: history) (b: Stream bool) (xs: list (ident * clock)) : Prop :=
    Forall (fun xc => sem_clocked_var H b (fst xc) (snd xc)) xs.

  Inductive sem_exp: history -> Stream bool -> exp -> Stream value -> Prop :=
  | Sconst:
      forall H b c cs,
        cs ≡ const b c ->
        sem_exp H b (Econst c) cs
  | Svar:
      forall H b x ty xs,
        sem_var H x xs ->
        sem_exp H b (Evar x ty) xs
  | Swhen:
      forall H b e x k es xs os,
        sem_exp H b e es ->
        sem_var H x xs ->
        when k es xs os ->
        sem_exp H b (Ewhen e x k) os
  | Sunop:
      forall H b op e ty es os,
        sem_exp H b e es ->
        lift1 op (typeof e) es os ->
        sem_exp H b (Eunop op e ty) os
  | Sbinop:
      forall H b op e1 e2 ty es1 es2 os,
        sem_exp H b e1 es1 ->
        sem_exp H b e2 es2 ->
        lift2 op (typeof e1) (typeof e2) es1 es2 os ->
        sem_exp H b (Ebinop op e1 e2 ty) os.

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
        sem_exp H b e es ->
        sem_cexp H b t ts ->
        sem_cexp H b f fs ->
        ite es ts fs os ->
        sem_cexp H b (Eite e t f) os
  | Sexp:
      forall H b e es,
        sem_exp H b e es ->
        sem_cexp H b (Eexp e) es.

  CoInductive sem_annot {A} (sem: history -> Stream bool -> A -> Stream value -> Prop):
    history -> Stream bool -> clock -> A -> Stream value -> Prop :=
  | Stick:
      forall H b ck a e es bs,
        sem H b a (present e ⋅ es) ->
        sem_clock H b ck (true ⋅ bs) ->
        sem_annot sem (history_tl H) (tl b) ck a es ->
        sem_annot sem H b ck a (present e ⋅ es)
  | Sabs:
      forall H b ck a es bs,
        sem H b a (absent ⋅ es) ->
        sem_clock H b ck (false ⋅ bs) ->
        sem_annot sem (history_tl H) (tl b) ck a es ->
        sem_annot sem H b ck a (absent ⋅ es).

  Definition sem_aexp := sem_annot sem_exp.
  Definition sem_caexp := sem_annot sem_cexp.

  CoFixpoint reset1 (v0: val) (xs: Stream value) (rs: Stream bool) (doreset : bool) : Stream value :=
    match xs, rs, doreset with
    | absent ⋅ xs, false ⋅ rs, false => absent ⋅ (reset1 v0 xs rs false)
    | absent ⋅ xs, true ⋅ rs, _
    | absent ⋅ xs, _ ⋅ rs, true => absent ⋅ (reset1 v0 xs rs true)
    | present x ⋅ xs, false ⋅ rs, false => present x ⋅ (reset1 v0 xs rs false)
    | present x ⋅ xs, true ⋅ rs, _
    | present x ⋅ xs, _ ⋅ rs, true => present v0 ⋅ (reset1 v0 xs rs false)
    end.

  Definition reset (v0: val) (xs: Stream value) (rs: Stream bool) : Stream value :=
    reset1 v0 xs rs false.

  Lemma reset_false : forall v0 xs,
      reset v0 xs (Streams.const false) ≡ xs.
  Proof.
    cofix CoFix. intros *.
    unfold_Stv xs; constructor; simpl; auto.
    1,2:apply CoFix.
  Qed.

  Lemma reset1_fby : forall v0 v xs rs,
      reset1 v0 (sfby v xs) rs true ≡ reset1 v0 (sfby v0 xs) rs false.
  Proof.
    intros *.
    apply ntheq_eqst. intros n. revert n v0 v xs rs.
    induction n; intros *.
    1,2:unfold_Stv xs; unfold_Stv rs; simpl; auto.
    - do 2 rewrite Str_nth_S_tl; simpl.
      etransitivity. 2:symmetry. 1,2:eapply IHn.
    - do 2 rewrite Str_nth_S_tl; simpl.
      eapply IHn.
  Qed.

  Lemma reset1_absent : forall n v0 xs rs r,
      xs # n = absent ->
      (reset1 v0 xs rs r) # n = absent.
  Proof.
    induction n;
      (intros * Hx;
       unfold_Stv xs; unfold_Stv rs;
       repeat rewrite Str_nth_0_hd in *; repeat rewrite Str_nth_S_tl in *;
       simpl in *; try congruence; auto).
    1-3:destruct r; auto.
  Qed.

  Fact lt_S_inv : forall n m,
      n < S m ->
      (n < m \/ n = m).
  Proof.
    intros * Hlt.
    apply Lt.le_lt_or_eq, Lt.lt_n_Sm_le; auto.
  Qed.

  Lemma reset1_present1 : forall n k v0 xs rs x,
      k < n ->
      xs # k = present x ->
      (reset1 v0 xs rs true) # n = (reset1 v0 xs rs false) # n.
  Proof.
    induction n;
      (intros * Hk Hx;
       unfold_Stv xs; unfold_Stv rs;
       repeat rewrite Str_nth_0_hd in *; repeat rewrite Str_nth_S_tl in *;
       simpl in *; try congruence; auto).
    - inv Hk.
    - apply lt_S_inv in Hk as [?|?]; subst.
      + destruct k. rewrite Str_nth_0 in Hx; congruence.
        rewrite Str_nth_S in Hx.
        eapply IHn; [|eauto]. apply Nat.lt_succ_l; auto.
      + destruct n. rewrite Str_nth_0 in Hx; congruence.
        specialize (IHn n).
        eapply IHn; eauto.
  Qed.

  Lemma reset1_present2 : forall n v0 xs rs x,
      (forall k, k < n -> xs # k = absent) ->
      xs # n = present x ->
      (reset1 v0 xs rs true) # n = present v0.
  Proof.
    induction n;
      (intros * Hk Hx;
       unfold_Stv xs; unfold_Stv rs;
       repeat rewrite Str_nth_0_hd in *; repeat rewrite Str_nth_S_tl in *;
       simpl in *; try congruence; auto).
    - eapply IHn; eauto.
      intros ? Hkn. specialize (Hk (S k)).
      rewrite Str_nth_S in Hk. apply Hk, lt_n_S; auto.
    - eapply IHn; eauto.
      intros ? Hkn. specialize (Hk (S k)).
      rewrite Str_nth_S in Hk. apply Hk, lt_n_S; auto.
    - specialize (Hk 0 (Nat.lt_0_succ _)).
      rewrite Str_nth_0 in Hk. inv Hk.
    - specialize (Hk 0 (Nat.lt_0_succ _)).
      rewrite Str_nth_0 in Hk. inv Hk.
  Qed.

  Section NodeSemantics.

    Variable G: global.

    Inductive sem_equation: history -> Stream bool -> equation -> Prop :=
    | SeqDef:
        forall H b x ck e es,
          sem_caexp H b ck e es ->
          sem_var H x es ->
          sem_equation H b (EqDef x ck e)
    | SeqApp:
        forall H b xs ck f es xrs ys rs ess oss,
          Forall2 (sem_exp H b) es ess ->
          sem_clock H b ck (clocks_of ess) ->
          Forall2 (sem_var H) (List.map fst xrs) ys ->
          bools_ofs ys rs ->
          (forall k, sem_node f (List.map (mask k rs) ess) (List.map (mask k rs) oss)) ->
          Forall2 (sem_var H) xs oss ->
          sem_equation H b (EqApp xs ck f es xrs)
    | SeqFby:
        forall H b x ck c0 e xrs es os ys rs,
          sem_aexp H b ck e es ->
          Forall2 (sem_var H) (List.map fst xrs) ys ->
          sem_clocked_vars H b xrs ->
          bools_ofs ys rs ->
          os = reset (sem_const c0) (sfby (sem_const c0) es) rs ->
          sem_var H x os ->
          sem_equation H b (EqFby x ck c0 e xrs)

    with sem_node: ident -> list (Stream value) -> list (Stream value) -> Prop :=
      SNode:
        forall H f n xss oss,
          find_node f G = Some n ->
          Forall2 (sem_var H) (List.map fst n.(n_in)) xss ->
          Forall2 (sem_var H) (List.map fst n.(n_out)) oss ->
          sem_clocked_vars H (clocks_of xss) (idck n.(n_in)) ->
          Forall (sem_equation H (clocks_of xss)) n.(n_eqs) ->
          sem_node f xss oss.

  End NodeSemantics.

  Section SemInd.

    Variable G: global.

    Variable P_equation: history -> Stream bool -> equation -> Prop.
    Variable P_node: ident -> list (Stream value) -> list (Stream value) -> Prop.

    Hypothesis EqDefCase:
      forall H b x ck e es,
        sem_caexp H b ck e es ->
        sem_var H x es ->
        P_equation H b (EqDef x ck e).

    Hypothesis EqAppCase:
      forall H b xs ck f es xrs ys rs ess oss,
        Forall2 (sem_exp H b) es ess ->
        sem_clock H b ck (clocks_of ess) ->
        Forall2 (sem_var H) (List.map fst xrs) ys ->
        bools_ofs ys rs ->
        (forall k, sem_node G f (List.map (mask k rs) ess) (List.map (mask k rs) oss)
              /\ P_node f (List.map (mask k rs) ess) (List.map (mask k rs) oss)) ->
        Forall2 (sem_var H) xs oss ->
        P_equation H b (EqApp xs ck f es xrs).

    Hypothesis EqFbyCase:
      forall H b x ck c0 e xrs es os ys rs,
        sem_aexp H b ck e es ->
        Forall2 (sem_var H) (List.map fst xrs) ys ->
        sem_clocked_vars H b xrs ->
        bools_ofs ys rs ->
        os = reset (sem_const c0) (sfby (sem_const c0) es) rs ->
        sem_var H x os ->
        P_equation H b (EqFby x ck c0 e xrs).

    Hypothesis NodeCase:
      forall H f n xss oss,
        find_node f G = Some n ->
        Forall2 (sem_var H) (List.map fst n.(n_in)) xss ->
        Forall2 (sem_var H) (List.map fst n.(n_out)) oss ->
        sem_clocked_vars H (clocks_of xss) (idck n.(n_in)) ->
        Forall (sem_equation G H (clocks_of xss)) n.(n_eqs) ->
        Forall (P_equation H (clocks_of xss)) n.(n_eqs) ->
        P_node f xss oss.

    Fixpoint sem_equation_mult
             (H: history) (b: Stream bool) (e: equation)
             (Sem: sem_equation G H b e) {struct Sem}
      : P_equation H b e
    with sem_node_mult
           (f: ident) (xss oss: list (Stream value))
           (Sem: sem_node G f xss oss) {struct Sem}
         : P_node f xss oss.
    Proof.
      - destruct Sem; eauto.
      - destruct Sem; eauto.
        eapply NodeCase; eauto.
        match goal with H: Forall _ _ |- _ => induction H; auto end.
    Qed.

    Combined Scheme sem_equation_node_ind from
             sem_equation_mult, sem_node_mult.

  End SemInd.

  (** ** Properties of the [global] environment *)

  Lemma sem_node_cons2:
    forall nd G f xs ys,
      Ordered_nodes G
      -> sem_node G f xs ys
      -> Forall (fun nd' : node => n_name nd <> n_name nd') G
      -> sem_node (nd::G) f xs ys.
  Proof.
    intros nd G f xs ys Hord Hsem Hnin.
    assert (Hnin':=Hnin).
    revert Hnin'.
    induction Hsem as [
                     | |
                     | bk f n xs ys Hfind Hinp Hout Hscvs Heqs IH]
      using sem_node_mult
      with (P_equation := fun bk H eq =>
                   ~Is_node_in_eq nd.(n_name) eq
                   -> sem_equation (nd::G) bk H eq);
      try eauto using sem_equation; try intro Hb.
    - econstructor; eauto. intro k.
      take (forall k, _ /\ _) and specialize (it k) as []. auto.
    -
      assert (nd.(n_name) <> f) as Hnf.
      { intro Hnf. rewrite Hnf in *.
        eapply Forall_forall in Hnin; [|eapply find_node_In; eauto].
        apply find_node_name in Hfind. auto. }
      econstructor; eauto.
      now apply find_node_other; auto.
      apply Forall_impl_In with (2:=IH).
      intros eq Hin HH. apply HH; clear HH.
      destruct eq; try inversion 1; subst.
      pose proof Hin as Hsem; apply Forall_forall with (1:=Heqs)in Hsem.
      inversion_clear Hsem as [| ??????????????? Hsemn|].
      specialize (Hsemn 0). inversion_clear Hsemn as [ ? ? ? ? ? Hfind'].
      pose proof (find_node_name _ _ _ Hfind').
      apply find_node_In in Hfind' as (_&Hfind').
      apply Forall_forall with (1:=Hnin) in Hfind'. auto.
  Qed.

  Lemma sem_equation_cons2:
    forall G b H eqs nd,
      Ordered_nodes (nd::G)
      -> Forall (sem_equation G H b) eqs
      -> ~Is_node_in nd.(n_name) eqs
      -> Forall (sem_equation (nd::G) H b) eqs.
  Proof.
    intros G b H eqs nd Hord Hsem Hnini.
    induction eqs as [|eq eqs IH]; [now constructor|].
    apply Forall_cons2 in Hsem.
    destruct Hsem as [Heq Heqs].
    apply not_Is_node_in_cons in Hnini.
    destruct Hnini as [Hnini Hninis].
    apply IH with (2:=Hninis) in Heqs.
    constructor; [|now apply Heqs].
    destruct Heq (* as [|? ? ? ? ? ? ? ? ? ? ? ? ? Hsem|] *);
      try now eauto using sem_equation.
    econstructor; eauto using sem_equation.
    inversion_clear Hord as [|? ? Hord' Hnn Hnns].
    auto using sem_node_cons2.
  Qed.


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

  Add Parametric Morphism : (const)
      with signature @EqSt bool ==> eq ==> @EqSt value
        as const_EqSt.
  Proof.
    cofix CoFix; intros b b' Eb.
    unfold_Stv b; unfold_Stv b';
      constructor; inv Eb; simpl in *; try discriminate; auto.
  Qed.

  Add Parametric Morphism : reset
      with signature @eq val ==> @EqSt value ==> @EqSt bool ==> @EqSt value
        as reset_EqSt.
  Proof.
    unfold reset. remember false as b. clear Heqb. revert b.
    cofix CoFix.
    intros * Heq1 * Heq2.
    unfold_St x; unfold_St x0; unfold_St y0; unfold_St y1.
    inv Heq1. inv Heq2. simpl in *; subst.
    destruct v0, b, b1; constructor; simpl; auto.
  Qed.

  Add Parametric Morphism H : (sem_exp H)
      with signature @EqSt bool ==> eq ==> @EqSt value ==> Basics.impl
        as sem_exp_morph.
  Proof.
    intros b b' Eb e xs xs' Exs Sem.
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
    intros b b' Eb e xs xs' Exs Sem.
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

  Add Parametric Morphism A sem H
    (sem_compat: Proper (eq ==> @EqSt bool ==> eq ==> @EqSt value ==> Basics.impl) sem)
    : (@sem_annot A sem H)
      with signature @EqSt bool ==> eq ==> eq ==> @EqSt value ==> Basics.impl
        as sem_annot_morph.
  Proof.
    revert H sem_compat; cofix Cofix.
    intros H HH b b' Eb ck e xs xs' Exs Sem.
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

  Add Parametric Morphism H : (sem_aexp H)
      with signature @EqSt bool ==> eq ==> eq ==> @EqSt value ==> Basics.impl
        as sem_aexp_morph.
  Proof.
    intros; eapply sem_annot_morph; eauto.
    solve_proper.
  Qed.

  Add Parametric Morphism H : (sem_caexp H)
      with signature @EqSt bool ==> eq ==> eq ==> @EqSt value ==> Basics.impl
        as sem_caexp_morph.
  Proof.
    intros; eapply sem_annot_morph; eauto.
    solve_proper.
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

  Add Parametric Morphism H : (sem_clocked_var H)
      with signature @EqSt bool ==> eq ==> eq ==> Basics.impl
        as sem_clocked_var_morph.
  Proof.
    intros bs bs' E x ck (Sem & Sem'); split; now setoid_rewrite <-E.
  Qed.

  Add Parametric Morphism G H : (sem_equation G H)
      with signature @EqSt bool ==> eq ==> Basics.impl
        as mod_sem_equation_morph.
  Proof.
    unfold Basics.impl; intros b b' Eb e Sem.
    induction Sem; econstructor; eauto; try now rewrite <-Eb.
    - eapply Forall2_impl_In with (P := sem_exp H b); auto.
      intros; now rewrite <-Eb.
    - unfold sem_clocked_vars in *.
      eapply Forall_impl; [|eauto].
      intros; now rewrite <-Eb.
  Qed.

  Add Parametric Morphism H : (sem_clocked_vars H)
      with signature @EqSt bool ==> eq ==> Basics.impl
        as sem_clocked_vars_morph.
  Proof.
    intros bs bs' E xs Sem.
    induction Sem; constructor; auto.
    now rewrite <-E.
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
    + now rewrite <-Exss.
    + apply Forall_impl with (P:=sem_equation G H (clocks_of xss)); auto.
      intro; now rewrite Exss.
  Qed.

  Add Parametric Morphism : (aligned)
      with signature @EqSt value ==> @EqSt bool ==> Basics.impl
        as aligned_EqSt.
  Proof.
    cofix CoFix.
    intros xs xs' Exs bs bs' Ebs Synchro.
    unfold_Stv xs'; unfold_Stv bs'; inv Synchro; inv Exs; inv Ebs;
      try discriminate; constructor; eapply CoFix; eauto.
  Qed.

End NLCOINDSEMANTICS.

Module NLCoindSemanticsFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (CESyn : CESYNTAX      Op)
       (Syn   : NLSYNTAX  Ids Op       CESyn)
       (Str   : COINDSTREAMS  Op OpAux)
       (Ord   : NLORDERED Ids Op CESyn Syn)
<: NLCOINDSEMANTICS Ids Op OpAux CESyn Syn Str Ord.
  Include NLCOINDSEMANTICS Ids Op OpAux CESyn Syn Str Ord.
End NLCoindSemanticsFun.
