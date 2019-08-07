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
From Velus Require Import Streams.

(** * The NLustre semantics *)

(**

  We provide a "standard" dataflow semantics relating an environment
  of streams to a stream of outputs.

 *)

Module Type NLSEMANTICSCOIND
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import CESyn : CESYNTAX      Op)
       (Import Syn   : NLSYNTAX  Ids Op       CESyn)
       (Import Str   : STREAMS       Op OpAux)
       (Import Ord   : NLORDERED Ids Op CESyn Syn).

  Definition History := Env.t (Stream value).

  Definition History_tl (H: History) : History := Env.map (@tl value) H.

   Inductive sem_var: History -> ident -> Stream value -> Prop :=
    sem_var_intro:
      forall H x xs xs',
        Env.find x H = Some xs' ->
        xs ≡ xs' ->
        sem_var H x xs.

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

  CoInductive synchronized: Stream value -> Stream bool -> Prop :=
  | synchro_present:
      forall v vs bs,
        synchronized vs bs ->
        synchronized (present v ::: vs) (true ::: bs)
  | synchro_absent:
      forall vs bs,
        synchronized vs bs ->
        synchronized (absent ::: vs) (false ::: bs).

  Definition sem_clocked_var (H: History) (b: Stream bool) (x: ident) (ck: clock) : Prop :=
    (forall xs,
        sem_var H x xs ->
        exists bs,
          sem_clock H b ck bs
          /\ synchronized xs bs)
    /\ (forall bs,
          sem_clock H b ck bs ->
          exists xs,
            sem_var H x xs).

  Definition sem_clocked_vars (H: History) (b: Stream bool) (xs: list (ident * clock)) : Prop :=
    Forall (fun xc => sem_clocked_var H b (fst xc) (snd xc)) xs.

  Inductive sem_exp: History -> Stream bool -> exp -> Stream value -> Prop :=
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
        sem_exp H b e es ->
        sem_cexp H b t ts ->
        sem_cexp H b f fs ->
        ite es ts fs os ->
        sem_cexp H b (Eite e t f) os
  | Sexp:
      forall H b e es,
        sem_exp H b e es ->
        sem_cexp H b (Eexp e) es.

  CoInductive sem_annot {A} (sem: History -> Stream bool -> A -> Stream value -> Prop):
    History -> Stream bool -> clock -> A -> Stream value -> Prop :=
  | Stick:
      forall H b ck a e es bs,
        sem H b a (present e ::: es) ->
        sem_clock H b ck (true ::: bs) ->
        sem_annot sem (History_tl H) (tl b) ck a es ->
        sem_annot sem H b ck a (present e ::: es)
  | Sabs:
      forall H b ck a es bs,
        sem H b a (absent ::: es) ->
        sem_clock H b ck (false ::: bs) ->
        sem_annot sem (History_tl H) (tl b) ck a es ->
        sem_annot sem H b ck a (absent ::: es).

  Definition sem_aexp := sem_annot sem_exp.
  Definition sem_caexp := sem_annot sem_cexp.

  CoFixpoint clocks_of (ss: list (Stream value)) : Stream bool :=
    existsb (fun s => hd s <>b absent) ss ::: clocks_of (List.map (@tl value) ss).

  CoFixpoint fby (v0: val) (xs: Stream value) : Stream value :=
    match xs with
    | absent    ::: xs => absent     ::: fby v0 xs
    | present x ::: xs => present v0 ::: fby x xs
    end.

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
          Forall2 (sem_exp H b) es ess ->
          sem_clock H b ck (clocks_of ess) ->
          sem_node f ess oss ->
          Forall2 (sem_var H) ys oss ->
          sem_equation H b (EqApp ys ck f es None)
    | SeqReset:
        forall H b xs ck f es y ys rs ess oss,
          Forall2 (sem_exp H b) es ess ->
          sem_clock H b ck (clocks_of ess) ->
          sem_var H y ys ->
          bools_of ys rs ->
          (forall k, sem_node f (List.map (mask k rs) ess) (List.map (mask k rs) oss)) ->
          Forall2 (sem_var H) xs oss ->
          sem_equation H b (EqApp xs ck f es (Some y))
    | SeqFby:
        forall H b x ck c0 e es os,
          sem_aexp H b ck e es ->
          os = fby (sem_const c0) es ->
          sem_var H x os ->
          sem_equation H b (EqFby x ck c0 e)

    with
    sem_node: ident -> list (Stream value) -> list (Stream value) -> Prop :=
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

    Variable P_equation: History -> Stream bool -> equation -> Prop.
    Variable P_node: ident -> list (Stream value) -> list (Stream value) -> Prop.

    Hypothesis EqDefCase:
      forall H b x ck e es,
        sem_caexp H b ck e es ->
        sem_var H x es ->
        P_equation H b (EqDef x ck e).

    Hypothesis EqAppCase:
      forall H b ys ck f es ess oss,
        Forall2 (sem_exp H b) es ess ->
        sem_clock H b ck (clocks_of ess) ->
        sem_node G f ess oss ->
        Forall2 (sem_var H) ys oss ->
        P_node f ess oss ->
        P_equation H b (EqApp ys ck f es None).

    Hypothesis EqResetCase:
      forall H b xs ck f es y ys rs ess oss,
        Forall2 (sem_exp H b) es ess ->
        sem_clock H b ck (clocks_of ess) ->
        sem_var H y ys ->
        bools_of ys rs ->
        (forall k, sem_node G f (List.map (mask k rs) ess) (List.map (mask k rs) oss)
              /\ P_node f (List.map (mask k rs) ess) (List.map (mask k rs) oss)) ->
        Forall2 (sem_var H) xs oss ->
        P_equation H b (EqApp xs ck f es (Some y)).

    Hypothesis EqFbyCase:
      forall H b x ck c0 e es os,
        sem_aexp H b ck e es ->
        os = fby (sem_const c0) es ->
        sem_var H x os ->
        P_equation H b (EqFby x ck c0 e).

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
             (H: History) (b: Stream bool) (e: equation)
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

  (* TODO: move to NLSyntax? *)
  Lemma find_node_In:
    forall f G n,
      find_node f G = Some n ->
      In n G.
  Proof.
    intros * Hfind.
    apply find_node_split in Hfind.
    destruct Hfind as (bG & aG & Hge).
    rewrite Hge. auto using in_app with datatypes.
  Qed.

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
                     |
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
        apply In_Forall with (2:=find_node_In _ _ _ Hfind) in Hnin.
        apply find_node_name in Hfind. auto. }
      econstructor; eauto.
      now apply find_node_other; auto.
      apply Forall_impl_In with (2:=IH).
      intros eq Hin HH. apply HH; clear HH.
      destruct eq; try inversion 1; subst.
      pose proof (In_Forall _ _ _ Heqs Hin) as Hsem.
      inversion_clear Hsem as [| ? ? ? ? ? ? ? ? ? ? Hsemn| |].
      inversion_clear Hsemn as [ ? ? ? ? ? Hfind'].
      pose proof (find_node_name _ _ _ Hfind').
      apply find_node_In in Hfind'.
      apply In_Forall with (1:=Hnin) in Hfind'. auto.
      take (forall k, _) and specialize (it 0) as Hsem.
      inversion_clear Hsem as [ ? ? ? ? ? Hfind'].
      pose proof (find_node_name _ _ _ Hfind').
      apply find_node_In in Hfind'.
      apply In_Forall with (1:=Hnin) in Hfind'. auto.
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
    econstructor; eauto. intro k.
    inv Hord. apply sem_node_cons2; eauto.
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

  Add Parametric Morphism : count
      with signature @EqSt bool ==> @EqSt nat
        as count_EqSt.
  Proof.
    unfold count; generalize 0.
    cofix Cofix; intros n xs xs' Exs.
    unfold_Stv xs; unfold_Stv xs'; constructor; inv Exs;
      simpl in *; try discriminate; auto.
  Qed.

  Add Parametric Morphism G H : (sem_equation G H)
      with signature @EqSt bool ==> eq ==> Basics.impl
        as mod_sem_equation_morph.
  Proof.
    unfold Basics.impl; intros b b' Eb e Sem.
    induction Sem; econstructor; eauto; try now rewrite <-Eb.
    - eapply Forall2_impl_In with (P := sem_exp H b); auto.
      intros; now rewrite <-Eb.
    - eapply Forall2_impl_In with (P := sem_exp H b); auto.
      intros; now rewrite <-Eb.
  Qed.

  Add Parametric Morphism H : (sem_clocked_var H)
      with signature @EqSt bool ==> eq ==> eq ==> Basics.impl
        as sem_clocked_var_morph.
  Proof.
    intros bs bs' E x ck (Sem & Sem'); split; now setoid_rewrite <-E.
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

  Add Parametric Morphism : (synchronized)
      with signature @EqSt value ==> @EqSt bool ==> Basics.impl
        as synchronized_EqSt.
  Proof.
    cofix CoFix.
    intros xs xs' Exs bs bs' Ebs Synchro.
    unfold_Stv xs'; unfold_Stv bs'; inv Synchro; inv Exs; inv Ebs;
      try discriminate; constructor; eapply CoFix; eauto.
  Qed.

  Lemma sem_var_det:
    forall x H xs xs',
      sem_var H x xs ->
      sem_var H x xs' ->
      xs ≡ xs'.
  Proof.
    inversion_clear 1 as [???? Find E];
      inversion_clear 1 as [???? Find' E'];
      rewrite Find in Find'; inv Find'.
    etransitivity; eauto; symmetry; auto.
  Qed.

End NLSEMANTICSCOIND.

Module NLSemanticsCoindFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (CESyn : CESYNTAX      Op)
       (Syn   : NLSYNTAX  Ids Op       CESyn)
       (Str   : STREAMS       Op OpAux)
       (Ord   : NLORDERED Ids Op CESyn Syn)
<: NLSEMANTICSCOIND Ids Op OpAux CESyn Syn Str Ord.
  Include NLSEMANTICSCOIND Ids Op OpAux CESyn Syn Str Ord.
End NLSemanticsCoindFun.
