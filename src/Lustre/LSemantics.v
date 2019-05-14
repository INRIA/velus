From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Streams.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Setoid.
From Coq Require Import Morphisms.

From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import CommonList.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import Lustre.LOrdered.
From Velus Require Import NLustre.Streams.

(** * Lustre semantics *)

Module Type LSEMANTICS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Syn   : LSYNTAX   Ids Op)
       (Import Lord  : LORDERED   Ids Op Syn).

  (* TODO: put this somewhere else *)
  Infix ":::" := Cons (at level 60, right associativity) : stream_scope.
  Delimit Scope stream_scope with Stream.
  Open Scope stream_scope.

  Definition history := Env.t (Stream value).

  CoFixpoint const (c: const) (b: Stream bool) : Stream value :=
    match b with
    | true  ::: b' => present (sem_const c) ::: const c b'
    | false ::: b' => absent ::: const c b'
    end.

  CoInductive lift1 (op: unop) (ty: type)
                                     : Stream value -> Stream value -> Prop :=
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

  CoInductive fby1
               : val -> Stream value -> Stream value -> Stream value -> Prop :=
  | Fby1A:
      forall v xs ys rs,
        fby1 v xs ys rs ->
        fby1 v (absent ::: xs) (absent ::: ys) (absent ::: rs)
  | Fby1P:
      forall v w s xs ys rs,
        fby1 s xs ys rs ->
        fby1 v (present w ::: xs) (present s ::: ys) (present v ::: rs).

  CoInductive fby: Stream value -> Stream value -> Stream value -> Prop :=
  | FbyA:
      forall xs ys rs,
        fby xs ys rs ->
        fby (absent ::: xs) (absent ::: ys) (absent ::: rs)
  | FbyP:
      forall x y xs ys rs,
        fby1 y xs ys rs ->
        fby (present x ::: xs) (present y ::: ys) (present x ::: rs).

  CoInductive when (k: bool)
                       : Stream value -> Stream value -> Stream value -> Prop :=
  | WhenA:
      forall cs xs rs,
        when k cs xs rs ->
        when k (absent ::: cs) (absent ::: xs) (absent ::: rs)
  | WhenPA:
      forall c x cs xs rs,
        when k cs xs rs ->
        val_to_bool c = Some (negb k) ->
        when k (present c ::: cs) (present x ::: xs) (absent ::: rs)
  | WhenPP:
      forall c x cs xs rs,
        when k cs xs rs ->
        val_to_bool c = Some k ->
        when k (present c ::: cs) (present x ::: xs) (present x ::: rs).

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

  Definition sclockof xs := map (fun x => x <> absent) xs.

  CoFixpoint sclocksof (ss: list (Stream value)) : Stream bool :=
    existsb (fun s=> hd s <>b absent) ss ::: sclocksof (List.map (@tl value) ss).

  (* TODO: Use everywhere, esp. in LustreElab.v *)
  (* TODO: replace idents with (list ident) *)
  Definition idents xs := List.map (@fst ident (type * clock)) xs.

  Inductive sem_var: history -> ident -> Stream value -> Prop :=
    sem_var_intro:
      forall H x xs xs',
        Env.MapsTo x xs' H ->
        xs ≡ xs' ->
        sem_var H x xs.

  Section NodeSemantics.

    Variable G : global.

    Inductive sem_exp
               : history -> Stream bool -> exp -> list (Stream value) -> Prop :=
    | Sconst:
        forall H b c cs,
          cs ≡ const c b ->
          sem_exp H b (Econst c) [cs]

    | Svar:
        forall H b x s ann,
          sem_var H x s ->
          sem_exp H b (Evar x ann) [s]

    | Sunop:
        forall H b e op ty s o ann,
          sem_exp H b e [s] ->
          typeof e = [ty] ->
          lift1 op ty s o ->
          sem_exp H b (Eunop op e ann) [o]

    | Sbinop:
        forall H b e1 e2 op ty1 ty2 s1 s2 o ann,
          sem_exp H b e1 [s1] ->
          sem_exp H b e2 [s2] ->
          typeof e1 = [ty1] ->
          typeof e2 = [ty2] ->
          lift2 op ty1 ty2 s1 s2 o ->
          sem_exp H b (Ebinop op e1 e2 ann) [o]

    | Sfby:
        forall H b e0s es anns s0ss sss os,
          Forall2 (sem_exp H b) e0s s0ss ->
          Forall2 (sem_exp H b) es sss ->
          Forall3 fby (concat s0ss) (concat sss) os ->
          sem_exp H b (Efby e0s es anns) os

    | Swhen:
        forall H b x s k es lann ss os,
          Forall2 (sem_exp H b) es ss ->
          sem_var H x s ->
          Forall2 (when k s) (concat ss) os ->
          sem_exp H b (Ewhen es x k lann) os

    | Smerge:
        forall H b x s ets efs lann ts fs os,
          sem_var H x s ->
          Forall2 (sem_exp H b) ets ts ->
          Forall2 (sem_exp H b) efs fs ->
          Forall3 (merge s) (concat ts) (concat fs) os ->
          sem_exp H b (Emerge x ets efs lann) os

    | Site:
        forall H b e s ets efs lann ts fs os,
          sem_exp H b e [s] ->
          Forall2 (sem_exp H b) ets ts ->
          Forall2 (sem_exp H b) efs fs ->
          Forall3 (ite s) (concat ts) (concat fs) os ->
          sem_exp H b (Eite e ets efs lann) os

    | Sapp:
        forall H b f es lann ss os,
          Forall2 (sem_exp H b) es ss ->
          sem_node f (concat ss) os ->
          sem_exp H b (Eapp f es lann) os

    with sem_equation: history -> Stream bool -> equation -> Prop :=
    | Seq:
        forall H b xs es ss,
          Forall2 (sem_exp H b) es ss ->
          Forall2 (sem_var H) xs (concat ss) ->
          sem_equation H b (xs, es)

    with sem_node: ident -> list (Stream value) -> list (Stream value) -> Prop :=
    | Snode:
        forall f ss os n H b,
          find_node f G = Some n ->
          Forall2 (sem_var H) (idents n.(n_in)) ss ->
          Forall2 (sem_var H) (idents n.(n_out)) os ->
          Forall (sem_equation H b) n.(n_eqs) ->
          b ≡ sclocksof ss ->
          sem_node f ss os.

  End NodeSemantics.

  Definition sem_nodes (G: global) : Prop :=
    Forall (fun n => exists xs ys, sem_node G n.(n_name) xs ys) G.

  (* TODO: tidy up file *)

  (** Custom induction schemes *)

  Section sem_exp_ind2.
    Variable G : global.

    Variable P_exp : history -> Stream bool -> exp -> list (Stream value) -> Prop.
    Variable P_equation : history -> Stream bool -> equation -> Prop.
    Variable P_node : ident -> list (Stream value) -> list (Stream value) -> Prop.

    Hypothesis ConstCase:
      forall H b c cs,
        cs ≡ const c b ->
        P_exp H b (Econst c) [cs].

    Hypothesis VarCase:
      forall H b x s ann,
        sem_var H x s ->
        P_exp H b (Evar x ann) [s].

    Hypothesis UnopCase:
      forall H b e op ty s o ann,
        sem_exp G H b e [s] ->
        P_exp H b e [s] ->
        typeof e = [ty] ->
        lift1 op ty s o ->
        P_exp H b (Eunop op e ann) [o].

    Hypothesis BinopCase:
      forall H b e1 e2 op ty1 ty2 s1 s2 o ann,
        sem_exp G H b e1 [s1] ->
        P_exp H b e1 [s1] ->
        sem_exp G H b e2 [s2] ->
        P_exp H b e2 [s2] ->
        typeof e1 = [ty1] ->
        typeof e2 = [ty2] ->
        lift2 op ty1 ty2 s1 s2 o ->
        P_exp H b (Ebinop op e1 e2 ann) [o].

    Hypothesis FbyCase:
      forall H b e0s es anns s0ss sss os,
        Forall2 (sem_exp G H b) e0s s0ss ->
        Forall2 (P_exp H b) e0s s0ss ->
        Forall2 (sem_exp G H b) es sss ->
        Forall2 (P_exp H b) es sss ->
        Forall3 fby (concat s0ss) (concat sss) os ->
        P_exp H b (Efby e0s es anns) os.

    Hypothesis WhenCase:
      forall H b x s k es lann ss os,
        Forall2 (sem_exp G H b) es ss ->
        Forall2 (P_exp H b) es ss ->
        sem_var H x s ->
        Forall2 (when k s) (concat ss) os ->
        P_exp H b (Ewhen es x k lann) os.

    Hypothesis MergeCase:
      forall H b x s ets efs lann ts fs os,
        sem_var H x s ->
        Forall2 (sem_exp G H b) ets ts ->
        Forall2 (P_exp H b) ets ts ->
        Forall2 (sem_exp G H b) efs fs ->
        Forall2 (P_exp H b) efs fs ->
        Forall3 (merge s) (concat ts) (concat fs) os ->
        P_exp H b (Emerge x ets efs lann) os.

    Hypothesis IteCase:
      forall H b e s ets efs lann ts fs os,
        sem_exp G H b e [s] ->
        P_exp H b e [s] ->
        Forall2 (sem_exp G H b) ets ts ->
        Forall2 (P_exp H b) ets ts ->
        Forall2 (sem_exp G H b) efs fs ->
        Forall2 (P_exp H b) efs fs ->
        Forall3 (ite s) (concat ts) (concat fs) os ->
        P_exp H b (Eite e ets efs lann) os.

    Hypothesis AppCase:
      forall H b f es lann ss os,
        Forall2 (sem_exp G H b) es ss ->
        Forall2 (P_exp H b) es ss ->
        sem_node G f (concat ss) os ->
        P_node f (concat ss) os ->
        P_exp H b (Eapp f es lann) os.

    Hypothesis Equation:
      forall H b xs es ss,
        Forall2 (sem_exp G H b) es ss ->
        Forall2 (P_exp H b) es ss ->
        Forall2 (sem_var H) xs (concat ss) ->
        P_equation H b (xs, es).

    Hypothesis Node:
      forall f ss os n H b,
        find_node f G = Some n ->
        Forall2 (sem_var H) (idents n.(n_in)) ss ->
        Forall2 (sem_var H) (idents n.(n_out)) os ->
        Forall (sem_equation G H b) n.(n_eqs) ->
        Forall (P_equation H b) n.(n_eqs) ->
        b ≡ sclocksof ss ->
        P_node f ss os.

    Local Ltac SolveForall :=
      match goal with
      | H: Forall ?P1 ?l |- Forall ?P2 ?l =>
        induction H; auto
      | H: Forall2 ?P1 ?l1 ?l2 |- Forall2 ?P2 ?l1 ?l2 =>
        induction H; auto
      | _ => idtac
      end.

    Fixpoint sem_exp_ind2
             (H: history) (b: Stream bool) (e: exp) (ss: list (Stream value))
             (Sem: sem_exp G H b e ss)
             {struct Sem}
      : P_exp H b e ss
    with sem_equation_ind2
           (H: history) (b: Stream bool) (e: equation)
           (Sem: sem_equation G H b e)
           {struct Sem}
         : P_equation H b e
    with sem_node_ind2
           (f: ident) (ss os: list (Stream value))
           (Sem: sem_node G f ss os)
           {struct Sem}
         : P_node f ss os.
    Proof.
      - destruct Sem.
        + apply ConstCase; eauto.
        + apply VarCase; auto.
        + eapply UnopCase; eauto.
        + eapply BinopCase; eauto.
        + eapply FbyCase; eauto; clear H2; SolveForall.
        + eapply WhenCase; eauto; clear H2; SolveForall.
        + eapply MergeCase; eauto; clear H3; SolveForall.
        + eapply IteCase; eauto; clear H2; SolveForall.
        + eapply AppCase; eauto; clear H1; SolveForall.
      - destruct Sem.
        eapply Equation with (ss:=ss); eauto; clear H1; SolveForall.
      - destruct Sem.
        eapply Node; eauto.
        SolveForall.
    Qed.

  End sem_exp_ind2.

  (** ** Properties of the [global] environment *)


  (* TODO: move to CommonList *)
  Remark In_Forall:
    forall {A} (x: A) xs P,
      Forall P xs ->
      In x xs ->
      P x.
  Proof.
    intros * Hforall Hin.
    induction xs; inversion Hin; inversion Hforall; subst; auto.
  Qed.

  Lemma sem_node_cons:
    forall node G f xs ys,
      Ordered_nodes (node::G)
      -> sem_node (node::G) f xs ys
      -> node.(n_name) <> f
      -> sem_node G f xs ys.
  Proof.
    intros node G f xs ys Hord Hsem Hnf.
    revert Hnf.
    induction Hsem using sem_node_ind2
      with (P_equation := fun bk H eq => ~Is_node_in_eq node.(n_name) eq
                                      -> sem_equation G bk H eq)
           (P_exp := fun H bk e ss => ~ Is_node_in_exp node.(n_name) e
                                   -> sem_exp G H bk e ss);
      try (now econstructor; eauto).
    - econstructor; eauto. apply IHHsem.
      intro. destruct H3. constructor. auto.
    - econstructor; eauto.
      apply IHHsem. intro. destruct H5. constructor. auto.
      apply IHHsem0. intro. destruct H5. constructor. auto.
    - econstructor; eauto.
      clear H2 H3 H4. induction H1; eauto. constructor. apply H1.
      intro. destruct H5. constructor. auto. inv H0.
      apply IHForall2; eauto. intro. destruct H5. constructor. inv H0.
      destruct H5; auto.
      clear H1 H2 H4. induction H3; eauto. constructor. apply H1.
      intro. destruct H5. constructor. auto.
      apply IHForall2; eauto. intro. destruct H5. constructor. inv H2.
      destruct H6; auto.
    - econstructor; eauto.
      clear H0 H3. induction H1; eauto. constructor. apply H0.
      intro. destruct H4. constructor. auto.
      apply IHForall2; eauto. intro. destruct H4. constructor. inv H3; eauto.
    - econstructor; eauto.
      clear H1 H3 H4 H5. induction H2; eauto. constructor. apply H1.
      intro. destruct H6. constructor. auto.
      apply IHForall2; eauto. intro. destruct H6. constructor. inv H3.
      destruct H6; auto.
      clear H1 H3 H2 H5. induction H4; eauto. constructor. apply H1.
      intro. destruct H6. constructor. auto.
      apply IHForall2; eauto. intro. destruct H6. constructor. inv H2.
      destruct H6; auto.
    - econstructor; eauto. apply IHHsem.
      intro. destruct H6. constructor. auto.
      clear H1 H3 H4 H5. induction H2; eauto. constructor. apply H1.
      intro. destruct H6. constructor. auto.
      apply IHForall2; eauto. intro. destruct H6. constructor. inv H3.
      destruct H6; auto. destruct H3; auto.
      clear H1 H3 H2 H5. induction H4; eauto. constructor. apply H1.
      intro. destruct H6. constructor. auto.
      apply IHForall2; eauto. intro. destruct H6. constructor. inv H2.
      destruct H6; auto. destruct H2; auto.
    - inv Hord.
      econstructor; try apply IHHsem.
      clear H0 Hsem IHHsem. induction H1; eauto.
      constructor. apply H0. intro. destruct H2. constructor. auto.
      apply IHForall2. intro. destruct H2. inv H3. constructor. auto.
      apply INEapp2.
      intro. apply H2. rewrite H3. apply INEapp2.
    - econstructor; eauto.
      clear H0 H2. induction H1; eauto.
      constructor. apply H0. intro. destruct H3. now constructor.
      apply IHForall2. intro. destruct H3. unfold Is_node_in_eq.
      simpl. Search Exists. rewrite Exists_cons. right. auto.
    - intro.
      rewrite find_node_tl with (1:=Hnf) in H0.
      eapply Snode; eauto.
      clear H3.
      eapply Forall_impl_In with (2:=H4).
      apply find_node_later_not_Is_node_in with (1:=Hord) in H0.
      intros eq Hin. intro Hini.
      rewrite Is_node_in_Forall in H0.
      apply In_Forall with (1:=H0) in Hin.
      auto.
  Qed.

  Lemma sem_equation_global_tl:
    forall nd G H b eq,
      Ordered_nodes (nd :: G) ->
      ~ Is_node_in_eq nd.(n_name) eq ->
      sem_equation (nd :: G) H b eq ->
      sem_equation G H b eq.
  Proof.
    destruct eq as [ xs es ]. intros * Hord Hnin Hsem. inv Hsem.

    econstructor; eauto.
    clear H6. induction H5 as [ | ? ? ? ? Hsem ]; eauto. constructor.

    clear IHForall2. revert dependent y.

    Ltac SolveNin Hnin :=
      let Hn := fresh in
      let Hn2 := fresh in
      let Hn3 := fresh in
      let Hn4 := fresh in
      intro Hn; destruct Hnin; inversion_clear Hn as [? ? Hn2 |]; subst;
      [ econstructor; econstructor; auto
      | unfold Is_node_in_eq; simpl; rewrite Exists_cons; right; auto];
      inversion_clear Hn2 as
          [ | | ? ? ? ? Hn3 | | ? ? ? ? ? Hn3 | ? ? ? ? ? Hn3 | | ]; auto;
      try (destruct Hn3 as [| Hn4 ]; eauto; destruct Hn4; eauto).

    induction x using exp_ind2; intros * Hsem; inv Hsem;
      try (now econstructor; eauto).
    - econstructor; eauto. eapply IHx; eauto. SolveNin Hnin.
    - econstructor; eauto.
      apply IHx1; eauto. SolveNin Hnin.
      apply IHx2; eauto. SolveNin Hnin.
    - econstructor; eauto.
      clear H5 H1 H11 H12. induction H9; auto. constructor.
      inv H0. apply H4; auto. SolveNin Hnin.
      inv H0. apply IHForall2; eauto. SolveNin Hnin.
      clear H5 H0 H9 H12. induction H11; auto. constructor.
      inv H1. apply H4; auto. SolveNin Hnin.
      inv H1. apply IHForall2; eauto. SolveNin Hnin.
    - econstructor; eauto.
      clear H5 H11 H12. induction H10; eauto. constructor.
      inv H0. apply H4; eauto. SolveNin Hnin.
      inv H0. apply IHForall2; eauto. SolveNin Hnin.
    - econstructor; eauto.
      clear H5 H1 H10 H13 H14. induction H12; auto. constructor.
      inv H0. apply H4; auto. SolveNin Hnin.
      inv H0. apply IHForall2; eauto. SolveNin Hnin.
      clear H5 H0 H10 H12 H14. induction H13; auto. constructor.
      inv H1. apply H4; auto. SolveNin Hnin.
      inv H1. apply IHForall2; eauto. SolveNin Hnin.
    - econstructor; eauto. eapply IHx; eauto. SolveNin Hnin.
      clear H5 H1 H10 H13 H14. induction H12; auto. constructor.
      inv H0. apply H4; auto. SolveNin Hnin.
      inv H0. apply IHForall2; eauto. SolveNin Hnin.
      clear H5 H0 H10 H12 H14. induction H13; auto. constructor.
      inv H1. apply H4; auto. SolveNin Hnin.
      inv H1. apply IHForall2; eauto. SolveNin Hnin.
    - econstructor; eauto.
      clear H5 H10. induction H9; eauto. constructor.
      inv H0. apply H4; eauto. SolveNin Hnin.
      inv H0. apply IHForall2; eauto.
      intro. destruct Hnin. inv H0.
      inv H3; econstructor. econstructor; eauto. apply INEapp2.
      unfold Is_node_in_eq; simpl; rewrite Exists_cons; right; auto.
      eapply sem_node_cons; eauto. intro. destruct Hnin. rewrite H1.
      econstructor. apply INEapp2.
    - apply IHForall2. intro. destruct Hnin. unfold Is_node_in_eq. simpl.
      rewrite Exists_cons. right. auto.
  Qed.

  Lemma Forall_sem_equation_global_tl:
    forall nd G b H eqs,
      Ordered_nodes (nd :: G)
      -> ~ Is_node_in nd.(n_name) eqs
      -> Forall (sem_equation (nd :: G) H b) eqs
      -> Forall (sem_equation G H b) eqs.
  Proof.
    intros nd G H b eqs Hord Hnini.
    apply Forall_impl_In.
    intros eq Hin Hsem.
    eapply sem_equation_global_tl; eauto.
    apply Is_node_in_Forall in Hnini.
    apply In_Forall with (1:=Hnini) (2:=Hin).
  Qed.





  Add Parametric Morphism v : (fby1 v)
      with signature @EqSt value ==> @EqSt value ==> @EqSt value ==> Basics.impl
        as fby1_EqSt.
  Proof.
    revert v.
    cofix Cofix.
    intros v cs cs' Ecs xs xs' Exs ys ys' Eys H.
    destruct cs' as [[]], xs' as [[]], ys' as [[]];
      inv H; inv Ecs; inv Exs; inv Eys; simpl in *;
        try discriminate.
    + constructor. eapply Cofix; eauto.
    + inv H4. econstructor. eapply Cofix; eauto. now inv H2.
  Qed.

  Add Parametric Morphism : fby
      with signature @EqSt value ==> @EqSt value ==> @EqSt value ==> Basics.impl
        as fby_EqSt.
  Proof.
    cofix Cofix.
    intros cs cs' Ecs xs xs' Exs ys ys' Eys H.
    destruct cs' as [[]], xs' as [[]], ys' as [[]];
      inv H; inv Ecs; inv Exs; inv Eys; simpl in *;
        try discriminate.
    + constructor; eapply Cofix; eauto.
    + inv H4. inv H. econstructor. inv H2.
      rewrite <- H1. rewrite <- H3. rewrite <- H5. assumption.
  Qed.

  Add Parametric Morphism k : (when k)
      with signature @EqSt value ==> @EqSt value ==> @EqSt value ==> Basics.impl
        as when_EqSt.
  Proof.
    revert k.
    cofix Cofix.
    intros k cs cs' Ecs xs xs' Exs ys ys' Eys H.
    destruct cs' as [[]], xs' as [[]], ys' as [[]];
      inv H; inv Ecs; inv Exs; inv Eys; simpl in *;
        try discriminate.
    + constructor; eapply Cofix; eauto.
    + constructor. eapply Cofix; eauto. now inv H.
    + inv H3. inv H5. econstructor. eapply Cofix; eauto. now inv H.
  Qed.

  Add Parametric Morphism : merge
      with signature @EqSt value ==> @EqSt value ==>
                           @EqSt value ==> @EqSt value ==> Basics.impl
        as merge_EqSt.
  Proof.
    cofix Cofix.
    intros cs cs' Ecs xs xs' Exs ys ys' Eys zs zs' Ezs H.
    destruct cs' as [[]], xs' as [[]], ys' as [[]], zs' as [[]];
      inv H; inv Ecs; inv Exs; inv Eys; inv Ezs; simpl in *;
        try discriminate.
    + constructor; eapply Cofix; eauto.
    + inv H. inv H4. inv H6. constructor. eapply Cofix; eauto.
    + inv H. inv H2. inv H6. constructor. eapply Cofix; eauto.
  Qed.

  Add Parametric Morphism : ite
      with signature @EqSt value ==> @EqSt value ==>
                           @EqSt value ==> @EqSt value ==> Basics.impl
        as ite_EqSt.
  Proof.
    cofix Cofix.
    intros cs cs' Ecs xs xs' Exs ys ys' Eys zs zs' Ezs H.
    destruct cs' as [[]], xs' as [[]], ys' as [[]], zs' as [[]];
      inv H; inv Ecs; inv Exs; inv Eys; inv Ezs; simpl in *;
        try discriminate.
    + constructor; eapply Cofix; eauto.
    + inv H. inv H2. inv H6. constructor; auto. eapply Cofix; eauto.
    + inv H. inv H4. inv H6. constructor; auto. eapply Cofix; eauto.
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
    cofix Cofix; intros b b' Eb.
    unfold_Stv b; unfold_Stv b';
      constructor; inv Eb; simpl in *; try discriminate; auto.
  Qed.

  Add Parametric Morphism : sclocksof
      with signature @EqSts value ==> @EqSt bool
        as sclocksof_EqSt.
  Proof.
    cofix Cofix; intros xs xs' Exs.
    constructor. simpl.
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

  Add Parametric Morphism H : (sem_var H)
      with signature eq ==> @EqSt value ==> Basics.impl
        as sem_var_EqSt.
  Proof.
    intros x xs xs' E; intro Sem; inv Sem.
    econstructor; eauto.
    Show Proof.
    transitivity xs; auto; symmetry; auto.
  Qed.

  Add Parametric Morphism G : (sem_node G)
      with signature eq ==> @EqSts value ==> @EqSts value ==> Basics.impl
        as mod_sem_node_morph.
  Proof.
    unfold Basics.impl; intros f xss xss' Exss yss yss' Eyss Sem.
    induction Sem.
    econstructor; eauto.
    + now rewrite <-Exss.
    + now rewrite <-Eyss.
    + now rewrite Exss in H4.
  Qed.

  Add Parametric Morphism G H : (sem_exp G H)
      with signature @EqSt bool ==> eq ==> @EqSts value ==> Basics.impl
        as sem_exp_morph.
  Proof.
    intros b b' Eb e xs xs' Exs Sem.
    revert b' xs' Eb Exs; induction Sem using sem_exp_ind2 with
                              (P_equation := fun H b e => True)
                              (P_node := fun i ls xs => True).
    - intros. inv Exs. inv H5.
      constructor.
      rewrite <-Eb.
      transitivity cs; auto.
      now symmetry.
    - intros. inv Exs. inv H5.
      econstructor; eauto.
      eapply sem_var_EqSt; eauto.
    - intros. inv Exs. inv H6.
      econstructor; eauto.
      apply IHSem; auto; try reflexivity.
      now rewrite <- H4.
    - intros. inv Exs. inv H7.
      econstructor; eauto.
      + apply IHSem1; auto; reflexivity.
      + apply IHSem2; auto; reflexivity.
      + now rewrite <- H5.
    - intros.
      econstructor.
      + instantiate (1 := s0ss).
        eapply Forall2_impl_In; [ idtac | apply H1 ].
        simpl. intros. apply H7; eauto. reflexivity.
      + instantiate (1 := sss).
        eapply Forall2_impl_In; [ idtac | apply H3 ].
        simpl. intros. apply H7; eauto. reflexivity.
      + eapply Forall3_EqSt; eauto. solve_proper.
    - intros. econstructor; eauto.
      + instantiate (1 := ss).
        eapply Forall2_impl_In; [ idtac | apply H1 ].
        simpl. intros. apply H6; eauto. reflexivity.
      + eapply Forall2_EqSt; eauto. solve_proper.
    - intros. econstructor; eauto.
      + instantiate (1 := ts).
        eapply Forall2_impl_In; [ idtac | apply H2 ].
        simpl. intros. apply H8; eauto. reflexivity.
      + instantiate (1 := fs).
        eapply Forall2_impl_In; [ idtac | apply H4 ].
        simpl. intros. apply H8; eauto. reflexivity.
      + eapply Forall3_EqSt; eauto. solve_proper.
    - intros. econstructor; eauto.
      + eapply IHSem; eauto. reflexivity.
      + instantiate (1 := ts).
        eapply Forall2_impl_In; [ idtac | apply H1 ].
        simpl. intros. apply H7; eauto. reflexivity.
      + instantiate (1 := fs).
        eapply Forall2_impl_In; [ idtac | apply H3 ].
        simpl. intros. apply H7; eauto. reflexivity.
      + eapply Forall3_EqSt; eauto. solve_proper.
    - intros. econstructor.
      + instantiate (1 := ss).
        eapply Forall2_impl_In; [ idtac | apply H1 ].
        intros. simpl. apply H5; auto. reflexivity.
      + now rewrite <- Exs.
    - split.
    - split.
  Qed.

End LSEMANTICS.

Module LSemanticsFun
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Syn   : LSYNTAX   Ids Op)
       (Import Lord  : LORDERED  Ids Op Syn)
       <: LSEMANTICS Ids Op OpAux Syn Lord.
  Include LSEMANTICS Ids Op OpAux Syn Lord.
End LSemanticsFun.
