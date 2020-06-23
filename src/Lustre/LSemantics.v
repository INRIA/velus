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
From Velus Require Import CoindStreams.

(** * Lustre semantics *)

Module Type LSEMANTICS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Syn   : LSYNTAX   Ids Op)
       (Import Lord  : LORDERED   Ids Op Syn)
       (Import Str   : COINDSTREAMS   Op OpAux).

  CoInductive fby1
    : val -> Stream value -> Stream value -> Stream value -> Prop :=
  | Fby1A:
      forall v xs ys rs,
        fby1 v xs ys rs ->
        fby1 v (absent ⋅ xs) (absent ⋅ ys) (absent ⋅ rs)
  | Fby1P:
      forall v w s xs ys rs,
        fby1 s xs ys rs ->
        fby1 v (present w ⋅ xs) (present s ⋅ ys) (present v ⋅ rs).

  CoInductive fby: Stream value -> Stream value -> Stream value -> Prop :=
  | FbyA:
      forall xs ys rs,
        fby xs ys rs ->
        fby (absent ⋅ xs) (absent ⋅ ys) (absent ⋅ rs)
  | FbyP:
      forall x y xs ys rs,
        fby1 y xs ys rs ->
        fby (present x ⋅ xs) (present y ⋅ ys) (present x ⋅ rs).

  (* TODO: Use everywhere, esp. in LustreElab.v *)
  Definition idents xs := List.map (@fst ident (type * clock)) xs.

  Section NodeSemantics.

    Variable G : global.

    Inductive sem_exp
      : history -> Stream bool -> exp -> list (Stream value) -> Prop :=
    | Sconst:
        forall H b c cs,
          cs ≡ const b c ->
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
          Forall2 (fun s' => when k s' s) (concat ss) os ->
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
          sem_exp H b (Eapp f es None lann) os

    | Sreset:
        forall H b f es r lann ss os rs bs,
          Forall2 (sem_exp H b) es ss ->
          sem_exp H b r [rs] ->
          bools_of rs bs ->
          (forall k, sem_node f (List.map (mask k bs) (concat ss)) (List.map (mask k bs) os)) ->
          sem_exp H b (Eapp f es (Some r) lann) os

    with sem_equation: history -> Stream bool -> equation -> Prop :=
           Seq:
             forall H b xs es ss,
               Forall2 (sem_exp H b) es ss ->
               Forall2 (sem_var H) xs (concat ss) ->
               sem_equation H b (xs, es)

    with sem_node: ident -> list (Stream value) -> list (Stream value) -> Prop :=
      Snode:
        forall f ss os n H b,
          find_node f G = Some n ->
          Forall2 (sem_var H) (idents n.(n_in)) ss ->
          Forall2 (sem_var H) (idents n.(n_out)) os ->
          Forall (sem_equation H b) n.(n_eqs) ->
          b = clocks_of ss ->
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
        cs ≡ const b c ->
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
        Forall2 (fun s' => when k s' s) (concat ss) os ->
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
        P_exp H b (Eapp f es None lann) os.

    Hypothesis ResetCase:
      forall H b f es r lann ss os rs bs,
        Forall2 (sem_exp G H b) es ss ->
        Forall2 (P_exp H b) es ss ->
        sem_exp G H b r [rs] ->
        P_exp H b r [rs] ->
        bools_of rs bs ->
        (forall k, sem_node G f (List.map (mask k bs) (concat ss)) (List.map (mask k bs) os)
              /\ P_node f (List.map (mask k bs) (concat ss)) (List.map (mask k bs) os)) ->
        P_exp H b (Eapp f es (Some r) lann) os.

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
        b = clocks_of ss ->
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
        + eapply ResetCase; eauto; clear H2; SolveForall.
      - destruct Sem.
        eapply Equation with (ss:=ss); eauto; clear H1; SolveForall.
      - destruct Sem.
        eapply Node; eauto.
        SolveForall.
    Qed.

  End sem_exp_ind2.

  (** ** Properties of the [global] environment *)

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
    - inv Hord.
      econstructor; eauto.
      + eapply Forall2_impl_In in H1; eauto. intros * ?? Hi. apply Hi. intro.
        take (~ _) and apply it. constructor. right. eapply Exists_exists; eauto.
      + apply IHHsem. intro. take (~ _) and apply it. constructor; eauto.
      + intro k. take (forall k, _ /\ _) and specialize (it k) as (? & Hk).
        apply Hk. intro Hn. subst. take (~ _) and apply it. constructor.
    - econstructor; eauto.
      clear H0 H2. induction H1; eauto.
      constructor. apply H0. intro. destruct H3. now constructor.
      apply IHForall2. intro. destruct H3. unfold Is_node_in_eq.
      simpl. rewrite Exists_cons. right. auto.
    - intro.
      rewrite find_node_tl with (1:=Hnf) in H0.
      eapply Snode; eauto.
      clear H3.
      eapply Forall_impl_In with (2:=H4).
      apply find_node_later_not_Is_node_in with (1:=Hord) in H0.
      intros eq Hin. intro Hini.
      rewrite Is_node_in_Forall in H0.
      apply Forall_forall with (1:=H0) in Hin.
      auto.
  Qed.

  Lemma sem_node_cons':
    forall node G f xs ys,
      Ordered_nodes (node::G)
      -> sem_node G f xs ys
      -> node.(n_name) <> f
      -> sem_node (node::G) f xs ys.
  Proof.
    intros node G f xs ys Hord Hsem.
    induction Hsem using sem_node_ind2
      with (P_equation := fun bk H eq => ~Is_node_in_eq node.(n_name) eq
                                      -> sem_equation (node::G) bk H eq)
           (P_exp := fun H bk e ss => ~ Is_node_in_exp node.(n_name) e
                                   -> sem_exp (node::G) H bk e ss);
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
      econstructor; try apply IHHsem; eauto.
      + eapply Forall2_impl_In; [| eauto].
        intros a0 b0 Hina Hinb Hsem'; simpl in Hsem'.
        eapply Hsem'.
        intro contra. apply H2. constructor.
        rewrite Exists_exists. exists a0; auto.
      + rewrite Forall_forall in H6.
        inv Hsem. unfold find_node in H7. apply find_some in H7; destruct H7 as [Hin Heq].
        rewrite ident_eqb_eq in Heq; subst. eauto.
    - inv Hord.
      econstructor; eauto.
      + eapply Forall2_impl_In in H1; eauto. intros * ?? Hi. apply Hi. intro.
        take (~ _) and apply it. constructor. right. eapply Exists_exists; eauto.
      + apply IHHsem. intro. take (~ _) and apply it. constructor; eauto.
      + intro k. take (forall k, _ /\ _) and specialize (it k) as (? & Hk).
        apply Hk.
        rewrite Forall_forall in H9.
        inv H4. unfold find_node in H10. apply find_some in H10; destruct H10 as [Hin Heq].
        rewrite ident_eqb_eq in Heq; subst. eauto.
    - econstructor; eauto.
      clear H0 H2. induction H1; eauto.
      constructor. apply H0. intro. destruct H3. now constructor.
      apply IHForall2. intro. destruct H3. unfold Is_node_in_eq.
      simpl. rewrite Exists_cons. right. auto.
    - intro Hnf.
      econstructor; eauto.
      + simpl.
        rewrite <- ident_eqb_neq in Hnf. rewrite Hnf; auto.
      + eapply Forall_impl_In; [| eauto].
        intros a HIn Hsem; simpl in Hsem.
        apply Hsem.
        eapply find_node_later_not_Is_node_in in H0; eauto.
        intro contra. apply H0.
        unfold Is_node_in. rewrite Exists_exists.
        exists a; auto.
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
          [ | | ? ? ? ? Hn3 | | ? ? ? ? ? Hn3 | ? ? ? ? ? Hn3 | | |]; auto;
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
    - econstructor.
      + eapply Forall2_impl_In; [| eauto]; intros * Hin ? Hsem.
        eapply Forall_forall in Hin as Hs; eauto. apply Hs; auto.
        intro Ini. apply Hnin. inv Ini. repeat constructor.
        apply Exists_exists; eauto. now constructor 2.
      + eapply sem_node_cons; eauto. intro. subst. apply Hnin.
        constructor. apply INEapp2.
    - econstructor; eauto.
      + eapply Forall2_impl_In; [| eauto]; intros * Hin ? Hsem.
        eapply Forall_forall in Hin as Hs; eauto. apply Hs; auto.
        intro Ini. apply Hnin. inv Ini. constructor. constructor. right.
        apply Exists_exists; eauto. now constructor 2.
      + apply H0; auto. SolveNin Hnin.
      + intro k. eapply sem_node_cons; eauto. intro. subst.
        apply Hnin. constructor. constructor.
    - apply IHForall2. intro. destruct Hnin. unfold Is_node_in_eq. simpl.
      rewrite Exists_cons. right. auto.
  Qed.

  Corollary Forall_sem_equation_global_tl:
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
    apply Forall_forall with (1:=Hnini) (2:=Hin).
  Qed.

  Lemma sem_equation_global_tl':
    forall nd G H b eq,
      Ordered_nodes (nd :: G) ->
      ~ Is_node_in_eq nd.(n_name) eq ->
      sem_equation G H b eq ->
      sem_equation (nd :: G) H b eq.
  Proof.
    destruct eq as [ xs es ]. intros * Hord Hnin Hsem. inv Hsem.

    econstructor; eauto.
    clear H6. induction H5 as [ | ? ? ? ? Hsem ]; eauto. constructor.

    clear IHForall2. revert dependent y.

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
    - econstructor.
      + eapply Forall2_impl_In; [| eauto]; intros * Hin ? Hsem.
        eapply Forall_forall in Hin as Hs; eauto. apply Hs; auto.
        intro Ini. apply Hnin. inv Ini. repeat constructor.
        apply Exists_exists; eauto. now constructor 2.
      + eapply sem_node_cons'; eauto. intro. subst. apply Hnin.
        constructor. apply INEapp2.
    - econstructor; eauto.
      + eapply Forall2_impl_In; [| eauto]; intros * Hin ? Hsem.
        eapply Forall_forall in Hin as Hs; eauto. apply Hs; auto.
        intro Ini. apply Hnin. inv Ini. constructor. constructor. right.
        apply Exists_exists; eauto. now constructor 2.
      + apply H0; auto. SolveNin Hnin.
      + intro k. eapply sem_node_cons'; eauto. intro. subst.
        apply Hnin. constructor. constructor.
    - apply IHForall2. intro. destruct Hnin. unfold Is_node_in_eq. simpl.
      rewrite Exists_cons. right. auto.
  Qed.

  Corollary Forall_sem_equation_global_tl':
    forall nd G b H eqs,
      Ordered_nodes (nd :: G)
      -> ~ Is_node_in nd.(n_name) eqs
      -> Forall (sem_equation G H b) eqs
      -> Forall (sem_equation (nd :: G) H b) eqs.
  Proof.
    intros nd G H b eqs Hord Hnini.
    apply Forall_impl_In.
    intros eq Hin Hsem.
    eapply sem_equation_global_tl'; eauto.
    apply Is_node_in_Forall in Hnini.
    apply Forall_forall with (1:=Hnini) (2:=Hin).
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
    + constructor. eapply Cofix; eauto. congruence.
    + inv H3. inv H5. inv H. econstructor. eapply Cofix; eauto. congruence.
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

  Add Parametric Morphism : const
      with signature @EqSt bool ==> eq ==> @EqSt value
        as const_EqSt.
  Proof.
    cofix Cofix; intros b b' Eb.
    unfold_Stv b; unfold_Stv b';
      constructor; inv Eb; simpl in *; try discriminate; auto.
  Qed.

  Add Parametric Morphism H : (sem_var H)
      with signature eq ==> @EqSt value ==> Basics.impl
        as sem_var_EqSt.
  Proof.
    intros x xs xs' E; intro Sem; inv Sem.
    econstructor; eauto.
    transitivity xs; auto; symmetry; auto.
  Qed.

  Add Parametric Morphism G H : (sem_exp G H)
      with signature @EqSt bool ==> eq ==> @EqSts value ==> Basics.impl
        as sem_exp_morph.
  Proof.
    intros b b' Eb e xs xs' Exs Sem.
    revert b' xs' Eb Exs; induction Sem using sem_exp_ind2 with
                              (P_equation := fun H b e => True)
                              (P_node := fun i xs ys => forall ys', EqSts ys ys' -> sem_node G i xs ys');
    auto; intros.
    - inv Exs; take (Forall2 _ _ _) and inv it.
      econstructor; rewrite <-Eb; etransitivity; eauto; now symmetry.
    - inv Exs; take (Forall2 _ _ _) and inv it.
      constructor; now rewrite <-H3.
    - inv Exs; take (Forall2 _ _ _) and inv it.
      econstructor; eauto.
      + apply IHSem; eauto; reflexivity.
      + now rewrite <-H4.
    - inv Exs; take (Forall2 _ _ _) and inv it.
      econstructor; eauto.
      + apply IHSem1; eauto; reflexivity.
      + apply IHSem2; eauto; reflexivity.
      + now rewrite <-H5.
    - econstructor.
      + eapply Forall2_impl_In; [|apply H1].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + eapply Forall2_impl_In; [|apply H3].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + eapply Forall3_EqSt; eauto. solve_proper.
    - econstructor; eauto.
      + eapply Forall2_impl_In; [|apply H1].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + eapply Forall2_EqSt; eauto. solve_proper.
    - econstructor; eauto.
      + eapply Forall2_impl_In; [|apply H2].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + eapply Forall2_impl_In; [|apply H4].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + eapply Forall3_EqSt; eauto. solve_proper.
    - econstructor; eauto.
      + eapply IHSem; eauto. reflexivity.
      + eapply Forall2_impl_In; [|apply H1].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + eapply Forall2_impl_In; [|apply H3].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + eapply Forall3_EqSt; eauto. solve_proper.
    - econstructor; eauto.
      eapply Forall2_impl_In; [|apply H1].
      intros * ?? Hs; apply Hs; auto; reflexivity.
    - econstructor; eauto.
      + eapply Forall2_impl_In; [|apply H1].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + apply IHSem; auto; reflexivity.
      + intro k; specialize (H3 k); destruct H3 as (?&Hr).
        apply Hr.
        apply map_st_EqSt_Proper; auto.
        intros ?? ->; reflexivity.

    - econstructor; eauto.
      eapply Forall2_EqSt; eauto. solve_proper.
  Qed.

  Add Parametric Morphism G H : (sem_equation G H)
      with signature @EqSt bool ==> eq ==> Basics.impl
        as sem_equation_morph.
  Proof.
    unfold Basics.impl; intros xs xs' Exss eq Hsem.
    inversion_clear Hsem as [????? Hseme Hsemv]. econstructor; eauto.
    clear Hsemv. induction Hseme; constructor; auto.
    now rewrite <- Exss.
  Qed.

  Add Parametric Morphism G : (sem_node G)
      with signature eq ==> @EqSts value ==> @EqSts value ==> Basics.impl
        as mod_sem_node_morph.
  Proof.
    unfold Basics.impl; intros f xss xss' Exss yss yss' Eyss Sem.
    induction Sem.
    subst.
    econstructor; try reflexivity; eauto.
    + instantiate (1 := H). now rewrite <-Exss.
    + now rewrite <-Eyss.
    + eapply Forall_forall; intros * Hin.
      eapply Forall_forall in H3; eauto.
      now rewrite <-Exss.
  Qed.

  Ltac rewrite_Forall_forall :=
    match goal with
    | H : Forall _ _ |- _ =>
      rewrite Forall_forall in H
    | H : Forall2 _ _ _ |- _ =>
      rewrite Forall2_forall2 in H; destruct H
    | H : Forall3 _ _ _ _ |- _ =>
      rewrite Forall3_forall3 in H; destruct H as [? [? ?]]
    | |- Forall _ _ =>
      rewrite Forall_forall; intros; subst
    | |- Forall2 _ _ _ =>
      rewrite Forall2_forall2; repeat split; auto; intros; subst
    | |- Forall3 _ _ _ _ =>
      rewrite Forall3_forall3; repeat split; auto; intros; subst
    end.

  (** ** Preservation of the semantics while refining an environment *)
  Fact sem_var_refines : forall H H' id v,
      Env.refines eq H H' ->
      sem_var H id v ->
      sem_var H' id v.
  Proof.
    intros H H' id v Href Hsem.
    destruct Hsem.
    econstructor; eauto.
    apply Env.find_1 in H0.
    apply Href in H0. destruct H0 as [? [? Hfind]]; subst.
    apply Env.find_2; auto.
  Qed.

  Hint Resolve nth_In.
  Fact sem_exp_refines : forall G b e H H' v,
      Env.refines eq H H' ->
      sem_exp G H b e v ->
      sem_exp G H' b e v.
  Proof with eauto.
    induction e using exp_ind2; intros Hi Hi' v Href Hsem; inv Hsem.
    - (* const *) constructor...
    - (* var *)
      constructor. eapply sem_var_refines...
    - (* unop *) econstructor...
    - (* binop *) econstructor...
    - (* fby *)
      econstructor; eauto; repeat rewrite_Forall_forall...
    - (* when *)
      econstructor; eauto; repeat rewrite_Forall_forall...
      eapply sem_var_refines...
    - (* merge *)
      econstructor; eauto; repeat rewrite_Forall_forall...
      eapply sem_var_refines...
    - (* ite *)
      econstructor; eauto; repeat rewrite_Forall_forall...
    - (* app *)
      econstructor; eauto; repeat rewrite_Forall_forall...
    - (* app (reset) *)
      econstructor; eauto; repeat rewrite_Forall_forall...
  Qed.

  Fact sem_equation_refines : forall G H H' b equ,
      Env.refines eq H H' ->
      sem_equation G H b equ ->
      sem_equation G H' b equ.
  Proof with eauto.
    intros G H H' b eq Href Hsem.
    destruct Hsem.
    econstructor.
    + eapply Forall2_impl_In; [| eauto].
      intros. eapply sem_exp_refines...
    + eapply Forall2_impl_In; [| eauto].
      intros. eapply sem_var_refines...
  Qed.

  (** ** Semantic refinement relation between nodes *)
  Section sem_ref.

    (** Functional equivalence for nodes *)
    Definition node_sem_refines G G' f : Prop :=
      (forall ins outs, (sem_node G f ins outs) -> (sem_node G' f ins outs)).

    Fact node_sem_refines_refl : forall G f, node_sem_refines G G f.
    Proof. intros G f ins outs. auto. Qed.

    Fact node_sem_refines_trans : forall G1 G2 G3 f,
        node_sem_refines G1 G2 f ->
        node_sem_refines G2 G3 f ->
        node_sem_refines G1 G3 f.
    Proof.
      intros G1 G2 G3 f H1 H2 ins outs Hsem.
      auto.
    Qed.

    Definition global_sem_refines G G' : Prop :=
      forall f, node_sem_refines G G' f.

    Hint Constructors sem_exp.
    Fact sem_eq_sem_exp : forall G G' H b e vs,
        global_sem_refines G G' ->
        sem_exp G H b e vs ->
        sem_exp G' H b e vs.
    Proof with eauto.
      induction e using exp_ind2; intros vs Heq Hsem; inv Hsem...
      - (* fby *)
        econstructor...
        + repeat rewrite_Forall_forall...
        + repeat rewrite_Forall_forall...
      - (* when *)
        econstructor...
        repeat rewrite_Forall_forall...
      - (* merge *)
        econstructor...
        + repeat rewrite_Forall_forall...
        + repeat rewrite_Forall_forall...
      - (* ite *)
        econstructor...
        + repeat rewrite_Forall_forall...
        + repeat rewrite_Forall_forall...
      - (* app *)
        econstructor...
        + repeat rewrite_Forall_forall...
        + specialize (Heq f (concat ss) vs).
          auto.
      - (* app (reset) *)
        econstructor...
        + repeat rewrite_Forall_forall...
        + intros k. specialize (H13 k).
          specialize (Heq f (List.map (mask k bs) (concat ss)) (List.map (mask k bs) vs)).
          auto.
    Qed.

    Fact sem_eq_sem_equation : forall G G' H b eq,
        global_sem_refines G G' ->
        sem_equation G H b eq ->
        sem_equation G' H b eq.
    Proof.
      intros G G' H b [xs es] Heq Hsem.
      inv Hsem.
      econstructor; eauto.
      eapply Forall2_impl_In; [| eauto].
      intros. eapply sem_eq_sem_exp; eauto.
    Qed.

    Fact global_sem_eq_nil :
      global_sem_refines [] [].
    Proof.
      intros f ins outs Hsem. assumption.
    Qed.

    Fact global_sem_eq_cons : forall G G' n n' f,
        Ordered_nodes (n::G) ->
        Ordered_nodes (n'::G') ->
        n_name n = f ->
        n_name n' = f ->
        global_sem_refines G G' ->
        node_sem_refines (n::G) (n'::G') f ->
        global_sem_refines (n::G) (n'::G').
    Proof with eauto.
      intros G G' n n' f Hord1 Hord2 Hname1 Hname2 Hglob Hnode f0 ins outs Hsem.
      inv Hsem.
      simpl in H0.
      destruct (ident_eqb (n_name n) f0) eqn:Heq.
      + specialize (Hnode ins outs).
        inv H0.
        rewrite ident_eqb_eq in Heq; subst.
        eapply Hnode.
        eapply Snode with (n:=n0)...
        simpl. rewrite ident_eqb_refl...
      + rewrite ident_eqb_neq in Heq.
        apply sem_node_cons'...
        specialize (Hglob f0 ins outs). apply Hglob.
        econstructor...
        rewrite Forall_forall in *. intros.
        eapply sem_equation_global_tl...
        eapply find_node_later_not_Is_node_in in Hord1; eauto.
        intro contra.
        rewrite Is_node_in_Forall in Hord1. rewrite Forall_forall in *.
        apply Hord1 in H4. congruence.
    Qed.

  End sem_ref.

  (** ** The number of streams equals numstreams *)

  Fact sem_exp_numstreams : forall G H b e v,
      wl_exp G e ->
      sem_exp G H b e v ->
      length v = numstreams e.
  Proof with eauto.
    induction e using exp_ind2; intros v Hsem Hwl; inv Hwl; inv Hsem; simpl; auto.
    - (* fby *)
      repeat rewrite_Forall_forall.
      rewrite <- H9. rewrite <- H10.
      unfold annots; rewrite flat_map_concat_map.
      apply concat_length_eq.
      rewrite Forall2_map_2.
      rewrite_Forall_forall.
      rewrite length_annot_numstreams. eapply H0.
      + apply nth_In; congruence.
      + apply H5. apply nth_In; congruence.
      + eapply H6... congruence.
    - (* when *)
      repeat rewrite_Forall_forall.
      rewrite <- H1. rewrite <- H7.
      unfold annots; rewrite flat_map_concat_map.
      apply concat_length_eq.
      rewrite Forall2_map_2.
      rewrite_Forall_forall.
      rewrite length_annot_numstreams. eapply H0; [| |eauto].
      + apply nth_In; congruence.
      + apply H4. apply nth_In; congruence.
      + eapply H5... congruence.
    - (* merge *)
      repeat rewrite_Forall_forall.
      rewrite <- H10. rewrite <- H11.
      unfold annots; rewrite flat_map_concat_map.
      apply concat_length_eq.
      rewrite Forall2_map_2.
      rewrite_Forall_forall.
      rewrite length_annot_numstreams. eapply H0; [| |eauto].
      + apply nth_In; congruence.
      + apply H7. apply nth_In; congruence.
      + eapply H5... congruence.
    - (* ite *)
      repeat rewrite_Forall_forall.
      rewrite <- H11. rewrite <- H15.
      unfold annots; rewrite flat_map_concat_map.
      apply concat_length_eq.
      rewrite Forall2_map_2.
      rewrite_Forall_forall.
      rewrite length_annot_numstreams. eapply H0; [| |eauto].
      + apply nth_In; congruence.
      + apply H7. apply nth_In; congruence.
      + eapply H5... congruence.
    - (* app *)
      inv H11.
      repeat rewrite_Forall_forall.
      rewrite H3 in H7; inv H7.
      unfold idents in H6.
      rewrite <- H6, map_length...
    - (* app (reset) *)
      specialize (H13 0). inv H13.
      repeat rewrite_Forall_forall.
      rewrite H3 in H14; inv H14.
      unfold idents in H5.
      repeat rewrite map_length in *. congruence.
  Qed.

  Corollary sem_exps_numstreams : forall G H b es vs,
      Forall (wl_exp G) es ->
      Forall2 (sem_exp G H b) es vs ->
      length (concat vs) = length (annots es).
  Proof.
    intros G H b es vs Hwt Hsem.
    assert (Forall2 (fun v e => length v = numstreams e) vs es) as Hf.
    { repeat rewrite_Forall_forall.
      eapply sem_exp_numstreams.
      + eapply Hwt. eapply nth_In. congruence.
      + eapply H1; eauto. congruence. }
    clear Hwt Hsem.
    induction Hf; simpl.
    - reflexivity.
    - repeat rewrite app_length.
      f_equal; auto.
      rewrite length_annot_numstreams. assumption.
  Qed.

  (** When we have the semantic for the equations of a node,
      we have a semantic for the internal variables, as well as the outputs *)
  Lemma sem_node_sem_vars : forall G H b vars eqs outs,
      Permutation (vars_defined eqs) (vars ++ outs) ->
      Forall (sem_equation G H b) eqs ->
      exists vs, Forall2 (sem_var H) vars vs.
  Proof.
    induction vars; intros * Hperm Hf.
    - exists []; constructor.
    - specialize (IHvars eqs (a::outs)); simpl in *.
      rewrite Permutation_middle in Hperm.
      specialize (IHvars Hperm Hf) as [vs Hsem].
      symmetry in Hperm. eapply Permutation_in with (x:= a) in Hperm.
      2: eapply in_or_app; right; left; auto.
      unfold vars_defined in Hperm.
      rewrite flat_map_concat_map, in_concat in Hperm; destruct Hperm as [l [Hin Hin']].
      apply in_map_iff in Hin' as [l' [? Hin']]; subst.
      eapply Forall_forall in Hin'; eauto. inv Hin'; simpl in Hin.
      eapply Forall2_in_left in Hin as [v [_ Hsem']]; [|eauto].
      exists (v::vs). constructor; auto.
  Qed.

  Lemma sem_node_sem_outs : forall G H b outs eqs vars,
      Permutation (vars_defined eqs) (vars ++ outs) ->
      Forall (sem_equation G H b) eqs ->
      exists vs, Forall2 (sem_var H) outs vs.
  Proof.
    induction outs; intros * Hperm Hf.
    - exists []; constructor.
    - specialize (IHouts eqs (a::vars)); simpl in *.
      rewrite Permutation_middle in IHouts.
      specialize (IHouts Hperm Hf) as [vs Hsem].
      symmetry in Hperm. eapply Permutation_in with (x:= a) in Hperm.
      2: eapply in_or_app; right; left; auto.
      unfold vars_defined in Hperm.
      rewrite flat_map_concat_map, in_concat in Hperm; destruct Hperm as [l [Hin Hin']].
      apply in_map_iff in Hin' as [l' [? Hin']]; subst.
      eapply Forall_forall in Hin'; eauto. inv Hin'; simpl in Hin.
      eapply Forall2_in_left in Hin as [v [_ Hsem']]; [|eauto].
      exists (v::vs). constructor; auto.
  Qed.

  Corollary sem_node_sem_vars_outs : forall G H b vars outs eqs,
      Permutation (vars_defined eqs) (idents (vars ++ outs)) ->
      Forall (sem_equation G H b) eqs ->
      (exists vs, Forall2 (sem_var H) (idents vars) vs) /\
      (exists os, Forall2 (sem_var H) (idents outs) os).
  Proof.
    intros * Hperm Hf.
    unfold idents in *; rewrite map_app in *; split.
    - eapply sem_node_sem_vars; eauto.
    - eapply sem_node_sem_outs; eauto.
  Qed.

End LSEMANTICS.

Module LSemanticsFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Syn   : LSYNTAX   Ids Op)
       (Lord  : LORDERED  Ids Op Syn)
       (Str   : COINDSTREAMS  Op OpAux)
<: LSEMANTICS Ids Op OpAux Syn Lord Str.
  Include LSEMANTICS Ids Op OpAux Syn Lord Str.
End LSemanticsFun.
