From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Streams.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Setoid.
From Coq Require Import Morphisms.

From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import CommonProgram.
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
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Syn   : LSYNTAX       Ids Op OpAux Cks)
       (Import Lord  : LORDERED      Ids Op OpAux Cks Syn)
       (Import Str   : COINDSTREAMS  Ids Op OpAux Cks).

  CoInductive fby1: value -> Stream svalue -> Stream svalue -> Stream svalue -> Prop :=
  | Fby1A:
      forall v xs ys rs,
        fby1 v xs ys rs ->
        fby1 v (absent ⋅ xs) (absent ⋅ ys) (absent ⋅ rs)
  | Fby1P:
      forall v w s xs ys rs,
        fby1 s xs ys rs ->
        fby1 v (present w ⋅ xs) (present s ⋅ ys) (present v ⋅ rs).

  CoInductive fby: Stream svalue -> Stream svalue -> Stream svalue -> Prop :=
  | FbyA:
      forall xs ys rs,
        fby xs ys rs ->
        fby (absent ⋅ xs) (absent ⋅ ys) (absent ⋅ rs)
  | FbyP:
      forall x y xs ys rs,
        fby1 y xs ys rs ->
        fby (present x ⋅ xs) (present y ⋅ ys) (present x ⋅ rs).

  CoInductive arrow1: Stream svalue -> Stream svalue -> Stream svalue -> Prop :=
  | Arrow1A: forall xs ys rs,
      arrow1 xs ys rs ->
      arrow1 (absent ⋅ xs) (absent ⋅ ys) (absent ⋅ rs)
  | Arrow1P: forall x y xs ys rs,
      arrow1 xs ys rs ->
      arrow1 (present x ⋅ xs) (present y ⋅ ys) (present y ⋅ rs).

  CoInductive arrow: Stream svalue -> Stream svalue -> Stream svalue -> Prop :=
  | ArrowA: forall xs ys rs,
      arrow xs ys rs ->
      arrow (absent ⋅ xs) (absent ⋅ ys) (absent ⋅ rs)
  | ArrowP: forall x y xs ys rs,
      arrow1 xs ys rs ->
      arrow (present x ⋅ xs) (present y ⋅ ys) (present x ⋅ rs).

  Section NodeSemantics.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Inductive sem_exp
      : history -> Stream bool -> exp -> list (Stream svalue) -> Prop :=
    | Sconst:
        forall H b c cs,
          cs ≡ const b c ->
          sem_exp H b (Econst c) [cs]

    | Senum:
        forall H b k ty es,
          es ≡ enum b k ->
          sem_exp H b (Eenum k ty) [es]

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

    | Sarrow:
        forall H b e0s es anns s0ss sss os,
          Forall2 (sem_exp H b) e0s s0ss ->
          Forall2 (sem_exp H b) es sss ->
          Forall3 arrow (concat s0ss) (concat sss) os ->
          sem_exp H b (Earrow e0s es anns) os

    | Swhen:
        forall H b x s k es lann ss os,
          Forall2 (sem_exp H b) es ss ->
          sem_var H x s ->
          Forall2 (fun s' => when k s' s) (concat ss) os ->
          sem_exp H b (Ewhen es x k lann) os

    | Smerge:
        forall H b x tx s es lann vs os,
          sem_var H x s ->
          Forall2 (Forall2 (sem_exp H b)) es vs ->
          Forall2Transpose (merge s) (List.map (@concat _) vs) os ->
          sem_exp H b (Emerge (x, tx) es lann) os

    | Scase:
        forall H b e s es d lann vs vd os,
          sem_exp H b e [s] ->
          Forall2 (fun oes vs => forall es, oes = Some es -> Forall2 (sem_exp H b) es vs) es vs ->
          Forall2 (fun oes vs => oes = None -> Forall2 EqSts vs vd) es vs ->
          Forall2 (sem_exp H b) d vd ->
          Forall2Transpose (case s) (List.map (@concat _) vs) os ->
          sem_exp H b (Ecase e es d lann) os

    | Sapp:
        forall H b f es er lann ss os rs bs,
          Forall2 (sem_exp H b) es ss ->
          Forall2 (fun e r => sem_exp H b e [r]) er rs ->
          bools_ofs rs bs ->
          (forall k, sem_node f (List.map (maskv k bs) (concat ss)) (List.map (maskv k bs) os)) ->
          sem_exp H b (Eapp f es er lann) os

    with sem_equation: history -> Stream bool -> equation -> Prop :=
      Seq:
        forall H b xs es ss,
          Forall2 (sem_exp H b) es ss ->
          Forall2 (sem_var H) xs (concat ss) ->
          sem_equation H b (xs, es)

    with sem_block: history -> Stream bool -> block -> Prop :=
    | Sbeq:
        forall H b eq,
          sem_equation H b eq ->
          sem_block H b (Beq eq)
    | Sreset:
        forall H b blocks er sr r,
          sem_exp H b er [sr] ->
          bools_of sr r ->
          (forall k, Forall (sem_block (mask_hist k r H) (maskb k r b)) blocks) ->
          sem_block H b (Breset blocks er)
    | Slocal:
        forall H H' b locs blks,
          (forall x vs, sem_var H' x vs -> ~InMembers x locs -> sem_var H x vs) ->
          Forall (sem_block H' b) blks ->
          sem_block H b (Blocal locs blks)

    with sem_node: ident -> list (Stream svalue) -> list (Stream svalue) -> Prop :=
      Snode:
        forall f ss os n H b,
          find_node f G = Some n ->
          Forall2 (sem_var H) (idents n.(n_in)) ss ->
          Forall2 (sem_var H) (idents n.(n_out)) os ->
          sem_block H b n.(n_block) ->
          b = clocks_of ss ->
          sem_node f ss os.

  End NodeSemantics.

  (** Custom induction schemes *)

  Section sem_exp_ind2.
    Context (PSyn : block -> Prop).
    Context (prefs : PS.t).
    Variable G : @global PSyn prefs.

    Variable P_exp : history -> Stream bool -> exp -> list (Stream svalue) -> Prop.
    Variable P_equation : history -> Stream bool -> equation -> Prop.
    Variable P_block : history -> Stream bool -> block -> Prop.
    Variable P_node : ident -> list (Stream svalue) -> list (Stream svalue) -> Prop.

    Hypothesis ConstCase:
      forall H b c cs,
        cs ≡ const b c ->
        P_exp H b (Econst c) [cs].

    Hypothesis EnumCase:
      forall H b k ty es,
        es ≡ enum b k ->
        P_exp H b (Eenum k ty) [es].

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

    Hypothesis ArrowCase:
      forall H b e0s es anns s0ss sss os,
        Forall2 (sem_exp G H b) e0s s0ss ->
        Forall2 (P_exp H b) e0s s0ss ->
        Forall2 (sem_exp G H b) es sss ->
        Forall2 (P_exp H b) es sss ->
        Forall3 arrow (concat s0ss) (concat sss) os ->
        P_exp H b (Earrow e0s es anns) os.

    Hypothesis WhenCase:
      forall H b x s k es lann ss os,
        Forall2 (sem_exp G H b) es ss ->
        Forall2 (P_exp H b) es ss ->
        sem_var H x s ->
        Forall2 (fun s' => when k s' s) (concat ss) os ->
        P_exp H b (Ewhen es x k lann) os.

    Hypothesis MergeCase:
      forall H b x tx s es lann vs os,
        sem_var H x s ->
        Forall2 (Forall2 (sem_exp G H b)) es vs ->
        Forall2 (Forall2 (P_exp H b)) es vs ->
        Forall2Transpose (merge s) (List.map (@concat _) vs) os ->
        P_exp H b (Emerge (x, tx) es lann) os.

    Hypothesis CaseCase:
      forall H b e s es d lann vs vd os,
        sem_exp G H b e [s] ->
        P_exp H b e [s] ->
        Forall2 (fun oes vs => forall es, oes = Some es -> Forall2 (sem_exp G H b) es vs) es vs ->
        Forall2 (fun oes vs => forall es, oes = Some es -> Forall2 (P_exp H b) es vs) es vs ->
        Forall2 (fun oes vs => oes = None -> Forall2 EqSts vs vd) es vs ->
        Forall2 (sem_exp G H b) d vd ->
        Forall2 (P_exp H b) d vd ->
        Forall2Transpose (case s) (List.map (@concat _) vs) os ->
        P_exp H b (Ecase e es d lann) os.

    Hypothesis AppCase:
      forall H b f es er lann ss os sr bs,
        Forall2 (sem_exp G H b) es ss ->
        Forall2 (P_exp H b) es ss ->
        Forall2 (fun e r => sem_exp G H b e [r]) er sr ->
        Forall2 (fun e r => P_exp H b e [r]) er sr ->
        bools_ofs sr bs ->
        (forall k, sem_node G f (List.map (maskv k bs) (concat ss)) (List.map (maskv k bs) os)
              /\ P_node f (List.map (maskv k bs) (concat ss)) (List.map (maskv k bs) os)) ->
        P_exp H b (Eapp f es er lann) os.

    Hypothesis Equation:
      forall H b xs es ss,
        Forall2 (sem_exp G H b) es ss ->
        Forall2 (P_exp H b) es ss ->
        Forall2 (sem_var H) xs (concat ss) ->
        P_equation H b (xs, es).

    Hypothesis BeqCase:
      forall H b eq,
        sem_equation G H b eq ->
        P_equation H b eq ->
        P_block H b (Beq eq).

    Hypothesis BresetCase:
      forall H b blocks er sr r,
        sem_exp G H b er [sr] ->
        P_exp H b er [sr] ->
        bools_of sr r ->
        (forall k, Forall (sem_block G (mask_hist k r H) (maskb k r b)) blocks /\
              Forall (P_block (mask_hist k r H) (maskb k r b)) blocks) ->
        P_block H b (Breset blocks er).

    Hypothesis BlocalCase:
      forall H H' b locs blks,
        (forall x vs, sem_var H' x vs -> ~(InMembers x locs) -> sem_var H x vs) ->
        Forall (sem_block G H' b) blks ->
        Forall (P_block H' b) blks ->
        P_block H b (Blocal locs blks).

    Hypothesis Node:
      forall f ss os n H b,
        find_node f G = Some n ->
        Forall2 (sem_var H) (idents n.(n_in)) ss ->
        Forall2 (sem_var H) (idents n.(n_out)) os ->
        sem_block G H b n.(n_block) ->
        P_block H b n.(n_block) ->
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
             (H: history) (b: Stream bool) (e: exp) (ss: list (Stream svalue))
             (Sem: sem_exp G H b e ss)
             {struct Sem}
      : P_exp H b e ss
    with sem_equation_ind2
           (H: history) (b: Stream bool) (e: equation)
           (Sem: sem_equation G H b e)
           {struct Sem}
         : P_equation H b e
    with sem_block_ind2
           (H: history) (b: Stream bool) (d: block)
           (Sem: sem_block G H b d)
           {struct Sem}
         : P_block H b d
    with sem_node_ind2
           (f: ident) (ss os: list (Stream svalue))
           (Sem: sem_node G f ss os)
           {struct Sem}
         : P_node f ss os.
    Proof.
      - destruct Sem.
        + apply ConstCase; eauto.
        + apply EnumCase; eauto.
        + apply VarCase; auto.
        + eapply UnopCase; eauto.
        + eapply BinopCase; eauto.
        + eapply FbyCase; eauto; clear H2; SolveForall.
        + eapply ArrowCase; eauto; clear H2; SolveForall.
        + eapply WhenCase; eauto; clear H2; SolveForall.
        + eapply MergeCase; eauto; clear H2; SolveForall.
          constructor; auto. SolveForall.
        + eapply CaseCase; eauto.
          * clear - sem_exp_ind2 H0.
            SolveForall. constructor; auto.
            intros; subst. specialize (H0 _ eq_refl). SolveForall.
          * clear - sem_exp_ind2 H2.
            SolveForall.
        + eapply AppCase; eauto; clear H2 H3; SolveForall.
      - destruct Sem.
        eapply Equation with (ss:=ss); eauto; clear H1; SolveForall.
      - destruct Sem.
        + apply BeqCase; eauto.
        + eapply BresetCase; eauto.
          intros k. specialize (H2 k). split; eauto. SolveForall.
        + eapply BlocalCase; eauto.
          SolveForall.
      - destruct Sem.
        eapply Node; eauto.
    Qed.

  End sem_exp_ind2.

  (** ** Properties of the [global] environment *)

  Lemma sem_block_cons {PSyn prefs} :
    forall (nd : @node PSyn prefs) nds enums bck H bk,
      Ordered_nodes (Global enums (nd::nds))
      -> sem_block (Global enums (nd::nds)) H bk bck
      -> ~Is_node_in_block nd.(n_name) bck
      -> sem_block (Global enums nds) H bk bck.
  Proof.
    intros * Hord Hsem Hnf.
    revert Hnf.
    induction Hsem using sem_block_ind2
      with
        (P_block := fun bk H d => ~Is_node_in_block nd.(n_name) d
                                     -> sem_block (Global enums0 nds) bk H d)
        (P_equation := fun bk H eq => ~Is_node_in_eq nd.(n_name) eq
                                   -> sem_equation (Global enums0 nds) bk H eq)
        (P_exp := fun H bk e ss => ~ Is_node_in_exp nd.(n_name) e
                                -> sem_exp (Global enums0 nds) H bk e ss)
        (P_node := fun f xs ys => nd.(n_name) <> f -> sem_node (Global enums0 nds) f xs ys);
      try (now econstructor; eauto); intros.
    - econstructor; eauto. apply IHHsem.
      intro. destruct H3. constructor. auto.
    - econstructor; eauto.
      apply IHHsem. intro. destruct H5. constructor. auto.
      apply IHHsem0. intro. destruct H5. constructor. auto.
    - econstructor; eauto;
        (eapply Forall2_impl_In; [|eauto]; intros;
         eapply H8; intro; apply H5; constructor);
        [left|right]; apply Exists_exists; eauto.
    - econstructor; eauto;
        (eapply Forall2_impl_In; [|eauto]; intros;
         eapply H8; intro; apply H5; constructor);
        [left|right]; apply Exists_exists; eauto.
    - econstructor; eauto.
      eapply Forall2_impl_In; [|eauto]; intros.
      apply H7; intro contra.
      apply H4; constructor. apply Exists_exists; eauto.
    - econstructor; eauto;
        (eapply Forall2_impl_In; [|eauto]; intros;
         eapply Forall2_impl_In; [|eauto]; intros;
         eapply H10; intro; apply H4;
         constructor;
         do 2 (apply Exists_exists; repeat esplit; eauto)).
    - econstructor; eauto.
      eapply IHHsem.
      2:(clear H3; do 2 (eapply Forall2_impl_In; [|eauto]; intros; subst);
         apply H12).
      3:eapply Forall2_impl_In; [|eauto]; intros; apply H10.
      1-3:(intro; apply H7; constructor; auto; right).
      + left. eapply Exists_exists. exists (Some es0).
        repeat esplit; eauto. eapply Exists_exists; eauto.
      + right. eapply Exists_exists; eauto.
    - inv Hord.
      econstructor; eauto.
      + eapply Forall2_impl_In in H1; [|eauto]; eauto.
        intros * ?? Sem. eapply Sem; intro. take (~ _) and apply it.
        constructor; left. eapply Exists_exists; eauto.
      + eapply Forall2_impl_In in H3; eauto. intros * ?? Hi. simpl. apply Hi. intro.
        take (~ _) and apply it. constructor. right. eapply Exists_exists; eauto.
      + intro k. take (forall k, _ /\ _) and specialize (it k) as (? & Hk).
        apply Hk. intro Hn. subst. take (~ _) and apply it. eapply INEapp2.
    - econstructor; eauto.
      clear H0 H2. induction H1; eauto.
      constructor. apply H0. intro. destruct H3. now constructor.
      apply IHForall2. intro. destruct H3. unfold Is_node_in_eq.
      simpl. rewrite Exists_cons. right. auto.
    - econstructor.
      eapply IHHsem. intro. apply H1. constructor; auto.
    - econstructor; eauto.
      + eapply IHHsem; intro. eapply H3.
        constructor; auto.
      + intros k. specialize (H2 k) as (Hsem&Hsem').
        eapply Forall_Forall in Hsem; eauto. clear Hsem'.
        eapply Forall_impl_In; [|eauto]; intros ? Hin (?&?).
        eapply H2. intro.
        eapply H3. constructor; left.
        eapply Exists_exists; eauto.
    - econstructor; eauto.
      rewrite Forall_forall in *; intros.
      eapply H2; eauto.
      contradict H3. constructor. eapply Exists_exists; eauto.
    - rewrite find_node_other with (1:=H4) in H0.
      eapply Snode; eauto.
      eapply IHHsem; eauto.
      apply find_node_later_not_Is_node_in with (1:=Hord) in H0; auto.
  Qed.

  Corollary sem_node_cons {PSyn prefs} :
    forall (nd : @node PSyn prefs) nds enums f xs ys,
      Ordered_nodes (Global enums (nd::nds))
      -> sem_node (Global enums (nd::nds)) f xs ys
      -> nd.(n_name) <> f
      -> sem_node (Global enums nds) f xs ys.
  Proof.
    intros * Hord Hsem Hnf.
    inv Hsem.
    rewrite find_node_other with (1:=Hnf) in H0.
    econstructor; eauto.
    eapply sem_block_cons; eauto.
    eapply find_node_later_not_Is_node_in; eauto.
  Qed.

  Lemma sem_block_cons' {PSyn prefs} :
    forall (nd : @node PSyn prefs) nds enums bck H bk,
      Ordered_nodes (Global enums (nd::nds))
      -> sem_block (Global enums nds) H bk bck
      -> ~Is_node_in_block nd.(n_name) bck
      -> sem_block (Global enums (nd::nds)) H bk bck.
  Proof.
    intros * Hord Hsem Hnf.
    revert Hnf.
    induction Hsem using sem_block_ind2
      with
        (P_block := fun bk H d => ~Is_node_in_block nd.(n_name) d
                                     -> sem_block (Global enums0 (nd::nds)) bk H d)
        (P_equation := fun bk H eq => ~Is_node_in_eq nd.(n_name) eq
                                   -> sem_equation (Global enums0 (nd::nds)) bk H eq)
        (P_exp := fun H bk e ss => ~ Is_node_in_exp nd.(n_name) e
                                -> sem_exp (Global enums0 (nd::nds)) H bk e ss)
        (P_node := fun f xs ys => nd.(n_name) <> f -> sem_node (Global enums0 (nd::nds)) f xs ys);
      try (now econstructor; eauto); intros.
    - econstructor; eauto. apply IHHsem.
      intro. destruct H3. constructor. auto.
    - econstructor; eauto.
      apply IHHsem. intro. destruct H5. constructor. auto.
      apply IHHsem0. intro. destruct H5. constructor. auto.
    - econstructor; eauto;
        (eapply Forall2_impl_In; [|eauto]; intros;
         eapply H8; intro; apply H5; constructor);
        [left|right]; apply Exists_exists; eauto.
    - econstructor; eauto;
        (eapply Forall2_impl_In; [|eauto]; intros;
         eapply H8; intro; apply H5; constructor);
        [left|right]; apply Exists_exists; eauto.
    - econstructor; eauto.
      eapply Forall2_impl_In; [|eauto]; intros.
      apply H7; intro contra.
      apply H4; constructor. apply Exists_exists; eauto.
    - econstructor; eauto;
        (eapply Forall2_impl_In; [|eauto]; intros;
         eapply Forall2_impl_In; [|eauto]; intros;
         eapply H10; intro; apply H4;
         constructor;
         do 2 (apply Exists_exists; repeat esplit; eauto)).
    - econstructor; eauto.
      eapply IHHsem.
      2:(clear H3; do 2 (eapply Forall2_impl_In; [|eauto]; intros; subst);
         apply H12).
      3:eapply Forall2_impl_In; [|eauto]; intros; apply H10.
      1-3:(intro; apply H7; constructor; auto; right).
      + left. eapply Exists_exists. exists (Some es0).
        repeat esplit; eauto. eapply Exists_exists; eauto.
      + right. eapply Exists_exists; eauto.
    - inv Hord.
      econstructor; eauto.
      + eapply Forall2_impl_In in H1; [|eauto]; eauto.
        intros * ?? Sem. eapply Sem; intro. take (~ _) and apply it.
        constructor; left. eapply Exists_exists; eauto.
      + eapply Forall2_impl_In in H3; eauto. intros * ?? Hi. simpl. apply Hi. intro.
        take (~ _) and apply it. constructor. right. eapply Exists_exists; eauto.
      + intro k. take (forall k, _ /\ _) and specialize (it k) as (? & Hk).
        apply Hk. intro Hn. subst. take (~ _) and apply it. eapply INEapp2.
    - econstructor; eauto.
      clear H0 H2. induction H1; eauto.
      constructor. apply H0. intro. destruct H3. now constructor.
      apply IHForall2. intro. destruct H3. unfold Is_node_in_eq.
      simpl. rewrite Exists_cons. right. auto.
    - econstructor.
      eapply IHHsem. intro. apply H1. constructor; auto.
    - econstructor; eauto.
      + eapply IHHsem; intro. eapply H3.
        constructor; auto.
      + intros k. specialize (H2 k) as (Hsem&Hsem').
        eapply Forall_Forall in Hsem; eauto. clear Hsem'.
        eapply Forall_impl_In; [|eauto]; intros ? Hin (?&?).
        eapply H2. intro.
        eapply H3. constructor; left.
        eapply Exists_exists; eauto.
    - econstructor; eauto.
      rewrite Forall_forall in *; intros.
      eapply H2; eauto.
      contradict H3. constructor. eapply Exists_exists; eauto.
    - econstructor; eauto.
      + erewrite find_node_other; eauto.
      + eapply IHHsem; eauto.
        apply find_node_later_not_Is_node_in with (1:=Hord) in H0; auto.
  Qed.

  Corollary sem_node_cons' {PSyn prefs} :
    forall (nd : @node PSyn prefs) nds enums f xs ys,
      Ordered_nodes (Global enums (nd::nds))
      -> sem_node (Global enums nds) f xs ys
      -> nd.(n_name) <> f
      -> sem_node (Global enums (nd::nds)) f xs ys.
  Proof.
    intros * Hord Hsem Hneq.
    inv Hsem.
    econstructor; eauto.
    erewrite <-find_node_other in H0; eauto.
    eapply sem_block_cons'; eauto.
    eapply find_node_later_not_Is_node_in in H0; eauto.
  Qed.

  Add Parametric Morphism v : (fby1 v)
      with signature @EqSt _ ==> @EqSt _ ==> @EqSt _ ==> Basics.impl
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
      with signature @EqSt _ ==> @EqSt _ ==> @EqSt _ ==> Basics.impl
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

  Add Parametric Morphism : arrow1
      with signature @EqSt _ ==> @EqSt _ ==> @EqSt _ ==> Basics.impl
        as arrow1_EqSt.
  Proof.
    cofix Cofix.
    intros cs cs' Ecs xs xs' Exs ys ys' Eys H.
    destruct cs' as [[]], xs' as [[]], ys' as [[]];
      inv H; inv Ecs; inv Exs; inv Eys; simpl in *;
        try discriminate.
    + constructor; eapply Cofix; eauto.
    + inv H. inv H2. inv H4. econstructor.
      eapply Cofix; eauto.
  Qed.

  Add Parametric Morphism : arrow
      with signature @EqSt _ ==> @EqSt _ ==> @EqSt _ ==> Basics.impl
        as arrow_EqSt.
  Proof.
    cofix Cofix.
    intros cs cs' Ecs xs xs' Exs ys ys' Eys H.
    destruct cs' as [[]], xs' as [[]], ys' as [[]];
      inv H; inv Ecs; inv Exs; inv Eys; simpl in *;
        try discriminate.
    + constructor; eapply Cofix; eauto.
    + inv H. inv H2. inv H4. econstructor.
      rewrite <- H1, <- H3, <- H5; auto.
  Qed.

  Add Parametric Morphism k : (when k)
      with signature @EqSt svalue ==> @EqSt svalue ==> @EqSt svalue ==> Basics.impl
        as when_EqSt.
  Proof.
    revert k.
    cofix Cofix.
    intros k cs cs' Ecs xs xs' Exs ys ys' Eys H.
    destruct cs' as [[]], xs' as [[]], ys' as [[]];
      inv H; inv Ecs; inv Exs; inv Eys; simpl in *;
        try discriminate.
    + constructor; eapply Cofix; eauto.
    + inv H. inv H3. inv H5. constructor; auto. eapply Cofix; eauto.
    + inv H. inv H2. inv H4. econstructor. eapply Cofix; eauto.
  Qed.

  Add Parametric Morphism : merge
      with signature @EqSt svalue ==> @EqSts svalue ==> @EqSt svalue ==> Basics.impl
        as merge_EqSt.
  Proof.
    cofix Cofix.
    intros cs cs' Ecs xs xs' Exs zs zs' Ezs H.
    destruct cs' as [[]], zs' as [[]];
      inv H; inv Ecs; inv Ezs; simpl in *;
        try discriminate.
    - constructor.
      + eapply Cofix; eauto. apply map_st_EqSt; auto.
        intros * Eq. rewrite Eq. reflexivity.
      + eapply Forall_EqSt; eauto.
        intros ?? Heq ?. rewrite <-Heq; auto.
    - inv H. inv H4. econstructor; eauto.
      + eapply Cofix; eauto. apply map_st_EqSt; auto.
        intros * Eq. rewrite Eq. reflexivity.
      + rewrite <-Exs; eauto.
  Qed.

  Add Parametric Morphism : case
      with signature @EqSt svalue ==> @EqSts svalue ==> @EqSt svalue ==> Basics.impl
        as case_EqSt.
  Proof.
    cofix Cofix.
    intros cs cs' Ecs xs xs' Exs zs zs' Ezs H.
    destruct cs' as [[]], zs' as [[]];
      inv H; inv Ecs; inv Ezs; simpl in *;
        try discriminate.
    - constructor.
      + eapply Cofix; eauto. apply map_st_EqSt; auto.
        intros * Eq. rewrite Eq. reflexivity.
      + eapply Forall_EqSt; eauto.
        intros ?? Heq ?. rewrite <-Heq; auto.
    - inv H. inv H4. econstructor; eauto.
      + eapply Cofix; eauto. apply map_st_EqSt; auto.
        intros * Eq. rewrite Eq. reflexivity.
      + eapply Forall_EqSt; eauto.
        intros ?? Heq ?. rewrite <-Heq; auto.
      + rewrite <-Exs; eauto.
  Qed.

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

  Add Parametric Morphism : const
      with signature @EqSt bool ==> eq ==> @EqSt svalue
        as const_EqSt.
  Proof.
    cofix Cofix; intros b b' Eb.
    unfold_Stv b; unfold_Stv b';
      constructor; inv Eb; simpl in *; try discriminate; auto.
  Qed.

  Add Parametric Morphism : enum
      with signature @EqSt bool ==> eq ==> @EqSt svalue
        as enum_EqSt.
  Proof.
    cofix Cofix; intros b b' Eb.
    unfold_Stv b; unfold_Stv b';
      constructor; inv Eb; simpl in *; try discriminate; auto.
  Qed.

  Add Parametric Morphism : sem_var
      with signature Env.Equiv (@EqSt _) ==> eq ==> @EqSt svalue ==> Basics.impl
        as sem_var_EqSt.
  Proof.
    intros H H' EH x xs xs' E; intro Sem; inv Sem.
    eapply Env.Equiv_orel in EH. rewrite H1 in EH. inv EH.
    econstructor; eauto.
    - symmetry in H3. eapply H3.
    - now rewrite <-E, H2, H4.
  Qed.

  Add Parametric Morphism {PSyn prefs} (G : @global PSyn prefs) : (sem_exp G)
      with signature Env.Equiv (@EqSt _) ==> @EqSt bool ==> eq ==> @EqSts svalue ==> Basics.impl
        as sem_exp_morph.
  Proof.
    intros H H' EH b b' Eb e xs xs' Exs Sem.
    revert H' b' xs' EH Eb Exs; induction Sem using sem_exp_ind2 with
                                    (P_equation := fun H b e => True)
                                    (P_block := fun H b d => True)
                                    (P_node := fun i xs ys => forall ys', EqSts ys ys' -> sem_node G i xs ys');
    auto; intros.
    - inv Exs; take (Forall2 _ _ _) and inv it.
      econstructor; rewrite <-Eb; etransitivity; eauto; now symmetry.
    - inv Exs; take (Forall2 _ _ _) and inv it.
      econstructor; rewrite <-Eb; etransitivity; eauto; now symmetry.
    - inv Exs; take (Forall2 _ _ _) and inv it.
      constructor; now rewrite <-EH, <-H3.
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
    - econstructor.
      + eapply Forall2_impl_In; [|apply H1].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + eapply Forall2_impl_In; [|apply H3].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + eapply Forall3_EqSt; eauto. solve_proper.
    - econstructor; eauto.
      + eapply Forall2_impl_In; [|apply H1].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + rewrite <-EH; eauto.
      + eapply Forall2_EqSt; eauto. solve_proper.
    - econstructor; eauto.
      + rewrite <-EH; eauto.
      + do 2 (eapply Forall2_impl_In; [|eauto]; intros); simpl in *.
        eapply H9; eauto. reflexivity.
      + eapply Forall2Transpose_EqSt; eauto. solve_proper.
    - econstructor; eauto.
      + eapply IHSem; eauto. reflexivity.
      + clear H2. do 2 (eapply Forall2_impl_In; [|eauto]; intros; subst).
        eapply H10; eauto. reflexivity.
      + eapply Forall2_impl_In; [|eauto]; intros.
        eapply H8; eauto. reflexivity.
      + eapply Forall2Transpose_EqSt; eauto. solve_proper.
    - econstructor; eauto.
      + eapply Forall2_impl_In; [|apply H1].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + eapply Forall2_impl_In; [|apply H3].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + intro k; specialize (H5 k); destruct H5 as (?&Hr).
        apply Hr.
        apply map_st_EqSt_Proper; auto.
        intros ?? ->; reflexivity.

    - econstructor; eauto.
      eapply Forall2_EqSt; eauto. solve_proper.
  Qed.

  Add Parametric Morphism {PSyn prefs} (G : @global PSyn prefs) : (sem_equation G)
      with signature Env.Equiv (@EqSt _) ==> @EqSt bool ==> eq ==> Basics.impl
        as sem_equation_morph.
  Proof.
    unfold Basics.impl; intros H H' EH xs xs' Exss eq Hsem.
    inversion_clear Hsem as [????? Hseme Hsemv]. econstructor; eauto.
    - eapply Forall2_impl_In; [|eauto]; intros.
      erewrite <-Exss, <-EH; eauto.
    - eapply Forall2_impl_In; [|eauto]; intros.
      now rewrite <-EH.
  Qed.

  Add Parametric Morphism {PSyn prefs} (G : @global PSyn prefs) : (sem_block G)
      with signature Env.Equiv (@EqSt _) ==> @EqSt bool ==> eq ==> Basics.impl
        as sem_block_morph.
  Proof.
    unfold Basics.impl; intros H H' EH b b' Eb d Sem.
    revert H' b' EH Eb; induction Sem using sem_block_ind2
      with (P_exp := fun _ _ _ _ => True)
           (P_equation := fun _ _ _ => True)
           (P_node := fun _ _ _ => True); intros; auto.
    - constructor. now rewrite <-EH, <-Eb.
    - econstructor; eauto.
      + now rewrite <-EH, <-Eb.
      + intros k. specialize (H2 k) as (Hsem&Hsem').
        eapply Forall_Forall in Hsem; eauto. clear Hsem'.
        eapply Forall_impl; [|eauto].
        intros ? (?&?). eapply H2; eauto.
        * now rewrite <-EH.
        * now rewrite <-Eb.
    - eapply Slocal with (H'1:=H'); eauto.
      + intros * ??. rewrite <-EH; eauto.
      + rewrite Forall_forall in *; intros.
        eapply H2; eauto. reflexivity.
  Qed.

  Add Parametric Morphism {PSyn prefs} (G : @global PSyn prefs) : (sem_node G)
      with signature eq ==> @EqSts svalue ==> @EqSts svalue ==> Basics.impl
        as sem_node_morph.
  Proof.
    unfold Basics.impl; intros f xss xss' Exss yss yss' Eyss Sem.
    induction Sem.
    subst.
    econstructor; try reflexivity; eauto.
    + instantiate (1 := H). now rewrite <-Exss.
    + now rewrite <-Eyss.
    + now rewrite <-Exss.
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
  (** If a new environment [refines] the previous one, it gives the same semantics
      to variables and therefore expressions, equations dans nodes *)

  Fact refines_eq_EqSt : forall H H' ,
      Env.refines eq H H' ->
      Env.refines (@EqSt svalue) H H'.
  Proof.
    intros * Href ?? Hfind.
    eapply Href in Hfind as (?&?&Hfind); subst.
    rewrite Hfind. do 2 esplit; eauto.
    reflexivity.
  Qed.

  Fact sem_var_refines : forall H H' id v,
      Env.refines (@EqSt _) H H' ->
      sem_var H id v ->
      sem_var H' id v.
  Proof.
    intros H H' id v Href Hsem.
    destruct Hsem.
    unfold Env.MapsTo in H0. eapply Href in H0 as (?&?&Hfind).
    econstructor; eauto.
    etransitivity; eauto.
  Qed.

  Hint Resolve nth_In.
  Fact sem_exp_refines {PSyn prefs} : forall (G : @global PSyn prefs) b e H H' v,
      Env.refines (@EqSt _) H H' ->
      sem_exp G H b e v ->
      sem_exp G H' b e v.
  Proof with eauto.
    induction e using exp_ind2; intros Hi Hi' v Href Hsem; inv Hsem.
    - (* const *) constructor...
    - (* enum *) constructor...
    - (* var *)
      constructor. eapply sem_var_refines...
    - (* unop *) econstructor...
    - (* binop *) econstructor...
    - (* fby *)
      econstructor; eauto; repeat rewrite_Forall_forall...
    - (* arrow *)
      econstructor; eauto; repeat rewrite_Forall_forall...
    - (* when *)
      econstructor; eauto; repeat rewrite_Forall_forall...
      eapply sem_var_refines...
    - (* merge *)
      econstructor; eauto.
      eapply sem_var_refines...
      do 2 (eapply Forall2_impl_In; [|eauto]; intros).
      do 2 (eapply Forall_forall in H; eauto).
    - (* ite *)
      econstructor; eauto.
      + clear H11. do 2 (eapply Forall2_impl_In; [|eauto]; intros; subst).
        do 2 (eapply Forall_forall in H; eauto; simpl in * ).
      + eapply Forall2_impl_In; [|eauto]; intros.
        eapply Forall_forall in H0; eauto.
    - (* app *)
      econstructor; eauto; repeat rewrite_Forall_forall...
  Qed.

  Fact sem_equation_refines {PSyn prefs} : forall (G : @global PSyn prefs) H H' b equ,
      Env.refines (@EqSt _) H H' ->
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

  Add Parametric Morphism {PSyn prefs} (G: @global PSyn prefs) : (sem_block G)
      with signature (Env.Equiv (@EqSt _) ==> eq ==> eq ==> Basics.impl)
        as sem_block_Equiv.
  Proof.
    intros Hi1 Hi2 HH bs blk. revert Hi1 Hi2 HH bs.
    induction blk using block_ind2; intros * HH * Hsem; inv Hsem.
    - (* equation *)
      constructor. eapply sem_equation_refines; [|eauto].
      now rewrite HH.
    - (* reset *)
      econstructor; eauto.
      + eapply sem_exp_refines; [|eauto]. now rewrite HH.
      + intros k. specialize (H7 k).
        rewrite Forall_forall in *. intros.
        eapply H; eauto.
        eapply Env.map_Equiv; eauto.
        intros ?? Heq. now rewrite Heq.
    - (* locals *)
      econstructor; [|eauto].
      intros * ??. rewrite <-HH; eauto.
  Qed.

  Fact sem_block_refines {PSyn prefs} : forall (G: @global PSyn prefs) d H H' b,
      Env.refines (@EqSt _) H H' ->
      sem_block G H b d ->
      sem_block G H' b d.
  Proof.
    induction d using block_ind2; intros * Href Hsem; inv Hsem.
    - (* equation *)
      econstructor; eauto using sem_equation_refines.
    - (* reset *)
      econstructor; eauto using sem_exp_refines.
      intros k. specialize (H8 k).
      rewrite Forall_forall in *. intros ? Hin.
      eapply H. 1,3:eauto.
      eapply Env.refines_map; eauto.
      intros ?? Heq. rewrite Heq. reflexivity.
    - (* locals *)
      econstructor; [|eauto].
      intros ?? Hv Hnin. eapply sem_var_refines; eauto.
  Qed.

  (** ** Semantic refinement relation between nodes *)

  Section props.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable (G : @global PSyn prefs).

    (** The number of streams generated by an expression [e] equals [numstreams e] *)

    Fact sem_exp_numstreams : forall H b e v,
        wl_exp G e ->
        sem_exp G H b e v ->
        length v = numstreams e.
    Proof with eauto.
      induction e using exp_ind2; intros v Hsem Hwl; inv Hwl; inv Hsem; simpl; auto.
      - (* fby *)
        repeat rewrite_Forall_forall.
        rewrite <- H9, <- H10.
        unfold annots; rewrite flat_map_concat_map.
        apply concat_length_eq.
        rewrite Forall2_map_2.
        rewrite_Forall_forall.
        rewrite length_annot_numstreams. eapply H0.
        + apply nth_In; congruence.
        + apply H5. apply nth_In; congruence.
        + eapply H6... congruence.
      - (* arrow *)
        repeat rewrite_Forall_forall.
        rewrite <- H9, <- H10.
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
        eapply Forall2Transpose_length in H10; rewrite Forall_map in H10.
        eapply Forall2_ignore2 in H9.
        destruct es; try congruence.
        inv H0. inv H6. inv H8. inv H9. destruct H8 as (?&Hin&Hsem).
        eapply Forall_forall in H10; eauto. rewrite <-H10, <-H6.
        unfold annots; rewrite flat_map_concat_map.
        apply concat_length_eq.
        rewrite Forall2_map_2, Forall2_swap_args.
        eapply Forall2_impl_In; [|eauto]. intros.
        rewrite length_annot_numstreams.
        eapply Forall_forall in H3; [|eauto]. eapply Forall_forall in H2; [|eauto]. eauto.
      - (* case *)
        eapply Forall2Transpose_length in H14; rewrite Forall_map in H14.
        eapply Forall2_ignore2 in H10.
        destruct es as [|[|]]; try congruence.
        + inv H0. inv H10. destruct H3 as (?&Hin&Hsem). simpl in *.
          eapply Forall_forall in H14; eauto.
          erewrite <-H14, <-H16; eauto with datatypes. simpl in *.
          unfold annots; rewrite flat_map_concat_map.
          apply concat_length_eq.
          rewrite Forall2_map_2, Forall2_swap_args.
          eapply Forall2_impl_In; [|eauto]. intros.
          rewrite length_annot_numstreams.
          eapply Forall_forall in H4; [|eauto]. eapply Forall_forall in H15; eauto.
        + inv H12. inv H14. specialize (H4 eq_refl).
          rewrite <-H5, <-H18.
          unfold annots; rewrite flat_map_concat_map.
          apply concat_length_eq.
          rewrite Forall2_map_2, Forall2_swap_args.
          clear - H4 H1 H13 H17.
          revert y H4.
          induction H13; intros; inv H4; inv H1; inv H17; constructor; auto.
          rewrite length_annot_numstreams.
          eapply H4; eauto. rewrite H6; auto.
      - (* app (reset) *)
        specialize (H13 0). inv H13.
        repeat rewrite_Forall_forall.
        rewrite H3 in H14; inv H14.
        unfold idents in H5.
        repeat rewrite map_length in *. congruence.
    Qed.

    Corollary sem_exps_numstreams : forall H b es vs,
        Forall (wl_exp G) es ->
        Forall2 (sem_exp G H b) es vs ->
        length (concat vs) = length (annots es).
    Proof.
      intros * Hwt Hsem.
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

    Lemma sem_vars_mask_inv: forall k r H xs vs,
        Forall2 (sem_var (mask_hist k r H)) xs vs ->
        exists vs', Forall2 (sem_var H) xs vs' /\ EqSts vs (List.map (maskv k r) vs').
    Proof.
      intros * Hvars.
      induction Hvars; simpl.
      - exists []; simpl; split; eauto. constructor.
      - destruct IHHvars as (vs'&Hvars'&Heqs).
        eapply sem_var_mask_inv in H0 as (v'&Hvar'&Heq).
        exists (v'::vs'). split; constructor; auto.
    Qed.

    Fact sem_vars_dom_lb : forall H xs vs,
        Forall2 (sem_var H) xs vs ->
        Env.dom_lb H xs.
    Proof.
      intros * Hf.
      eapply Forall2_ignore2 in Hf.
      eapply Env.dom_lb_intro; intros ? Hin.
      eapply Forall_forall in Hf as (?&?&Hvar); eauto.
      inv Hvar. eexists; eauto.
    Qed.

    Fact sem_block_dom_lb : forall blk xs H bs,
        VarsDefined blk xs ->
        NoDupLocals xs blk ->
        sem_block G H bs blk ->
        Env.dom_lb H xs.
    Proof.
      induction blk using block_ind2; intros * Hnd Hvars Hsem;
        inv Hnd; inv Hvars; inv Hsem; simpl in *.
      - (* equation *)
        inv H4. eapply sem_vars_dom_lb; eauto.
      - (* reset *)
        specialize (H10 0).
        eapply Env.dom_lb_concat. rewrite Forall_forall in *; intros * Hin.
        eapply Forall2_ignore1, Forall_forall in H4 as (?&?&?); eauto.
        eapply Env.dom_lb_map, H; eauto.
        eapply NoDupLocals_incl; eauto using incl_concat.
      - (* local *)
        assert (Env.dom_lb H' (concat xs0)) as Hdom'.
        { eapply Env.dom_lb_concat. rewrite Forall_forall in *; intros * Hin.
          eapply Forall2_ignore1, Forall_forall in H3 as (?&?&?); eauto.
          eapply H; eauto.
          eapply NoDupLocals_incl; eauto.
          rewrite Permutation_app_comm, H5. eapply incl_concat; eauto.
        }
        eapply Env.dom_lb_intro; intros * Hin.
        eapply Env.dom_lb_use in Hdom' as (vs&Hfind). 2:rewrite <-H5, in_app_iff; eauto.
        assert (sem_var H' x vs) as Hvar' by (econstructor; eauto; reflexivity).
        assert (~InMembers x locs) as Hnin by (contradict Hin; eauto).
        specialize (H11 _ _ Hvar' Hnin); inv H11.
        econstructor; eauto.
    Qed.
  End props.

  (** ** Restriction *)

  Fact sem_var_restrict : forall vars H id v,
      In id vars ->
      sem_var H id v ->
      sem_var (Env.restrict H vars) id v.
  Proof.
    intros * HIn Hsem.
    inv Hsem.
    econstructor; eauto.
    apply Env.find_1 in H1. apply Env.find_2.
    apply Env.restrict_find; auto.
  Qed.

  Hint Resolve EqStrel EqStrel_Reflexive EqStrel_Transitive.

  Fact sem_var_restrict_inv : forall vars H id v,
      sem_var (Env.restrict H vars) id v ->
      In id vars /\ sem_var H id v.
  Proof.
    intros * Hvar; split.
    - pose proof (Env.restrict_dom_ub vars H) as Hdom.
      eapply Env.dom_ub_use in Hdom; eauto.
      inv Hvar. econstructor; eauto.
    - eapply sem_var_refines; [|eauto].
      eapply Env.restrict_refines; eauto.
  Qed.

  (* Lemma sem_clock_restrict : forall vars ck H bs bs', *)
  (*     wc_clock vars ck -> *)
  (*     sem_clock H bs ck bs' -> *)
  (*     sem_clock (Env.restrict H (map fst vars)) bs ck bs'. *)
  (* Proof. *)
  (*   intros * Hwc Hsem. *)
  (*   eapply sem_clock_refines'; [eauto| |eauto]. *)
  (*   intros ?? Hinm Hvar. *)
  (*   eapply sem_var_restrict; eauto. apply fst_InMembers; auto. *)
  (* Qed. *)

  Fact sem_exp_restrict {PSyn prefs} : forall (G : @global PSyn prefs) vars H b e vs,
      wx_exp vars e ->
      sem_exp G H b e vs ->
      sem_exp G (Env.restrict H vars) b e vs.
  Proof with eauto.
    induction e using exp_ind2; intros vs Hwt Hsem; inv Hwt; inv Hsem.
    - (* const *) constructor...
    - (* enum *) constructor...
    - (* var *)
      constructor. eapply sem_var_restrict...
    - (* unop *)
      econstructor...
    - (* binop *)
      econstructor...
    - (* fby *)
      econstructor...
      + repeat rewrite_Forall_forall. eapply H0...
      + repeat rewrite_Forall_forall. eapply H1...
    - (* arrow *)
      econstructor...
      + repeat rewrite_Forall_forall. eapply H0...
      + repeat rewrite_Forall_forall. eapply H1...
    - (* when *)
      econstructor...
      + repeat rewrite_Forall_forall. eapply H0...
      + eapply sem_var_restrict...
    - (* merge *)
      econstructor...
      + eapply sem_var_restrict...
      + do 2 (eapply Forall2_impl_In; [|eauto]; intros).
        do 2 (eapply Forall_forall in H5; eauto).
        do 2 (eapply Forall_forall in H0; eauto).
    - (* case *)
      econstructor...
      + clear H15. do 2 (eapply Forall2_impl_In; [|eauto]; intros; subst).
        do 2 (eapply Forall_forall in H0; eauto; simpl in * ).
        eapply Forall_forall in H7; eauto.
      + eapply Forall2_impl_In; [|eauto]; intros; subst.
        eapply Forall_forall in H1; eauto.
        eapply Forall_forall in H8; eauto.
    - (* app *)
      econstructor...
      1,2:repeat rewrite_Forall_forall.
      eapply H0... eapply H1...
  Qed.

  Lemma sem_equation_restrict {PSyn prefs} : forall (G : @global PSyn prefs) vars H b eq,
      wx_equation vars eq ->
      sem_equation G H b eq ->
      sem_equation G (Env.restrict H vars) b eq.
  Proof with eauto.
    intros G vars H b [xs es] Hwc Hsem.
    destruct Hwc as (?&?). inv Hsem.
    econstructor.
    + repeat rewrite_Forall_forall; eauto.
      eapply sem_exp_restrict...
    + repeat rewrite_Forall_forall.
      eapply sem_var_restrict...
  Qed.

  Lemma sem_block_restrict {PSyn prefs} : forall (G: @global PSyn prefs) blk vars H b,
      wx_block vars blk ->
      sem_block G H b blk ->
      sem_block G (Env.restrict H vars) b blk.
  Proof.
    induction blk using block_ind2; intros * Hwc Hsem; inv Hwc; inv Hsem.
    - (* equation *)
      econstructor.
      eapply sem_equation_restrict; eauto.
    - (* reset *)
      econstructor; eauto.
      + eapply sem_exp_restrict; eauto.
      + intros k; specialize (H10 k).
        rewrite Forall_forall in *. intros ? Hin.
        eapply sem_block_Equiv; try eapply H; eauto.
        now setoid_rewrite <-Env.restrict_map.
    - (* locals *)
      eapply Slocal with (H'0:=Env.restrict H' (vars ++ List.map fst locs)).
      + intros * Hsem Hnin.
        eapply sem_var_restrict_inv in Hsem as (Hin&Hsem).
        eapply sem_var_restrict; eauto.
        apply in_app_iff in Hin as [Hin|Hin]; auto.
        exfalso. apply Hnin, fst_InMembers; auto.
      + rewrite Forall_forall in *; intros; eauto.
  Qed.

  (** ** Alignment *)

  (** fby keeps the synchronization *)

  Lemma ac_fby1 :
    forall xs ys rs,
      fby xs ys rs -> abstract_clock xs ≡ abstract_clock rs.
  Proof.
    cofix Cofix.
    intros * Hfby.
    unfold_Stv xs; inv Hfby; econstructor; simpl; eauto.
    clear - H3. revert H3. revert y xs ys0 rs0.
    cofix Cofix.
    intros * Hfby1.
    unfold_Stv xs; inv Hfby1; econstructor; simpl; eauto.
  Qed.

  Lemma ac_fby2 :
    forall xs ys rs,
      fby xs ys rs -> abstract_clock ys ≡ abstract_clock rs.
  Proof.
    cofix Cofix. intros * Hfby.
    unfold_Stv ys; inv Hfby; econstructor; simpl; eauto.
    clear - H3. revert H3. revert v ys xs0 rs0.
    cofix Cofix. intros * Hfby1.
    unfold_Stv ys; inv Hfby1; econstructor; simpl; eauto.
  Qed.

  Lemma fby_aligned : forall bs xs ys zs,
      fby xs ys zs ->
      (aligned xs bs \/ aligned ys bs \/ aligned zs bs) ->
      (aligned xs bs /\ aligned ys bs /\ aligned zs bs).
  Proof with eauto.
    intros bs xs ys zs Hfby.
    specialize (ac_fby1 _ _ _ Hfby) as Hac1. specialize (ac_fby2 _ _ _ Hfby) as Hac2.
    specialize (ac_aligned xs) as Hs1. specialize (ac_aligned ys) as Hs2. specialize (ac_aligned zs) as Hs3.
    intros [Hsync|[Hsync|Hsync]]; repeat split; auto.
    - eapply aligned_EqSt in Hs1; eauto. rewrite Hs1, Hac1, <- Hac2; auto.
    - eapply aligned_EqSt in Hs1; eauto. rewrite Hs1, Hac1; auto.
    - eapply aligned_EqSt in Hs2; eauto. rewrite Hs2, Hac2, <- Hac1; auto.
    - eapply aligned_EqSt in Hs2; eauto. rewrite Hs2, Hac2; auto.
    - eapply aligned_EqSt in Hs3; eauto. rewrite Hs3, <- Hac1; auto.
    - eapply aligned_EqSt in Hs3; eauto. rewrite Hs3, <- Hac2; auto.
  Qed.

  Lemma ac_arrow1 : forall xs ys rs,
      arrow xs ys rs -> abstract_clock xs ≡ abstract_clock rs.
  Proof.
    cofix Cofix.
    intros * Harrow.
    unfold_Stv xs; inv Harrow; econstructor; simpl; eauto.
    clear - H3. revert H3. revert xs ys0 rs0.
    cofix Cofix.
    intros * Harrow1.
    unfold_Stv xs; inv Harrow1; econstructor; simpl; eauto.
  Qed.

  Lemma ac_arrow2 : forall xs ys rs,
      arrow xs ys rs -> abstract_clock ys ≡ abstract_clock rs.
  Proof.
    cofix Cofix.
    intros * Harrow.
    unfold_Stv ys; inv Harrow; econstructor; simpl; eauto.
    clear - H3. revert H3. revert xs0 ys rs0.
    cofix Cofix.
    intros * Harrow1.
    unfold_Stv ys; inv Harrow1; econstructor; simpl; eauto.
  Qed.

  Lemma arrow_aligned : forall bs xs ys zs,
      arrow xs ys zs ->
      (aligned xs bs \/ aligned ys bs \/ aligned zs bs) ->
      (aligned xs bs /\ aligned ys bs /\ aligned zs bs).
  Proof with eauto.
    intros bs xs ys zs Hfby.
    specialize (ac_arrow1 _ _ _ Hfby) as Hac1. specialize (ac_arrow2 _ _ _ Hfby) as Hac2.
    specialize (ac_aligned xs) as Hs1. specialize (ac_aligned ys) as Hs2. specialize (ac_aligned zs) as Hs3.
    intros [Hsync|[Hsync|Hsync]]; repeat split; auto.
    - eapply aligned_EqSt in Hs1; eauto. rewrite Hs1, Hac1, <- Hac2; auto.
    - eapply aligned_EqSt in Hs1; eauto. rewrite Hs1, Hac1; auto.
    - eapply aligned_EqSt in Hs2; eauto. rewrite Hs2, Hac2, <- Hac1; auto.
    - eapply aligned_EqSt in Hs2; eauto. rewrite Hs2, Hac2; auto.
    - eapply aligned_EqSt in Hs3; eauto. rewrite Hs3, <- Hac1; auto.
    - eapply aligned_EqSt in Hs3; eauto. rewrite Hs3, <- Hac2; auto.
  Qed.

End LSEMANTICS.

Module LSemanticsFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS        Ids Op OpAux)
       (Syn   : LSYNTAX       Ids Op OpAux Cks)
       (Lord  : LORDERED      Ids Op OpAux Cks Syn)
       (Str   : COINDSTREAMS  Ids Op OpAux Cks)
<: LSEMANTICS Ids Op OpAux Cks Syn Lord Str.
  Include LSEMANTICS Ids Op OpAux Cks Syn Lord Str.
End LSemanticsFun.
