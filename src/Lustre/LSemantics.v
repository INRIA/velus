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

  CoInductive fby1 : option value -> Stream svalue -> Stream svalue -> Stream bool -> Stream svalue -> Prop :=
  | FbyRA: (* Reset while absent *)
      forall v xs ys rs zs,
        fby1 None xs ys rs zs ->
        fby1 v (absent ⋅ xs) (absent ⋅ ys) (true ⋅ rs) (absent ⋅ zs)
  | FbyRP: (* Reset while present *)
      forall v x y xs ys rs zs,
        fby1 (Some y) xs ys rs zs ->
        fby1 v (present x ⋅ xs) (present y ⋅ ys) (true ⋅ rs) (present x ⋅ zs)
  | FbyA: (* Absence *)
      forall v xs ys rs zs,
        fby1 v xs ys rs zs ->
        fby1 v (absent ⋅ xs) (absent ⋅ ys) (false ⋅ rs) (absent ⋅ zs)
  | FbyP1: (* First presence *)
      forall x y xs ys rs zs,
        fby1 (Some y) xs ys rs zs ->
        fby1 None (present x ⋅ xs) (present y ⋅ ys) (false ⋅ rs) (present x ⋅ zs)
  | FbyP2: (* Following presences *)
      forall v x y xs ys rs zs,
        fby1 (Some y) xs ys rs zs ->
        fby1 (Some v) (present x ⋅ xs) (present y ⋅ ys) (false ⋅ rs) (present v ⋅ zs).

  Definition fby := fby1 None.

  CoInductive arrow1: bool -> Stream svalue -> Stream svalue -> Stream bool -> Stream svalue -> Prop :=
  | ArrowRA:
      forall b xs ys rs zs,
      arrow1 true xs ys rs zs ->
      arrow1 b (absent ⋅ xs) (absent ⋅ ys) (true ⋅ rs) (absent ⋅ zs)
  | ArrowRP:
      forall b x y xs ys rs zs,
      arrow1 false xs ys rs zs ->
      arrow1 b (present x ⋅ xs) (present y ⋅ ys) (true ⋅ rs) (present x ⋅ zs)
  | ArrowA:
      forall b xs ys rs zs,
      arrow1 b xs ys rs zs ->
      arrow1 b (absent ⋅ xs) (absent ⋅ ys) (false ⋅ rs) (absent ⋅ zs)
  | ArrowP1: (* First presence *)
      forall x y xs ys rs zs,
      arrow1 false xs ys rs zs ->
      arrow1 true (present x ⋅ xs) (present y ⋅ ys) (false ⋅ rs) (present x ⋅ zs)
  | ArrowP2: (* Following presences *)
      forall x y xs ys rs zs,
      arrow1 false xs ys rs zs ->
      arrow1 false (present x ⋅ xs) (present y ⋅ ys) (false ⋅ rs) (present y ⋅ zs).

  Definition arrow := arrow1 true.

  Section NodeSemantics.
    Context {prefs : PS.t}.
    Variable G : @global prefs.

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
        forall H b e0s es er anns s0ss sss sr r os,
          Forall2 (sem_exp H b) e0s s0ss ->
          Forall2 (sem_exp H b) es sss ->
          Forall2 (fun e r => sem_exp H b e [r]) er sr ->
          bools_ofs sr r ->
          Forall3 (fun s0 s1 o => fby s0 s1 r o) (concat s0ss) (concat sss) os ->
          sem_exp H b (Efby e0s es er anns) os

    | Sarrow:
        forall H b e0s es er anns s0ss sss sr r os,
          Forall2 (sem_exp H b) e0s s0ss ->
          Forall2 (sem_exp H b) es sss ->
          Forall2 (fun e r => sem_exp H b e [r]) er sr ->
          bools_ofs sr r ->
          Forall3 (fun s0 s1 o => arrow s0 s1 r o) (concat s0ss) (concat sss) os ->
          sem_exp H b (Earrow e0s es er anns) os

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
          (forall k, sem_node f (List.map (mask k bs) (concat ss)) (List.map (mask k bs) os)) ->
          sem_exp H b (Eapp f es er lann) os

    with sem_equation: history -> Stream bool -> equation -> Prop :=
           Seq:
             forall H b xs es ss,
               Forall2 (sem_exp H b) es ss ->
               Forall2 (sem_var H) xs (concat ss) ->
               sem_equation H b (xs, es)

    with sem_node: ident -> list (Stream svalue) -> list (Stream svalue) -> Prop :=
      Snode:
        forall f ss os n H b,
          find_node f G = Some n ->
          Forall2 (sem_var H) (idents n.(n_in)) ss ->
          Forall2 (sem_var H) (idents n.(n_out)) os ->
          Forall (sem_equation H b) n.(n_eqs) ->
          b = clocks_of ss ->
          sem_node f ss os.

  End NodeSemantics.

  (** Custom induction schemes *)

  Section sem_exp_ind2.
    Context (prefs : PS.t).
    Variable G : @global prefs.

    Variable P_exp : history -> Stream bool -> exp -> list (Stream svalue) -> Prop.
    Variable P_equation : history -> Stream bool -> equation -> Prop.
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
      forall H b e0s es er anns s0ss sss sr r os,
        Forall2 (sem_exp G H b) e0s s0ss ->
        Forall2 (P_exp H b) e0s s0ss ->
        Forall2 (sem_exp G H b) es sss ->
        Forall2 (P_exp H b) es sss ->
        Forall2 (fun e r => sem_exp G H b e [r]) er sr ->
        Forall2 (fun e r => P_exp H b e [r]) er sr ->
        bools_ofs sr r ->
        Forall3 (fun s0 s1 o => fby s0 s1 r o) (concat s0ss) (concat sss) os ->
        P_exp H b (Efby e0s es er anns) os.

    Hypothesis ArrowCase:
      forall H b e0s es er anns s0ss sss sr r os,
        Forall2 (sem_exp G H b) e0s s0ss ->
        Forall2 (P_exp H b) e0s s0ss ->
        Forall2 (sem_exp G H b) es sss ->
        Forall2 (P_exp H b) es sss ->
        Forall2 (fun e r => sem_exp G H b e [r]) er sr ->
        Forall2 (fun e r => P_exp H b e [r]) er sr ->
        bools_ofs sr r ->
        Forall3 (fun s0 s1 o => arrow s0 s1 r o) (concat s0ss) (concat sss) os ->
        P_exp H b (Earrow e0s es er anns) os.

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
        (forall k, sem_node G f (List.map (mask k bs) (concat ss)) (List.map (mask k bs) os)
              /\ P_node f (List.map (mask k bs) (concat ss)) (List.map (mask k bs) os)) ->
        P_exp H b (Eapp f es er lann) os.

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
             (H: history) (b: Stream bool) (e: exp) (ss: list (Stream svalue))
             (Sem: sem_exp G H b e ss)
             {struct Sem}
      : P_exp H b e ss
    with sem_equation_ind2
           (H: history) (b: Stream bool) (e: equation)
           (Sem: sem_equation G H b e)
           {struct Sem}
         : P_equation H b e
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
        + eapply FbyCase; eauto; clear H3 H4; SolveForall.
        + eapply ArrowCase; eauto; clear H3 H4; SolveForall.
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
        eapply Node; eauto.
        SolveForall.
    Qed.

  End sem_exp_ind2.

  (** ** Properties of the [global] environment *)

  Lemma sem_node_cons {prefs} :
    forall (nd : @node prefs) nds enums f xs ys,
      Ordered_nodes (Global enums (nd::nds))
      -> sem_node (Global enums (nd::nds)) f xs ys
      -> nd.(n_name) <> f
      -> sem_node (Global enums nds) f xs ys.
  Proof.
    intros * Hord Hsem Hnf.
    revert Hnf.
    induction Hsem using sem_node_ind2
      with (P_equation := fun bk H eq => ~Is_node_in_eq nd.(n_name) eq
                                      -> sem_equation (Global enums0 nds) bk H eq)
           (P_exp := fun H bk e ss => ~ Is_node_in_exp nd.(n_name) e
                                   -> sem_exp (Global enums0 nds) H bk e ss);
      try (now econstructor; eauto); intros.
    - econstructor; eauto. apply IHHsem.
      intro. destruct H3. constructor. auto.
    - econstructor; eauto.
      apply IHHsem. intro. destruct H5. constructor. auto.
      apply IHHsem0. intro. destruct H5. constructor. auto.
    - econstructor; eauto;
        (eapply Forall2_impl_In; [|eauto]; intros;
         eapply H11; intro; apply H8; constructor);
        [left|right;left|right;right]; apply Exists_exists; eauto.
    - econstructor; eauto;
        (eapply Forall2_impl_In; [|eauto]; intros;
         eapply H11; intro; apply H8; constructor);
        [left|right;left|right;right]; apply Exists_exists; eauto.
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
    - rewrite find_node_other with (1:=Hnf) in H0.
      eapply Snode; eauto.
      clear H3.
      eapply Forall_impl_In with (2:=H4).
      apply find_node_later_not_Is_node_in with (1:=Hord) in H0.
      intros eq Hin. intro Hini.
      rewrite Is_node_in_Forall in H0.
      apply Forall_forall with (1:=H0) in Hin.
      auto.
  Qed.

  Lemma sem_node_cons' {prefs} :
    forall (nd : @node prefs) nds enums f xs ys,
      Ordered_nodes (Global enums (nd::nds))
      -> sem_node (Global enums nds) f xs ys
      -> nd.(n_name) <> f
      -> sem_node (Global enums (nd::nds)) f xs ys.
  Proof.
    intros * Hord Hsem.
    induction Hsem using sem_node_ind2
      with (P_equation := fun bk H eq => ~Is_node_in_eq nd.(n_name) eq
                                      -> sem_equation (Global enums0 (nd::nds)) bk H eq)
           (P_exp := fun H bk e ss => ~ Is_node_in_exp nd.(n_name) e
                                   -> sem_exp (Global enums0 (nd::nds)) H bk e ss);
      try (now econstructor; eauto); intros.
    - econstructor; eauto. apply IHHsem.
      intro. destruct H3. constructor. auto.
    - econstructor; eauto.
      apply IHHsem. intro. destruct H5. constructor. auto.
      apply IHHsem0. intro. destruct H5. constructor. auto.
   - econstructor; eauto;
        (eapply Forall2_impl_In; [|eauto]; intros;
         eapply H11; intro; apply H8; constructor);
        [left|right;left|right;right]; apply Exists_exists; eauto.
    - econstructor; eauto;
        (eapply Forall2_impl_In; [|eauto]; intros;
         eapply H11; intro; apply H8; constructor);
        [left|right;left|right;right]; apply Exists_exists; eauto.
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
    - econstructor; eauto.
      + erewrite <-find_node_other in H0; eauto.
      + eapply Forall_impl_In; [| eauto].
        intros a HIn Hsem; simpl in Hsem.
        apply Hsem.
        eapply find_node_later_not_Is_node_in in H0; eauto.
        intro contra. apply H0.
        unfold Is_node_in. rewrite Exists_exists.
        exists a; auto.
  Qed.

  Corollary sem_node_cons_iff {prefs} : forall (n : @node prefs) nds enums f xs ys,
      Ordered_nodes (Global enums (n::nds)) ->
      n_name n <> f ->
      sem_node (Global enums nds) f xs ys <-> sem_node (Global enums (n::nds)) f xs ys.
  Proof.
    intros * Hord Hname.
    split; intros Hsem.
    - eapply sem_node_cons'; eauto.
    - eapply sem_node_cons; eauto.
  Qed.

  Lemma sem_equation_global_tl {prefs} :
    forall (nd : @node prefs) nds enums H b eq,
      Ordered_nodes (Global enums (nd :: nds)) ->
      ~ Is_node_in_eq nd.(n_name) eq ->
      sem_equation (Global enums (nd :: nds)) H b eq ->
      sem_equation (Global enums nds) H b eq.
  Proof.
    destruct eq as [ xs es ]. intros * Hord Hnin Hsem. inv Hsem.

    econstructor; eauto.
    clear H6. induction H5 as [ | ? ? ? ? Hsem ]; eauto. constructor.

    clear IHForall2. revert dependent y.

    Ltac SolveNin' Hnin :=
      let Hn := fresh in
      let Hn2 := fresh in
      let Hn3 := fresh in
      let Hn4 := fresh in
      intro Hn; destruct Hnin; inversion_clear Hn as [? ? Hn2 |]; subst;
      [ econstructor; econstructor; auto
      | unfold Is_node_in_eq; simpl; rewrite Exists_cons; right; auto].

    Ltac SolveNin Hnin :=
      let Hn := fresh in
      let Hn2 := fresh in
      let Hn3 := fresh in
      let Hn4 := fresh in
      intro Hn; destruct Hnin; inversion_clear Hn as [? ? Hn2 |]; subst;
      [ econstructor; econstructor; auto
      | unfold Is_node_in_eq; simpl; rewrite Exists_cons; right; auto];
      inversion_clear Hn2 as
          [ | | ? ? ? ? ? Hn3 | ? ? ? ? ? Hn3 | | ? ? ? ? ? Hn3 | ? ? ? ? ? Hn3 | |]; auto;
      try (destruct Hn3 as [| Hn4 ]; eauto; destruct Hn4; eauto).

    induction x using exp_ind2; intros * Hsem; inv Hsem;
      try (now econstructor; eauto).
    - econstructor; eauto. eapply IHx; eauto. SolveNin Hnin.
    - econstructor; eauto.
      apply IHx1; eauto. SolveNin Hnin.
      apply IHx2; eauto. SolveNin Hnin.
    - econstructor; eauto.
      clear H5 H1 H14 H16. induction H9; auto. constructor.
      inv H0. apply H5; auto. SolveNin Hnin.
      inv H0. apply IHForall2; eauto. SolveNin Hnin.
      clear H5 H0 H14 H16. induction H12; auto. constructor.
      inv H1. apply H5; auto. SolveNin Hnin.
      inv H1. apply IHForall2; eauto. SolveNin Hnin.
      clear H5 H0 H1 H9 H12 H15 H16. induction H14; auto. constructor.
      inv H2. apply H4; auto. SolveNin Hnin.
      inv H2. apply IHForall2; eauto. SolveNin Hnin.
    - econstructor; eauto.
      clear H5 H1 H14 H16. induction H9; auto. constructor.
      inv H0. apply H5; auto. SolveNin Hnin.
      inv H0. apply IHForall2; eauto. SolveNin Hnin.
      clear H5 H0 H14 H16. induction H12; auto. constructor.
      inv H1. apply H5; auto. SolveNin Hnin.
      inv H1. apply IHForall2; eauto. SolveNin Hnin.
      clear H5 H0 H1 H9 H12 H15 H16. induction H14; auto. constructor.
      inv H2. apply H4; auto. SolveNin Hnin.
      inv H2. apply IHForall2; eauto. SolveNin Hnin.
    - econstructor; eauto.
      clear H5 H11 H12. induction H10; eauto. constructor.
      inv H0. apply H4; eauto. SolveNin Hnin.
      inv H0. apply IHForall2; eauto. SolveNin Hnin.
    - econstructor; eauto.
      clear H5 H8 H11.
      do 2 (eapply Forall2_impl_In; [|eauto]; intros).
      do 2 (eapply Forall_forall in H0; eauto).
      eapply H0; eauto.
      contradict Hnin. inv Hnin; [left|right]; auto. constructor.
      do 2 (eapply Exists_exists; repeat esplit; eauto).
    - econstructor; eauto. eapply IHx; eauto. SolveNin Hnin.
      + clear H13. do 2 (eapply Forall2_impl_In; [|eauto]; intros; subst).
        do 2 (eapply Forall_forall in H0; eauto; simpl in * ).
        eapply H0; eauto.
        contradict Hnin. inv Hnin; [left|right]; auto. constructor; right; left.
        do 2 (eapply Exists_exists; repeat esplit; eauto).
      + eapply Forall2_impl_In; [|eauto]; intros.
        eapply Forall_forall in H1; eauto.
        eapply H1; eauto.
        contradict Hnin. inv Hnin; [left|right]; auto. constructor; right; right.
        eapply Exists_exists; repeat esplit; eauto.
    - econstructor; eauto.
      + clear H1 H12 H14. induction H10; auto. constructor.
        inv H0. apply H4; auto. SolveNin Hnin.
        inv H0. apply IHForall2; eauto.
        intro Hn; destruct Hnin; inversion_clear Hn as [? ? Hn2 |]; subst;
          [ econstructor; eauto
          | unfold Is_node_in_eq; simpl; rewrite Exists_cons; right; auto].
          inversion_clear Hn2.
        * constructor. destruct H0; auto.
        * apply INEapp2.
      + eapply Forall2_impl_In; [| eauto]; intros * Hin ? Hsem.
        eapply Forall_forall in Hin as Hs; eauto. apply Hs; auto.
        intro Ini. apply Hnin. inv Ini. constructor. constructor. right.
        apply Exists_exists; eauto. now constructor 2.
      + intro k. eapply sem_node_cons; eauto. intro. subst.
        apply Hnin. constructor. apply INEapp2.
    - apply IHForall2. intro. destruct Hnin. unfold Is_node_in_eq. simpl.
      rewrite Exists_cons. right. auto.
  Qed.

  Corollary Forall_sem_equation_global_tl {prefs}:
    forall (nd : @node prefs) nds enums b H eqs,
      Ordered_nodes (Global enums (nd :: nds))
      -> ~ Is_node_in nd.(n_name) eqs
      -> Forall (sem_equation (Global enums (nd :: nds)) H b) eqs
      -> Forall (sem_equation (Global enums nds) H b) eqs.
  Proof.
    intros * Hord Hnini.
    apply Forall_impl_In.
    intros eq Hin Hsem.
    eapply sem_equation_global_tl; eauto.
    apply Is_node_in_Forall in Hnini.
    apply Forall_forall with (1:=Hnini) (2:=Hin).
  Qed.

  Lemma sem_equation_global_tl' {prefs}:
    forall (nd : @node prefs) nds enums H b eq,
      Ordered_nodes (Global enums (nd :: nds)) ->
      ~ Is_node_in_eq nd.(n_name) eq ->
      sem_equation (Global enums nds) H b eq ->
      sem_equation (Global enums (nd :: nds)) H b eq.
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
      clear H5 H1 H14 H16. induction H9; auto. constructor.
      inv H0. apply H5; auto. SolveNin Hnin.
      inv H0. apply IHForall2; eauto. SolveNin Hnin.
      clear H5 H0 H14 H16. induction H12; auto. constructor.
      inv H1. apply H5; auto. SolveNin Hnin.
      inv H1. apply IHForall2; eauto. SolveNin Hnin.
      clear H5 H0 H1 H9 H12 H15 H16. induction H14; auto. constructor.
      inv H2. apply H4; auto. SolveNin Hnin.
      inv H2. apply IHForall2; eauto. SolveNin Hnin.
    - econstructor; eauto.
      clear H5 H1 H14 H16. induction H9; auto. constructor.
      inv H0. apply H5; auto. SolveNin Hnin.
      inv H0. apply IHForall2; eauto. SolveNin Hnin.
      clear H5 H0 H14 H16. induction H12; auto. constructor.
      inv H1. apply H5; auto. SolveNin Hnin.
      inv H1. apply IHForall2; eauto. SolveNin Hnin.
      clear H5 H0 H1 H9 H12 H15 H16. induction H14; auto. constructor.
      inv H2. apply H4; auto. SolveNin Hnin.
      inv H2. apply IHForall2; eauto. SolveNin Hnin.
    - econstructor; eauto.
      clear H5 H11 H12. induction H10; eauto. constructor.
      inv H0. apply H4; eauto. SolveNin Hnin.
      inv H0. apply IHForall2; eauto. SolveNin Hnin.
    - econstructor; eauto.
      clear H5 H8 H11.
      do 2 (eapply Forall2_impl_In; [|eauto]; intros).
      do 2 (eapply Forall_forall in H0; eauto).
      eapply H0; eauto.
      contradict Hnin. inv Hnin; [left|right]; auto. constructor.
      do 2 (eapply Exists_exists; repeat esplit; eauto).
    - econstructor; eauto. eapply IHx; eauto. SolveNin Hnin.
      + clear H13. do 2 (eapply Forall2_impl_In; [|eauto]; intros; subst).
        do 2 (eapply Forall_forall in H0; eauto; simpl in * ).
        eapply H0; eauto.
        contradict Hnin. inv Hnin; [left|right]; auto. constructor; right; left.
        do 2 (eapply Exists_exists; repeat esplit; eauto).
      + eapply Forall2_impl_In; [|eauto]; intros.
        eapply Forall_forall in H1; eauto.
        eapply H1; eauto.
        contradict Hnin. inv Hnin; [left|right]; auto. constructor; right; right.
        eapply Exists_exists; repeat esplit; eauto.
    - econstructor; eauto.
      + clear H1 H12 H14. induction H10; auto. constructor.
        inv H0. apply H4; auto. SolveNin Hnin.
        inv H0. apply IHForall2; eauto.
        intro Hn; destruct Hnin; inversion_clear Hn as [? ? Hn2 |]; subst;
          [ econstructor; eauto
          | unfold Is_node_in_eq; simpl; rewrite Exists_cons; right; auto].
          inversion_clear Hn2.
        * constructor. destruct H0; auto.
        * apply INEapp2.
      + eapply Forall2_impl_In; [| eauto]; intros * Hin ? Hsem.
        eapply Forall_forall in Hin as Hs; eauto. apply Hs; auto.
        intro Ini. apply Hnin. inv Ini. constructor. constructor. right.
        apply Exists_exists; eauto. now constructor 2.
      + intro k. eapply sem_node_cons'; eauto. intro. subst.
        apply Hnin. constructor. apply INEapp2.
    - apply IHForall2. intro. destruct Hnin. unfold Is_node_in_eq. simpl.
      rewrite Exists_cons. right. auto.
  Qed.

  Corollary Forall_sem_equation_global_tl' {prefs}:
    forall (nd : @node prefs) nds enums b H eqs,
      Ordered_nodes (Global enums (nd :: nds))
      -> ~ Is_node_in nd.(n_name) eqs
      -> Forall (sem_equation (Global enums nds) H b) eqs
      -> Forall (sem_equation (Global enums (nd :: nds)) H b) eqs.
  Proof.
    intros * Hord Hnini.
    apply Forall_impl_In.
    intros eq Hin Hsem.
    eapply sem_equation_global_tl'; eauto.
    apply Is_node_in_Forall in Hnini.
    apply Forall_forall with (1:=Hnini) (2:=Hin).
  Qed.

  Add Parametric Morphism v : (fby1 v)
      with signature @EqSt svalue ==> @EqSt svalue ==> @EqSt bool ==> @EqSt svalue ==> Basics.impl
        as fby1_EqSt.
  Proof.
    revert v.
    cofix Cofix.
    intros v xs xs' Exs ys ys' Eys rs rs' Ers zs zs' Ezs H.
    destruct xs', ys', rs', zs';
      inv H; inv Exs; inv Eys; inv Ers; inv Ezs; simpl in *;
        try discriminate; subst.
    1-5:constructor; eauto; eapply Cofix; eauto.
  Qed.

  Add Parametric Morphism : fby
      with signature @EqSt svalue ==> @EqSt svalue ==> @EqSt bool ==> @EqSt svalue ==> Basics.impl
        as fby_EqSt.
  Proof.
    intros * Exs * Eys * Ers * Ezs H.
    unfold fby in *. rewrite Exs, Eys, Ers, Ezs in H; auto.
  Qed.

  Add Parametric Morphism b : (arrow1 b)
      with signature @EqSt svalue ==> @EqSt svalue ==> @EqSt bool ==> @EqSt svalue ==> Basics.impl
        as arrow1_EqSt.
  Proof.
    revert b.
    cofix Cofix.
    intros b xs xs' Exs ys ys' Eys rs rs' Ers zs zs' Ezs H.
    destruct xs', ys', rs', zs';
      inv H; inv Exs; inv Eys; inv Ers; inv Ezs; simpl in *;
        try discriminate; subst.
    1-5:constructor; eauto; eapply Cofix; eauto.
  Qed.

  Add Parametric Morphism : arrow
      with signature @EqSt svalue ==> @EqSt svalue ==> @EqSt bool ==> @EqSt svalue ==> Basics.impl
        as arrow_EqSt.
  Proof.
    intros * Exs * Eys * Ers * Ezs H.
    unfold arrow in *. rewrite Exs, Eys, Ers, Ezs in H; auto.
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

  Add Parametric Morphism H : (sem_var H)
      with signature eq ==> @EqSt svalue ==> Basics.impl
        as sem_var_EqSt.
  Proof.
    intros x xs xs' E; intro Sem; inv Sem.
    econstructor; eauto.
    transitivity xs; auto; symmetry; auto.
  Qed.

  Add Parametric Morphism {prefs} (G : @global prefs) H : (sem_exp G H)
      with signature @EqSt bool ==> eq ==> @EqSts svalue ==> Basics.impl
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
      + eapply Forall2_impl_In; [|eapply H5].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + eauto.
      + eapply Forall3_EqSt; eauto. solve_proper.
    - econstructor.
      + eapply Forall2_impl_In; [|apply H1].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + eapply Forall2_impl_In; [|apply H3].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + eapply Forall2_impl_In; [|eapply H5].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + eauto.
      + eapply Forall3_EqSt; eauto. solve_proper.
    - econstructor; eauto.
      + eapply Forall2_impl_In; [|apply H1].
        intros * ?? Hs; apply Hs; auto; reflexivity.
      + eapply Forall2_EqSt; eauto. solve_proper.
    - econstructor; eauto.
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

  Add Parametric Morphism {prefs} (G : @global prefs) H : (sem_equation G H)
      with signature @EqSt bool ==> eq ==> Basics.impl
        as sem_equation_morph.
  Proof.
    unfold Basics.impl; intros xs xs' Exss eq Hsem.
    inversion_clear Hsem as [????? Hseme Hsemv]. econstructor; eauto.
    clear Hsemv. induction Hseme; constructor; auto.
    now rewrite <- Exss.
  Qed.

  Add Parametric Morphism {prefs} (G : @global prefs) : (sem_node G)
      with signature eq ==> @EqSts svalue ==> @EqSts svalue ==> Basics.impl
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
  (** If a new environment [refines] the previous one, it gives the same semantics
      to variables and therefore expressions, equations dans nodes *)

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
  Fact sem_exp_refines {prefs} : forall (G : @global prefs) b e H H' v,
      Env.refines eq H H' ->
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

  Fact sem_equation_refines {prefs} : forall (G : @global prefs) H H' b equ,
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
    Context {prefs1 prefs2 : PS.t}.

    (** We develop a notion of refinement over globals :
        [node_sem_refines G G' f] means that if [f] exists and has a given semantic in [G],
        then it also exists and has the same semantic in [G'].
        This is just a shorthand definition, but is useful when proving the correctness
        of transformation passes over the Lustre AST.
     *)
    Definition node_sem_refines (G : @global prefs1) (G' : @global prefs2) f : Prop :=
      (forall ins outs, (sem_node G f ins outs) -> (sem_node G' f ins outs)).

    (* Fact node_sem_refines_refl : forall G f, node_sem_refines G G f. *)
    (* Proof. intros G f ins outs. auto. Qed. *)

    (* Fact node_sem_refines_trans : forall G1 G2 G3 f, *)
    (*     node_sem_refines G1 G2 f -> *)
    (*     node_sem_refines G2 G3 f -> *)
    (*     node_sem_refines G1 G3 f. *)
    (* Proof. *)
    (*   intros G1 G2 G3 f H1 H2 ins outs Hsem. *)
    (*   auto. *)
    (* Qed. *)

    Definition global_sem_refines G G' : Prop :=
      forall f, node_sem_refines G G' f.

    Hint Constructors sem_exp.
    Fact sem_ref_sem_exp : forall G G' H b e vs,
        global_sem_refines G G' ->
        sem_exp G H b e vs ->
        sem_exp G' H b e vs.
    Proof with eauto.
      induction e using exp_ind2; intros vs Heq Hsem; inv Hsem;
        econstructor...
      1-7:repeat rewrite_Forall_forall...
      - (* merge *)
        do 2 (eapply Forall2_impl_In; [|eauto]; intros).
        do 2 (eapply Forall_forall in H0; eauto).
      - (* case *)
        clear H12. do 2 (eapply Forall2_impl_In; [|eauto]; intros; subst).
        do 2 (eapply Forall_forall in H0; eauto; simpl in * ).
      - eapply Forall2_impl_In; [|eauto]; intros.
        eapply Forall_forall in H1; [|eauto]; eauto.
      (* app *)
      - eapply Forall2_impl_In; [|eauto]; intros.
        eapply Forall_forall in H0; eauto.
      - eapply Forall2_impl_In; [|eauto]; intros.
        eapply Forall_forall in H1; eauto.
      - intros k. specialize (H13 k).
        specialize (Heq f (List.map (mask k bs) (concat ss)) (List.map (mask k bs) vs)).
        auto.
    Qed.

    Fact sem_ref_sem_equation : forall G G' H b eq,
        global_sem_refines G G' ->
        sem_equation G H b eq ->
        sem_equation G' H b eq.
    Proof.
      intros G G' H b [xs es] Heq Hsem.
      inv Hsem.
      econstructor; eauto.
      eapply Forall2_impl_In; [| eauto].
      intros. eapply sem_ref_sem_exp; eauto.
    Qed.

    Fact global_sem_ref_nil : forall enums,
      global_sem_refines (Global enums []) (Global enums []).
    Proof.
      intros * f ins outs Hsem.
      exfalso. inv Hsem.
      unfold find_node in H0; simpl in H0. inv H0.
    Qed.

    Fact global_sem_ref_cons : forall enums nds nds' n n' f,
        Ordered_nodes (Global enums (n::nds)) ->
        Ordered_nodes (Global enums (n'::nds')) ->
        n_name n = f ->
        n_name n' = f ->
        global_sem_refines (Global enums nds) (Global enums nds') ->
        node_sem_refines (Global enums (n::nds)) (Global enums (n'::nds')) f ->
        global_sem_refines (Global enums (n::nds)) (Global enums (n'::nds')).
    Proof with eauto.
      intros * Hord1 Hord2 Hname1 Hname2 Hglob Hnode f0 ins outs Hsem.
      inv Hsem.
      simpl in H0.
      destruct (ident_eq_dec (n_name n) f0); subst.
      + specialize (Hnode ins outs).
        inv H0.
        eapply Hnode.
        eapply Snode with (n1:=n0)...
      + apply sem_node_cons'...
        specialize (Hglob f0 ins outs). apply Hglob.
        rewrite find_node_other in H0; eauto.
        econstructor...
        rewrite Forall_forall in *. intros.
        eapply sem_equation_global_tl...
        eapply find_node_later_not_Is_node_in in Hord1; eauto.
        intro contra.
        rewrite Is_node_in_Forall in Hord1. rewrite Forall_forall in *.
        apply Hord1 in H4. congruence.
    Qed.

  End sem_ref.

  Section props.
    Context {prefs : PS.t}.
    Variable (G : @global prefs).

    (** The number of streams generated by an expression [e] equals [numstreams e] *)

    Fact sem_exp_numstreams : forall H b e v,
        wl_exp G e ->
        sem_exp G H b e v ->
        length v = numstreams e.
    Proof with eauto.
      induction e using exp_ind2; intros v Hsem Hwl; inv Hwl; inv Hsem; simpl; auto.
      - (* fby *)
        repeat rewrite_Forall_forall.
        rewrite <- H13, <- H16.
        unfold annots; rewrite flat_map_concat_map.
        apply concat_length_eq.
        rewrite Forall2_map_2.
        rewrite_Forall_forall.
        rewrite length_annot_numstreams. eapply H0.
        + apply nth_In; congruence.
        + apply H7. apply nth_In; congruence.
        + eapply H10... congruence.
      - (* arrow (reset) *)
        repeat rewrite_Forall_forall.
        rewrite <- H13, <- H16.
        unfold annots; rewrite flat_map_concat_map.
        apply concat_length_eq.
        rewrite Forall2_map_2.
        rewrite_Forall_forall.
        rewrite length_annot_numstreams. eapply H0.
        + apply nth_In; congruence.
        + apply H7. apply nth_In; congruence.
        + eapply H10... congruence.
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

    (** When we have the semantic for the equations of a node,
      we have a semantic for the internal variables, as well as the outputs *)
    Lemma sem_node_sem_vars : forall H b vars eqs outs,
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

    Lemma sem_node_sem_outs : forall H b outs eqs vars,
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

    Corollary sem_node_sem_vars_outs : forall H b vars outs eqs,
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
  End props.

  (** *** Alignement properties *)

  (** fby keeps the synchronization *)

  Lemma ac_fby11 : forall v xs ys rs zs,
      fby1 v xs ys rs zs ->
      abstract_clock xs ≡ abstract_clock zs.
  Proof.
    cofix Cofix.
    intros * Hfby.
    inv Hfby; simpl; constructor; simpl; auto;
      eapply Cofix; eauto.
  Qed.

  Corollary ac_fby1 : forall xs ys rs zs,
      fby xs ys rs zs ->
      abstract_clock xs ≡ abstract_clock zs.
  Proof. intros. eapply ac_fby11; eauto. Qed.

  Lemma ac_fby12 : forall v xs ys rs zs,
      fby1 v xs ys rs zs ->
      abstract_clock ys ≡ abstract_clock zs.
  Proof.
    cofix Cofix.
    intros * Hfby.
    inv Hfby; simpl; constructor; simpl; auto;
      eapply Cofix; eauto.
  Qed.

  Corollary ac_fby2 : forall xs ys rs zs,
      fby xs ys rs zs ->
      abstract_clock ys ≡ abstract_clock zs.
  Proof. intros. eapply ac_fby12; eauto. Qed.

  Lemma fby1_aligned : forall v bs xs ys rs zs,
      fby1 v xs ys rs zs ->
      (aligned xs bs \/ aligned ys bs \/ aligned zs bs) ->
      (aligned xs bs /\ aligned ys bs /\ aligned zs bs).
  Proof with eauto.
    intros * Hfby.
    specialize (ac_fby11 _ _ _ _ _ Hfby) as Hac1. specialize (ac_fby12 _ _ _ _ _ Hfby) as Hac2.
    specialize (ac_aligned xs) as Hs1. specialize (ac_aligned ys) as Hs2. specialize (ac_aligned zs) as Hs3.
    intros [Hsync|[Hsync|Hsync]]; repeat split; auto.
    - eapply aligned_EqSt in Hs1; eauto. rewrite Hs1, Hac1, <- Hac2; auto.
    - eapply aligned_EqSt in Hs1; eauto. rewrite Hs1, Hac1; auto.
    - eapply aligned_EqSt in Hs2; eauto. rewrite Hs2, Hac2, <- Hac1; auto.
    - eapply aligned_EqSt in Hs2; eauto. rewrite Hs2, Hac2; auto.
    - eapply aligned_EqSt in Hs3; eauto. rewrite Hs3, <- Hac1; auto.
    - eapply aligned_EqSt in Hs3; eauto. rewrite Hs3, <- Hac2; auto.
  Qed.

  Corollary fby_aligned : forall bs xs ys rs zs,
      fby xs ys rs zs ->
      (aligned xs bs \/ aligned ys bs \/ aligned zs bs) ->
      (aligned xs bs /\ aligned ys bs /\ aligned zs bs).
  Proof. intros. eapply fby1_aligned; eauto. Qed.

  Lemma ac_arrow11 : forall v xs ys rs zs,
      arrow1 v xs ys rs zs ->
      abstract_clock xs ≡ abstract_clock zs.
  Proof.
    cofix Cofix.
    intros * Harrow.
    inv Harrow; simpl; constructor; simpl; auto;
      eapply Cofix; eauto.
  Qed.

  Corollary ac_arrow1 : forall xs ys rs zs,
      arrow xs ys rs zs ->
      abstract_clock xs ≡ abstract_clock zs.
  Proof. intros. eapply ac_arrow11; eauto. Qed.

  Lemma ac_arrow12 : forall v xs ys rs zs,
      arrow1 v xs ys rs zs ->
      abstract_clock ys ≡ abstract_clock zs.
  Proof.
    cofix Cofix.
    intros * Harrow.
    inv Harrow; simpl; constructor; simpl; auto;
      eapply Cofix; eauto.
  Qed.

  Corollary ac_arrow2 : forall xs ys rs zs,
      arrow xs ys rs zs ->
      abstract_clock ys ≡ abstract_clock zs.
  Proof. intros. eapply ac_arrow12; eauto. Qed.

  Lemma arrow1_aligned : forall v bs xs ys rs zs,
      arrow1 v xs ys rs zs ->
      (aligned xs bs \/ aligned ys bs \/ aligned zs bs) ->
      (aligned xs bs /\ aligned ys bs /\ aligned zs bs).
  Proof with eauto.
    intros * Harrow.
    specialize (ac_arrow11 _ _ _ _ _ Harrow) as Hac1. specialize (ac_arrow12 _ _ _ _ _ Harrow) as Hac2.
    specialize (ac_aligned xs) as Hs1. specialize (ac_aligned ys) as Hs2. specialize (ac_aligned zs) as Hs3.
    intros [Hsync|[Hsync|Hsync]]; repeat split; auto.
    - eapply aligned_EqSt in Hs1; eauto. rewrite Hs1, Hac1, <- Hac2; auto.
    - eapply aligned_EqSt in Hs1; eauto. rewrite Hs1, Hac1; auto.
    - eapply aligned_EqSt in Hs2; eauto. rewrite Hs2, Hac2, <- Hac1; auto.
    - eapply aligned_EqSt in Hs2; eauto. rewrite Hs2, Hac2; auto.
    - eapply aligned_EqSt in Hs3; eauto. rewrite Hs3, <- Hac1; auto.
    - eapply aligned_EqSt in Hs3; eauto. rewrite Hs3, <- Hac2; auto.
  Qed.

  Corollary arrow_aligned : forall bs xs ys rs zs,
      arrow xs ys rs zs ->
      (aligned xs bs \/ aligned ys bs \/ aligned zs bs) ->
      (aligned xs bs /\ aligned ys bs /\ aligned zs bs).
  Proof. intros. eapply arrow1_aligned; eauto. Qed.

  (** *** Additional facts *)

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
