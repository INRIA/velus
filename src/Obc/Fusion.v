From Coq Require Import FSets.FMapPositive.
From Coq Require Import PArith.
From Velus Require Import Common.
From Velus Require Import CommonTyping.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Obc.ObcSyntax.
From Velus Require Import Obc.ObcSemantics.
From Velus Require Import Obc.ObcInvariants.
From Velus Require Import Obc.ObcTyping.
From Velus Require Import Obc.Equiv.

From Velus Require Import VelusMemory.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Relations.
From Coq Require Import Morphisms.
From Coq Require Import Setoid.

Module Type FUSION
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import SynObc: OBCSYNTAX     Ids Op OpAux)
       (Import ComTyp: COMMONTYPING  Ids Op OpAux)
       (Import SemObc: OBCSEMANTICS  Ids Op OpAux SynObc)
       (Import InvObc: OBCINVARIANTS Ids Op OpAux SynObc        SemObc)
       (Import TypObc: OBCTYPING     Ids Op OpAux SynObc ComTyp SemObc)
       (Import Equ   : EQUIV         Ids Op OpAux SynObc ComTyp SemObc TypObc).

  (** ** Fusion functions *)

  Definition option_map2_defaults {A B C} (f: A -> B -> C) (da: A) (db: B) (oa: option A) (ob: option B) : option C :=
    match oa, ob with
    | Some a, Some b => Some (f a b)
    | Some a, None   => Some (f a db)
    | None, Some b   => Some (f da b)
    | None, None     => None
    end.

  Fixpoint zip s1 s2 : stmt :=
    match s1, s2 with
    | Switch e1 ss1 d1, Switch e2 ss2 d2 =>
      if e1 ==b e2
      then Switch e1 (CommonList.map2 (option_map2_defaults zip d1 d2) ss1 ss2) (zip d1 d2)
      else Comp s1 s2
    | Skip, s => s
    | s,    Skip => s
    | Comp s1' s2', _ => Comp s1' (zip s2' s2)
    | s1,   s2 => Comp s1 s2
    end.

  Fixpoint fuse' s1 s2 : stmt :=
    match s1, s2 with
    | s1, Comp s2 s3 => fuse' (zip s1 s2) s3
    | s1, s2 => zip s1 s2
    end.

  (*
      NB: almost got rid of zip, but this function decreases on the first
      argument, whereas the remaining instance of zip requires a decrease
      on the second argument...

      Fixpoint fuse' s1 s2 : stmt :=
        match s1, s2 with
        | Ifte e1 t1 f1, Ifte e2 t2 f2 =>
          if exp_eqb e1 e2
          then Ifte e1 (fuse' t1 t2) (fuse' f1 f2)
          else Comp s1 s2
        | s1, Comp s2 s3 => fuse' (fuse' s1 s2) s3
        | Skip, s => s
        | s,    Skip => s
        | Comp s1' s2', Ifte _ _ _ => Comp s1' (zip s2' s2)
        | s1,   s2 => Comp s1 s2
        end.
   *)

  Definition fuse s : stmt :=
    match s with
    | Comp s1 s2 => fuse' s1 s2
    | _ => s
    end.

  Definition fuse_method (m: method): method :=
    match m with
      mk_method name ins vars out body nodup good =>
      mk_method name ins vars out (fuse body) nodup good
    end.

  Lemma map_m_name_fuse_methods:
    forall methods,
      map m_name (map fuse_method methods) = map m_name methods.
  Proof.
    intro ms; induction ms as [|m ms]; auto.
    simpl. rewrite IHms.
    now destruct m.
  Qed.

  Program Definition fuse_class (c: class): class :=
    match c with
      mk_class name mems objs methods nodup _ _ =>
      mk_class name mems objs (map fuse_method methods) nodup _ _
    end.
  Next Obligation.
    now rewrite map_m_name_fuse_methods.
  Qed.

  Global Program Instance fuse_class_transform_unit: TransformUnit class class :=
    { transform_unit := fuse_class }.
  Next Obligation.
    unfold fuse_class; cases.
  Defined.

  Global Program Instance fuse_class_transform_state_unit: TransformStateUnit class class.
  Next Obligation.
    unfold fuse_class; cases.
  Defined.

  (** ** Basic lemmas around [fuse_class] and [fuse_method]. *)

  Lemma fuse_class_c_name:
    forall c, (fuse_class c).(c_name) = c.(c_name).
  Proof. destruct c; auto. Qed.

  Lemma fuse_class_c_objs:
    forall c,
      (fuse_class c).(c_objs) = c.(c_objs).
  Proof.
    unfold fuse_class. destruct c; auto.
  Qed.

  Lemma fuse_class_c_mems:
    forall c,
      (fuse_class c).(c_mems) = c.(c_mems).
  Proof.
    unfold fuse_class. destruct c; auto.
  Qed.

  Lemma fuse_method_m_name:
    forall m, (fuse_method m).(m_name) = m.(m_name).
  Proof. destruct m; auto. Qed.

  Lemma fuse_method_in:
    forall m, (fuse_method m).(m_in) = m.(m_in).
  Proof. destruct m; auto. Qed.

  Lemma fuse_method_out:
    forall m, (fuse_method m).(m_out) = m.(m_out).
  Proof. destruct m; auto. Qed.

  Lemma fuse_method_body:
    forall fm,
      (fuse_method fm).(m_body) = fuse fm.(m_body).
  Proof.
    now destruct fm.
  Qed.

  Definition fuse_program : program -> program := transform_units.

  Lemma fuse_find_class:
    forall p id c p',
      find_class id p = Some (c, p') ->
      find_class id (fuse_program p) = Some (fuse_class c, fuse_program p').
  Proof.
    intros * Find; apply find_unit_transform_units_forward in Find; auto.
  Qed.

  Lemma fuse_find_method:
    forall id c m,
      find_method id (fuse_class c).(c_methods) = Some m ->
      exists m', m = fuse_method m'
                 /\ find_method id c.(c_methods) = Some m'.
  Proof.
    intros * Find.
    destruct c as [? ? ? meths ? Nodup]; simpl in *.
    induction meths as [|m']; simpl in *; try discriminate.
    inv Nodup; auto.
    rewrite fuse_method_m_name in Find.
    destruct (ident_eqb (m_name m') id); auto.
    inv Find.
    exists m'; auto.
  Qed.

  Lemma map_fuse_class_c_name:
    forall p,
      map (fun cls => (fuse_class cls).(c_name)) p = map c_name p.
  Proof.
    induction p; auto.
    simpl. now rewrite IHp, fuse_class_c_name.
  Qed.

  Lemma fuse_find_method':
    forall f fm cls,
      find_method f cls.(c_methods) = Some fm ->
      find_method f (fuse_class cls).(c_methods) = Some (fuse_method fm).
  Proof.
    destruct cls; simpl.
    induction c_methods0 as [|m ms]; inversion 1.
    simpl.
    destruct (ident_eq_dec m.(m_name) f) as [He|Hne].
    - rewrite fuse_method_m_name, He, ident_eqb_refl in *.
      now injection H1; intro; subst.
    - apply ident_eqb_neq in Hne.
      rewrite fuse_method_m_name, Hne in *.
      inv c_nodupm0; auto.
  Qed.

  (** *** Reading the current, or last value of a variable *)

  Inductive read_var :=
  | RCurrent : ident -> read_var (* Temp variable, or current value of state variable *)
  | RLast : ident -> read_var. (* Last value of a state variable *)

  Inductive Is_free_in_exp : read_var -> exp -> Prop :=
  | FreeVar: forall i ty,
      Is_free_in_exp (RCurrent i) (Var i ty)
  | FreeState: forall i ty,
      Is_free_in_exp (RCurrent i) (State i ty false)
  | FreeLast: forall i ty,
      Is_free_in_exp (RLast i) (State i ty true)
  | FreeUnop: forall i op e ty,
      Is_free_in_exp i e ->
      Is_free_in_exp i (Unop op e ty)
  | FreeBinop: forall i op e1 e2 ty,
      Is_free_in_exp i e1 \/ Is_free_in_exp i e2 ->
      Is_free_in_exp i (Binop op e1 e2 ty)
  | FreeValid: forall i t,
      Is_free_in_exp (RCurrent i) (Valid i t).

  Inductive Is_free_in_stmt : read_var -> stmt -> Prop :=
  | FreeAssign: forall x y e,
      Is_free_in_exp x e ->
      Is_free_in_stmt x (Assign y e)
  | FreeAssignSt: forall x y e isreset,
      Is_free_in_exp x e ->
      Is_free_in_stmt x (AssignSt y e isreset)
  | FreeSwitch1: forall x e ss d,
      Is_free_in_exp x e ->
      Is_free_in_stmt x (Switch e ss d)
  | FreeSwitch2: forall x e ss d,
      Exists (fun s => Is_free_in_stmt x (or_default d s)) ss ->
      Is_free_in_stmt x (Switch e ss d)
  | FreeCall: forall x xs cls i f es,
      Exists (Is_free_in_exp x) es ->
      Is_free_in_stmt x (Call xs cls i f es)
  | FreeExternCall: forall x y f fty es,
      Exists (Is_free_in_exp x) es ->
      Is_free_in_stmt x (ExternCall y f es fty)
  | FreeComp1: forall x s1 s2,
      Is_free_in_stmt x s1 ->
      Is_free_in_stmt x (Comp s1 s2)
  | FreeComp2: forall x s1 s2,
      Is_free_in_stmt x s2 ->
      Is_free_in_stmt x (Comp s1 s2).

  Global Hint Constructors Is_free_in_stmt : obcinv.

  Lemma not_free_unop_inv : forall i op e ty,
      ~Is_free_in_exp i (Unop op e ty) ->
      ~Is_free_in_exp i e.
  Proof.
    auto using Is_free_in_exp.
  Qed.

  Lemma not_free_binop_inv : forall i op e1 e2 ty,
      ~Is_free_in_exp i (Binop op e1 e2 ty) ->
      ~Is_free_in_exp i e1 /\ ~Is_free_in_exp i e2.
  Proof.
    intros i op e1 e2 ty Hfree; split; intro H; apply Hfree;
      constructor; [now left | now right].
  Qed.

  Ltac not_free :=
    match goal with
    | H : ~Is_free_in_exp ?x (Var ?i _) |- _ =>
        let HH := fresh in
        let Eq := fresh in
        assert (HH : RCurrent i <> x) by (intro Eq; inv Eq; subst; apply H; constructor);
        clear H; rename HH into H
    | H : ~Is_free_in_exp (RCurrent ?x) (State ?i _ _) |- _ =>
        let HH := fresh in
        let Eq := fresh in
        assert (HH : i <> x) by (intro Eq; inv Eq; subst; apply H; constructor);
        clear H; rename HH into H
    | H : ~Is_free_in_exp (RLast ?x) (State ?i _ _) |- _ =>
        let HH := fresh in
        let Eq := fresh in
        assert (HH : i <> x) by (intro Eq; inv Eq; subst; apply H; constructor);
        clear H; rename HH into H
    | H : ~Is_free_in_exp ?x (Valid ?i _) |- _ =>
        let HH := fresh in
        let Eq := fresh in
        assert (HH : RCurrent i <> x) by (intro Eq; inv Eq; apply H; constructor);
        clear H; rename HH into H
    | H : ~Is_free_in_exp ?x (Unop _ _ _) |- _ =>
        apply not_free_unop_inv in H
    | H : ~Is_free_in_exp ?x (Binop ?op ?e1 ?e2 ?ty) |- _ =>
        destruct (not_free_binop_inv x op e1 e2 ty H)
    end.

  (** ** Determine whether an Obc command can modify a variable or state. *)

  Inductive write_var :=
  | WCurrent: ident -> write_var (* Temp variable, or current value of state variable *)
  | WReset : ident -> write_var. (* Reset write for state variable *)

  Inductive Can_write_in : write_var -> stmt -> Prop :=
  | CWIAssign: forall x e,
      Can_write_in (WCurrent x) (Assign x e)
  | CWIAssignSt: forall x e,
      Can_write_in (WCurrent x) (AssignSt x e false)
  | CWIAssignStReset: forall x e,
      Can_write_in (WReset x) (AssignSt x e true)
  | CWISwitch: forall x e ss d,
      Exists (fun s => Can_write_in x (or_default d s)) ss ->
      Can_write_in x (Switch e ss d)
  | CWICall_ap: forall x xs cls i f es,
      In x xs ->
      Can_write_in (WCurrent x) (Call xs cls i f es)
  | CWIExternCall: forall y f fty es,
      Can_write_in (WCurrent y) (ExternCall y f fty es)
  | CWIComp1: forall x s1 s2,
      Can_write_in x s1 ->
      Can_write_in x (Comp s1 s2)
  | CWIComp2: forall x s1 s2,
      Can_write_in x s2 ->
      Can_write_in x (Comp s1 s2).

  Global Hint Constructors Can_write_in : obcinv.

  Lemma cannot_write_in_Switch:
    forall x e ss d,
      ~ Can_write_in x (Switch e ss d)
      <->
      Forall (fun s => ~ Can_write_in x (or_default d s)) ss.
  Proof.
    intros; split; intro H.
    - induction ss; constructor; auto with obcinv.
      apply IHss; intro W; apply H.
      inv W; constructor. now right.
    - induction ss; intro HH; inv HH; inv H; take (Exists _ _) and inv it; eauto.
      apply IHss; auto with obcinv.
  Qed.

  Lemma Can_write_in_Comp:
    forall x s1 s2,
      Can_write_in x (Comp s1 s2) <-> (Can_write_in x s1 \/ Can_write_in x s2).
  Proof.
    split; intros HH.
    - inversion_clear HH; auto.
    - destruct HH; auto with obcinv.
  Qed.

  Lemma cannot_write_in_Comp:
    forall x s1 s2,
      ~ Can_write_in x (Comp s1 s2)
      <->
      ~ Can_write_in x s1 /\ ~ Can_write_in x s2.
  Proof.
    intros; split; intro; try (intro HH; inversion_clear HH); intuition.
  Qed.

  Lemma Can_write_in_Switch:
    forall e ss d x,
      Can_write_in x (Switch e ss d) <-> (Exists (fun s => Can_write_in x (or_default d s)) ss).
  Proof.
    split; [inversion_clear 1|intros [HH|HH]]; auto with obcinv.
  Qed.

  (** If we add irrelevent values to [ve], evaluation does not change. *)
  Lemma exp_eval_extend_venv : forall me ve x v' e v,
      ~Is_free_in_exp (RCurrent x) e ->
      (exp_eval me ve e v <-> exp_eval me (Env.add x v' ve) e v).
  Proof.
    intros me ve x v' e v Hfree.
    split; intro Heval.
    - revert v Hfree Heval.
      induction e; intros ? Hfree Heval; inv Heval;
        try not_free; eauto using exp_eval.
      + erewrite <-Env.gso; eauto; try constructor. congruence.
      + constructor; rewrite Env.gso; auto. congruence.
    - revert v Hfree Heval.
      induction e; intros ? Hfree Heval; inv Heval;
        try not_free; eauto using exp_eval.
      + erewrite Env.gso; eauto; try constructor. congruence.
      + constructor; erewrite <-Env.gso; eauto. congruence.
  Qed.

  Lemma exp_eval_adds_extend_venv:
    forall me e xs rvs ve v,
      (forall x, In x xs -> ~Is_free_in_exp (RCurrent x) e) ->
      (exp_eval me (Env.adds_opt xs rvs ve) e v <-> exp_eval me ve e v).
  Proof.
    induction xs as [|x xs IH]; destruct rvs as [|rv rvs]; auto; try reflexivity.
    destruct rv.
    2:now setoid_rewrite Env.adds_opt_cons_cons_None; auto with datatypes.
    intros ve v' Hnfree.
    rewrite Env.adds_opt_cons_cons, <-exp_eval_extend_venv; auto with datatypes.
  Qed.

  Lemma exp_eval_adds_opt_extend_venv:
    forall me e xs rvs ve v,
      (forall x, In x xs -> ~Is_free_in_exp (RCurrent x) e) ->
      (exp_eval me (Env.adds_opt xs rvs ve) e v <-> exp_eval me ve e v).
  Proof.
    induction xs as [|x xs IH]; destruct rvs as [|rv rvs]; auto; try reflexivity.
    intros ve v' Hnfree.
    destruct rv.
    - rewrite Env.adds_opt_cons_cons, <-exp_eval_extend_venv; auto with datatypes.
    - rewrite Env.adds_opt_cons_cons_None; auto with datatypes.
  Qed.

  (** If we add irrelevent values to [me], evaluation does not change. *)
  Lemma exp_eval_extend_menv : forall me ve x v' e v,
      ~Is_free_in_exp (RCurrent x) e ->
      ~Is_free_in_exp (RLast x) e ->
      (exp_eval (add_val x v' me) ve e v <-> exp_eval me ve e v).
  Proof.
    intros me ve x v' e v Hfree Hfreel. split.
    - revert v Hfree.
      induction e; intros v1 Hfree Heval; inv Heval;
        try do 2 not_free; try rewrite find_val_gso in *; eauto using exp_eval.
      + destruct b; not_free; auto.
      + clear Hfree. do 2 not_free. eauto using exp_eval.
    - revert v Hfree.
      induction e; intros v1 Hfree Heval; inv Heval;
        try do 2 not_free; eauto using exp_eval.
      + constructor; rewrite find_val_gso; auto.
        destruct b; not_free; auto.
      + clear Hfree. do 2 not_free. eauto using exp_eval.
  Qed.

  (** If we add objects to [me], evaluation does not change. *)
  Lemma exp_eval_extend_menv_by_obj : forall me ve f obj e v,
      exp_eval (add_inst f obj me) ve e v <-> exp_eval me ve e v.
  Proof.
    intros me ve f v' e v. split; revert v.
    - induction e; intros v1 Heval; inv Heval; eauto using exp_eval.
    - induction e; intros v1 Heval; inv Heval; eauto using exp_eval.
  Qed.

  Ltac cannot_write :=
    repeat progress
           match goal with
           | |- forall x, Is_free_in_exp x _ -> _ => intros
           | Hfw: (forall x, Is_free_in_exp x ?e -> _),
                  Hfree: Is_free_in_exp ?x ?e |- _
             => pose proof (Hfw x Hfree); clear Hfw
           | |- _ /\ _ => split
           | |- ~Can_write_in _ _ => intro
           | H: Can_write_in _ (Comp _ _) |- _ => inversion_clear H
           | _ => now intuition
           end.

  Local Hint Constructors Is_free_in_exp : obcinv.

  Lemma cannot_write_exp_eval:
    forall prog s me ve me' ve' e v,
      (forall x, Is_free_in_exp (RCurrent x) e \/ Is_free_in_exp (RLast x) e ->
            Can_write_in (WCurrent x) s \/ Can_write_in (WReset x) s -> False)
      -> exp_eval me ve e v
      -> stmt_eval prog me ve s (me', ve')
      -> exp_eval me' ve' e v.
  Proof.
    induction s using stmt_ind2; intros me ve me' ve' e' v Hfree Hexp Hstmt.
    - inv Hstmt.
      rewrite <-exp_eval_extend_venv; auto.
      intro Habs. apply (Hfree x); eauto with obcinv.
    - inv Hstmt.
      eapply exp_eval_extend_menv; eauto.
      1,2:intro Habs; apply (Hfree x); auto with obcinv.
      1,2:destruct isreset; eauto with obcinv.
    - inv Hstmt.
      take (nth_error _ _ = _) and eapply nth_error_In in it as Hin.
      pose proof Hin as Hin'; eapply Forall_forall in Hin'; eauto; simpl in Hin'.
      cases.
      eapply Hin'; eauto.
      intros ???; eapply Hfree; eauto.
      destruct H1; [left|right]; constructor; apply Exists_exists; eauto.
    - inv Hstmt.
      take (stmt_eval _ _ _ s1 _) and eapply IHs1 in it; eauto.
      take (stmt_eval _ _ _ s2 _) and eapply IHs2 in it; eauto.
      1,2:intros * F; specialize (Hfree _ F); now cannot_write.
    - inv Hstmt.
      apply exp_eval_extend_menv_by_obj.
      rewrite exp_eval_adds_opt_extend_venv; auto.
      intros x Hin Hfree'.
      eapply Hfree; eauto with obcinv.
    - inv Hstmt.
      rewrite <-exp_eval_extend_venv; auto.
      intros Habs. apply (Hfree y); eauto with obcinv.
    - now inv Hstmt.
  Qed.

  (** ** Invariant sufficient to justify semantic preservation of fusion. *)

  (*
   The property "Fusible (translate_tcs mems clkvars tcs)"
   is obtained from the form of the Stc program, using scheduling assumptions
  *)

  Inductive Fusible : stmt -> Prop :=
  | IFAssign: forall x e,
      Fusible (Assign x e)
  | IFAssignSt: forall x e isreset,
      Fusible (AssignSt x e isreset)
  | IFExternCall: forall x f es ty,
      Fusible (ExternCall x f es ty)
  | IFSwitch: forall e ss d,
      Forall (fun s => Fusible (or_default d s)) ss ->
      (forall x, Is_free_in_exp (RCurrent x) e -> Forall (fun s => ~(Can_write_in (WCurrent x) (or_default d s) \/ Can_write_in (WReset x) (or_default d s))) ss) ->
      (forall x, Is_free_in_exp (RLast x) e -> Forall (fun s => ~Can_write_in (WReset x) (or_default d s)) ss) ->
      Fusible (Switch e ss d)
  | IFStep_ap: forall xs cls i f es,
      Fusible (Call xs cls i f es)
  | IFComp: forall s1 s2,
      Fusible s1 ->
      Fusible s2 ->
      (forall x, Can_write_in (WCurrent x) s1 -> ~Is_free_in_stmt (RLast x) s2) ->
      Fusible (Comp s1 s2)
  | IFSkip:
      Fusible Skip.

  Global Hint Constructors Fusible : obcinv.

  Definition ClassFusible (c: class) : Prop :=
    Forall (fun m=> Fusible m.(m_body)) c.(c_methods).

  Definition ProgramFusible (p: program) : Prop :=
    Forall ClassFusible p.(classes).

  Lemma lift_Switch:
    forall e ss d1 tt d2,
      (forall x, Is_free_in_exp (RCurrent x) e \/ Is_free_in_exp (RLast x) e ->
            Forall (fun s => ~ (Can_write_in (WCurrent x) (or_default d1 s) \/ Can_write_in (WReset x) (or_default d1 s))) ss) ->
      stmt_eval_eq (Comp (Switch e ss d1) (Switch e tt d2))
                   (Switch e (CommonList.map2 (option_map2_defaults Comp d1 d2) ss tt) (Comp d1 d2)).
  Proof.
    intros * Hfw prog memv env menv' env'.
    split; intro Hstmt.
    - inversion_clear Hstmt as [| | | |? ? ? ? ? env'' menv'' ? ? Hs Ht| | ].
      inversion_clear Hs as   [| | | | |? ? ? ? ? ? ? ? ? ? Hx1 Nths Hss|].
      inversion_clear Ht as [| | | | |? ? ? ? ? ? ? ? ? ? Hx3 Ntht Hts|].
      econstructor; eauto.
      + assert (c0 = c); subst.
        { eapply cannot_write_exp_eval in Hx1; eauto.
          2:{ intros * F. specialize (Hfw _ F).
              apply nth_error_In in Nths. now simpl_Forall. }
          eapply exp_eval_det in Hx3; eauto. congruence.
        }
        pose proof (conj Nths Ntht) as Nth.
        apply combine_nth_error in Nth.
        rewrite map2_combine.
        apply map_nth_error with (f := fun '(a, b) => option_map2_defaults Comp d1 d2 a b); eauto.
      + simpl; unfold option_map2_defaults; cases; simpl in *; eauto with obcsem.
    - inversion_clear Hstmt as [| | | | |? ? ? ? ? ? ? ? ? ? Hx Hv Hs|].
      rewrite map2_combine in Hv.
      apply map_nth_error_inv in Hv as ((s1 & s2) & Nth & ?); subst.
      apply combine_nth_error in Nth as (Nths &?).
      unfold option_map2_defaults in Hs;
        cases; simpl in *; inv Hs; do 2 (econstructor; eauto);
        eapply cannot_write_exp_eval; eauto;
        intros * F; specialize (Hfw _ F);
        apply nth_error_In in Nths; now simpl_Forall.
  Qed.

  Lemma zip_Comp':
    forall s1 s2,
      Fusible s1 ->
      (forall x, Can_write_in (WCurrent x) s1 -> ~Is_free_in_stmt (RLast x) s2) ->
      stmt_eval_eq (zip s1 s2) (Comp s1 s2).
  Proof.
    induction s1 using stmt_ind2; destruct s2;
      try rewrite stmt_eval_eq_Comp_Skip1;
      try rewrite stmt_eval_eq_Comp_Skip2;
      try reflexivity;
      intros * Fus Cw; inv Fus; simpl;
      repeat progress
        match goal with
        | |- context [equiv_decb ?e1 ?e2]
          => destruct (equiv_decb e1 e2) eqn:Heq;
            (rewrite equiv_decb_equiv in Heq; rewrite <-Heq in * )
            || rewrite not_equiv_decb_equiv in Heq
        | H:Fusible ?s1, IH:context [stmt_eval_eq (zip ?s1 _) _] |- context [zip ?s1 ?s2]
          => rewrite IH with (1:=H)
        | |- forall _, _ -> _ => intros * Cw'; eapply Cw; eauto with obcinv
        (* | |- forall _, _ -> _ => intros * Cw' ?; eapply Cw2; eauto with obcinv *)
        end;
      try rewrite Comp_assoc;
      try reflexivity.
    rewrite lift_Switch.
    2:{ intros * [F|F]; eauto.
        simpl_Forall. intros [|]; [eapply Cw|]; eauto with obcinv.
        - constructor. solve_Exists.
        - eapply H5 in F. simpl_Forall. contradiction.
    }
    intros p me ve me' ve'.
    rewrite 2 map2_combine.
    split; inversion_clear 1.
    - take (nth_error _ _ = _) and apply map_nth_error_inv in it as ((os1 & os2) & Hin & ?); subst.
      pose proof Hin.
      apply combine_nth_error in Hin as (Hin1 & Hin2).
      apply nth_error_In in Hin1. apply nth_error_In in Hin2.
      do 2 (take (Forall _ _) and eapply Forall_forall in it; eauto).
      rename it into IH.
      take (stmt_eval _ _ _ _ _) and unfold option_map2_defaults in it.
      cases; simpl in *; take (stmt_eval _ _ _ _ _) and eapply IH in it; eauto;
        [econstructor; eauto; try erewrite map_nth_error; eauto
        |intros ? Cw' F'; eapply Cw;
         [econstructor|eapply FreeSwitch2]; solve_Exists].
    - take (nth_error _ _ = _) and apply map_nth_error_inv in it as ((os1 & os2) & Hin & ?); subst.
      pose proof Hin.
      apply combine_nth_error in Hin as (Hin1 & Hin2).
      apply nth_error_In in Hin1. apply nth_error_In in Hin2.
      do 2 (take (Forall _ _) and eapply Forall_forall in it; eauto).
      rename it into IH.
      take (stmt_eval _ _ _ _ _) and unfold option_map2_defaults in it.
      cases; simpl in *; take (stmt_eval _ _ _ _ _) and eapply IH in it; eauto;
        [econstructor; eauto; try erewrite map_nth_error; eauto
        |intros ? Cw' F'; eapply Cw;
         [econstructor|eapply FreeSwitch2]; solve_Exists].
  Qed.

  Section CannotWriteZip.

    Variables (p: program)
              (insts: list (ident * ident))
              (Γm: list (ident * type))
              (Γv: list (ident * type)).

    Lemma Can_write_in_zip:
      forall s1 s2 x,
        wt_stmt p insts Γm Γv s1 ->
        wt_stmt p insts Γm Γv s2 ->
        (Can_write_in x s1 \/ Can_write_in x s2)
        <-> Can_write_in x (zip s1 s2).
    Proof.
      induction s1 using stmt_ind2; destruct s2; simpl; inversion_clear 1; inversion_clear 1;
        repeat progress
               match goal with
               | H:Can_write_in _ (Comp _ _) |- _ => inversion H; subst; clear H
               | H:Can_write_in _ (Switch _ _ _) |- _ => inversion H; subst; clear H
               | H:Can_write_in _ Skip |- _ => now inversion H
               | |- context [equiv_decb ?e1 ?e2] =>
                 destruct (equiv_decb e1 e2) eqn:Heq
               | H:Can_write_in _ (zip _ _) |- _ =>
                 (apply IHs1_1 in H || apply IHs1_2 in H); eauto with obctyping obcinv
               | |- Can_write_in _ (Comp _ (zip _ _)) =>
                 now (apply CWIComp2; apply IHs1_2; eauto with obctyping obcinv; intuition)
               | _ => intuition eauto with obctyping obcinv
               end.
      - constructor.
        rewrite map2_combine, Exists_map, Exists_exists.
        take (Exists _ _) and apply Exists_exists in it as (d1 & Hin & Can).
        rewrite equiv_decb_equiv in Heq.
        assert (e = e0 ); auto; subst.
        match goal with H: typeof _ = _, H': typeof _ = _ |- _ => rewrite H in H'; inv H' end.
        assert (length l = length ss) by congruence.
        repeat take (Forall _ ss) and eapply Forall_forall in it; eauto.
        eapply length_in_left_combine with (l' := l) in Hin as (s & Hin); eauto.
        eexists; split; eauto.
        pose proof Hin as Hin'; apply in_combine_r in Hin; apply in_combine_l in Hin'.
        destruct d1, s; simpl in *; apply it; auto.
      - constructor.
        rewrite map2_combine, Exists_map, Exists_exists.
        take (Exists _ _) and apply Exists_exists in it as (d2 & Hin & Can).
        rewrite equiv_decb_equiv in Heq.
        assert (e = e0 ); auto; subst.
        match goal with H: typeof _ = _, H': typeof _ = _ |- _ => rewrite H in H'; inv H' end.
        assert (length l = length ss) by congruence.
        pose proof Hin as Hin'.
        eapply length_in_right_combine with (l := ss) in Hin as (s & Hin); eauto.
        eexists; split; eauto.
        apply in_combine_l in Hin.
        repeat take (Forall _ ss) and eapply Forall_forall in it; eauto.
        destruct d2, s; apply it; auto;
          eapply Forall_forall in Hin'; eauto; simpl in Hin'; auto.
      - take (Exists _ _) and apply Exists_exists in it as (s & Hin & Can).
        rewrite map2_combine, in_map_iff in Hin; destruct Hin as ((os1 & os2) & E & Hin); subst.
        pose proof Hin as Hin'.
        apply in_combine_l in Hin.
        apply in_combine_r in Hin'.
        repeat take (Forall _ _) and eapply Forall_forall in it; eauto; simpl in it.
        unfold option_map2_defaults in Can.
        cases; simpl in *; apply it in Can as [|]; auto;
          ((now left; constructor; apply Exists_exists; eauto) ||
           (now right; constructor; apply Exists_exists; eauto)).
    Qed.

    Corollary Cannot_write_in_zip:
      forall s1 s2 x,
        wt_stmt p insts Γm Γv s1 ->
        wt_stmt p insts Γm Γv s2 ->
        (~Can_write_in x s1 /\ ~Can_write_in x s2)
        <-> ~Can_write_in x (zip s1 s2).
    Proof.
      intros s1 s2 x.
      split; intro HH.
      - intro Hcan; eapply Can_write_in_zip in Hcan; intuition.
      - split; intro Hcan; apply HH; apply Can_write_in_zip; intuition.
    Qed.

    Lemma Can_write_in_var_zip:
      forall s1 s2 x,
        wt_stmt p insts Γm Γv s1 ->
        wt_stmt p insts Γm Γv s2 ->
        (Can_write_in_var x s1 \/ Can_write_in_var x s2)
        <-> Can_write_in_var x (zip s1 s2).
    Proof.
      induction s1 using stmt_ind2; destruct s2; simpl; inversion_clear 1; inversion_clear 1;
        repeat progress
               match goal with
               | H:Can_write_in_var _ (Comp _ _) |- _ => inversion H; subst; clear H
               | H:Can_write_in_var _ (Switch _ _ _) |- _ => inversion H; subst; clear H
               | H:Can_write_in_var _ Skip |- _ => now inversion H
               | |- context [equiv_decb ?e1 ?e2] =>
                 destruct (equiv_decb e1 e2) eqn:Heq
               | H:Can_write_in_var _ (zip _ _) |- _ =>
                 (apply IHs1_1 in H || apply IHs1_2 in H); eauto with obctyping obcinv
               | |- Can_write_in_var _ (Comp _ (zip _ _)) =>
                 now (apply CWIVComp2; apply IHs1_2; eauto with obctyping obcinv; intuition)
               | _ => intuition eauto with obctyping obcinv
               end.
      - constructor.
        rewrite map2_combine, Exists_map, Exists_exists.
        take (Exists _ _) and apply Exists_exists in it as (d1 & Hin & Can).
        rewrite equiv_decb_equiv in Heq.
        assert (e = e0 ); auto; subst.
        match goal with H: typeof _ = _, H': typeof _ = _ |- _ => rewrite H in H'; inv H' end.
        assert (length l = length ss) by congruence.
        repeat take (Forall _ ss) and eapply Forall_forall in it; eauto.
        eapply length_in_left_combine with (l' := l) in Hin as (s & Hin); eauto.
        eexists; split; eauto.
        pose proof Hin as Hin'; apply in_combine_r in Hin; apply in_combine_l in Hin'.
        destruct d1, s; simpl in *; apply it; auto.
      - constructor.
        rewrite map2_combine, Exists_map, Exists_exists.
        take (Exists _ _) and apply Exists_exists in it as (d2 & Hin & Can).
        rewrite equiv_decb_equiv in Heq.
        assert (e = e0 ); auto; subst.
        match goal with H: typeof _ = _, H': typeof _ = _ |- _ => rewrite H in H'; inv H' end.
        assert (length l = length ss) by congruence.
        pose proof Hin as Hin'.
        eapply length_in_right_combine with (l := ss) in Hin as (s & Hin); eauto.
        eexists; split; eauto.
        apply in_combine_l in Hin.
        repeat take (Forall _ ss) and eapply Forall_forall in it; eauto.
        destruct d2, s; apply it; auto;
          eapply Forall_forall in Hin'; eauto; simpl in Hin'; auto.
      - take (Exists _ _) and apply Exists_exists in it as (s & Hin & Can).
        rewrite map2_combine, in_map_iff in Hin; destruct Hin as ((os1 & os2) & E & Hin); subst.
        pose proof Hin as Hin'.
        apply in_combine_l in Hin.
        apply in_combine_r in Hin'.
        repeat take (Forall _ _) and eapply Forall_forall in it; eauto; simpl in it.
        unfold option_map2_defaults in Can.
        cases; simpl in *; apply it in Can as [|]; auto;
          ((now left; constructor; apply Exists_exists; eauto) ||
           (now right; constructor; apply Exists_exists; eauto)).
    Qed.

    Corollary Cannot_write_in_var_zip:
      forall s1 s2 x,
        wt_stmt p insts Γm Γv s1 ->
        wt_stmt p insts Γm Γv s2 ->
        (~Can_write_in_var x s1 /\ ~Can_write_in_var x s2)
        <-> ~Can_write_in_var x (zip s1 s2).
    Proof.
      intros s1 s2 x.
      split; intro HH.
      - intro Hcan; eapply Can_write_in_var_zip in Hcan; intuition.
      - split; intro Hcan; apply HH; apply Can_write_in_var_zip; intuition.
    Qed.

    Lemma zip_free_in_stmt : forall x s1 s2,
        Is_free_in_stmt x (zip s1 s2) ->
        Is_free_in_stmt x s1 \/ Is_free_in_stmt x s2.
    Proof.
      induction s1 using stmt_ind2; intros; simpl in *; cases; auto.
      2-7:take (Is_free_in_stmt _ (Comp _ _)) and inv it; auto using Is_free_in_stmt.
      2-7:match goal with
          | Hind: (forall _, Is_free_in_stmt _ (zip ?s1 _) -> _), H:Is_free_in_stmt _ (zip ?s1 _) |- _ =>
              apply Hind in H as [|]; auto using Is_free_in_stmt
          | _ => idtac
          end.
      rewrite map2_combine in H0.
      inv H0; auto using Is_free_in_stmt. simpl_Exists.
      apply in_combine_l in Hin as Inl. apply in_combine_r in Hin as InR. simpl_Forall.
      destruct o, o0; simpl in *.
      all:eapply H in H3 as [|]; [left|right]; apply FreeSwitch2; solve_Exists.
    Qed.

    Lemma zip_free_write:
      forall s1 s2,
        wt_stmt p insts Γm Γv s1 ->
        wt_stmt p insts Γm Γv s2 ->
        Fusible (Comp s1 s2) ->
        Fusible (zip s1 s2).
    Proof.
      induction s1 using stmt_ind2; destruct s2;
        intros WTs1 WTs2 Hfree1; inv WTs1; inv WTs2;
        inversion_clear Hfree1 as [| | | | |?? Hf1 Hf2 Cw|]; inv Hf1; inv Hf2;
        simpl; eauto with obctyping obcinv.
      2-7:econstructor; eauto 8 with obctyping obcinv.
      2-7:(intros * Cw' F'; apply zip_free_in_stmt in F' as [F'|F']; eauto 6;
           [|eapply Cw; eauto with obcinv]).
      2-7:take (forall x, _ -> ~Is_free_in_stmt _ s1_2) and eapply it; eauto.
      destruct (e ==b e0) eqn: E; eauto with obcinv.
      rewrite equiv_decb_equiv in E.
      assert (e = e0) by auto; subst.
      rewrite map2_combine.
      constructor.
      - apply Forall_map, Forall_forall.
        intros (s & s') Hin.
        pose proof Hin as Hin'.
        eapply in_combine_l in Hin.
        eapply in_combine_r in Hin'.
        simpl_Forall.
        unfold option_map2_defaults.
        cases; simpl in *; eapply H; eauto; econstructor; eauto.
        all:intros * Cw' F'; eapply Cw; [econstructor|eapply FreeSwitch2]; solve_Exists.
      - intros * Free.
        do 2 (take (forall x, Is_free_in_exp (RCurrent _) _ -> _) and (specialize (it _ Free))).
        apply Forall_map, Forall_forall.
        intros (s & s') Hin.
        pose proof Hin as Hin'.
        eapply in_combine_l in Hin.
        eapply in_combine_r in Hin'.
        simpl_Forall.
        unfold option_map2_defaults.
        cases; simpl in *; rewrite not_or', <- 2 Cannot_write_in_zip; eauto.
        all:repeat split; intros ?; try (now (eapply it; eauto)); try (now (eapply it0; eauto)).
      - intros * Free.
        do 2 (take (forall x, Is_free_in_exp (RLast _) _ -> _) and (specialize (it _ Free))).
        apply Forall_map, Forall_forall.
        intros (s & s') Hin.
        pose proof Hin as Hin'.
        eapply in_combine_l in Hin.
        eapply in_combine_r in Hin'.
        simpl_Forall.
        unfold option_map2_defaults.
        cases; simpl in *; rewrite <- Cannot_write_in_zip; eauto.
    Qed.

    Lemma wt_stmt_zip:
      forall s1 s2,
        wt_stmt p insts Γm Γv s1 ->
        wt_stmt p insts Γm Γv s2 ->
        wt_stmt p insts Γm Γv (zip s1 s2).
    Proof.
      induction s1 using stmt_ind2'; destruct s2; simpl; inversion_clear 1; inversion_clear 1; eauto with obctyping.
      cases_eqn E; eauto with obctyping.
      rewrite equiv_decb_equiv in E; assert (e = e0) by auto; subst.
      match goal with H: typeof _ = _, H': typeof _ = _ |- _ => rewrite H in H'; inv H' end.
      assert (length ss = length l) as E' by congruence.
      rewrite map2_combine.
      econstructor; eauto with obctyping.
      - rewrite map_length, combine_length. lia.
      - intros * Hin; apply in_map_iff in Hin as ((os1, os2) & Eq & Hin).
        pose proof Hin as Hin'; apply in_combine_l in Hin; apply in_combine_r in Hin'.
        take (Forall _ ss) and apply Forall_forall with (2 := Hin) in it; eauto.
        destruct os1, os2; simpl in *; inv Eq; eauto with obctyping.
    Qed.

    Lemma Can_write_in_var_fuse':
      forall s1 s2 x,
        wt_stmt p insts Γm Γv s1 ->
        wt_stmt p insts Γm Γv s2 ->
        Can_write_in_var x (Comp s1 s2) <-> Can_write_in_var x (fuse' s1 s2).
    Proof.
      intros s1 s2; revert s1; induction s2; simpl; intros;
        try setoid_rewrite <-Can_write_in_var_zip;
        try setoid_rewrite Can_write_in_var_Comp;
        try reflexivity; auto.
      take (wt_stmt _ _ _ _ (Comp _ _)) and inv it.
      setoid_rewrite <-IHs2_2; auto.
      - setoid_rewrite Can_write_in_var_Comp.
        setoid_rewrite <-Can_write_in_var_zip; auto.
        intuition.
      - apply wt_stmt_zip; auto.
    Qed.

    Corollary Can_write_in_var_fuse:
      forall s x,
        wt_stmt p insts Γm Γv s ->
        Can_write_in_var x s <-> Can_write_in_var x (fuse s).
    Proof.
      destruct s; simpl; try reflexivity.
      inversion_clear 1; apply Can_write_in_var_fuse'; auto.
    Qed.

    Lemma fuse'_Comp:
      forall s2 s1,
        wt_stmt p insts Γm Γv s1 ->
        wt_stmt p insts Γm Γv s2 ->
        Fusible (Comp s1 s2) ->
        stmt_eval_eq (fuse' s1 s2) (Comp s1 s2).
    Proof.
      induction s2 using stmt_ind2;
        intros s1 WTs1 WTs2 Fus; inv Fus; simpl; inv WTs2;
          try (rewrite zip_Comp'; intuition).
      rewrite Comp_assoc.
      take (Fusible (Comp _ _)) and inv it.
      rewrite IHs2_2; auto.
      - intros prog menv env menv' env'.
        rewrite zip_Comp'; auto.
        reflexivity.
        intros * Cw F.
        take (forall x, _ -> ~Is_free_in_stmt _ (Comp _ _)) and eapply it; eauto using Is_free_in_stmt.
      - apply wt_stmt_zip; auto.
      - constructor; auto.
        + apply zip_free_write; auto.
          constructor; auto.
          intros * Cw F.
          take (forall x, _ -> ~Is_free_in_stmt _ (Comp _ _)) and eapply it; eauto using Is_free_in_stmt.
        + intros * Cw.
          apply Can_write_in_zip in Cw as [Cw|Cw]; eauto.
          intros F. take (forall x, _ -> ~Is_free_in_stmt _ (Comp _ _)) and eapply it; eauto using Is_free_in_stmt.
    Qed.

    Corollary fuse_Comp:
      forall s,
        wt_stmt p insts Γm Γv s ->
        Fusible s ->
        stmt_eval_eq (fuse s) s.
    Proof.
      intros s WT Hfree prog menv env menv' env'.
      destruct s; simpl; try reflexivity.
      inv WT.
      apply fuse'_Comp; auto.
    Qed.

    Lemma No_Overwrites_zip:
      forall s1 s2,
        wt_stmt p insts Γm Γv s1 ->
        wt_stmt p insts Γm Γv s2 ->
        No_Overwrites (Comp s1 s2) ->
        No_Overwrites (zip s1 s2).
    Proof with eauto with obctyping obcinv.
      induction s1 using stmt_ind2; destruct s2; inversion_clear 1; inversion_clear 1;
        intros Hno; inv Hno; simpl; eauto with obcinv; repeat (take (No_Overwrites (_ _)) and inv it).
      2-7:constructor; eauto with obctyping obcinv; intros;
      repeat match goal with
             | |- ~ _ => intros contra
             | H:Can_write_in_var _ (zip _ _) |- _ =>
                 apply Can_write_in_var_zip in H as [|]; eauto with obctyping obcinv
             | Hc: Can_write_in_var _ ?e, Hnc: forall x, _ -> ~ Can_write_in_var _ ?e |- _ =>
                 try solve [eapply Hnc; eauto with obcinv]; clear Hnc
             | H: forall x, _ -> _ -> _ -> No_Overwrites (zip ?e1 _) |- No_Overwrites (zip ?e1 _) =>
                 eapply H; eauto with obctyping; constructor; eauto with obcinv; intros
             end.
      - destruct (e ==b e0)...
        constructor.
        rewrite map2_combine; apply Forall_map, Forall_forall; intros (os1, os2) Hin.
        pose proof Hin as Hin'; apply in_combine_l in Hin; apply in_combine_r in Hin'.
        repeat (take (Forall _ ss) and eapply Forall_forall with (2:=Hin) in it).
        repeat (take (Forall _ _) and eapply Forall_forall with (2:=Hin') in it).
        match goal with H: (forall x: ident, _), H': (forall x: ident, _) |- _ =>
                        rename H into Cannot1; rename H' into Cannot2 end.
        unfold option_map2_defaults;
          cases; simpl in *; apply it1; auto;
            constructor; auto; intros x Can_s Can_t;
              ((now eapply Cannot1; constructor; solve_Exists) ||
                 (now eapply Cannot2; constructor; solve_Exists)).
    Qed.

    Lemma No_Overwrites_fuse':
      forall s1 s2,
        wt_stmt p insts Γm Γv s1 ->
        wt_stmt p insts Γm Γv s2 ->
        No_Overwrites (Comp s1 s2) ->
        No_Overwrites (fuse' s1 s2).
    Proof.
      intros s1 s2; revert s1; induction s2; simpl; inversion_clear 2; inversion_clear 1;
        try apply No_Overwrites_zip; eauto with obctyping obcinv.
      match goal with H:No_Overwrites (Comp _ _) |- _ => inv H end.
      apply IHs2_2; auto with obctyping.
      - now apply wt_stmt_zip.
      - constructor; auto.
        + intros x Hcw.
          apply Can_write_in_var_zip in Hcw as [Hcw|Hcw]; auto.
          match goal with H:forall x, Can_write_in_var x s1 -> _ |- _ => apply H in Hcw end.
          apply cannot_write_in_var_Comp in Hcw as (? & ?); auto.
        + intros x Hcw; apply Cannot_write_in_var_zip; auto with obcinv.
        + apply No_Overwrites_zip; auto.
          constructor; auto with obcinv. intros x Hcw.
          match goal with H:forall x, Can_write_in_var x s1 -> _ |- _ => apply H in Hcw end.
          apply cannot_write_in_var_Comp in Hcw as (? & ?); auto with obcinv.
    Qed.

    Corollary No_Overwrites_fuse:
      forall s,
        wt_stmt p insts Γm Γv s ->
        No_Overwrites s ->
        No_Overwrites (fuse s).
    Proof.
      destruct s; intros WT Hnoo; auto; inv WT.
      now apply No_Overwrites_fuse'.
    Qed.

  End CannotWriteZip.

  Lemma fuse_call:
    forall p n me me' f xss rs,
      wt_program p ->
      ProgramFusible p ->
      stmt_call_eval p me n f xss me' rs ->
      stmt_call_eval (fuse_program p) me n f xss me' rs.
  Proof.
    cut ((forall p me ve stmt e',
             stmt_eval p me ve stmt e' ->
             wt_program p ->
             ProgramFusible p ->
             stmt_eval (fuse_program p) me ve stmt e')
         /\ (forall p me clsid f vs me' rvs,
                stmt_call_eval p me clsid f vs me' rvs ->
                wt_program p ->
                ProgramFusible p ->
                stmt_call_eval (fuse_program p) me clsid f vs me' rvs)).
    now destruct 1 as (Hf1 & Hf2); intros; apply Hf2; auto.
    apply stmt_eval_call_ind; intros; eauto using stmt_eval.
    take (find_class _ _ = _) and rename it into Find.
    take (find_method _ _ = _) and rename it into Findm.
    take (wt_program _) and rename it into WTp.
    take (ProgramFusible _) and rename it into Fusp.
    take (wt_program _ -> _) and rename it into IH.
    pose proof (find_unit_In _ _ _ _ Find) as [? Hinp].
    pose proof (find_method_In _ _ _ Findm) as Hinc.
    pose proof (find_unit_spec _ _ _ _ Find) as (?& Hprog').
    pose proof (wt_program_find_unit _ _ _ _ _ WTp Find) as (WTc & WTp').
    pose proof (wt_class_find_method _ _ _ _ WTc Findm) as (WTm & Henums).
    apply fuse_find_class in Find.
    apply fuse_find_method' in Findm.
    econstructor; eauto.
    - now rewrite fuse_method_in.
    - rewrite fuse_method_in.
      apply Forall_forall with (1:=Fusp) in Hinp.
      apply Forall_forall with (1:=Hinp) in Hinc.
      rewrite fuse_method_body.
      rewrite fuse_Comp with (2:=Hinc); eauto.
      destruct Hprog' as (cls'' & Hprog & Hfind).
      unfold ProgramFusible in Fusp; setoid_rewrite Hprog in Fusp.
      apply Forall_app in Fusp.
      rewrite Forall_cons2 in Fusp.
      apply IH; intuition.
    - now rewrite fuse_method_out; eassumption.
  Qed.

  Corollary fuse_loop_call:
    forall f c ins outs prog me,
      wt_program prog ->
      ProgramFusible prog ->
      loop_call prog c f ins outs 0 me ->
      loop_call (fuse_program prog) c f ins outs 0 me.
  Proof.
    intros ?????; generalize 0%nat.
    cofix COINDHYP.
    intros n me WT HCF Hdo.
    destruct Hdo.
    econstructor; eauto using fuse_call.
  Qed.

  (** ** Fusion preserves well-typing. *)

  Lemma wt_exp_fuse_program:
    forall p Γm Γv e,
      wt_exp p Γm Γv e ->
      wt_exp (fuse_program p) Γm Γv e.
  Proof.
    induction e; inversion_clear 1; eauto using wt_exp.
  Qed.

  Lemma wt_stmt_fuse_program:
    forall p insts Γm Γv s,
      wt_stmt p insts Γm Γv s ->
      wt_stmt (fuse_program p) insts Γm Γv s.
  Proof.
    induction s using stmt_ind2'; inversion_clear 1; eauto using wt_exp_fuse_program, wt_stmt.
    - econstructor; eauto using wt_exp_fuse_program.
      intros * Hin.
      take (Forall _ _) and eapply Forall_forall in it; eauto; simpl in *; eauto.
    - eapply wt_Call
        with (cls:=fuse_class cls) (p':=fuse_program p') (fm:=fuse_method fm);
        auto; try (now destruct fm; auto).
      + erewrite fuse_find_class; eauto.
      + now apply fuse_find_method'.
      + apply Forall_forall; intros * Hin.
        take (Forall _ _) and eapply Forall_forall in it; eauto using wt_exp_fuse_program.
    - econstructor; simpl_Forall; eauto using wt_exp_fuse_program.
  Qed.

  Lemma wt_stmt_fuse:
    forall p insts Γm Γv s,
      wt_stmt p insts Γm Γv s ->
      wt_stmt p insts Γm Γv (fuse s).
  Proof.
    intros * WTs.
    destruct s; auto; simpl; inv WTs.
    match goal with H1:wt_stmt _ _ _ _ s1, H2:wt_stmt _ _ _ _ s2 |- _ =>
                    revert s2 s1 H1 H2 end.
    induction s2; simpl; auto using wt_stmt_zip.
    intros s2 WTs1 WTcomp.
    inv WTcomp.
    apply IHs2_2; auto.
    apply wt_stmt_zip; auto.
  Qed.

  Lemma meth_vars_fuse_method:
    forall m,
      meth_vars (fuse_method m) = meth_vars m.
  Proof.
    destruct m; simpl; auto.
  Qed.

  Lemma fuse_wt_program:
    forall p,
      wt_program p ->
      wt_program (fuse_program p).
  Proof.
    intros * WT.
    eapply transform_units_wt_program in WT; eauto; simpl.
    inversion_clear 1 as (Hos & Hms).
    constructor.
    - rewrite fuse_class_c_objs.
      apply Forall_impl_In with (2:=Hos).
      intros ic Hin Hfind.
      apply not_None_is_Some in Hfind.
      destruct Hfind as ((cls & p') & Hfind).
      apply fuse_find_class in Hfind; unfold fuse_program in Hfind; simpl in *.
      setoid_rewrite Hfind.
      discriminate.
    - destruct u; simpl in *.
      clear c_nodup0 c_nodupm0 Hos.
      induction c_methods0 as [|m ms]; simpl; auto using Forall_nil.
      apply Forall_cons2 in Hms.
      destruct Hms as ((WTm & Henums) & WTms).
      apply Forall_cons; auto. clear IHms WTms.
      split; rewrite meth_vars_fuse_method; auto.
      destruct m; simpl in *.
      apply wt_stmt_fuse; eauto.
      apply wt_stmt_fuse_program in WTm; auto.
  Qed.

  Lemma fuse_wt_memory:
    forall me p c,
      wt_memory me p c.(c_mems) c.(c_objs) ->
      wt_memory me (fuse_program p) (fuse_class c).(c_mems) (fuse_class c).(c_objs).
  Proof.
    intros * WT.
    pose proof transform_units_wt_memory' as Spec; simpl in Spec.
    apply Spec in WT; auto.
  Qed.

  (** ** Fusion preserves [Can_write_in]. *)

  Lemma fuse_cannot_write_inputs:
    forall p,
      wt_program p ->
      Forall_methods (fun m => Forall (fun x => ~ Can_write_in_var x (m_body m)) (map fst (m_in m))) p ->
      Forall_methods (fun m => Forall (fun x => ~ Can_write_in_var x (m_body m)) (map fst (m_in m)))
                     (fuse_program p).
  Proof.
    intros * WTp HH.
    apply Forall_forall; intros * Hin;
      apply Forall_forall; intros * Hin';
        apply Forall_forall; intros ? Hin''.
    apply in_map_iff in Hin as (c &?& Hin); subst.
    edestruct In_find_unit as (?& Find); eauto using wt_program_nodup_classes.
    eapply wt_program_find_unit in Find as (WTc & ?); eauto; destruct WTc as (?& WTms).
    eapply Forall_forall in HH; eauto.
    destruct c; simpl in *.
    apply in_map_iff in Hin' as (m &?&?); subst.
    eapply Forall_forall in HH; eauto.
    eapply Forall_forall in WTms as (?&?); eauto.
    destruct m; simpl in *.
    eapply Forall_forall in HH; eauto.
    rewrite <-Can_write_in_var_fuse; eauto.
  Qed.

  (** ** Fusion preserves [No_Overwrites]. *)

  Lemma fuse_No_Overwrites:
    forall p,
      wt_program p ->
      Forall_methods (fun m => No_Overwrites (m_body m)) p ->
      Forall_methods (fun m => No_Overwrites (m_body m)) (fuse_program p).
  Proof.
    intros * WTp HH.
    apply Forall_forall; intros * Hin;
      apply Forall_forall; intros * Hin'.
    apply in_map_iff in Hin as (c &?&?); subst.
    edestruct In_find_unit as (?& Find); eauto using wt_program_nodup_classes.
    eapply wt_program_find_unit in Find as (WTc & ?); eauto; destruct WTc as (?& WTms).
    eapply Forall_forall in HH; eauto.
    destruct c; simpl in *.
    apply in_map_iff in Hin' as (m &?& Hin'); subst.
    eapply Forall_forall with (2 := Hin') in HH; eauto.
    eapply Forall_forall in WTms as (?&?); eauto.
    destruct m; simpl in *.
    eapply No_Overwrites_fuse; eauto.
  Qed.

End FUSION.

Module FusionFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (SynObc: OBCSYNTAX     Ids Op OpAux)
       (ComTyp: COMMONTYPING  Ids Op OpAux)
       (SemObc: OBCSEMANTICS  Ids Op OpAux SynObc)
       (InvObc: OBCINVARIANTS Ids Op OpAux SynObc         SemObc)
       (TypObc: OBCTYPING     Ids Op OpAux SynObc ComTyp SemObc)
       (Equ   : EQUIV         Ids Op OpAux SynObc ComTyp SemObc TypObc)
       <: FUSION Ids Op OpAux SynObc ComTyp SemObc InvObc TypObc Equ.
  Include FUSION Ids Op OpAux SynObc ComTyp SemObc InvObc TypObc Equ.
End FusionFun.
