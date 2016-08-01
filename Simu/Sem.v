Require common.Values cfrontend.Cop.
Require Import lib.Integers lib.Floats.
        
Require Import Rustre.Common.
Require Import Rustre.RMemory.
Require Import List.

Require Import Syn.

Require Import LibTactics.

(* SEMANTICS *)
Definition val: Type := Values.val.

Definition menv: Type := memory val.
Definition venv: Type := PM.t val.

Definition m_empty: menv := empty_memory _.
Definition v_empty: venv := PM.empty val.

Definition state := (menv * venv)%type.

Definition find_var (S: state) (x: ident) (v: val) :=
  PM.find x (snd S) = Some v.
Definition find_vars (S: state) (xs: list (ident * typ)) := 
  Forall2 (find_var S) (fst (split xs)). 

Lemma find_vars_cons:
  forall S xs vs x ty v,
    find_vars S ((x, ty) :: xs) (v :: vs) ->
    find_var S x v /\ find_vars S xs vs.
Proof.
  unfold find_vars, find_var; simpl.
  intros; destruct S. destruct (split xs); simpl in *.
  inverts H; simpl in *; split; auto.
Qed.

Definition find_field (S: state) (x: ident) (v: val) :=
  mfind_mem x (fst S) = Some v.
Definition find_inst (S: state) (o: ident) (me: memory val) :=
  mfind_inst o (fst S) = Some me.

Definition update_var (S: state) (x: ident) (v: val) :=
  (fst S, PM.add x v (snd S)).

Definition update_vars (S: state) (xs: list (ident * typ)) (vs: list val) :=
  (fst S, adds' xs vs (snd S)).

Theorem add_comm:
    forall x x' (v v': val) m,
      x <> x' ->
      PM.add x v (PM.add x' v' m) = PM.add x' v' (PM.add x v m).
Proof.
  induction x, x', m; simpl; intro Neq;
  ((f_equal; apply IHx; intro Eq; apply Neq; now inversion Eq) || now contradict Neq).
Qed.

Lemma adds'_cons_cons:
  forall xs x (t: typ) (v: val) vs S,
    ~ InMembers x xs ->
    adds' ((x, t) :: xs) (v :: vs) S = adds' xs vs (PM.add x v S).
Proof.
  unfold adds'.
  induction xs as [|(x', t')]; intros ** NotIn; simpl; auto.
  destruct vs as [|v']; simpl; auto.
  rewrite <-IHxs with (t:=t).
  - simpl.
    rewrite add_comm; auto.
    intro Eq.
    apply NotIn; subst.
    apply inmembers_eq.
  - now apply NotInMembers_cons in NotIn.
Qed.

Lemma update_vars_cons:
  forall S xs vs x ty v,
    NoDupMembers ((x, ty) :: xs) ->
    update_vars S ((x, ty) :: xs) (v :: vs) = update_vars (update_var S x v) xs vs.
Proof.
  introv Nodup.
  destruct S.
  unfold update_vars, update_var, adds'; simpl.
  f_equal.
  revert x v Nodup.
  induction (combine xs vs) as [|xtv]; intros; auto.
  simpl in *. 
  rewrite <-IHl; auto.
  destruct xtv  as ((x', t'), v'). 
  rewrite add_comm; auto.
  admit.
Qed.

    
Definition update_field (S: state) (x: ident) (v: val) :=
  (madd_mem x v (fst S), snd S).
Definition update_inst (S: state) (o: ident) (me: memory val) :=
  (madd_obj o me (fst S), snd S).

Definition val_of_const c :=
  match c with
  | Cint i => Values.Vint i
  | Cfloat f => Values.Vfloat f
  | Csingle s => Values.Vsingle s
  | Clong l => Values.Vlong l
  end.

Lemma bool_val_ptr:
  forall v t m m',
    (forall ty attr, Ctypes.typeconv t <> Ctypes.Tpointer ty attr) ->
    Cop.bool_val v t m = Cop.bool_val v t m'.
Proof.
  intros.
  unfold Cop.bool_val.
  destruct v, t; try destruct i0; try destruct f; simpl in *;
  (auto || (edestruct H; eauto)). 
Qed.

Definition chunk_of_type ty := AST.chunk_of_type (Ctypes.typ_of_type ty).

Definition valid_val (v: val) (t: typ): Prop :=
    Ctypes.access_mode t = Ctypes.By_value (chunk_of_type t)
    /\ v <> Values.Vundef
    /\ Values.Val.has_type v (Ctypes.typ_of_type t)
    /\ v = Values.Val.load_result (chunk_of_type t) v.

Inductive exp_eval (S: state): exp -> val -> Prop :=
| evar: forall x v ty,
    find_var S x v ->
    valid_val v ty ->
    exp_eval S (Var x ty) v
| estate: forall x v ty,
    find_field S x v ->
    valid_val v ty ->
    exp_eval S (State x ty) v
| econst: forall c ty,
    valid_val (val_of_const c) ty ->
    exp_eval S (Const c ty) (val_of_const c).

Remark find_var_det:
  forall x v1 v2 S,
    find_var S x v1 ->
    find_var S x v2 ->
    v1 = v2.
Proof.
  unfold find_var.
  intros ** H1 H2.
  rewrite H1 in H2; inverts H2; reflexivity.
Qed.

Ltac app_find_var_det :=
  match goal with
  | H1: find_var ?S ?x ?v1,
        H2: find_var ?S ?x ?v2 |- _ =>
    assert (v1 = v2) by (eapply find_var_det; eauto); subst v2; clear H2 
  end.

Remark find_vars_det:
  forall xs vs1 vs2 S,
    find_vars S xs vs1 ->
    find_vars S xs vs2 ->
    vs1 = vs2.
Proof.
  unfold find_vars.
  intros ** H1 H2.
  revert dependent vs2.
  induction H1; inversion 1; auto.  
  app_find_var_det; f_equal; auto. 
Qed.

Remark find_field_det:
  forall x v1 v2 S,
    find_field S x v1 ->
    find_field S x v2 ->
    v1 = v2.
Proof.
  unfold find_field.
  intros ** H1 H2.
  rewrite H1 in H2; inverts H2; reflexivity.
Qed.

Remark find_inst_det:
  forall x me1 me2 S,
    find_inst S x me1 ->
    find_inst S x me2 ->
    me1 = me2.
Proof.
  unfold find_inst.
  intros ** H1 H2.
  rewrite H1 in H2; inverts H2; reflexivity.
Qed.

Ltac app_find_inst_det :=
  match goal with
  | H1: find_inst ?S ?x ?me1,
        H2: find_inst ?S ?x ?me2 |- _ =>
    assert (me1 = me2) by (eapply find_inst_det; eauto); subst me2; clear H2 
  end.

Theorem exp_eval_det:
  forall S e v1 v2,
    exp_eval S e v1 ->
    exp_eval S e v2 ->
    v1 = v2.
Proof.
  induction e; intros v1 v2 H1 H2;
  inversion H1 as [? ? ? Hv1|? ? ? Hv1|];
  inversion H2 as [? ? ? Hv2|? ? ? Hv2|];
  [eapply find_var_det; eauto|eapply find_field_det; eauto|auto]. 
Qed.

Ltac app_exp_eval_det :=
  match goal with
  | H1: exp_eval ?S ?e ?v1,
        H2: exp_eval ?S ?e ?v2 |- _ =>
    assert (v1 = v2) by (eapply exp_eval_det; eauto); subst v2; clear H2 
  end.

Theorem exps_eval_det:
  forall S es vs1 vs2,
    Nelist.Forall2 (exp_eval S) es vs1 ->
    Nelist.Forall2 (exp_eval S) es vs2 ->
    vs1 = vs2.
Proof.
  induction es, vs1, vs2; intros H1 H2; inverts H1; inverts H2; app_exp_eval_det; auto.  
  f_equal; apply IHes; auto.
Qed.

Ltac app_exps_eval_det :=
  match goal with
  | H1: Nelist.Forall2 (exp_eval ?S) ?es ?vs1,
        H2: Nelist.Forall2 (exp_eval ?S) ?es ?vs2 |- _ =>
    assert (vs1 = vs2) by (eapply exps_eval_det; eauto); subst vs2; clear H2 
  end.

(* =stmt_eval= *)
Inductive stmt_eval: program -> state -> stmt -> state -> Prop :=
| Iassign: forall prog S x e v,
    exp_eval S e v ->
    stmt_eval prog S (Assign x e) (update_var S x v)
| Iassignst: forall prog S x e v,
    exp_eval S e v ->
    stmt_eval prog S (AssignSt x e) (update_field S x v)
| Iifte: forall prog S e m v b s1 s2 S',
    exp_eval S e v ->
    (forall ty attr, Ctypes.typeconv (typeof e) <> Ctypes.Tpointer ty attr) ->
    Cop.bool_val v (typeof e) m = Some b ->
    stmt_eval prog S (if b then s1 else s2) S' ->
    stmt_eval prog S (Ifte e s1 s2) S'    
| Icomp: forall prog S1 s1 S2 s2 S3,
    stmt_eval prog S1 s1 S2 ->
    stmt_eval prog S2 s2 S3 ->
    stmt_eval prog S1 (Comp s1 s2) S3
| Icall: forall prog S es vs clsid o f omenv omenv' rvs ys,
    find_inst S o omenv ->
    Forall2 (exp_eval S) es vs ->
    stmt_call_eval prog omenv clsid f vs omenv' rvs ->
    length ys = length rvs ->
    stmt_eval prog S (Call ys clsid o f es)
              (update_vars (update_inst S o omenv') ys rvs)
| Iskip: forall prog S,
    stmt_eval prog S Skip S

with stmt_call_eval: program -> menv -> ident -> ident -> list val -> menv -> list val -> Prop :=
     Iecall: forall prog prog' menv clsid f meth vs c S' rvs,
         find_class clsid prog = Some (c, prog') ->
         find_method f c.(c_methods) = Some meth ->
         stmt_eval prog' (update_vars (menv, v_empty) meth.(m_in) vs) meth.(m_body) S' ->
         find_vars S' meth.(m_out) rvs ->
         stmt_call_eval prog menv clsid f vs (fst S') rvs.

Scheme stmt_eval_ind_2 := Minimality for stmt_eval Sort Prop
                         with stmt_call_eval_ind_2 := Minimality for stmt_call_eval Sort Prop.
Combined Scheme stmt_eval_call_ind from stmt_eval_ind_2, stmt_call_eval_ind_2.

Ltac app_bool_val :=
  match goal with
  | H: forall ty attr, Ctypes.typeconv ?t <> Ctypes.Tpointer ty attr,
    H1: Cop.bool_val ?v ?t ?m = Some ?b,
    H2: Cop.bool_val ?v ?t ?m' = Some ?b' |- _ =>
let Heq := fresh in
pose proof (bool_val_ptr v _ m m' H) as Heq; rewrite Heq in H1; rewrite H1 in H2; inverts H2
end.

Lemma stmt_call_eval_det:
  forall prog me clsid f vs me1 rvs1 me2 rvs2,
    stmt_call_eval prog me clsid f vs me1 rvs1 ->
    stmt_call_eval prog me clsid f vs me2 rvs2 ->
    me1 = me2 /\ rvs1 = rvs2.
Proof.
  introv Hstp1; revert me2 rvs2.
  induction Hstp1 using stmt_call_eval_ind_2 with
  (P := fun p S s S' => forall S'', stmt_eval p S s S' -> stmt_eval p S s S'' -> S' = S'');
  try (introv Hev1 Hev2; inverts Hev2); try app_exp_eval_det; auto.
  - app_bool_val; auto.
  - apply* IHHstp0.
    asserts_rewrite* (S2 = S4).
  - assert (omenv = omenv0) by apply* find_inst_det; subst omenv0.
    assert (vs = vs0) by (eapply Forall2_det; eauto; eapply exp_eval_det); subst vs0.
    repeat fequals; apply* IHHstp1.
  - introv Hstp2; inverts Hstp2 as Hfindcls Hfindmeth.
    rewrite Hfindcls in H; inverts H.
    rewrite Hfindmeth in H0; inverts H0.
    assert (S' = S'0); auto; subst S'0.
    split*.
    apply* find_vars_det.
Qed.

Ltac app_stmt_step_eval_det :=
  match goal with
  | H1: stmt_call_eval ?prog ?me ?clsid ?f ?vs ?me1 ?rvs1,
        H2: stmt_call_eval ?prog ?me ?clsid ?f ?vs ?me2 ?rvs2 |- _ =>
    let H := fresh in
    assert (me1 = me2 /\ rvs1 = rvs2) as H by (eapply stmt_call_eval_det; eauto); inverts H; clear H2
  end.

Theorem stmt_eval_det:
  forall prog S s S1 S2,
    stmt_eval prog S s S1 ->
    stmt_eval prog S s S2 ->
    S1 = S2.
Proof.
  intros until S2; intro Hev1; revert S2;
  induction Hev1; intros S2' Hev2; inverts Hev2;
  try app_exp_eval_det; auto.
  - apply IHHev1.
    app_bool_val; auto.
  - apply IHHev1_2.
    asserts_rewrite* (S2 = S4).
  - assert (omenv = omenv0) by apply* find_inst_det; subst omenv0.
    assert (vs = vs0) by (eapply Forall2_det; eauto; eapply exp_eval_det); subst vs0.
    repeat fequals; apply* stmt_call_eval_det.
Qed.

Ltac app_stmt_eval_det :=
  match goal with
  | H1: stmt_eval ?prog ?S ?s ?S1,
        H2: stmt_eval ?prog ?S ?s ?S2 |- _ =>
    let H := fresh in
    assert (S2 = S1) as H by (eapply stmt_eval_det; eauto); inverts H; clear H2
  end.

Lemma stmt_step_eval_det': 
  forall prog1 prog2 me clsid f vs me1 rvs1 me2 rvs2, 
    WelldefClasses prog1 -> 
    stmt_call_eval prog1 me clsid f vs me1 rvs1 -> 
    stmt_call_eval prog2 me clsid f vs me2 rvs2 -> 
    sub_prog prog2 prog1 -> 
    me1 = me2 /\ rvs1 = rvs2. 
Proof. 
  introv WD Hstp1; revert me2 rvs2 prog2. 
  induction Hstp1 using stmt_call_eval_ind_2 with 
  (P := fun p S s S' => WelldefClasses p -> forall S'', stmt_eval p S s S' -> stmt_eval p S s S'' -> S' = S''); 
    [| | | | | |introv Hstp2 Hsub]; try (introv Hev1 Hev2; inverts Hev2); try app_exp_eval_det; auto.  
  - app_bool_val; auto. 
  - apply* IHHstp0. 
    asserts_rewrite* (S2 = S4). 
  - assert (omenv = omenv0) by apply* find_inst_det; subst omenv0. 
    assert (vs = vs0) by (eapply Forall2_det; eauto; eapply exp_eval_det); subst vs0. 
    repeat fequals; apply* IHHstp1; 
    rewrite* <-List.app_nil_l; simpl. 
  - inverts Hstp2. 
    forwards* H': find_class_sub_same. 
    rewrite H' in H; inverts H. 
    rewrite H0 in H4; inverts H4.
    forwards WD': find_class_welldef WD H'. 
    assert (S' = S'0); auto.
    subst S'0. 
    split*. 
    apply* find_vars_det. 
Qed. 
 
Theorem stmt_eval_det': 
  forall prog1 prog2 S s S1 S2, 
    WelldefClasses prog1 -> 
    stmt_eval prog1 S s S1 -> 
    stmt_eval prog2 S s S2 -> 
    sub_prog prog2 prog1 -> 
    S1 = S2. 
Proof. 
  intros until S2; intros WD Hev1; revert S2; 
  induction Hev1; intros S2' Hev2 Hsub; inverts Hev2; inverts Hsub; 
  try app_exp_eval_det; auto. 
  - apply* IHHev1. 
    app_bool_val; eauto.     
  - apply* IHHev1_2. 
    asserts_rewrite* (S2 = S4). 
  - assert (omenv = omenv0) by apply* find_inst_det; subst omenv0. 
    assert (vs = vs0) by (eapply Forall2_det; eauto; eapply exp_eval_det); subst vs0. 
    repeat fequals; apply* stmt_step_eval_det'. 
Qed. 
 
Ltac app_stmt_eval_det' := 
  match goal with 
  | H1: stmt_eval ?prog1 ?S ?s ?S1, 
        H2: stmt_eval ?prog2 ?S ?s ?S2, 
            H3: sub_prog ?prog2 ?prog1, 
                H4: WelldefClasses ?prog1 |- _ => 
    let H := fresh in 
    assert (S1 = S2) as H by (applys stmt_eval_det' H4 H1 H2 H3; eauto); inverts H; clear H2 
  end.