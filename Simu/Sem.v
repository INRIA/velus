Require common.Values cfrontend.Cop.
Require Import lib.Integers lib.Floats.
        
Require Export Rustre.Common.
Require Export Rustre.RMemory.

Require Export Syn.

Ltac inv H := inversion H; clear H; subst.

(* SEMANTICS *)
Definition val: Type := Values.val.

Definition menv: Type := memory val.
Definition venv: Type := PM.t val.

Definition m_empty: menv := empty_memory _.
Definition v_empty: venv := PM.empty val.

Definition state := (menv * venv)%type.

Definition find_var (x: ident) (S: state) (v: val) := PM.find x (snd S) = Some v.
Definition find_field (x: ident) (S: state) (v: val) := mfind_mem x (fst S) = Some v.

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

Inductive exp_eval (S: state): exp -> val -> Prop :=
| evar: forall x v ty,
    find_var x S v ->
    exp_eval S (Var x ty) v
| estate: forall x v ty,
    find_field x S v ->
    exp_eval S (State x ty) v
| econst: forall c ty,
    exp_eval S (Const c ty) (val_of_const c).

Remark find_var_det:
  forall x v1 v2 S,
    find_var x S v1 ->
    find_var x S v2 ->
    v1 = v2.
Proof.
  unfold find_var.
  intros ** H1 H2.
  rewrite H1 in H2; inv H2; reflexivity.
Qed.

Remark find_field_det:
  forall x v1 v2 S,
    find_field x S v1 ->
    find_field x S v2 ->
    v1 = v2.
Proof.
  unfold find_field.
  intros ** H1 H2.
  rewrite H1 in H2; inv H2; reflexivity.
Qed.

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

Definition update_var (x: ident) (S: state) (v: val) := (fst S, PM.add x v (snd S)).
Definition update_field (x: ident) (S: state) (v: val) := (madd_mem x v (fst S), snd S).

(* =stmt_eval= *)
Inductive stmt_eval (S: state): stmt -> state -> Prop :=
| Iassign: forall x e v,
    exp_eval S e v ->
    stmt_eval S (Assign x e) (update_var x S v)
| Iassignst: forall x e v,
    exp_eval S e v ->
    stmt_eval S (AssignSt x e) (update_field x S v)
| Iifte: forall e m v b s1 s2 S',
    exp_eval S e v ->
    (forall ty attr, Ctypes.typeconv (typeof e) <> Ctypes.Tpointer ty attr) ->
    Cop.bool_val v (typeof e) m = Some b ->
    stmt_eval S (if b then s1 else s2) S' ->
    stmt_eval S (Ifte e s1 s2) S'    
| Icomp: forall s1 S2 s2 S3,
    stmt_eval S s1 S2 ->
    stmt_eval S2 s2 S3 ->
    stmt_eval S (Comp s1 s2) S3
| Iskip: 
    stmt_eval S Skip S.

Ltac app_bool_val :=
  match goal with
  | H: forall ty attr, Ctypes.typeconv ?t <> Ctypes.Tpointer ty attr,
    H1: Cop.bool_val ?v ?t ?m = Some ?b,
    H2: Cop.bool_val ?v ?t ?m' = Some ?b' |- _ =>
let Heq := fresh in
pose proof (bool_val_ptr v _ m m' H) as Heq; rewrite Heq in H1; rewrite H1 in H2; inv H2
end.

Theorem stmt_eval_det:
  forall S s S1 S2,
    stmt_eval S s S1 ->
    stmt_eval S s S2 ->
    S1 = S2.
Proof.
  intros until S2; intro Hev1; revert S2;
  induction Hev1; intros S2' Hev2; inv Hev2;
  try app_exp_eval_det; auto.
  - apply IHHev1.
    app_bool_val; auto.
  - assert (S2 = S0) as Heq by now apply IHHev1_1.
    apply IHHev1_2; rewrite Heq; auto.
Qed.

Ltac app_stmt_eval_det :=
  match goal with
  | H1: stmt_eval ?S ?s ?S1,
        H2: stmt_eval ?S ?s ?S2 |- _ =>
    let H := fresh in
    assert (S2 = S1) as H by (eapply stmt_eval_det; eauto); inv H; clear H2
  end.

(* Inductive cont := *)
(* | Kstop: cont *)
(* | Kseq: stmt -> cont -> cont. *)

(* (* =stmt_eval= *) *)
(* Inductive stmt_eval_cont: state * stmt * cont -> state * stmt * cont -> Prop := *)
(* | Iassign_cont: forall me ve x e v ve' k, *)
(*     exp_eval me ve e v -> *)
(*     PM.add x v ve = ve' -> *)
(*     stmt_eval_cont ((me, ve), Assign x e, k) ((me, ve'), Skip, k) *)
(* | Iassignst_cont: forall me ve x e v me' k, *)
(*     exp_eval me ve e v -> *)
(*     madd_mem x v me = me' -> *)
(*     stmt_eval_cont ((me, ve), AssignSt x e, k) ((me', ve), Skip, k) *)
(* | Iifte_cont: forall me ve m e v b s1 s2 k, *)
(*     exp_eval me ve e v -> *)
(*     (forall ty attr, Ctypes.typeconv (typeof e) <> Ctypes.Tpointer ty attr) -> *)
(*     Cop.bool_val v (typeof e) m = Some b -> *)
(*     stmt_eval_cont ((me, ve), Ifte e s1 s2, k) ((me, ve), if b then s1 else s2, k)     *)
(* | Icomp_cont: forall st s1 s2 k, *)
(*     stmt_eval_cont (st, Comp s1 s2, k) (st, s1, Kseq s2 k) *)
(* | Iskip_comp_cont: forall st s k, *)
(*     stmt_eval_cont (st, Skip, Kseq s k) (st, s, k). *)

(* Section SEQUENCES. *)
(*   Set Implicit Arguments. *)

(*   Variable A: Type.  *)
(*   Variable R: A -> A -> Prop.  *)

(*   Inductive star: A -> A -> Prop := *)
(*   | star_refl: forall a, *)
(*       star a a *)
(*   | star_step: forall a b c, *)
(*       R a b -> star b c -> star a c. *)

(*   Hint Constructors star. *)

(*   Lemma star_one: *)
(*     forall (a b: A), R a b -> star a b. *)
(*   Proof. *)
(*     intros. econstructor; eauto.  *)
(*   Qed. *)

(*   Lemma star_trans: *)
(*     forall (a b: A), star a b -> forall c, star b c -> star a c. *)
(*   Proof. *)
(*     induction 1; intros. auto. econstructor; eauto. *)
(*   Qed. *)

(*   Lemma one_star_trans: *)
(*     forall (a b: A), R a b -> forall c, star b c -> star a c. *)
(*   Proof. *)
(*     intros. econstructor; eauto. *)
(*   Qed. *)

(* End SEQUENCES. *)

(* Definition terminates (S: state) (s: stmt) (S': state) : Prop := *)
(*   star stmt_eval_cont (S, s, Kstop) (S', Skip, Kstop). *)

(* Hint Resolve star_one star_trans one_star_trans.  *)
(* Hint Constructors star stmt_eval_cont. *)

(* Theorem to_cont: *)
(*   forall S s S', *)
(*     stmt_eval S s S' -> *)
(*     forall k, star stmt_eval_cont (S, s, k) (S', Skip, k). *)
(* Proof. *)
(*   induction 1; eauto. *)
(* Qed. *)


(* Inductive keval: cont -> state -> state -> Prop := *)
(* | KE_stop: forall S, *)
(*     keval Kstop S S *)
(* | KE_seq: forall s k S S' S'', *)
(*     stmt_eval S s S' -> *)
(*     keval k S' S'' -> *)
(*     keval (Kseq s k) S S''. *)

(* Inductive skeval: state * stmt * cont -> state -> Prop := *)
(*   ske_intro: forall s k S S' S'', *)
(*       stmt_eval S s S' -> *)
(*       keval k S' S'' -> *)
(*       skeval (S, s, k) S''. *)

(* Require Import Coq.Program.Equality. *)

(* Hint Constructors stmt_eval. *)

(* Lemma stmt_eval_cont_skeval: *)
(*   forall S s k S' s' k', *)
(*     stmt_eval_cont (S, s, k) (S', s', k') -> *)
(*     forall S'', *)
(*       skeval (S', s', k') S'' -> *)
(*       skeval (S, s, k) S''. *)
(* Proof. *)
(*   intros until k'. intro STEP. dependent induction STEP; intros. *)
(*   - inv H0. inv H5. econstructor; eauto; auto. *)
(*   - inv H0. inv H5. econstructor; eauto; auto. *)
(*   - inv H2. destruct S'. econstructor. econstructor; eauto. auto. *)
(*   - inv H. inv H5. econstructor; eauto. destruct S', S'1, S'0. econstructor; eauto. *)
(*   - inv H. econstructor; eauto. econstructor; eauto. *)
(* Qed. *)

(* Lemma stmt_eval_cont_skeval': *)
(*   forall S s k S' s' k' S'', *)
(*     star stmt_eval_cont (S, s, k) (S', s', k') -> *)
(*     skeval (S', s', k') S'' -> *)
(*     skeval (S, s, k) S''. *)
(* Proof. *)
(*   intros; dependent induction H; auto. *)
(*   destruct b as [[S1 s1] k1]. *)
(*   eapply stmt_eval_cont_skeval; eauto. *)
(* Qed. *)

(* Hint Constructors keval. *)

(* Theorem from_cont: *)
(*   forall S s S', *)
(*   terminates S s S' -> stmt_eval S s S'. *)
(* Proof. *)
(*   unfold terminates; intros. *)
(*   assert (SKEV: skeval (S, s, Kstop) S'). *)
(*   - eapply stmt_eval_cont_skeval'; eauto. *)
(*     econstructor; eauto.  *)
(*   - inv SKEV. inv H5; auto. *)
(* Qed. *)
