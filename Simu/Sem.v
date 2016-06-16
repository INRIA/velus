Require Import CommonSem.

Definition state := (menv * venv * stmt)%type.

(* =stmt_eval= *)
Inductive stmt_eval: state -> state -> Prop :=
| Iassign: forall me ve x e v ve',
    exp_eval me ve e v ->
    PM.add x v ve = ve' ->
    stmt_eval (me, ve, Assign x e) (me, ve', Skip)
| Iassignst: forall me ve x e v me',
    exp_eval me ve e v ->
    madd_mem x v me = me' ->
    stmt_eval (me, ve, AssignSt x e) (me', ve, Skip)
| Iifte: forall me ve m e v b s1 s2 me' ve',
    exp_eval me ve e v ->
    (forall ty attr, Ctypes.typeconv (typeof e) <> Ctypes.Tpointer ty attr) ->
    Cop.bool_val v (typeof e) m = Some b ->
    stmt_eval (me, ve, if b then s1 else s2) (me', ve', Skip) ->
    stmt_eval (me, ve, Ifte e s1 s2) (me', ve', Skip)
| Icomp: forall me1 ve1 s1 me2 ve2 s2 me3 ve3,
    stmt_eval (me1, ve1, s1) (me2, ve2, Skip) ->
    stmt_eval (me2, ve2, s2) (me3, ve3, Skip) ->
    stmt_eval (me1, ve1, Comp s1 s2) (me3, ve3, Skip)
| Iskip_comp: forall me ve s me' ve',
    stmt_eval (me, ve, s) (me', ve', Skip) ->
    stmt_eval (me, ve, Comp Skip s) (me', ve', Skip)
(* | Icomp_skip: forall me ve s me' ve', *)
(*     stmt_eval (me, ve, s) (me', ve', Skip) -> *)
(*     stmt_eval (me, ve, Comp s Skip) (me', ve', Skip) *).
(** ** Determinism of semantics *)

Theorem exp_eval_det:
  forall me ve e v1 v2,
    exp_eval me ve e v1 ->
    exp_eval me ve e v2 ->
    v1 = v2.
Proof.
  induction e; intros v1 v2 H1 H2;
  inversion H1 as [? ? ? Hv1|? ? ? Hv1|];
  inversion H2 as [? ? ? Hv2|? ? ? Hv2|];
  auto; unfold PM.MapsTo in *; rewrite Hv1 in Hv2; now injection Hv2.
Qed.

Ltac app_exp_eval_det :=
  match goal with
  | H1: exp_eval ?me ?ve ?e ?v1,
        H2: exp_eval ?me ?ve ?e ?v2 |- _ =>
    assert (v1 = v2) by (eapply exp_eval_det; eauto); subst v2; clear H2 
  end.

Ltac inv_stmt_eval :=
  match goal with
  | H: stmt_eval (_, _, Skip) _ |- _ => inversion H
  end.

Theorem stmt_eval_det:
  forall st st1 st2,
    stmt_eval st st1 ->
    stmt_eval st st2 ->
    st1 = st2.
Proof.
  intros.
  revert st2 H0. induction H; intros st2 H2'; inv H2';
                 ((app_exp_eval_det; auto) || inv_stmt_eval || idtac).
  - pose proof (bool_val_ptr v _ m0 m H0) as Hptr. rewrite Hptr in H11. rewrite H1 in H11; inv H11. apply IHstmt_eval in H12; auto.
  - apply IHstmt_eval1 in H6. inv H6. apply IHstmt_eval2; auto.
  - apply IHstmt_eval in H4; auto.
  (* - apply IHstmt_eval in H5; auto. *)
Qed.

Ltac app_stmt_eval_det :=
  match goal with
  | H1: stmt_eval ?st (?me1, ?ve1, ?s1),
        H2: stmt_eval ?st (?me2, ?ve2, ?s2) |- _ =>
    let H := fresh in
    assert ((me2, ve2, s2) = (me1, ve1, s1)) as H by (eapply stmt_eval_det; eauto); inv H; clear H2
  end.