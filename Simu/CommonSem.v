Require common.Values.

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

Definition val_of_const c :=
  match c with
  | Cint i => Values.Vint i
  | Cfloat f => Values.Vfloat f
  | Csingle s => Values.Vsingle s
  | Clong l => Values.Vlong l
  end.

Inductive exp_eval (me: menv) (ve: venv): exp -> val -> Prop :=
| evar: forall x v ty,
    PM.MapsTo x v ve ->
    exp_eval me ve (Var x ty) v
| estate: forall x v ty,
    mfind_mem x me = Some v ->
    exp_eval me ve (State x ty) v
| econst: forall c ty,
    exp_eval me ve (Const c ty) (val_of_const c).

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

