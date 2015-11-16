Require Import Coq.FSets.FMapPositive.

Require Import Rustre.Common.

Set Implicit Arguments.

Inductive memory (A: Type): Type := mk_memory {
  mm_values : PM.t A;
  mm_instances : PM.t (memory A)
}.

Section Operations.

  Variable A B: Type.
  Implicit Type menv: memory A.

  Definition map (f: A -> B)(m: memory A): memory B. Admitted.

  Definition empty_memory : memory A :=
    {| mm_values := PM.empty _;
       mm_instances := PM.empty _ |}.

  Definition mfind_mem x menv := PM.find x menv.(mm_values).
  Definition mfind_inst x menv := PM.find x menv.(mm_instances).

  Definition madd_mem (id: ident) (v: A) (M: memory A) : memory A :=
    mk_memory (PM.add id v M.(mm_values))
              M.(mm_instances).

  Definition madd_obj (id: ident) (M': memory A) (M: memory A) : memory A :=
    mk_memory M.(mm_values)
                  (PM.add id M' M.(mm_instances)).
  
  Lemma mfind_mem_gss:
    forall x v M,
      mfind_mem x (madd_mem x v M) = Some v.
  Proof.
    intros x v M.
    unfold mfind_mem, madd_mem.
    now apply PM.gss.
  Qed.

  Lemma mfind_mem_gso:
    forall x y v M,
      x <> y
      -> mfind_mem x (madd_mem y v M) = mfind_mem x M.
  Proof.
    intros x y v M.
    unfold mfind_mem, madd_mem.
    now apply PM.gso.
  Qed.

  Lemma mfind_inst_gss:
    forall x v M,
      mfind_inst x (madd_obj x v M) = Some v.
  Proof.
    intros x v M.
    unfold mfind_inst, madd_obj.
    now apply PM.gss.
  Qed.

  Lemma mfind_inst_gso:
    forall x y v M,
      x <> y
      -> mfind_inst x (madd_obj y v M) = mfind_inst x M.
  Proof.
    intros x y v M.
    unfold mfind_inst, madd_obj.
    now apply PM.gso.
  Qed.

  Lemma mfind_mem_add_inst:
    forall x y omenv menv,
      mfind_mem x (madd_obj y omenv menv) = mfind_mem x menv.
  Proof.
    unfold mfind_mem, madd_obj.
    reflexivity.
  Qed.
  
(*
Lemma find_mem_gss:
  forall y c m, mfind_mem y (madd_mem y c m) = Some c.
Proof.
  intros. apply PM.gss.
Qed.

Lemma find_mem_gso:
  forall x y c m, x <> y -> find_mem x (add_mem y c m) = find_mem x m.
Proof.
  intros. apply PM.gso. assumption.
Qed.

Lemma find_obj_gss:
  forall y c m, find_obj y (add_obj y c m) = Some c.
Proof.
  intros. apply PM.gss.
Qed.

Lemma find_obj_gso:
  forall x y c m, x <> y -> find_obj x (add_obj y c m) = find_obj x m.
Proof.
  intros. apply PM.gso. assumption.
Qed.

Lemma find_mem_add_obj:
  forall x y omenv menv,
    find_mem x (add_obj y omenv menv) = find_mem x menv.
Proof.
  unfold find_mem, add_obj.
  reflexivity.
Qed.

*)

End Operations.