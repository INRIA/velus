Require Import Coq.FSets.FMapPositive.

Require Import Rustre.Common.

Set Implicit Arguments.

(** * Memory *)

(** 

  Both Minimp and the Lustre rely on a rather structured notion of
  (static) memory, as found in object-oriented languages. Every node
  instance/class instance forms a node whose leafs are nodes/instances
  it is calling upon. This is captured by the [memory] tree-like
  datastructure.

 *)

(** ** Datatype *)

(* =memory= *)
Inductive memory (V: Type): Type := mk_memory {
  mm_values : PM.t V;
  mm_instances : PM.t (memory V) }.
(* =end= *)

(** ** Operations *) 

Section Operations.

  Variable A B: Type.
  Implicit Type menv : memory A.

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
  
End Operations.

(** ** Properties *)

Section Properties.
  
  Variable A B: Type.
  Variables (x y: ident)
            (v: A)
            (menv omenv: memory A).

  Lemma mfind_mem_gss:
      mfind_mem x (madd_mem x v menv) = Some v.
  Proof.
    unfold mfind_mem, madd_mem.
    now apply PM.gss.
  Qed.

  Lemma mfind_mem_gso:
      x <> y
      -> mfind_mem x (madd_mem y v menv) = mfind_mem x menv.
  Proof.
    unfold mfind_mem, madd_mem.
    now apply PM.gso.
  Qed.

  Lemma mfind_inst_gss:
      mfind_inst x (madd_obj x omenv menv) = Some omenv.
  Proof.
    unfold mfind_inst, madd_obj.
    now apply PM.gss.
  Qed.

  Lemma mfind_inst_gso:
      x <> y
      -> mfind_inst x (madd_obj y omenv menv) = mfind_inst x menv.
  Proof.
    unfold mfind_inst, madd_obj.
    now apply PM.gso.
  Qed.

  Lemma mfind_mem_add_inst:
      mfind_mem x (madd_obj y omenv menv) = mfind_mem x menv.
  Proof.
    unfold mfind_mem, madd_obj.
    reflexivity.
  Qed.

End Properties.