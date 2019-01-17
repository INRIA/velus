Require Import Velus.Common.

Require Import List.
Import List.ListNotations.

Set Implicit Arguments.

(** * Memory *)

(**

  Both Obc and the Lustre rely on a rather structured notion of
  (static) memory, as found in object-oriented languages. Every node
  instance/class instance forms a node whose leafs are nodes/instances
  it is calling upon. This is captured by the [memory] tree-like
  datastructure.

 *)

(** ** Datatype *)

Definition env := Env.t.

Inductive memory (V: Type) :=
  Mem {
      values: env V;
      instances: env (memory V)
    }.

Definition max (l: list nat) : nat :=
  fold_left (fun m x => if NPeano.leb x m then m else x) l 0.

(** ** Operations *)

Section Operations.

  Variable V W: Type.

  Definition empty_memory : memory V := Mem (Env.empty V) (Env.empty (memory V)).

  Definition find_val (x: ident) (m: memory V) : option V :=
    Env.find x (values m).

  Definition find_inst (x: ident) (m: memory V) : option (memory V) :=
    Env.find x (instances m).

  Definition sub_inst (x: ident) (m m': memory V) : Prop :=
    find_inst x m = Some m'.

  Definition add_val (x: ident) (v: V) (m: memory V) : memory V :=
    Mem (Env.add x v (values m)) (instances m).

  Definition add_vals (xs: list ident) (vs: list V) (m: memory V) : memory V :=
    Mem (Env.adds xs vs (values m)) (instances m).

  Definition add_inst (x: ident) (m': memory V) (m: memory V) : memory V :=
    Mem (values m) (Env.add x m' (instances m)).

  Fixpoint mmap (f: V -> W) (m: memory V) : memory W :=
    Mem (Env.map f (values m)) (Env.map (mmap f) (instances m)).

  (* Fixpoint mmapi (f: list ident -> ident -> V -> W) (p: list ident) (m: memory V) : memory W := *)
  (*   Mnode (Env.mapi (f p) (values m)) (Env.mapi (fun i => mmapi f (p ++ [i])) (instances m)). *)

End Operations.

(** ** Induction Scheme *)

Section MemoryInd.

  Variable V: Type.
  Variable P: memory V -> Prop.

  Hypothesis MemCase:
    forall m,
      (forall m' x, sub_inst x m m' -> P m') ->
      P m.

  Fixpoint memory_ind' (m : memory V): P m.
  Proof.
    unfold sub_inst, find_inst in MemCase.
    destruct m as [? xms].
    apply MemCase; simpl.
    induction xms; intros ** Find.
    - rewrite Env.gleaf in Find; discriminate.
    - destruct x; simpl in Find.
      + eapply IHxms2; eauto.
      + eapply IHxms1; eauto.
      + destruct o.
        * symmetry in Find; inv Find. apply memory_ind'.
        * discriminate.
  Qed.

End MemoryInd.


(** ** Properties *)

Section Properties.

  Variable V W: Type.
  Variables (x y: ident)
            (v: V)
            (f: V -> W)
            (m m': memory V).

  Lemma find_val_gss:
    find_val x (add_val x v m) = Some v.
  Proof.
    unfold find_val, add_val.
    now apply Env.gss.
  Qed.

  Lemma find_val_gso:
    x <> y ->
    find_val x (add_val y v m) = find_val x m.
  Proof.
    unfold find_val, add_val.
    now apply Env.gso.
  Qed.

  Lemma find_inst_gss:
      find_inst x (add_inst x m' m) = Some m'.
  Proof.
    unfold find_inst, add_inst.
    now apply Env.gss.
  Qed.

  Lemma find_inst_gso:
    x <> y ->
    find_inst x (add_inst y m' m) = find_inst x m.
  Proof.
    unfold find_inst, add_inst.
    now apply Env.gso.
  Qed.

  Lemma find_val_add_inst:
    find_val x (add_inst y m' m) = find_val x m.
  Proof.
    unfold find_val, add_inst.
    reflexivity.
  Qed.

  Lemma find_inst_add_val:
    find_inst x (add_val y v m) = find_inst x m.
  Proof.
    unfold find_inst, add_val.
    reflexivity.
  Qed.

  Lemma find_val_mmap:
    find_val x (mmap f m) = option_map f (find_val x m).
  Proof.
    unfold find_val.
    destruct m; simpl.
    apply Env.Props.P.F.map_o.
  Qed.

  (* Lemma find_val_mmapi: *)
  (*   forall (f: list ident -> ident -> V -> W) p, *)
  (*     find_val x (mmapi f p m) = option_map (f p x) (find_val x m). *)
  (* Proof. *)
  (*   intros; unfold find_val. *)
  (*   destruct m; simpl. *)
  (*   apply Env.find_mapi. *)
  (* Qed. *)

  Lemma find_inst_mmap:
    find_inst x (mmap f m) = option_map (mmap f) (find_inst x m).
  Proof.
    unfold find_inst.
    destruct m; simpl.
    apply Env.Props.P.F.map_o.
  Qed.

  (* Lemma find_inst_mmapi: *)
  (*   forall (f: list ident -> ident -> V -> W) p, *)
  (*     find_inst x (mmapi f p m) = option_map (mmapi f (p ++ [x])) (find_inst x m). *)
  (* Proof. *)
  (*   intros; unfold find_inst. *)
  (*   destruct m; simpl. *)
  (*   apply Env.find_mapi. *)
  (* Qed. *)
  (* Lemma values_mmap: *)
  (*   Env.map f (values m) = values (mmap f m). *)
  (* Proof. *)
  (*   intros; now destruct m. *)
  (* Qed. *)

  (* Lemma instances_mmap: *)
  (*   Env.map (mmap f) (instances m) = instances (mmap f m). *)
  (* Proof. *)
  (*   intros; now destruct m. *)
  (* Qed. *)

  (* Lemma values_mmapi: *)
  (*   forall (g: list ident -> ident -> V -> W) p, *)
  (*     Env.mapi (g p) (values m) = values (mmapi g p m). *)
  (* Proof. *)
  (*   intros; now destruct m. *)
  (* Qed. *)

  (* Lemma instances_mmapi: *)
  (*   forall (g: list ident -> ident -> V -> W) p, *)
  (*     Env.mapi (fun i => mmapi g (p ++ [i])) (instances m) = instances (mmapi g p m). *)
  (* Proof. *)
  (*   intros; now destruct m. *)
  (* Qed. *)

End Properties.
