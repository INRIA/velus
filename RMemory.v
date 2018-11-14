Require Import Velus.Common.

(* Require Import Coq.FSets.FMapPositive. *)
Require Import List.
Import List.ListNotations.

Require Velus.Environment.
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

Module Env := Environment.

Definition env := Env.t.

Inductive memory (V: Type) :=
  Mnode: env V -> env (memory V) -> memory V.

Definition values (V: Type) (m: memory V) : env V :=
  match m with Mnode xvs _ => xvs end.

Definition instances (V: Type) (m: memory V) : env (memory V) :=
  match m with Mnode _ xms => xms end.

Section memory_ind'.
  Variable V: Type.
  Variable P: memory V -> Prop.

  Hypothesis MnodeCase:
    forall xvs xms,
      Forall P (map snd xms) ->
      P (Mnode xvs xms).

  Fixpoint memory_ind' (m : memory V): P m.
  Proof.
    destruct m as [? xms].
    apply MnodeCase.
    induction xms; simpl; auto.
  Qed.

End memory_ind'.

(* Require Coq.FSets.FMapList. *)
(* Module PML := Coq.FSets.FMapList.Make Coq.Structures.OrderedTypeEx.PositiveOrderedTypeBits. *)

(* Check PML.find. *)

(* Inductive mem (A: Type): Type := *)
(*     { *)
(*       mems : PML.t A; *)
(*       insts : PML.t (mem A) *)
(*     }. *)



(* Fixpoint tree_ind' (A : Type) (P : tree A -> Prop) *)
(*          (H: forall n ts, *)
(*              Forall P (map snd ts) -> *)
(*              P {| node := n; children := ts |}) *)
(*          (t : tree A) : P t. *)
(* Proof. *)
(*   destruct t as [n ts]. *)
(*   apply H. *)
(*   induction ts. *)
(*   - simpl. apply Forall_nil. *)
(*   - simpl. apply Forall_cons. *)
(*     + apply tree_ind'. *)
(*       exact H. *)
(*     + exact IHts. *)
(* Qed. *)

(* Fixpoint size (A: Type) (t: tree A) : nat := *)
  (* fold_left (fun s t => s + size (snd t)) (children t) 1. *)

(* =memory= *)
(* Inductive memory (V: Type): Type := mk_memory { *)
(*   mm_values : PM.t V; *)
(*   mm_instances : PM.t (memory V) }. *)
(* =end= *)

(* Check mk_memory. *)
(* Require Import Coq.FSets.FMapFacts. *)

(* Module Import PMProp := Properties PM. *)

(* Fixpoint depth (V: Type) (m: memory V) : nat := *)
(*   match PM.elements (m.(mm_instances)) with *)
(*   | [] => 0 *)
(*   | (_, m) :: _ => 1 + depth m *)
(*   end. *)

(* Require Import Program. *)
(* Definition app_snd (A B C: Type) (f: B -> C) (x: A * B) := f (snd x). *)
(* Definition instances (V: Type) (ms: PM.t (memory V)) := map snd (PM.elements ms).  *)
(* Inductive memory' (V: Type): Type := *)
(*   MNode: PM.t V -> PM.t (memory' V) -> memory' V. *)

(* Check memory'_ind. *)

(* Section MemoryInd. *)
(*   Variable V: Type. *)
(*   Variable P: memory' V -> Prop. *)

(*   Hypothesis H: *)
(*     forall (vs : PM.t V) (ms : PM.t (memory' V)), *)
(*       (forall x m', PM.find x ms = Some m' -> P m') -> *)
(*       P (MNode vs ms). *)

(*   Print Forall_cons. *)
(*   Print map_induction_bis. *)

(*   Fixpoint memory_ind' (m: memory' V):  P m. *)
(*   Proof. *)
(*     induction m as [vs ms]. *)
(*     apply H. *)
(*     induction ms as [?? Eq| |] using map_induction_bis. *)
(*     - unfold PM.Equal in Eq. *)
(*       intros ** Find. *)
(*       eapply IHms1; rewrite Eq; eauto. *)
(*     - intros ** Find. *)
(*       rewrite PM.gempty in Find; discriminate. *)
(*     - intros y ** Find. *)
(*       destruct (ident_eq_dec y x). *)
(*       + subst. *)
(*         rewrite PM.gss in Find. *)
(*         apply memory_ind'. *)
(*       + rewrite PM.gso in Find; auto. *)
(*         Show Proof. *)
(*   Defined. *)


(*     := *)
(*     match m with *)
(*       MNode vs ms => *)
(*       H vs ms *)
(*         (map_induction_bis *)
(*            (P := fun ms0 : PM.t (memory' V) => forall (x : positive) (m' : memory' V), PM.find x ms0 = Some m' -> P m') *)
(*            (fun (ms1 ms2 : PM.t (memory' V)) (Eq : PM.Equal ms1 ms2) *)
(*               (IHms1 : forall (x : positive) (m' : memory' V), PM.find x ms1 = Some m' -> P m')  *)
(*               (x : positive) (m' : memory' V) (Find : PM.find x ms2 = Some m') => *)
(*               IHms1 x m' (eq_ind_r (fun o : option (memory' V) => o = Some m') Find (Eq x))) *)
(*            (fun (x : positive) (m' : memory' V) (Find : PM.find x (PM.empty (memory' V)) = Some m') => *)
(*               (fun Find0 : None = Some m' => *)
(*                  (fun H0 : False => (fun H1 : False => False_ind (P m') H1) H0) *)
(*                    (eq_ind None (fun e : option (memory' V) => match e with *)
(*                                                             | Some _ => False *)
(*                                                             | None => True *)
(*                                                             end) I  *)
(*                            (Some m') Find0)) *)
(*                 (eq_ind (PM.find x (PM.empty (memory' V)))  *)
(*                         (fun o : option (memory' V) => o = Some m') Find None  *)
(*                         (PM.gempty (memory' V) x))) *)
(*            (fun (x : PM.key) (e : memory' V) (ms0 : PM.t (memory' V))  *)
(*               (_ : ~ PM.In x ms0) (IHms : forall (x0 : positive) (m' : memory' V), PM.find x0 ms0 = Some m' -> P m') *)
(*               (y : positive) (m' : memory' V) (Find : PM.find y (PM.add x e ms0) = Some m') => *)
(*               let s := ident_eq_dec y x in *)
(*               match s with *)
(*               | left e0 => *)
(*                 eq_ind_r (fun y0 : positive => PM.find y0 (PM.add x e ms0) = Some m' -> P m') *)
(*                          (fun Find0 : PM.find x (PM.add x e ms0) = Some m' => *)
(*                             (fun _ : Some e = Some m' => memory_ind' m') *)
(*                               (eq_ind (PM.find x (PM.add x e ms0))  *)
(*                                       (fun o : option (memory' V) => o = Some m') Find0  *)
(*                                       (Some e) (PM.gss x e ms0))) e0 Find *)
(*               | right n => *)
(*                 (fun Find0 : PM.find y ms0 = Some m' => IHms y m' Find0) *)
(*                   (eq_ind (PM.find y (PM.add x e ms0))  *)
(*                           (fun o : option (memory' V) => o = Some m') Find  *)
(*                           (PM.find y ms0) (PM.gso e ms0 n)) *)
(*               end) ms) *)
(*     end. *)

(*     match m with *)
(*       MNode vs ms => *)
(*       H vs ms *)
(*         (let l := map snd (PM.elements ms) in *)
(*          (fix list_ind' (ms: list (memory' V)): Forall P ms := *)
(*             match ms with *)
(*             | [] => Forall_nil P *)
(*             | m :: ms => *)
(*               Forall_cons m (memory_ind' m) (list_ind' ms) *)
(*             end) l) *)
(*     end. *)

(* Section MemoryInd. *)
(*   Variable V: Type. *)
(*   Variable P: memory' V -> Prop. *)

(*   Hypothesis H: *)
(*     forall (vs : PM.t V) (ms : PM.t (memory' V)), *)
(*       Forall P (map snd (PM.elements ms)) -> *)
(*       P (MNode vs ms). *)

(*   Print Forall_cons. *)

(*   Fixpoint memory_ind' (m: memory' V):  P m := *)
(*     match m with *)
(*       MNode vs ms => *)
(*       H vs ms *)
(*         (let l := map snd (PM.elements ms) in *)
(*          (fix list_ind' (ms: list (memory' V)): Forall P ms := *)
(*             match ms with *)
(*             | [] => Forall_nil P *)
(*             | m :: ms => *)
(*               Forall_cons m (memory_ind' m) (list_ind' ms) *)
(*             end) l) *)
(*     end. *)

(* Proof. *)
(*   destruct m as [vs ms]. *)
(*   apply H. *)
(*   induction (PM.elements ms) as [|[? m]]; auto. *)
(* Qed. *)

(*   constructor; auto. *)
(*   simpl; apply memory_ind'. apply H. *)
(* Admitted. *)

(* End MemoryInd. *)

(* Fixpoint memory_ind'' (V : Type) (P : memory V -> Prop) *)
(*          (H: forall (vs : PM.t V) (ms : PM.t (memory V)), *)
(*              (forall x m', PM.find x ms = Some m' -> P m') -> *)
(*              P {| mm_values := vs; mm_instances := ms |}) (m : memory V) {struct m} : P m. *)
(* Proof. *)
(*   destruct m as [vs ms]. *)
(*   apply H. *)
(*   induction ms as [?? Eq| |] using map_induction_bis. *)
(*   - unfold PM.Equal in Eq. *)
(*     intros ** Find. *)
(*     eapply IHms1; rewrite Eq; eauto. *)
(*   - intros ** Find. *)
(*     rewrite PM.gempty in Find; discriminate. *)
(*   - intros y ** Find. *)
(*     destruct (ident_eq_dec y x). *)
(*     + subst. *)
(*       rewrite PM.gss in Find. *)
(*       apply memory_ind''. *)
(*       auto. *)
(*     + rewrite PM.gso in Find; auto. *)
(*       eapply IHms; eauto. *)
(* Qed. *)

(* Admitted. *)

(** ** Operations *)

Section Operations.

  Variable V W: Type.

  Definition empty_memory : memory V := Mnode [] [].

  Definition find_val (x: ident) (m: memory V) : option V :=
    Env.find x (values m).

  Definition find_inst (x: ident) (m: memory V) : option (memory V) :=
    Env.find x (instances m).

  Definition sub_inst (x: ident) (m m': memory V) : Prop :=
    find_inst x m = Some m'.

  Definition add_val (x: ident) (v: V) (m: memory V) : memory V :=
    Mnode (Env.add x v (values m)) (instances m).

  Definition add_inst (x: ident) (m': memory V) (m: memory V) : memory V :=
    Mnode (values m) (Env.add x m' (instances m)).

  Fixpoint mmap (f: V -> W) (m: memory V) : memory W :=
    Mnode (Env.map f (values m)) (Env.map (mmap f) (instances m)).

  Fixpoint mmapi (f: list ident -> ident -> V -> W) (p: list ident) (m: memory V) : memory W :=
    Mnode (Env.mapi (f p) (values m)) (Env.mapi (fun i => mmapi f (p ++ [i])) (instances m)).

End Operations.

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
    apply Env.find_map.
  Qed.

  Lemma find_val_mmapi:
    forall (f: list ident -> ident -> V -> W) p,
      find_val x (mmapi f p m) = option_map (f p x) (find_val x m).
  Proof.
    intros; unfold find_val.
    destruct m; simpl.
    apply Env.find_mapi.
  Qed.

  Lemma find_inst_mmap:
    find_inst x (mmap f m) = option_map (mmap f) (find_inst x m).
  Proof.
    unfold find_inst.
    destruct m; simpl.
    apply Env.find_map.
  Qed.

  Lemma find_inst_mmapi:
    forall (f: list ident -> ident -> V -> W) p,
      find_inst x (mmapi f p m) = option_map (mmapi f (p ++ [x])) (find_inst x m).
  Proof.
    intros; unfold find_inst.
    destruct m; simpl.
    apply Env.find_mapi.
  Qed.
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
