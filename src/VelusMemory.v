From Velus Require Import Common.
From Velus Require Import Environment.

From Coq Require Import Setoid Morphisms.
From Coq Require Import List.
Import List.ListNotations.

Set Implicit Arguments.

(** * VelusMemory *)

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

(** ** Operations *)

Section Operations.

  Variable V W: Type.

  Definition empty_memory : memory V := Mem (Env.empty V) (Env.empty (memory V)).

  Definition find_val (x: ident) (m: memory V) : option V :=
    Env.find x (values m).

  Definition find_inst (x: ident) (m: memory V) : option (memory V) :=
    Env.find x (instances m).

  Definition add_val (x: ident) (v: V) (m: memory V) : memory V :=
    Mem (Env.add x v (values m)) (instances m).

  Definition add_inst (x: ident) (m': memory V) (m: memory V) : memory V :=
    Mem (values m) (Env.add x m' (instances m)).

  Fixpoint mmap (f: V -> W) (m: memory V) : memory W :=
    Mem (Env.map f (values m)) (Env.map (mmap f) (instances m)).

  Definition remove_inst (x: ident) (m: memory V) : memory V :=
    Mem (values m) (Env.remove x (instances m)).

  Definition remove_val (x: ident) (m: memory V) : memory V :=
    Mem (Env.remove x (values m)) (instances m).

End Operations.

(** ** Induction Scheme *)

Section VelusMemoryInd.

  Variable V: Type.
  Variable P: memory V -> Prop.

  Hypothesis MemCase:
    forall m,
      (forall m' x, find_inst x m = Some m' -> P m') ->
      P m.

  Fixpoint memory_ind' (m : memory V): P m.
  Proof.
    unfold find_inst in MemCase.
    destruct m as [? xms].
    apply MemCase; simpl.
    induction xms; intros * Find.
    - rewrite Env.gleaf in Find; discriminate.
    - destruct x; simpl in Find.
      + eapply IHxms2; eauto.
      + eapply IHxms1; eauto.
      + destruct o.
        * symmetry in Find; inv Find. apply memory_ind'.
        * discriminate.
  Qed.

End VelusMemoryInd.

Inductive equal_memory {V: Type} : memory V -> memory V -> Prop :=
  equal_memory_intro:
    forall m m',
      Env.Equal (values m) (values m') ->
      Env.Equiv equal_memory (instances m) (instances m') ->
      equal_memory m m'.

Infix "≋" := equal_memory (at level 70, no associativity).
Infix "⌈≋⌉" := (orel equal_memory) (at level 70, no associativity).

Section EqualVelusMemory.

  Context {V: Type}.

  Lemma equal_memory_refl:
    forall (m: memory V),
      m ≋ m.
  Proof.
    induction m as [? IH] using memory_ind'.
    constructor.
    - reflexivity.
    - split.
      + reflexivity.
      + intros * Find ?.
        eapply Env.Props.P.F.MapsTo_fun in Find; eauto.
        rewrite <-Find; eauto.
  Qed.

  Lemma equal_memory_sym:
  forall (m m': memory V),
    m ≋ m' -> m' ≋ m.
  Proof.
    induction m as [? IH] using memory_ind'.
    inversion_clear 1 as [?? Vals Insts].
    constructor.
    - now symmetry.
    - destruct Insts as (Insts1 & Insts2); split.
      now symmetry; auto.
      intros k e1 e2 M1 M2.
      eapply Insts2 in M1; eauto.
  Qed.

  Lemma equal_memory_trans:
    forall (m1 m2 m3: memory V),
      m1 ≋ m2 -> m2 ≋ m3 -> m1 ≋ m3.
  Proof.
    induction m1 as [? IH] using memory_ind'.
    inversion_clear 1 as [?? Vals12 Insts12];
      inversion_clear 1 as [?? Vals23 Insts23].
    constructor.
    - now rewrite Vals12.
    - destruct Insts12 as (In12 & HMapsTo12).
      destruct Insts23 as (?& HMapsTo23).
      split.
      + now setoid_rewrite In12.
      + intros * Find1 Find3.
        assert (exists e'', Env.MapsTo k e'' (instances m2)) as (e'' &?).
        { setoid_rewrite Env.Props.P.F.find_mapsto_iff.
          rewrite <-Env.In_find, <-In12, Env.In_find.
          setoid_rewrite <-Env.Props.P.F.find_mapsto_iff; eauto.
        }
      pose proof Find1.
      apply (HMapsTo12 _ _ e'') in Find1; auto.
      apply (HMapsTo23 _ e'') in Find3; eauto.
  Qed.

  Add Relation (memory V) equal_memory
    reflexivity proved by equal_memory_refl
    symmetry proved by equal_memory_sym
    transitivity proved by equal_memory_trans
      as equal_memory_rel.

End EqualVelusMemory.

Existing Instance equal_memory_rel.
Hint Immediate equal_memory_rel_Reflexive.
Hint Immediate equal_memory_rel_Transitive.

Add Parametric Morphism V: (@values V)
    with signature equal_memory ==> Env.Equal
      as values_equal_memory.
Proof.
  intros * E x.
  inversion_clear E as [?? Vals]; now rewrite Vals.
Qed.

Add Parametric Morphism V: (@instances V)
    with signature equal_memory ==> Env.Equiv equal_memory
      as instances_equal_memory.
Proof.
  intros * E.
  inversion_clear E as [??? Insts]; auto.
Qed.

Add Parametric Morphism V x: (@add_inst V x)
    with signature equal_memory ==> equal_memory ==> equal_memory
      as add_inst_equal_memory.
Proof.
  intros ? ?  E1  ? ? E2.
  constructor; simpl; rewrite E2.
  + reflexivity.
  + now rewrite E1.
Qed.

Add Parametric Morphism V x: (@add_val V x)
    with signature eq ==> equal_memory ==> equal_memory
      as add_val_equal_memory.
Proof.
  intros * E.
  constructor; simpl; rewrite E; reflexivity.
Qed.

Add Parametric Morphism V x: (@find_val V x)
    with signature equal_memory ==> eq
      as find_val_equal_memory.
Proof.
  intros * E.
  inversion_clear E as [?? Vals].
  apply Vals.
Qed.

(** ** Properties *)

Section Properties.

  Variable V: Type.
  Variables (x y: ident)
            (v: V)
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
    forall W (f: V -> W),
      find_val x (mmap f m) = option_map f (find_val x m).
  Proof.
    unfold find_val.
    destruct m; simpl.
    intros; apply Env.Props.P.F.map_o.
  Qed.

  Lemma find_inst_mmap:
    forall W (f: V -> W),
      find_inst x (mmap f m) = option_map (mmap f) (find_inst x m).
  Proof.
    unfold find_inst.
    destruct m; simpl.
    intros; apply Env.Props.P.F.map_o.
  Qed.

  Lemma add_remove_inst_same:
    find_inst x m = Some m' ->
    m ≋ add_inst x m' (remove_inst x m).
  Proof.
    unfold add_inst, find_inst; intros * Find.
    constructor; simpl.
    - reflexivity.
    - split.
      + setoid_rewrite Env.Props.P.F.add_in_iff;
          setoid_rewrite Env.Props.P.F.remove_in_iff.
        split; intros * Hin.
        * destruct (ident_eq_dec x k); auto.
        * destruct Hin; try tauto.
          subst; apply Env.In_find; eauto.
      + intros * HMapsTo Hremove.
        rewrite Env.Props.P.F.add_mapsto_iff, Env.Props.P.F.remove_mapsto_iff in Hremove.
        destruct Hremove as [(?&?)|(?&?& HMapsTo')].
        * subst.
          apply Env.find_1 in HMapsTo; rewrite HMapsTo in Find; inv Find.
          reflexivity.
        * eapply Env.Props.P.F.MapsTo_fun in HMapsTo as <-; eauto.
          reflexivity.
  Qed.

  Lemma find_inst_grs:
    find_inst x (remove_inst x m) = None.
  Proof.
    intros; apply Env.grs.
  Qed.

  Lemma find_inst_gro:
    x <> y ->
    find_inst x (remove_inst y m) = find_inst x m.
  Proof.
    intros; apply Env.gro; auto.
  Qed.

  Lemma add_remove_val_same:
    find_val x m = Some v ->
    m ≋ add_val x v (remove_val x m).
  Proof.
    unfold add_val, find_val; intros * Find.
    constructor; simpl.
    - intro z.
      destruct (ident_eq_dec z x).
      + subst; now rewrite Env.gss.
      + rewrite Env.gso, Env.gro; auto.
    - reflexivity.
  Qed.

  Lemma find_val_grs:
    find_val x (remove_val x m) = None.
  Proof.
    intros; apply Env.grs.
  Qed.

  Lemma find_val_gro:
    x <> y ->
    find_val x (remove_val y m) = find_val x m.
  Proof.
    intros; apply Env.gro; auto.
  Qed.

  Lemma find_inst_gempty:
    find_inst x (empty_memory V) = None.
  Proof.
    apply Env.gempty.
  Qed.

  Lemma find_val_gempty:
    find_val x (empty_memory V) = None.
  Proof.
    apply Env.gempty.
  Qed.

  Lemma add_inst_val_comm:
    add_inst x m' (add_val y v m) = add_val y v (add_inst x m' m).
  Proof eq_refl.

  Lemma add_val_comm:
    forall w,
      x <> y ->
      add_val x v (add_val y w m) = add_val y w (add_val x v m).
  Proof.
    intros; unfold add_val; simpl.
    now rewrite Env.add_comm.
  Qed.

  Lemma In_find_inst:
    forall x (m : memory V),
      Env.In x (instances m) -> exists v, find_inst x m = Some v.
  Proof.
    unfold find_inst. setoid_rewrite Env.In_find; auto.
  Qed.

  Lemma find_inst_In:
    forall x (m : memory V) v,
      find_inst x m = Some v -> Env.In x (instances m).
  Proof.
    unfold find_inst. intros * HH.
    now apply Env.find_In in HH.
  Qed.

  Lemma MapsTo_find_inst:
    forall i (m mi : memory V),
      Env.MapsTo i mi (instances m) <-> find_inst i m = Some mi.
  Proof.
    unfold find_inst. split; intro HH; now apply Env.find_1.
  Qed.

  (** Combined with [orel] *)

  Global Instance find_inst_Proper {A : Type}:
    Proper (eq ==> equal_memory ==> orel equal_memory) (@find_inst A).
  Proof.
    intros s t Exy mm mn Emn; subst.
    apply instances_equal_memory in Emn.
    rewrite Env.Equiv_orel in Emn.
    apply Emn.
  Qed.

  Lemma memory_equiv_orel_inst:
    forall (S T : memory V),
      S ≋ T ->
      forall x, find_inst x S ⌈≋⌉ find_inst x T.
  Proof.
    intros * EM. now setoid_rewrite EM.
  Qed.

  Lemma memory_equiv_orel_val:
    forall (S T : memory V),
      S ≋ T ->
      forall x, orel eq (find_val x S) (find_val x T).
  Proof.
    intros * EM. now setoid_rewrite EM.
  Qed.

  Lemma equal_memory_find_inst:
    forall (M : memory V) N x Mx,
      N ≋ M ->
      find_inst x M = Some Mx ->
      exists Nx, find_inst x N = Some Nx /\ Nx ≋ Mx.
  Proof.
    intros * NM Fx.
    apply memory_equiv_orel_inst with (x:=x0) in NM.
    rewrite Fx in NM. inv NM; eauto.
  Qed.

  Lemma orel_find_inst_Some (R : relation (memory V)):
    forall insts x m,
      orel R (find_inst x insts) (Some m) ->
      exists m', R m' m /\ find_inst x insts = Some m'.
  Proof.
    unfold find_inst. eauto using Env.orel_find_Some.
  Qed.

  Lemma orel_find_val_Some (R : relation V):
    forall vals x m,
      orel R (find_val x vals) (Some m) ->
      exists m', R m' m /\ find_val x vals = Some m'.
  Proof.
    unfold find_val. eauto using Env.orel_find_Some.
  Qed.

End Properties.
