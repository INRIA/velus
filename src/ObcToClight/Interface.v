From compcert Require Import lib.Integers.
From compcert Require Import lib.Floats.
From Velus Require Import Common.
From Velus Require Import Common.CompCertLib.
From Velus Require Import Operators.
From Velus Require Import Ident.

From compcert Require common.Values.
From compcert Require cfrontend.Cop.
From compcert Require cfrontend.Ctypes.
From compcert Require cfrontend.Ctyping.
From compcert Require common.Memory.
From compcert Require common.Memdata.
From compcert Require lib.Maps.
From Coq Require Import String.
From Coq Require Import ZArith.BinInt.

Open Scope bool_scope.
(* Interface avec CompCert *)

Hint Resolve Z.divide_refl.

Definition empty_composite_env : Ctypes.composite_env := (Maps.PTree.empty _).

Module Export Op <: OPERATORS.
  Definition val: Type := Values.val.

  Inductive type' : Type :=
  | Tint:   Ctypes.intsize -> Ctypes.signedness -> type'
  | Tlong:  Ctypes.signedness -> type'
  | Tfloat: Ctypes.floatsize -> type'.

  Definition type := type'.

  Definition cltype (ty: type) : Ctypes.type :=
    match ty with
    | Tint sz sg => Ctypes.Tint sz sg Ctypes.noattr
    | Tlong sg   => Ctypes.Tlong sg (Ctypes.mk_attr false (Some (Npos 3)))
    | Tfloat sz  => Ctypes.Tfloat sz Ctypes.noattr
    end.

  Definition typecl (ty: Ctypes.type) : option type :=
    match ty with
    | Ctypes.Tint sz sg attr => Some (Tint sz sg)
    | Ctypes.Tlong sg attr => Some (Tlong sg)
    | Ctypes.Tfloat sz attr => Some (Tfloat sz)
    | _ => None
    end.

  Definition type_chunk (ty: type) : AST.memory_chunk :=
    match ty with
    | Tint Ctypes.I8 Ctypes.Signed    => AST.Mint8signed
    | Tint Ctypes.I8 Ctypes.Unsigned  => AST.Mint8unsigned
    | Tint Ctypes.I16 Ctypes.Signed   => AST.Mint16signed
    | Tint Ctypes.I16 Ctypes.Unsigned => AST.Mint16unsigned
    | Tint Ctypes.I32 _               => AST.Mint32
    | Tint Ctypes.IBool _             => AST.Mint8unsigned
    | Tlong _                         => AST.Mint64
    | Tfloat Ctypes.F32               => AST.Mfloat32
    | Tfloat Ctypes.F64               => AST.Mfloat64
    end.

  Lemma cltype_align:
    forall gcenv ty,
      (Memdata.align_chunk (type_chunk ty) | Ctypes.alignof gcenv (cltype ty))%Z.
  Proof.
    destruct ty; simpl; cases.
  Qed.

  Lemma cltype_access_by_value:
  forall ty,
    Ctypes.access_mode (cltype ty) = Ctypes.By_value (type_chunk ty).
  Proof.
    destruct ty; simpl; cases.
  Qed.

  Lemma sizeof_translate_chunk:
    forall gcenv t,
      Ctypes.sizeof gcenv (cltype t) = Memdata.size_chunk (type_chunk t).
  Proof.
    intros; apply sizeof_by_value, cltype_access_by_value.
  Qed.

  Definition true_val := Values.Vtrue.
  Definition false_val := Values.Vfalse.

  Lemma true_not_false_val: true_val <> false_val.
  Proof. discriminate. Qed.

  Definition bool_type : type := Tint Ctypes.IBool Ctypes.Signed.

  Inductive constant : Type :=
  | Cint: Integers.int -> Ctypes.intsize -> Ctypes.signedness -> constant
  | Clong: Integers.int64 -> Ctypes.signedness -> constant
  | Cfloat: Floats.float -> constant
  | Csingle: Floats.float32 -> constant.

  Definition const := constant.

  Definition type_const (c: const) : type :=
    match c with
    | Cint _ sz sg => Tint sz sg
    | Clong _ sg   => Tlong sg
    | Cfloat _     => Tfloat Ctypes.F64
    | Csingle _    => Tfloat Ctypes.F32
    end.

  Definition sem_const (c: const) : val :=
    match c with
    | Cint i sz sg => Values.Vint (Cop.cast_int_int sz sg i)
    | Clong i sg   => Values.Vlong i
    | Cfloat f     => Values.Vfloat f
    | Csingle f    => Values.Vsingle f
    end.

  Definition init_type (ty: type) : const :=
    match ty with
    | Tint sz sg => Cint Integers.Int.zero sz sg
    | Tlong sg   => Clong Integers.Int64.zero sg
    | Tfloat Ctypes.F64 => Cfloat Floats.Float.zero
    | Tfloat Ctypes.F32 => Csingle Floats.Float32.zero
    end.

  Inductive unop' : Type :=
  | UnaryOp: Cop.unary_operation -> unop'
  | CastOp:  type -> unop'.

  Definition unop := unop'.
  Definition binop := Cop.binary_operation.

  Definition sem_unop (uop: unop) (v: val) (ty: type) : option val :=
    match uop with
    | UnaryOp op => Cop.sem_unary_operation op v (cltype ty) Memory.Mem.empty
    | CastOp ty' => Cop.sem_cast v (cltype ty) (cltype ty') Memory.Mem.empty
    end.

  Definition sem_binop (op: binop) (v1: val) (ty1: type)
                                   (v2: val) (ty2: type) : option val :=
    Cop.sem_binary_operation
      empty_composite_env op v1 (cltype ty1) v2 (cltype ty2) Memory.Mem.empty.

  Definition is_bool_type (ty: type) : bool :=
    match ty with
    | Tint Ctypes.IBool sg => true
    | _ => false
    end.

  Definition unop_always_returns_bool (op: Cop.unary_operation) : bool :=
    match op with
    | Cop.Onotbool => true
    | _            => false
    end.

  Definition type_unop (uop: unop) (ty: type) : option type :=
    match uop with
    | UnaryOp op => if unop_always_returns_bool op then Some bool_type
                    else match Ctyping.type_unop op (cltype ty) with
                         | Errors.OK ty' => typecl ty'
                         | Errors.Error _ => None
                         end
    | CastOp ty' => match Ctyping.check_cast (cltype ty) (cltype ty') with
                    | Errors.OK _ => Some ty'
                    | Errors.Error _ => None
                    end
    end.

  Definition binop_always_returns_bool (op: binop) : bool :=
    match op with
    | Cop.Oeq  => true
    | Cop.One  => true
    | Cop.Olt  => true
    | Cop.Ogt  => true
    | Cop.Ole  => true
    | Cop.Oge  => true
    | _        => false
    end.

  Definition is_bool_binop (op: binop) : bool :=
    match op with
    | Cop.Oand => true
    | Cop.Oor  => true
    | Cop.Oxor => true
    | _        => false
    end.

  Open Scope bool.

  Definition type_binop (op: binop) (ty1 ty2: type) : option type :=
    if binop_always_returns_bool op
       || (is_bool_binop op && (is_bool_type ty1 && is_bool_type ty2))
    then Some bool_type
    else match Ctyping.type_binop op (cltype ty1) (cltype ty2) with
         | Errors.OK ty' => typecl ty'
         | Errors.Error _ => None
         end.

  (* Neither Vundef nor Vptr is well-typed.

     In CompCert's Ctyping, we have:
       forall ty, wt_val Vundef ty

     Allowing that, in particular, values read from uninitialized
     memory are well-typed. Our typing invariant is slightly stronger,
     since Vundef is not well-typed. We treat uninitialized memory
     in Obc using None. The ObcToClight correctness proof works by
     treating a None in Obc as a don't care in Clight (i.e., the
     variable is associated to a value but we don't know or care what
     it is). All Some values that we read successfully in Obc are
     otherwise well-typed (and never Vundef).

     There is a special case in wt_val_int because in Clight a boolean
     value is considered well-typed if Int.zero_ext 8 n = n.
     We could have, for instance, wt_val' (Vint 7) type_bool.
     But this is problematic in our development because we want
     Cop.sem_cast to be idempotent (sem_cast_same), since it is
     implicit in a Clight assignment, but not by an Obc assignment.
     This property is not true in Clight (C99) since casting to
     a bool gives 0 or 1. For example,
       Cop.sem_cast (Vint 7) type_bool type_bool = Some (Vint 1)

     Why not just change the definition of Ctyping.wt_int?
     Unfortunately, this would make it impossible to prove
     Ctyping.wt_load_result (access_mode ty = By_value chunk ->
      wt_val (Val.load_result chunk v) ty). That is, for bools it
     would not be enough to simply load the value from memory, we
     would have to know that the memory also contained either 0 or 1.
     The C99 type system is not strong enough for our purposes.
   *)
  Inductive wt_val' : val -> type -> Prop :=
  | wt_val_int:
      forall n sz sg,
        Ctyping.wt_int n sz sg ->
        (sz = Ctypes.IBool -> (n = Int.zero \/ n = Int.one)) ->
        wt_val' (Values.Vint n) (Tint sz sg)
  | wt_val_long:
      forall n sg,
        wt_val' (Values.Vlong n) (Tlong sg)
  | wt_val_float:
      forall f,
        wt_val' (Values.Vfloat f) (Tfloat Ctypes.F64)
  | wt_val_single:
      forall f,
        wt_val' (Values.Vsingle f) (Tfloat Ctypes.F32).

  Definition wt_val : val -> type -> Prop := wt_val'.

  Hint Unfold wt_val.
  Hint Constructors wt_val'.

  Lemma wt_val_bool:
    forall v, (v = true_val \/ v = false_val) <-> wt_val v bool_type.
  Proof.
    split; intro HH.
    - destruct HH as [HH|HH]; subst; apply wt_val_int; intuition.
    -  inversion_clear HH as [??? WT Hbool Hv| | |].
       specialize (Hbool eq_refl) as [Hbool|Hbool]; subst; auto.
  Qed.

  Lemma wt_val_const:
    forall c, wt_val (sem_const c) (type_const c).
  Proof.
    destruct c.
    - apply wt_val_int.
      + apply Ctyping.pres_cast_int_int.
      + intro; subst; simpl.
        destruct (Int.eq i Int.zero); auto.
    - apply wt_val_long.
    - apply wt_val_float.
    - apply wt_val_single.
  Qed.

  Lemma wt_init_type:
    forall ty, wt_val (sem_const (init_type ty)) ty.
  Proof.
    destruct ty.
    - apply wt_val_int.
      + apply Ctyping.pres_cast_int_int.
      + intro; subst; simpl; auto.
    - apply wt_val_long.
    - destruct f.
      + apply wt_val_single.
      + apply wt_val_float.
  Qed.

  Lemma type_init_type:
    forall ty, type_const (init_type ty) = ty.
  Proof.
    destruct ty; auto.
    destruct f; auto.
  Qed.

  Ltac DestructCases :=
    match goal with
    | H: ?x <> ?x |- _ => now contradiction H
    | _ => Ctyping.DestructCases
    end.

  Definition good_bool (v: Values.val) (ty: Ctypes.type) :=
    match ty, v with
    | Ctypes.Tint Ctypes.IBool sg a, Values.Vint v =>
      (v = Int.zero \/ v = Int.one)
    | _, _ => True
    end.

  Lemma wt_value_good_bool:
    forall v ty,
      wt_val v ty ->
      good_bool v (cltype ty).
  Proof.
    intros * WTv. unfold good_bool.
    inv WTv; simpl; auto.
    match goal with H:sz = Ctypes.IBool -> _ |- _ =>
                    destruct sz; auto; destruct H; subst; auto
    end.
  Qed.

  Lemma good_bool_vtrue:
    forall ty,
      good_bool Values.Vtrue ty.
  Proof.
    intros; destruct ty; simpl; try destruct i; auto.
  Qed.

  Lemma good_bool_vfalse:
    forall ty,
      good_bool Values.Vfalse ty.
  Proof.
    intros; destruct ty; simpl; try destruct i; auto.
  Qed.

  Lemma good_bool_vlong:
    forall ty i,
      good_bool (Values.Vlong i) ty.
  Proof.
    intros; destruct ty; simpl; try destruct i0; auto.
  Qed.

  Lemma good_bool_vfloat:
    forall ty f,
      good_bool (Values.Vfloat f) ty.
  Proof.
    intros; destruct ty; simpl; try destruct i; auto.
  Qed.

  Lemma good_bool_vsingle:
    forall ty f,
      good_bool (Values.Vsingle f) ty.
  Proof.
    intros; destruct ty; simpl; try destruct i; auto.
  Qed.

  Lemma good_bool_tint:
    forall v sz sg a,
      sz <> Ctypes.IBool ->
      good_bool v (Ctypes.Tint sz sg a).
  Proof.
    intros; destruct v, sz; simpl; intuition.
  Qed.

  Lemma good_bool_tlong:
    forall v sg a,
      good_bool v (Ctypes.Tlong sg a).
  Proof.
    intros; destruct v; simpl; auto.
  Qed.

  Lemma good_bool_tfloat:
    forall v sz a,
      good_bool v (Ctypes.Tfloat sz a).
  Proof.
    intros; destruct v; simpl; auto.
  Qed.

  Local Hint Immediate good_bool_vtrue good_bool_vfalse good_bool_vlong
        good_bool_vfloat good_bool_vsingle good_bool_tlong
        good_bool_tfloat.

  Lemma good_bool_not_bool:
    forall v ty,
      (forall sg a, ty <> Ctypes.Tint Ctypes.IBool sg a) ->
      good_bool v ty.
  Proof.
    intros v ty Hty.
    destruct ty; simpl; eauto.
    destruct i, v; auto.
    now contradiction (Hty s a).
  Qed.

  Local Hint Resolve good_bool_not_bool.

  Opaque good_bool.

  Lemma good_bool_zero_or_one:
    forall i sz sg a,
      good_bool (Values.Vint i) (Ctypes.Tint sz sg a) ->
      sz = Ctypes.IBool ->
      i = Int.zero \/ i = Int.one.
  Proof.
    intros * Hgb Hsz; subst; inversion_clear Hgb; auto.
  Qed.

  Local Hint Resolve good_bool_zero_or_one.

  Lemma wt_val_Vfalse_bool_type:
    wt_val (Values.Vfalse) bool_type.
  Proof.
    constructor; unfold Ctyping.wt_int; [now vm_compute|intuition].
  Qed.

  Lemma wt_val_Vtrue_bool_type:
    wt_val (Values.Vtrue) bool_type.
  Proof.
    constructor; unfold Ctyping.wt_int; [now vm_compute|intuition].
  Qed.

  Local Hint Resolve wt_val_Vfalse_bool_type wt_val_Vtrue_bool_type.

  Lemma wt_val_of_bool_bool_type:
    forall v,
      wt_val (Values.Val.of_bool v) bool_type.
  Proof.
    destruct v; simpl; auto.
  Qed.

  Local Hint Resolve wt_val_of_bool_bool_type.

  Lemma typecl_wt_val_wt_val:
    forall cty ty v,
      typecl cty = Some ty ->
      Ctyping.wt_val v cty ->
      v <> Values.Vundef ->
      (forall b ofs, v <> Values.Vptr b ofs) ->
      good_bool v cty ->
      wt_val v ty.
  Proof.
    intros * Htcl Hcty Hnun Hnptr Hgb.
    destruct cty;
      simpl in *;
      destruct v;
      DestructCases;
      inversion Hcty;
      subst;
      eauto.
    exfalso; now eapply Hnptr.
    exfalso; now eapply Hnptr.
  Qed.

  Lemma wt_val_not_vundef_nor_vptr:
    forall v ty,
      wt_val v ty ->
      v <> Values.Vundef /\ (forall b ofs, v <> Values.Vptr b ofs).
  Proof.
    intros * Hwt.
    destruct ty; inversion Hwt; subst;
      split; discriminate.
  Qed.

  Lemma wt_val_wt_val_cltype:
    forall v ty,
      wt_val v ty ->
      Ctyping.wt_val v (cltype ty).
  Proof.
    intros * Hwt.
    destruct ty; inversion_clear Hwt;
    eauto using Ctyping.wt_val.
  Qed.

  Lemma is_bool_type_true:
    forall ty,
      is_bool_type ty = true ->
      exists sg, ty = Tint Ctypes.IBool sg.
  Proof.
    destruct ty; try destruct i, s; simpl; intuition.
    - exists Ctypes.Signed; auto.
    - exists Ctypes.Unsigned; auto.
  Qed.

  Lemma type_castop:
    forall ty ty',
      type_unop (CastOp ty') ty = Some ty'.
  Proof.
    intros ty ty'.
    destruct ty, ty';
      try destruct i, s; try destruct i0; try destruct s0;
      try destruct f; try destruct f0; auto.
  Qed.

  Ltac GoalMatchMatch :=
    repeat match goal with
           | |- match match ?x with _ => _ end with _ => _ end = _ =>
             destruct x
           end; auto.

  Lemma check_cltype_cast:
    forall ty ty',
      Ctyping.check_cast (cltype ty) (cltype ty') = Errors.OK tt.
  Proof.
    intros ty ty'.
    unfold Ctyping.check_cast.
    destruct ty, ty'; simpl; GoalMatchMatch.
  Qed.

  Lemma pres_sem_unop:
    forall op ty1 ty v1 v,
      type_unop op ty1 = Some ty ->
      sem_unop op v1 ty1 = Some v ->
      wt_val v1 ty1 ->
      wt_val v ty.
  Proof.
    intros * Htop Hsop Hv1.
    pose proof (wt_val_not_vundef_nor_vptr _ _ Hv1) as [Hnun Hnptr].
    unfold type_unop, sem_unop in *.
    destruct op as [uop|].
    - (* UnaryOp *)
      destruct (unop_always_returns_bool uop) eqn:Huop.
      + destruct uop; try discriminate Huop.
        inv Htop; intros; subst.
        simpl in Hsop.
        unfold Cop.sem_notbool, Cop.classify_bool, Coqlib.option_map in Hsop;
          DestructCases; auto.
      + apply wt_val_wt_val_cltype in Hv1.
        destruct (Ctyping.type_unop uop (cltype ty1)) as [cty|] eqn:Hok;
          [|discriminate].
        assert (Hok':=Hok).
        apply Ctyping.pres_sem_unop with (2:=Hsop) (3:=Hv1) in Hok;
          DestructCases.
        cut (v <> Values.Vundef
             /\ (forall b ofs, v <> Values.Vptr b ofs)
             /\ good_bool v cty).
        { destruct 1 as (Hnun' & Hnptr' & Hgb). eauto using typecl_wt_val_wt_val. }
        destruct uop; simpl in *.
        * clear Hok'. rewrite Cop.notbool_bool_val in Hsop.
          DestructCases. destruct b; repeat split; try discriminate; auto.
        * unfold Cop.sem_notint in Hsop.
          destruct v1; DestructCases; repeat split; try discriminate; auto.
        * unfold Cop.sem_neg in Hsop.
          destruct v1; DestructCases; repeat split; try discriminate; auto.
        * unfold Cop.sem_absfloat in Hsop.
          destruct v1; DestructCases; repeat split; try discriminate; auto.
    - (* CastOp *)
      rewrite check_cltype_cast in Htop.
      injection Htop; intro; subst.
      apply wt_val_wt_val_cltype in Hv1.
      pose proof (Ctyping.pres_sem_cast _ _ _ _ _ Hv1 Hsop).
      eapply typecl_wt_val_wt_val with (2:=H).
      destruct ty; now simpl.
      + (* result cannot be Vundef *)
        unfold Cop.sem_cast, Cop.classify_cast in Hsop.
        destruct Hv1; DestructCases; try discriminate; auto.
      + (* result cannot be Vptr *)
        unfold Cop.sem_cast, Cop.classify_cast in Hsop.
        intros b ofs.
        specialize (Hnptr b ofs).
        destruct Hv1; DestructCases; try discriminate; auto.
      + (* booleans must be zero or one *)
        destruct ty; simpl; auto.
        destruct i; try now (apply good_bool_tint; discriminate).
        unfold Cop.sem_cast in Hsop.
        simpl in Hsop.
        DestructCases;
          try match goal with |- context [if ?x then _ else _] => destruct x end;
          simpl; auto.
  Qed.

  Lemma sem_cast_same:
    forall m v t,
      wt_val v t ->
      Cop.sem_cast v (cltype t) (cltype t) m = Some v.
  Proof.
    intros * WTv.
    apply Cop.cast_val_casted.
    destruct (wt_val_not_vundef_nor_vptr _ _ WTv) as (Hnun & Hnptr).
    pose proof (wt_value_good_bool _ _ WTv) as Hgb.
    apply wt_val_wt_val_cltype in WTv.
    destruct v.
    - tauto.
    - inv WTv; try match goal with H:_ = cltype t |- _ =>
                                   destruct t; now inv H end.
      constructor.
      match goal with H:Ctypes.Tint ?sz ?sg _ = cltype t |- _ =>
        rewrite <-H in Hgb; destruct sz, sg; simpl in *; auto
      end; destruct (good_bool_zero_or_one _ _ _ _ Hgb);
        try subst; auto.
    - inv WTv. apply Cop.val_casted_long.
      * match goal with H:Ctypes.Tpointer _ _ = cltype t |- _
                        => destruct t; inv H end.
      * match goal with H:Ctypes.Tvoid = cltype t |- _ => destruct t; inv H end.
    - inv WTv. apply Cop.val_casted_float.
      match goal with H:Ctypes.Tvoid = cltype t |- _ => destruct t; inv H end.
    - inv WTv. apply Cop.val_casted_single.
      match goal with H:Ctypes.Tvoid = cltype t |- _ => destruct t; inv H end.
    - specialize (Hnptr b i); intuition.
  Qed.

  (* Solve goal with hypothesis of the form:
       (forall b ofs, Values.Vptr b' ofs' <> Values.Vptr b ofs) *)
  Ltac ContradictNotVptr :=
      match goal with
      | H: context [Values.Vptr ?b ?i <> Values.Vptr _ _] |- _ =>
        contradiction (H b i)
      end.

  Lemma cases_of_bool:
    forall P b,
      P Values.Vtrue ->
      P Values.Vfalse ->
      P (Values.Val.of_bool b).
  Proof.
    destruct b; auto.
  Qed.

  Lemma option_map_of_bool_true_false:
    forall e x,
      Coqlib.option_map Values.Val.of_bool e = Some x ->
      x = Values.Vtrue \/ x = Values.Vfalse.
  Proof.
    intros e x Hom.
    destruct e as [b|]; [destruct b|].
    - injection Hom; intro; subst; intuition.
    - injection Hom; intro; subst; intuition.
    - discriminate Hom.
  Qed.

  Lemma sem_cmp_not_vundef_nor_vptr:
    forall cop v1 ty1 v2 ty2 m v,
      Cop.sem_cmp cop v1 ty1 v2 ty2 m = Some v ->
      v <> Values.Vundef /\ (forall b ofs, v <> Values.Vptr b ofs).
  Proof.
    intros * H.
    unfold Cop.sem_cmp in H;
      DestructCases; split; try discriminate;
        try (apply option_map_of_bool_true_false in H;
             destruct H; subst; discriminate).
    + unfold Cop.sem_binarith in H; DestructCases;
        apply cases_of_bool; discriminate.
    + unfold Cop.sem_binarith in H; DestructCases;
        apply cases_of_bool; discriminate.
  Qed.

  Lemma classify_add_cltypes:
    forall ty1 ty2,
      Cop.classify_add (cltype ty1) (cltype ty2) = Cop.add_default.
  Proof.
    unfold Cop.classify_add, cltype; destruct ty1, ty2; simpl; GoalMatchMatch.
  Qed.

  Lemma classify_sub_cltypes:
    forall ty1 ty2,
      Cop.classify_sub (cltype ty1) (cltype ty2) = Cop.sub_default.
  Proof.
    unfold Cop.classify_sub, cltype; destruct ty1, ty2; simpl; GoalMatchMatch.
  Qed.

  Lemma classify_cmp_cltypes:
    forall ty1 ty2,
      Cop.classify_cmp (cltype ty1) (cltype ty2) = Cop.cmp_default.
  Proof.
    unfold Cop.classify_cmp, cltype; destruct ty1, ty2; simpl; GoalMatchMatch.
  Qed.

  Lemma sem_cmp_true_or_false:
    forall cop v1 ty1 v2 ty2 m v,
      Cop.sem_cmp cop v1 ty1 v2 ty2 m = Some v ->
      v = Values.Vtrue \/ v = Values.Vfalse.
  Proof.
    intros * Hsem.
    unfold Cop.sem_cmp, Cop.sem_binarith, Cop.cmp_ptr in Hsem.
    DestructCases;
      try repeat match goal with
                 | H:Coqlib.option_map Values.Val.of_bool ?r = Some _ |- _ =>
                   destruct r; simpl in H; try discriminate;
                     injection H; clear H; intro; subst
                 | |- context [Values.Val.of_bool ?b] => destruct b; auto
                 end.
  Qed.

  (* Boolean binary operations (&&, ||) are elaborated into Sifthenelse's. *)
  Lemma binop_never_bool:
    forall op ty1 ty2 ty,
      Ctyping.type_binop op ty1 ty2 = Errors.OK ty ->
      forall sz a, ty <> Ctypes.Tint Ctypes.IBool sz a.
  Proof.
    intros op ty1 ty2 ty Htype sz a.
    unfold Ctyping.type_binop, Ctyping.binarith_type,
           Ctyping.comparison_type, Ctyping.binarith_int_type,
           Ctyping.shift_op_type in Htype.
    DestructCases; discriminate.
  Qed.

  Lemma pres_sem_binop:
    forall op ty1 ty2 ty v1 v2 v,
      type_binop op ty1 ty2 = Some ty ->
      sem_binop op v1 ty1 v2 ty2 = Some v ->
      wt_val v1 ty1 ->
      wt_val v2 ty2 ->
      wt_val v ty.
  Proof.
    unfold type_binop, sem_binop.
    intros * Hty Hsem Hwt1 Hwt2.
    destruct (binop_always_returns_bool op) eqn:Heq1; simpl in Hty;
      [|destruct
          (is_bool_binop op && (is_bool_type ty1 && is_bool_type ty2)) eqn:Heq2];
      simpl in Hty.
    - (* Binary comparisons always return a bool (zero or one). *)
      injection Hty; intro; subst.
      destruct op; try discriminate Heq1;
        unfold Cop.sem_binary_operation in Hsem;
        destruct (sem_cmp_true_or_false _ _ _ _ _ _ _ Hsem); subst; auto.
    - (* Binary operators that are closed on bool. *)
      injection Hty; intro; subst; clear Hty.
      apply andb_prop in Heq2; destruct Heq2 as (Hbop & Heq2).
      apply andb_prop in Heq2; destruct Heq2 as (Hbty1 & Hbty2).
      destruct (is_bool_type_true _ Hbty1) as (sg1 & Hty1).
      destruct (is_bool_type_true _ Hbty2) as (sg2 & Hty2).
      subst; clear Hbty1 Hbty2 Heq1.
      destruct op; try discriminate Hbop;
        destruct v1, v2;
        inv Hwt1; inv Hwt2;
          repeat match goal with H:?x = ?x -> _ \/ _ |- _ =>
                                 destruct (H eq_refl); clear H end;
          subst;
          vm_compute in Hsem;
          injection Hsem; intro; subst v; auto.
    - (* Everything else. *)
      destruct (Ctyping.type_binop op (cltype ty1) (cltype ty2)) eqn:Hok;
        [|discriminate].
      pose proof (binop_never_bool _ _ _ _ Hok) as Hnbool.
      pose proof (wt_val_not_vundef_nor_vptr _ _ Hwt1) as (Hnun1 & Hnptr1).
      pose proof (wt_val_not_vundef_nor_vptr _ _ Hwt2) as (Hnun2 & Hnptr2).
      apply wt_val_wt_val_cltype in Hwt1.
      apply wt_val_wt_val_cltype in Hwt2.
      pose proof (Ctyping.pres_sem_binop _ _ _ _ _ _ _ _ _ Hok Hsem Hwt1 Hwt2)
        as Hwt.
      cut (v <> Values.Vundef
           /\ (forall b ofs, v <> Values.Vptr b ofs)
           /\ good_bool v t).
      { destruct 1 as (Hnun' & Hnptr' & Hgb). eauto using typecl_wt_val_wt_val. }
      destruct op; simpl in Hsem; try discriminate Heq1.
      + (* add *)
        unfold Cop.sem_add, Cop.sem_binarith in Hsem.
        rewrite classify_add_cltypes in Hsem.
        DestructCases; repeat split; try discriminate; try ContradictNotVptr; auto.
      + (* sub *)
        unfold Cop.sem_sub, Cop.sem_binarith in Hsem.
        rewrite classify_sub_cltypes in Hsem.
        DestructCases; repeat split; try discriminate; try ContradictNotVptr; auto.
      + (* mul *)
        unfold Cop.sem_mul, Cop.sem_binarith in Hsem.
        DestructCases; repeat split; try discriminate; try ContradictNotVptr; auto.
      + (* div *)
        unfold Cop.sem_div, Cop.sem_binarith in Hsem.
        DestructCases; repeat split; try discriminate; try ContradictNotVptr; auto.
      + (* mod *)
        unfold Cop.sem_mod, Cop.sem_binarith in Hsem.
        DestructCases; repeat split; try discriminate; try ContradictNotVptr; auto.
      + (* and *)
        unfold Cop.sem_and, Cop.sem_binarith in Hsem.
        DestructCases; repeat split; try discriminate; try ContradictNotVptr; auto.
      + (* or *)
        unfold Cop.sem_or, Cop.sem_binarith in Hsem.
        DestructCases; repeat split; try discriminate; try ContradictNotVptr; auto.
      + (* xor *)
        unfold Cop.sem_xor, Cop.sem_binarith in Hsem.
        DestructCases; repeat split; try discriminate; try ContradictNotVptr; auto.
      + (* shl *)
        unfold Cop.sem_shl, Cop.sem_shift in Hsem.
        DestructCases; repeat split; try discriminate; try ContradictNotVptr; auto.
      + (* shr *)
        unfold Cop.sem_shr, Cop.sem_shift in Hsem.
        DestructCases; repeat split; try discriminate; try ContradictNotVptr; auto.
  Qed.

  Lemma val_dec   : forall v1 v2 : val, {v1 = v2} + {v1 <> v2}.
  Proof Values.Val.eq.

  Lemma type_dec   : forall t1 t2 : type, {t1 = t2} + {t1 <> t2}.
  Proof.
    decide equality; (apply Ctyping.signedness_eq
                      || apply Ctyping.intsize_eq
                      || apply Ctyping.floatsize_eq).
  Qed.

  Lemma const_dec : forall c1 c2 : const, {c1 = c2} + {c1 <> c2}.
  Proof.
    decide equality; (apply Ctyping.signedness_eq
                      || apply Ctyping.intsize_eq
                      || apply Int.eq_dec
                      || apply Int64.eq_dec
                      || apply Float.eq_dec
                      || apply Float32.eq_dec).
  Qed.

  Lemma unop_dec  : forall op1 op2 : unop, {op1 = op2} + {op1 <> op2}.
  Proof.
    assert (forall (x y: Cop.unary_operation), {x=y} + {x<>y})
      by decide equality.
    decide equality.
    apply type_dec.
  Qed.

  Lemma binop_dec : forall op1 op2 : binop, {op1 = op2} + {op1 <> op2}.
  Proof.
    decide equality.
  Qed.

  Lemma sem_unary_operation_any_mem:
    forall op v ty M1 M2,
      (forall b ofs, v <> Values.Vptr b ofs) ->
      Cop.sem_unary_operation op v ty M1
      = Cop.sem_unary_operation op v ty M2.
  Proof.
    intros * Hnptr.
    destruct op, v; simpl;
      unfold Cop.sem_notbool, Cop.sem_notint, Cop.sem_neg, Cop.sem_absfloat;
      repeat match goal with
             | |- (match ?x with _ => _ end) = _ => destruct x; auto
             | _ => ContradictNotVptr
             end;
      try (now destruct ty; auto).
    specialize (Hnptr b i); contradiction.
  Qed.

  Lemma sem_cast_any_mem:
    forall v ty1 ty2 M1 M2,
      (forall b ofs, v <> Values.Vptr b ofs) ->
      Cop.sem_cast v ty1 ty2 M1 = Cop.sem_cast v ty1 ty2 M2.
  Proof.
    intros * Hnptr.
    unfold Cop.sem_cast.
    destruct (Cop.classify_cast ty1 ty2); auto.
    destruct v; auto.
    specialize (Hnptr b i); contradiction.
  Qed.

  Lemma sem_binary_operation_any_cenv_mem:
    forall op v1 ty1 v2 ty2 M1 M2 cenv1 cenv2,
      (forall b ofs, v1 <> Values.Vptr b ofs) ->
      (forall b ofs, v2 <> Values.Vptr b ofs) ->
      Cop.sem_binary_operation cenv1 op v1 (cltype ty1) v2 (cltype ty2) M1
      = Cop.sem_binary_operation cenv2 op v1 (cltype ty1) v2 (cltype ty2) M2.
  Proof.
    intros * Hnptr1 Hnptr2.
    destruct op; simpl;
      unfold Cop.sem_add, Cop.sem_sub, Cop.sem_mul, Cop.sem_div, Cop.sem_mod,
             Cop.sem_and, Cop.sem_or, Cop.sem_xor, Cop.sem_shl, Cop.sem_shr,
             Cop.sem_cmp, Cop.sem_binarith;
      try rewrite classify_add_cltypes;
      try rewrite classify_sub_cltypes;
      try rewrite classify_cmp_cltypes;
      try rewrite (sem_cast_any_mem v1 (cltype ty1) _ M1 M2 Hnptr1);
      try rewrite (sem_cast_any_mem v2 (cltype ty2) _ M1 M2 Hnptr2);
      GoalMatchMatch.
  Qed.

  Lemma access_mode_cltype:
    forall ty,
      Ctypes.access_mode (cltype ty) = Ctypes.By_value (type_chunk ty).
  Proof.
    destruct ty as [sz sg|sz|f].
    - destruct sz, sg; auto.
    - destruct sz; auto.
    - destruct f; auto.
  Qed.

  Lemma wt_val_load_result:
    forall ty v,
      wt_val v ty ->
      v = Values.Val.load_result (type_chunk ty) v.
  Proof.
    intros * Hwt.
    destruct ty as [sz sg|sz|sz].
    - destruct sz, sg; simpl;
        inv Hwt; auto;
        match goal with
        | H:Ctyping.wt_int _ _ _ |- _ => rewrite <-H
        end;
        try rewrite Int.sign_ext_idem;
        try rewrite Int.zero_ext_idem;
        intuition.
    - destruct sz; inv Hwt; auto.
    - destruct sz; inv Hwt; auto.
  Qed.

  (* Operator typing *)

  (*
    Types and concrete syntax
    -------------------------
    Tint I8    Signed          "int8"
    Tint I8    Unsigned        "uint8"
    Tint I16   Signed          "int16"
    Tint I16   Unsigned        "uint16"
    Tint I32   Signed          "int32" / "int"
    Tint I32   Unsigned        "uint32"
    Tint IBool Signed          "bool"
    Tint IBool Unsigned        "bool"
    Tlong      Signed          "int64"
    Tlong      Unsigned        "uint64"
    Tfloat     F32             "float32"
    Tfloat     F64             "float64" / "real"

    Unary operators (prefix)
    ------------------------
    Onotbool      "not"
    Onotint       "lnot"
    Oneg          "-"

    Unary cast (mix fix)
    --------------------
    "(" e ":" type ")"

    Binary operators (infix)
    ------------------------
    Oadd          "+"
    Osub          "-"
    Omul          "*"
    Odiv          "/"
    Omod          "mod"
    Oand          "land" / "and"
    Oor           "lor"  / "or"
    Oxor          "lxor"
    Oshl          "lsl"
    Oshr          "lsr"
    Oeq           "="
    One           "<>"
    Olt           "<"
    Ogt           ">"
    Ole           "<="
    Oge           ">="

    Trinary operators (mixfix)
    --------------------------
    "if" / "then" / "else"
   *)

  Definition type_unop' (uop: unop) (ty: type) : option type :=
    match uop with
    | UnaryOp op =>
        match op with
        | Cop.Onotbool           => Some bool_type
        | Cop.Onotint =>
          match ty with
          | Tint Ctypes.I32 sg   => Some ty
          | Tlong sg             => Some ty
          | Tint _ _             => Some (Tint Ctypes.I32 Ctypes.Signed)
          | _                    => None
          end
        | Cop.Oneg =>
          match ty with
          | Tint Ctypes.I32 sg   => Some ty
          | Tlong sg             => Some ty
          | Tint _ _             => Some (Tint Ctypes.I32 Ctypes.Signed)
          | Tfloat sz            => Some ty
          end
        | Cop.Oabsfloat          => Some (Tfloat Ctypes.F64)
        end
    | CastOp ty' => Some ty'
    end.

  Definition type_binop' (op: binop) (ty1 ty2: type) : option type :=
    match op with
    | Cop.Oadd | Cop.Osub | Cop.Omul | Cop.Odiv =>
        match ty1, ty2 with
        | Tfloat Ctypes.F64              , _                               => Some (Tfloat Ctypes.F64)
        | _                              , Tfloat Ctypes.F64               => Some (Tfloat Ctypes.F64)
        | Tfloat Ctypes.F32              , _                               => Some (Tfloat Ctypes.F32)
        | _                              , Tfloat Ctypes.F32               => Some (Tfloat Ctypes.F32)
        | Tlong Ctypes.Unsigned          , _                               => Some (Tlong Ctypes.Unsigned)
        | _                              , Tlong Ctypes.Unsigned           => Some (Tlong Ctypes.Unsigned)
        | Tlong Ctypes.Signed            , _                               => Some (Tlong Ctypes.Signed)
        | _                              , Tlong Ctypes.Signed             => Some (Tlong Ctypes.Signed)
        | Tint Ctypes.I32 Ctypes.Unsigned, _                               => Some (Tint Ctypes.I32 Ctypes.Unsigned)
        | _                              , Tint Ctypes.I32 Ctypes.Unsigned => Some (Tint Ctypes.I32 Ctypes.Unsigned)
        | Tint _ _                       , Tint _ _                        => Some (Tint Ctypes.I32 Ctypes.Signed)
        end
    | Cop.Omod =>
        match ty1, ty2 with
        | Tfloat _                       , _                               => None
        | _                              , Tfloat _                        => None
        | Tlong Ctypes.Unsigned          , _                               => Some (Tlong Ctypes.Unsigned)
        | _                              , Tlong Ctypes.Unsigned           => Some (Tlong Ctypes.Unsigned)
        | Tlong Ctypes.Signed            , _                               => Some (Tlong Ctypes.Signed)
        | _                              , Tlong Ctypes.Signed             => Some (Tlong Ctypes.Signed)
        | Tint Ctypes.I32 Ctypes.Unsigned, _                               => Some (Tint Ctypes.I32 Ctypes.Unsigned)
        | _                              , Tint Ctypes.I32 Ctypes.Unsigned => Some (Tint Ctypes.I32 Ctypes.Unsigned)
        | Tint _ _                       , Tint _ _                        => Some (Tint Ctypes.I32 Ctypes.Signed)
        end
    | Cop.Oand | Cop.Oor | Cop.Oxor =>
        match ty1, ty2 with
        | Tfloat _                       , _                               => None
        | _                              , Tfloat _                        => None
        | Tlong Ctypes.Unsigned          , _                               => Some (Tlong Ctypes.Unsigned)
        | _                              , Tlong Ctypes.Unsigned           => Some (Tlong Ctypes.Unsigned)
        | Tlong Ctypes.Signed            , _                               => Some (Tlong Ctypes.Signed)
        | _                              , Tlong Ctypes.Signed             => Some (Tlong Ctypes.Signed)
        | Tint Ctypes.IBool sg1          , Tint Ctypes.IBool sg2           => Some (Tint Ctypes.IBool Ctypes.Signed)
        | Tint Ctypes.I32 Ctypes.Unsigned, _                               => Some (Tint Ctypes.I32 Ctypes.Unsigned)
        | _                              , Tint Ctypes.I32 Ctypes.Unsigned => Some (Tint Ctypes.I32 Ctypes.Unsigned)
        | Tint _ _                       , Tint _ _                        => Some (Tint Ctypes.I32 Ctypes.Signed)
        end
    | Cop.Oshl | Cop.Oshr =>
        match ty1, ty2 with
        | Tfloat _                       , _         => None
        | _                              , Tfloat _  => None
        | Tlong sg                       , _         => Some (Tlong sg)
        | Tint Ctypes.I32 Ctypes.Unsigned, _         => Some (Tint Ctypes.I32 Ctypes.Unsigned)
        | Tint _ _                       , _         => Some (Tint Ctypes.I32 Ctypes.Signed)
        end
    | Cop.Oeq | Cop.One | Cop.Olt | Cop.Ogt | Cop.Ole | Cop.Oge => Some bool_type
    end.

  Lemma type_unop'_correct:
    forall op ty,
      type_unop' op ty = type_unop op ty.
  Proof.
    intros. destruct op.
    - destruct u, ty; try destruct i; try destruct s; try destruct f;
        simpl in *; now DestructCases.
    - destruct t, ty; try destruct i; try destruct s; try destruct f;
        try destruct f0; simpl in *; DestructCases; auto.
  Qed.

  Lemma type_binop'_correct:
    forall op ty1 ty2,
      type_binop' op ty1 ty2 = type_binop op ty1 ty2.
  Proof.
    intros.
    unfold type_binop.
    destruct (binop_always_returns_bool op) eqn:Heq1; simpl;
      [|destruct
          (is_bool_binop op && (is_bool_type ty1 && is_bool_type ty2)) eqn:Heq2].
    - destruct op; simpl in *; try discriminate; auto.
    - unfold type_binop'.
      repeat rewrite Bool.andb_true_iff in Heq2.
      destruct Heq2 as (Heq2 & Heq3 & Heq4).
      apply is_bool_type_true in Heq3; destruct Heq3 as (sg1 & Heq3).
      apply is_bool_type_true in Heq4; destruct Heq4 as (sg2 & Heq4).
      subst; destruct op; try discriminate; auto.
    - repeat rewrite Bool.andb_false_iff in Heq2.
      destruct op; simpl in *; try discriminate Heq1;
      (destruct ty1, ty2; try destruct i; try destruct i0;
       try destruct s; try destruct s0; try destruct f;
       try destruct f0; auto);
        (destruct Heq2 as [Heq2|[Heq2|Heq2]]; discriminate).
  Qed.

  Open Scope string_scope.

  Definition string_of_type (ty: type) : String.string :=
    match ty with
    | Tint Ctypes.IBool sg            => "bool"
    | Tint Ctypes.I8 Ctypes.Signed    => "int8"
    | Tint Ctypes.I8 Ctypes.Unsigned  => "uint8"
    | Tint Ctypes.I16 Ctypes.Signed   => "int16"
    | Tint Ctypes.I16 Ctypes.Unsigned => "uint16"
    | Tint Ctypes.I32 Ctypes.Signed   => "int32"
    | Tint Ctypes.I32 Ctypes.Unsigned => "uint32"
    | Tlong Ctypes.Signed             => "int64"
    | Tlong Ctypes.Unsigned           => "uint64"
    | Tfloat Ctypes.F32               => "float32"
    | Tfloat Ctypes.F64               => "float64"
    end.

End Op.

Hint Resolve cltype_access_by_value cltype_align wt_val_load_result sem_cast_same.

Module OpAux := OperatorsAux Op.

Lemma val_to_bool_bool_val:
  forall v b m,
    OpAux.val_to_bool v = Some b ->
    Cop.bool_val v (cltype bool_type) m = Some b.
Proof.
  intros * Vtb.
  unfold Cop.bool_val; simpl.
  destruct b.
  - apply OpAux.val_to_bool_true' in Vtb; subst; simpl.
    rewrite Int.eq_false; auto; discriminate.
  - apply OpAux.val_to_bool_false' in Vtb; subst; simpl.
    rewrite Int.eq_true; auto.
Qed.
Hint Resolve val_to_bool_bool_val.

From Velus Require Import Stream.
From Velus Require Import Streams.
From Velus Require Import Obc.

Module Str  := StreamFun  Op OpAux.
Module Strs := StreamsFun Op OpAux.
Module Obc  := ObcFun Ids Op OpAux.
