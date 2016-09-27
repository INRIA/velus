Require Import lib.Integers.
Require Import lib.Floats.
Require Import Rustre.Common.
Require Import Rustre.Operators.

Require compcert.common.Values.
Require compcert.cfrontend.Cop.
Require compcert.cfrontend.Ctypes.
Require compcert.cfrontend.Ctyping.
Require compcert.common.Memory.
Require compcert.lib.Maps.

(* Interface avec CompCert *)

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
    | Tlong sg   => Ctypes.Tlong sg Ctypes.noattr
    | Tfloat sz  => Ctypes.Tfloat sz Ctypes.noattr
    end.

  Definition typecl (ty: Ctypes.type) : option type :=
    match ty with
    | Ctypes.Tint sz sg (Ctypes.mk_attr false None) => Some (Tint sz sg)
    | Ctypes.Tlong sg   (Ctypes.mk_attr false None) => Some (Tlong sg)
    | Ctypes.Tfloat sz  (Ctypes.mk_attr false None) => Some (Tfloat sz)
    | _ => None
    end.
  
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

  Definition type_unop (uop: unop) (ty: type) : option type :=
    match uop with
    | UnaryOp op => match Ctyping.type_unop op (cltype ty) with
                    | Errors.OK ty' => typecl ty'
                    | Errors.Error _ => None
                    end
    | CastOp ty' => match Ctyping.check_cast (cltype ty) (cltype ty') with
                    | Errors.OK _ => Some ty'
                    | Errors.Error _ => None
                    end
    end.

  Definition type_binop (op: binop) (ty1 ty2: type) : option type :=
    match Ctyping.type_binop op (cltype ty1) (cltype ty2) with
    | Errors.OK ty' => typecl ty'
    | Errors.Error _ => None
    end.

  (* Neither Vundef nor Vptr is well-typed.

     In CompCert's Ctyping, we have:
       forall ty, wt_val Vundef ty

     Allowing that, in particular, values read from uninitialized
     memory are well-typed. Our typing invariants become slightly more
     complicated -- they will require that variables be initialized before
     they are read -- but also slightly stronger, since we need not treat
     the Vundef case.
  *)
  Inductive wt_val' : val -> type -> Prop :=
  | wt_val_int:
      forall n sz sg,
        Ctyping.wt_int n sz sg ->
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
  
  Lemma wt_val_true:
    wt_val true_val bool_type.
  Proof.
    apply wt_val_int. reflexivity.
  Qed.

  Lemma wt_val_false:
    wt_val false_val bool_type.
  Proof.
    apply wt_val_int. reflexivity.
  Qed.

  Lemma wt_val_const:
    forall c, wt_val (sem_const c) (type_const c).
  Proof.
    destruct c.
    - apply wt_val_int. apply Ctyping.pres_cast_int_int.
    - apply wt_val_long.
    - apply wt_val_float.
    - apply wt_val_single.
  Qed.

  Ltac DestructCases :=
    match goal with
    | H: ?x <> ?x |- _ => now contradiction H
    | _ => Ctyping.DestructCases
    end.
  
  Lemma typecl_wt_val_wt_val:
    forall cty ty v,
      typecl cty = Some ty ->
      Ctyping.wt_val v cty ->
      v <> Values.Vundef ->
      (forall b ofs, v <> Values.Vptr b ofs) ->
      wt_val v ty.
  Proof.
    intros ** Htcl Hcty Hnun Hnptr.
    destruct cty;
      simpl in *;
      destruct v;
      DestructCases;
      inversion Hcty;
      auto.
    exfalso; now eapply Hnptr.
  Qed.

  Lemma wt_val_not_vundef_nor_vptr:
    forall v ty,
      wt_val v ty ->
      v <> Values.Vundef /\ (forall b ofs, v <> Values.Vptr b ofs).
  Proof.
    intros ** Hwt.
    destruct ty; inversion Hwt; subst;
      split; discriminate.
  Qed.

  Lemma wt_val_wt_val_cltype:
    forall v ty,
      wt_val v ty ->
      Ctyping.wt_val v (cltype ty).
  Proof.
    intros ** Hwt.
    destruct ty; inversion_clear Hwt;
    eauto using Ctyping.wt_val.
  Qed.

  Lemma pres_sem_unop:
    forall op ty1 ty v1 v,
      type_unop op ty1 = Some ty ->
      sem_unop op v1 ty1 = Some v ->
      wt_val v1 ty1 ->
      wt_val v ty.
  Proof.
    intros ** Htop Hsop Hv1.
    pose proof (wt_val_not_vundef_nor_vptr _ _ Hv1) as [Hnun Hnptr].
    unfold type_unop, sem_unop in *.
    destruct op as [uop|].
    - (* UnaryOp *)
      apply wt_val_wt_val_cltype in Hv1.
      destruct (Ctyping.type_unop uop (cltype ty1)) as [cty|] eqn:Hok;
        [|discriminate].
      apply Ctyping.pres_sem_unop with (2:=Hsop) (3:=Hv1) in Hok;
        DestructCases.
      cut (v <> Values.Vundef /\ (forall b ofs, v <> Values.Vptr b ofs)).
      { destruct 1 as (Hnun' & Hnptr'). eauto using typecl_wt_val_wt_val. }
      destruct uop; simpl in *.
      + rewrite Cop.notbool_bool_val in Hsop.
        DestructCases. destruct b; split; discriminate.
      + unfold Cop.sem_notint in Hsop.
        destruct v1; DestructCases; split; discriminate.
      + unfold Cop.sem_neg in Hsop.
        destruct v1; DestructCases; split; discriminate.
      + unfold Cop.sem_absfloat in Hsop.
        destruct v1; DestructCases; split; discriminate.
    - (* CastOp *)
      destruct (Ctyping.check_cast (cltype ty1) (cltype t));
        [injection Htop; intro; subst; clear Htop|discriminate].
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
  Qed.

  (* Solve goal with hypothesis of the form:
       (forall b ofs, Values.Vptr b' ofs' <> Values.Vptr b ofs) *)
  Ltac ContradictNotVptr :=
      match goal with
      | H: context [Values.Vptr ?b ?i <> Values.Vptr _ _] |- _ =>
        now contradiction (H b i)
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
    intros ** H.
    unfold Cop.sem_cmp in H;
      DestructCases; split; try discriminate;
        try (apply option_map_of_bool_true_false in H;
             destruct H; subst; discriminate).
    + unfold Cop.sem_binarith in H; DestructCases;
        apply cases_of_bool; discriminate.
    + unfold Cop.sem_binarith in H; DestructCases;
        apply cases_of_bool; discriminate.
  Qed.

  Ltac GoalMatchMatch :=
    repeat match goal with
           | |- match match ?x with _ => _ end with _ => _ end = _ =>
             destruct x
           end; auto.
  
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
  
  Lemma pres_sem_binop:
    forall op ty1 ty2 ty v1 v2 v,
      type_binop op ty1 ty2 = Some ty ->
      sem_binop op v1 ty1 v2 ty2 = Some v ->
      wt_val v1 ty1 ->
      wt_val v2 ty2 ->
      wt_val v ty.
  Proof.
    unfold type_binop, sem_binop.
    intros ** Hty Hsem Hwt1 Hwt2.
    destruct (Ctyping.type_binop op (cltype ty1) (cltype ty2)) eqn:Hok;
      [|discriminate].
    pose proof (wt_val_not_vundef_nor_vptr _ _ Hwt1) as (Hnun1 & Hnptr1).
    pose proof (wt_val_not_vundef_nor_vptr _ _ Hwt2) as (Hnun2 & Hnptr2).
    apply wt_val_wt_val_cltype in Hwt1.
    apply wt_val_wt_val_cltype in Hwt2.
    pose proof (Ctyping.pres_sem_binop _ _ _ _ _ _ _ _ _ Hok Hsem Hwt1 Hwt2)
      as Hwt.
    cut (v <> Values.Vundef /\ (forall b ofs, v <> Values.Vptr b ofs)).
    { destruct 1 as (Hnun' & Hnptr'). eauto using typecl_wt_val_wt_val. }
    destruct op; simpl in Hsem.
    - (* add *)
      unfold Cop.sem_add, Cop.sem_binarith in Hsem.
      rewrite classify_add_cltypes in Hsem.
      DestructCases; split; try discriminate; ContradictNotVptr.
    - (* sub *)
      unfold Cop.sem_sub, Cop.sem_binarith in Hsem.
      rewrite classify_sub_cltypes in Hsem.
      DestructCases; split; try discriminate; ContradictNotVptr.
    - (* mul *)
      unfold Cop.sem_mul, Cop.sem_binarith in Hsem.
      DestructCases; split; discriminate; ContradictNotVptr.
    - (* div *)
      unfold Cop.sem_div, Cop.sem_binarith in Hsem.
      DestructCases; split; discriminate; ContradictNotVptr.
    - (* mod *)
      unfold Cop.sem_mod, Cop.sem_binarith in Hsem.
      DestructCases; split; discriminate; ContradictNotVptr.
    - (* and *)
      unfold Cop.sem_and, Cop.sem_binarith in Hsem.
      DestructCases; split; discriminate; ContradictNotVptr.
    - (* or *)
      unfold Cop.sem_or, Cop.sem_binarith in Hsem.
      DestructCases; split; discriminate; ContradictNotVptr.
    - (* xor *)
      unfold Cop.sem_xor, Cop.sem_binarith in Hsem.
      DestructCases; split; discriminate; ContradictNotVptr.
    - (* shl *)
      unfold Cop.sem_shl, Cop.sem_shift in Hsem.
      DestructCases; split; discriminate; ContradictNotVptr.
    - (* shr *)
      unfold Cop.sem_shr, Cop.sem_shift in Hsem.
      DestructCases; split; discriminate; ContradictNotVptr.
      (* comparisons *)
    - apply sem_cmp_not_vundef_nor_vptr in Hsem; intuition.
    - apply sem_cmp_not_vundef_nor_vptr in Hsem; intuition.
    - apply sem_cmp_not_vundef_nor_vptr in Hsem; intuition.
    - apply sem_cmp_not_vundef_nor_vptr in Hsem; intuition.
    - apply sem_cmp_not_vundef_nor_vptr in Hsem; intuition.
    - apply sem_cmp_not_vundef_nor_vptr in Hsem; intuition.
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
    intros ** Hnptr.
    destruct op, v; simpl;
      unfold Cop.sem_notbool, Cop.sem_notint, Cop.sem_neg, Cop.sem_absfloat;
      repeat match goal with
             | |- (match ?x with _ => _ end) = _ => destruct x; auto
             | _ => ContradictNotVptr
             end.
  Qed.

  Lemma sem_cast_any_mem:
    forall v ty1 ty2 M1 M2,
      (forall b ofs, v <> Values.Vptr b ofs) ->
      Cop.sem_cast v ty1 ty2 M1 = Cop.sem_cast v ty1 ty2 M2.
  Proof.
    intros ** Hnptr.
    unfold Cop.sem_cast.
    destruct (Cop.classify_cast ty1 ty2); auto.
    destruct v; auto.
    ContradictNotVptr.
  Qed.

  Lemma sem_binary_operation_any_cenv_mem:
    forall op v1 ty1 v2 ty2 M1 M2 cenv1 cenv2,
      (forall b ofs, v1 <> Values.Vptr b ofs) ->
      (forall b ofs, v2 <> Values.Vptr b ofs) ->
      Cop.sem_binary_operation cenv1 op v1 (cltype ty1) v2 (cltype ty2) M1
      = Cop.sem_binary_operation cenv2 op v1 (cltype ty1) v2 (cltype ty2) M2.
  Proof.
    intros ** Hnptr1 Hnptr2.
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
    
End Op.

