Require Import lib.Integers.
Require Import lib.Floats.
Require Import Rustre.Common.
Require Import Rustre.Operators.

Require common.Values.
Require cfrontend.Cop.
Require cfrontend.Ctypes.
Require cfrontend.Ctyping.
Require common.Memory.
Require lib.Maps.

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
    | Tlong sg   => Ctypes.Tlong sg (Ctypes.mk_attr false (Some 3%N))
    | Tfloat sz  => Ctypes.Tfloat sz Ctypes.noattr
    end.

  Definition typecl (ty: Ctypes.type) : option type :=
    match ty with
    | Ctypes.Tint sz sg (Ctypes.mk_attr false None) => Some (Tint sz sg)
    | Ctypes.Tlong sg   (Ctypes.mk_attr false (Some 3%N)) => Some (Tlong sg)
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

  Lemma wt_val_true:
    wt_val true_val bool_type.
  Proof.
    apply wt_val_int.
    reflexivity.
  Qed.

  Lemma wt_val_false:
    wt_val false_val bool_type.
  Proof.
    apply wt_val_int.
    reflexivity.
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

  Lemma typecl_wt_val_wt_val:
    forall cty ty v,
      typecl cty = Some ty ->
      Ctyping.wt_val v cty ->
      v <> Values.Vundef ->
      (forall b ofs, v <> Values.Vptr b ofs) ->
      wt_val v ty.
  Proof.
    intros ** Htcl Hcty Hnun Hnptr.
    destruct cty; try discriminate;
      (destruct a; destruct attr_volatile; destruct attr_alignas;
       try discriminate; simpl in *; fold Ctypes.noattr in Hcty).
    - injection Htcl; intro HR; rewrite HR in *; clear Htcl.
      rewrite <-HR; clear HR.
      destruct v; try now inversion Hcty.
      + now contradiction Hnun.
      + inversion_clear Hcty. now apply wt_val_int.
      + exfalso; now eapply Hnptr.
    - destruct n; try destruct p; try discriminate.
      destruct p; try discriminate.
      injection Htcl; intro HR; rewrite HR in *; clear Htcl.
      rewrite <-HR; clear HR.
      destruct v; try now inversion Hcty.
      + now contradiction Hnun.
      + now apply wt_val_long.
    - injection Htcl; intro HR; rewrite HR in *; clear Htcl.
      rewrite <-HR; clear HR.
      destruct v; try now inversion Hcty.
      + now contradiction Hnun.
      + destruct f; try now inversion Hcty.
        now apply wt_val_float.
      + destruct f; try now inversion Hcty.
        now apply wt_val_single.
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
    destruct ty; inversion_clear Hwt.
    - now apply Ctyping.wt_val_int.
    - now apply Ctyping.wt_val_long.
    - now apply Ctyping.wt_val_float.
    - now apply Ctyping.wt_val_single.
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
    destruct op as [uop|].
    - (* UnaryOp *)
      simpl in *.
      destruct (Ctyping.type_unop uop (cltype ty1)) as [cty|] eqn:Hok;
        [|discriminate].
      pose proof (Ctyping.pres_sem_unop _ _ _ _ _ _ Hok Hsop
                                        (wt_val_wt_val_cltype _ _ Hv1)) as Hcwt.
      clear Hok.
      cut (v <> Values.Vundef /\ (forall b ofs, v <> Values.Vptr b ofs)).
      destruct 1 as (Hnun' & Hnptr');
        now apply typecl_wt_val_wt_val with (1:=Htop); eauto.
      destruct uop; simpl in *.
      + rewrite Cop.notbool_bool_val in Hsop.
        destruct (Cop.bool_val v1 (cltype ty1) Memory.Mem.empty);
          try discriminate.
        injection Hsop; intro; subst v.
        destruct b; simpl; split; discriminate.
      + unfold Cop.sem_notint in Hsop.
          destruct (Cop.classify_notint (cltype ty1));
            destruct v1; try discriminate;
            injection Hsop; intro; subst; split; discriminate.
      + unfold Cop.sem_neg in Hsop.
        destruct (Cop.classify_neg (cltype ty1));
          destruct v1; try discriminate;
          injection Hsop; intro; subst; split; discriminate.
      + unfold Cop.sem_absfloat in Hsop.
        destruct (Cop.classify_neg (cltype ty1));
          destruct v1; try discriminate;
            injection Hsop; intro; subst; split; discriminate.
    - (* CastOp *)
      (* TODO: automate proof on the example of Ctyping.pres_sem_cast *)
      simpl in Hsop. simpl in Htop.
      destruct (Ctyping.check_cast (cltype ty1) (cltype t));
        [|discriminate].
      destruct ty1 as [i1 s1|s1|f1];
        destruct t as [i2 s2|s2|f2];
        injection Htop; intro; subst; simpl in Hsop;
          destruct v1 as [i|i|f|f|b|ofs]; inversion_clear Hv1.
      + destruct i, i1, s1, i2, s2; inversion_clear Hsop;
          try (apply wt_val_int; simpl;
               try (rewrite Int.sign_ext_idem||rewrite Int.zero_ext_idem);
               intuition);
          match goal with |- context [if ?c then _ else _] => destruct c end;
          auto.
      + destruct i, i1, s1, s2; inversion_clear Hsop; apply wt_val_long.
      + destruct i, i1, s1, f2; inversion_clear Hsop;
          (apply wt_val_single || apply wt_val_float).
      + destruct f, s1, i2, s2; inversion_clear Hsop;
          try (apply wt_val_int; simpl;
               try (rewrite Int.sign_ext_idem||rewrite Int.zero_ext_idem);
               intuition);
          match goal with |- context [if ?c then _ else _] => destruct c end;
          auto.
      + destruct f, s1; inversion_clear Hsop; apply wt_val_long.
      + destruct f, s1, f2; inversion_clear Hsop;
          (apply wt_val_single || apply wt_val_float).
      + unfold Cop.sem_cast in Hsop.
        destruct f1, i2, s2; simpl in Hsop; try discriminate;
          (destruct (Float.to_int f) || destruct (Float.to_intu f));
          try (destruct (Float.to_intu f));
          try discriminate;
          injection Hsop; intro; subst; apply wt_val_int; simpl;
          try ((rewrite Int.sign_ext_idem||rewrite Int.zero_ext_idem);
               now intuition);
          try match goal with |- context [if ?c then _ else _] => destruct c end;
          auto.
      + unfold Cop.sem_cast in Hsop.
        destruct f1, i2, s2; simpl in Hsop; try discriminate;
          (destruct (Float32.to_int b) || destruct (Float32.to_intu b));
          try (destruct (Float32.to_intu b));
          try discriminate;
          injection Hsop; intro; subst; apply wt_val_int; simpl;
          try ((rewrite Int.sign_ext_idem||rewrite Int.zero_ext_idem);
               now intuition);
          try match goal with |- context [if ?c then _ else _] => destruct c end;
          auto.
      + apply Cop.cast_val_is_casted in Hsop;
          inversion_clear Hsop.
        apply wt_val_long.
      + apply Cop.cast_val_is_casted in Hsop;
          inversion_clear Hsop.
        apply wt_val_long.
      + apply Cop.cast_val_is_casted in Hsop;
          inversion_clear Hsop.
        now apply wt_val_float.
        now apply wt_val_single.
      + apply Cop.cast_val_is_casted in Hsop;
          inversion_clear Hsop.
        now apply wt_val_float.
        now apply wt_val_single.
  Qed.

  Lemma pres_sem_binop:
    forall op ty1 ty2 ty v1 v2 v,
      type_binop op ty1 ty2 = Some ty ->
      sem_binop op v1 ty1 v2 ty2 = Some v ->
      wt_val v1 ty1 ->
      wt_val v2 ty2 ->
      wt_val v ty.
  Proof.
  Admitted.

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
    
End Op.

