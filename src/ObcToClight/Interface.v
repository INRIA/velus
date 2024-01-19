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
From compcert Require cfrontend.ClightBigstep.
From compcert Require common.Memory.
From compcert Require common.Memdata.
From compcert Require lib.Maps.
From Coq Require Import String.
From Coq Require Import ZArith.BinInt.

Import List.ListNotations.
Open Scope list_scope.

Open Scope bool_scope.
(* Interface avec CompCert *)

Global Hint Resolve Z.divide_refl : core.

Definition empty_composite_env : Ctypes.composite_env := (Maps.PTree.empty _).

Module Export Op <: OPERATORS.
  Definition cvalue: Type := Values.val.

  Inductive ctype' : Type :=
  | Tint:   Ctypes.intsize -> Ctypes.signedness -> ctype'
  | Tlong:  Ctypes.signedness -> ctype'
  | Tfloat: Ctypes.floatsize -> ctype'.

  Definition ctype := ctype'.

  Definition cltype (ty: ctype) : Ctypes.type :=
    match ty with
    | Tint sz sg => Ctypes.Tint sz sg Ctypes.noattr
    | Tlong sg   => Ctypes.Tlong sg (Ctypes.mk_attr false (Some (Npos 3)))
    | Tfloat sz  => Ctypes.Tfloat sz Ctypes.noattr
    end.

  Definition list_type_to_typelist : list Ctypes.type -> Ctypes.typelist :=
    List.fold_right (Ctypes.Tcons) Ctypes.Tnil.

  Definition typecl (ty: Ctypes.type) : option ctype :=
    match ty with
    | Ctypes.Tint sz sg attr => Some (Tint sz sg)
    | Ctypes.Tlong sg attr => Some (Tlong sg)
    | Ctypes.Tfloat sz attr => Some (Tfloat sz)
    | _ => None
    end.

  Definition type_chunk (ty: ctype) : AST.memory_chunk :=
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
    intros; destruct ty; simpl; try rewrite align_noattr; cases;
      try (simpl; replace Archi.align_float64 with (2 * 4)%Z; auto; apply Z.divide_factor_r).
  Qed.

  Lemma cltype_access_by_value:
  forall ty,
    Ctypes.access_mode (cltype ty) = Ctypes.By_value (type_chunk ty).
  Proof.
    destruct ty; simpl; cases.
  Qed.

  Lemma sizeof_cltype_chunk:
    forall gcenv t,
      Ctypes.sizeof gcenv (cltype t) = Memdata.size_chunk (type_chunk t).
  Proof.
    intros; apply sizeof_by_value, cltype_access_by_value.
  Qed.

  Inductive constant : Type :=
  | Cint: Integers.int -> Ctypes.intsize -> Ctypes.signedness -> constant
  | Clong: Integers.int64 -> Ctypes.signedness -> constant
  | Cfloat: Floats.float -> constant
  | Csingle: Floats.float32 -> constant.

  Definition cconst := constant.

  Definition enumtag := nat.

  Definition enumtag_to_int (c: enumtag) : int :=
    Int.repr (Z.of_nat c).

  Inductive value :=
  | Vscalar : cvalue -> value
  | Venum   : enumtag -> value.

  Inductive type :=
  | Tprimitive : ctype -> type
  | Tenum      : ident -> list ident -> type.

  Inductive const :=
  | Const: cconst -> const
  | Enum : enumtag -> const.

  Definition ctype_cconst (c: cconst) : ctype :=
    match c with
    | Cint _ sz sg => Tint sz sg
    | Clong _ sg   => Tlong sg
    | Cfloat _     => Tfloat Ctypes.F64
    | Csingle _    => Tfloat Ctypes.F32
    end.

  Definition sem_cconst (c: cconst) : cvalue :=
    match c with
    | Cint i sz sg => Values.Vint (Cop.cast_int_int sz sg i)
    | Clong i sg   => Values.Vlong i
    | Cfloat f     => Values.Vfloat f
    | Csingle f    => Values.Vsingle f
    end.

  Definition init_ctype (ty: ctype) : cconst :=
    match ty with
    | Tint sz sg => Cint Integers.Int.zero sz sg
    | Tlong sg   => Clong Integers.Int64.zero sg
    | Tfloat Ctypes.F64 => Cfloat Floats.Float.zero
    | Tfloat Ctypes.F32 => Csingle Floats.Float32.zero
    end.

  (* Booleans *)
  (* Definition true_const : const := Cint Int.one Ctypes.IBool Ctypes.Signed. *)
  (* Definition false_const : const := Cint Int.zero Ctypes.IBool Ctypes.Signed. *)
  (* Definition sem_true_const : sem_const true_const = true_val := eq_refl. *)
  (* Definition sem_false_const : sem_const false_const = false_val := eq_refl. *)
  (* Definition type_true_const : type_const true_const = bool_type := eq_refl. *)
  (* Definition type_false_const : type_const false_const = bool_type := eq_refl. *)

  Inductive unop' : Type :=
  | UnaryOp: Cop.unary_operation -> unop'
  | CastOp:  ctype -> unop'.

  Definition unop := unop'.
  Definition binop := Cop.binary_operation.

  Open Scope nat_scope.

  Definition intsize_of_enumtag (n: enumtag): Ctypes.intsize :=
    if n <=? 2 ^ 8 then Ctypes.I8
    else if n <=? 2 ^ 16 then Ctypes.I16
         else Ctypes.I32.

  Definition enumtag_ctype (n: nat) : ctype :=
    Tint (intsize_of_enumtag n) Ctypes.Unsigned.

  Definition sem_unop_bool (uop: unop) (c: enumtag) : option enumtag :=
    match uop with
    | UnaryOp op =>
      match op with
      | Cop.Onotbool =>
        match c with
        | 0 => Some 1
        | 1 => Some 0
        | _ => None
        end
      | _ => None
      end
    | CastOp _ => None
    end.

  Definition sem_unop (uop: unop) (v: value) (ty: type) : option value :=
    match v, ty with
    | Vscalar v, Tprimitive ty =>
      option_map Vscalar
                 match uop with
                 | UnaryOp op => Cop.sem_unary_operation op v (cltype ty) Memory.Mem.empty
                 | CastOp ty' => Cop.sem_cast v (cltype ty) (cltype ty') Memory.Mem.empty
                 end
    | Venum c, Tenum t _ =>
      if t ==b bool_id
      then option_map Venum (sem_unop_bool uop c)
      else None
    | _, _ => None
    end.

  Definition truth_table (c1 c2: enumtag) (c00 c10 c01 c11: enumtag): option enumtag :=
    match c1, c2 with
    | 0, 0 => Some c00
    | 1, 0 => Some c10
    | 0, 1 => Some c01
    | 1, 1 => Some c11
    | _, _ => None
    end.

  Definition sem_binop_bool (bop: binop) (c1 c2: enumtag) : option enumtag :=
    match bop with
    | Cop.Oand => truth_table c1 c2 0 0 0 1
    | Cop.Oor  => truth_table c1 c2 0 1 1 1
    | Cop.Oxor => truth_table c1 c2 0 1 1 0
    | Cop.Oeq  => truth_table c1 c2 1 0 0 1
    | Cop.One  => truth_table c1 c2 0 1 1 0
    | Cop.Olt  => truth_table c1 c2 0 0 1 0
    | Cop.Ogt  => truth_table c1 c2 0 1 0 0
    | Cop.Ole  => truth_table c1 c2 1 0 1 1
    | Cop.Oge  => truth_table c1 c2 1 1 0 1
    | _ => None
    end.

  Definition enumtag_of_cvalue (v: cvalue) : enumtag :=
    match v with
    | Values.Vundef
    | Values.Vlong _
    | Values.Vfloat _
    | Values.Vsingle _
    | Values.Vptr _ _ => 0%nat
    | Values.Vint n => Z.to_nat (Int.unsigned n)
    end.

  Definition binop_always_returns_bool (op: binop) : bool :=
    match op with
    | Cop.Oeq
    | Cop.One
    | Cop.Olt
    | Cop.Ogt
    | Cop.Ole
    | Cop.Oge  => true
    | _        => false
    end.

  Definition binop_sometimes_returns_bool (op: binop) : bool :=
    match op with
    | Cop.Oand
    | Cop.Oor
    | Cop.Oxor
    | Cop.Oeq
    | Cop.One
    | Cop.Olt
    | Cop.Ogt
    | Cop.Ole
    | Cop.Oge  => true
    | _        => false
    end.

  Definition sem_binop (bop: binop) (v1: value) (ty1: type)
                                    (v2: value) (ty2: type) : option value :=
    match v1, ty1, v2, ty2 with
    | Vscalar v1, Tprimitive ty1, Vscalar v2, Tprimitive ty2 =>
      let v' := Cop.sem_binary_operation empty_composite_env
                                         bop v1 (cltype ty1) v2 (cltype ty2)
                                         Memory.Mem.empty
      in
      if binop_always_returns_bool bop
      then option_map Venum (option_map enumtag_of_cvalue v')
      else option_map Vscalar v'
    | Venum c1, Tenum t1 _, Venum c2, Tenum t2 _ =>
      if (t1 ==b bool_id) && (t2 ==b bool_id)
      then option_map Venum (sem_binop_bool bop c1 c2)
      else match bop with
           | Cop.Oeq => Some (Venum (if Int.eq (enumtag_to_int c1) (enumtag_to_int c2) then 1 else 0))
           | Cop.One => Some (Venum (if Int.eq (enumtag_to_int c1) (enumtag_to_int c2) then 0 else 1))
           | _ => None
           end
    | _, _, _, _ => None
    end.

  (* Operator typing *)

  Definition bool_type := Tenum bool_id [false_id; true_id].

  Definition type_unop (uop: unop) (ty: type) : option type :=
    match ty with
    | Tprimitive ty =>
      match uop with
      | UnaryOp op =>
        match Ctyping.type_unop op (cltype ty) with
        | Errors.OK ty' => option_map Tprimitive (typecl ty')
        | Errors.Error _ => None
        end
      | CastOp ty' =>
        match Ctyping.check_cast (cltype ty) (cltype ty') with
        | Errors.OK _ => Some (Tprimitive ty')
        | Errors.Error _ => None
        end
      end
    | Tenum t _ =>
      if t ==b bool_id then
        match uop with
        | UnaryOp Cop.Onotbool => Some bool_type
        | _ => None
        end
      else None
    end.

  Definition type_binop (bop: binop) (ty1 ty2: type) : option type :=
    match ty1, ty2 with
    | Tprimitive ty1, Tprimitive ty2 =>
      if binop_always_returns_bool bop then Some bool_type
      else match Ctyping.type_binop bop (cltype ty1) (cltype ty2) with
           | Errors.OK ty' => option_map Tprimitive (typecl ty')
           | Errors.Error _ => None
           end
    | Tenum t1 _, Tenum t2 _ =>
      if (t1 ==b bool_id) && (t2 ==b bool_id) && (binop_sometimes_returns_bool bop)
      then Some bool_type
      else match bop with
           | Cop.Oeq => Some bool_type
           | Cop.One => Some bool_type
           | _ => None
           end
    | _, _ => None
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
  Inductive wt_cvalue' : cvalue -> ctype -> Prop :=
  | wt_cvalue_int:
      forall n sz sg,
        Ctyping.wt_int n sz sg ->
        (sz = Ctypes.IBool -> (n = Int.zero \/ n = Int.one)) ->
        wt_cvalue' (Values.Vint n) (Tint sz sg)
  | wt_cvalue_long:
      forall n sg,
        wt_cvalue' (Values.Vlong n) (Tlong sg)
  | wt_cvalue_float:
      forall f,
        wt_cvalue' (Values.Vfloat f) (Tfloat Ctypes.F64)
  | wt_cvalue_single:
      forall f,
        wt_cvalue' (Values.Vsingle f) (Tfloat Ctypes.F32).

  Definition wt_cvalue : cvalue -> ctype -> Prop := wt_cvalue'.

  Global Hint Unfold wt_cvalue : typing.
  Global Hint Constructors wt_cvalue' : typing.

  Lemma wt_cvalue_cconst:
    forall c, wt_cvalue (sem_cconst c) (ctype_cconst c).
  Proof.
    destruct c.
    - apply wt_cvalue_int.
      + apply Ctyping.pres_cast_int_int.
      + intro; subst; simpl.
        destruct (Int.eq i Int.zero); auto.
    - apply wt_cvalue_long.
    - apply wt_cvalue_float.
    - apply wt_cvalue_single.
  Qed.

  Lemma wt_init_ctype:
    forall ty, wt_cvalue (sem_cconst (init_ctype ty)) ty.
  Proof.
    destruct ty.
    - apply wt_cvalue_int.
      + apply Ctyping.pres_cast_int_int.
      + intro; subst; simpl; auto.
    - apply wt_cvalue_long.
    - destruct f.
      + apply wt_cvalue_single.
      + apply wt_cvalue_float.
  Qed.

  Lemma ctype_init_ctype:
    forall ty, ctype_cconst (init_ctype ty) = ty.
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

  Lemma wt_cvalue_good_bool:
    forall v ty,
      wt_cvalue v ty ->
      good_bool v (cltype ty).
  Proof.
    intros * WTv. unfold good_bool.
    inv WTv; simpl; auto.
    match goal with H:sz = Ctypes.IBool -> _ |- _ =>
                    destruct sz; auto; destruct H; subst; auto
    end.
  Qed.

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

  Local Hint Resolve good_bool_not_bool : core.

  (* Opaque good_bool. *)

  Lemma good_bool_zero_or_one:
    forall i sz sg a,
      good_bool (Values.Vint i) (Ctypes.Tint sz sg a) ->
      sz = Ctypes.IBool ->
      i = Int.zero \/ i = Int.one.
  Proof.
    intros * Hgb Hsz; subst; inversion_clear Hgb; auto.
  Qed.

  Lemma typecl_wt_val_wt_cvalue:
    forall cty ty v,
      typecl cty = Some ty ->
      Ctyping.wt_val v cty ->
      v <> Values.Vundef ->
      (forall b ofs, v <> Values.Vptr b ofs) ->
      good_bool v cty ->
      wt_cvalue v ty.
  Proof.
    intros * Htcl Hcty Hnun Hnptr Hgb.
    inv Hcty; inv Htcl; simpl in *; eauto with typing;
      try contradiction; try discriminate.
    - constructor; auto.
      intros; subst; auto.
    - exfalso; now eapply Hnptr.
  Qed.

  Lemma wt_cvalue_not_vundef_nor_vptr:
    forall v ty,
      wt_cvalue v ty ->
      v <> Values.Vundef /\ (forall b ofs, v <> Values.Vptr b ofs).
  Proof.
    intros * Hwt.
    destruct ty; inversion Hwt; subst;
      split; discriminate.
  Qed.

  Lemma wt_cvalue_wt_val_cltype:
    forall v ty,
      wt_cvalue v ty ->
      Ctyping.wt_val v (cltype ty).
  Proof.
    intros * Hwt.
    destruct ty; inversion_clear Hwt;
    eauto using Ctyping.wt_val.
  Qed.

  Lemma type_castop:
    forall ty ty',
      type_unop (CastOp ty') (Tprimitive ty) = Some (Tprimitive ty').
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

  Inductive wt_value: value -> type -> Prop :=
  | WTVScalarPrimitive: forall v t,
      wt_cvalue v t ->
      wt_value (Vscalar v) (Tprimitive t)
  | WTVEnum: forall v tx tn,
      v < List.length tn ->
      wt_value (Venum v) (Tenum tx tn).

  Lemma typecl_cltype:
    forall t, typecl (cltype t) = Some t.
  Proof.
    now destruct t.
  Qed.

  Lemma pres_sem_unop:
    forall op ty1 ty v1 v,
      type_unop op ty1 = Some ty ->
      sem_unop op v1 ty1 = Some v ->
      wt_value v1 ty1 ->
      wt_value v ty.
  Proof.
    intros * Htop Hsop Hv1.
    unfold type_unop, sem_unop in *.
    destruct op as [uop|].
    - (* UnaryOp *)
      inv Hv1.
      + take (wt_cvalue _ _) and pose proof (wt_cvalue_not_vundef_nor_vptr _ _ it)
          as [Hnun Hnptr]; apply wt_cvalue_wt_val_cltype in it.
        destruct (Ctyping.type_unop uop (cltype t)) as [ct'|] eqn: E;
          simpl in *; try discriminate.
        apply option_map_inv in Hsop as (v' & Hsop &?); subst.
        apply option_map_inv in Htop as (t' & Htop &?); subst.
        pose proof E.
        eapply Ctyping.pres_sem_unop in E; eauto.
        constructor.
        cut (v' <> Values.Vundef
             /\ (forall b ofs, v' <> Values.Vptr b ofs)
             /\ good_bool v' ct').
        { destruct 1 as (Hnun' & Hnptr' & Hgb); eauto using typecl_wt_val_wt_cvalue. }
        destruct uop; simpl in *.
        * rewrite Cop.notbool_bool_val in Hsop.
          DestructCases; destruct b; repeat split; try discriminate; auto.
        * unfold Cop.sem_notint in Hsop.
          DestructCases; repeat split; try discriminate; auto.
        * unfold Cop.sem_neg in Hsop.
          DestructCases; repeat split; try discriminate; auto.
        * unfold Cop.sem_absfloat in Hsop.
          DestructCases; repeat split; try discriminate; auto.
    + destruct (tx ==b bool_id), uop; try discriminate.
      inv Htop.
      apply option_map_inv in Hsop as (v' & Hsop &?); subst.
      constructor.
      simpl in *.
      cases.

    - (* CastOp *)
      inv Hv1.
      + take (wt_cvalue _ _) and pose proof (wt_cvalue_not_vundef_nor_vptr _ _ it)
          as [Hnun Hnptr]; apply wt_cvalue_wt_val_cltype in it.
        rewrite check_cltype_cast in Htop; inv Htop.
        apply option_map_inv in Hsop as (v' & Hsop &?); subst.
        constructor.
        pose proof (Ctyping.pres_sem_cast _ _ _ _ _ it Hsop).
        eapply typecl_wt_val_wt_cvalue; eauto.
        * apply typecl_cltype.
        * (* result cannot be Vundef *)
          unfold Cop.sem_cast, Cop.classify_cast in Hsop.
          DestructCases; try discriminate; auto.
        * (* result cannot be Vptr *)
          unfold Cop.sem_cast, Cop.classify_cast in Hsop.
          intros b ofs.
          specialize (Hnptr b ofs).
          DestructCases; try discriminate; auto.
        * (* booleans must be zero or one *)
          destruct c; simpl; auto.
          destruct i, v'; auto.
          simpl in *.
          unfold Cop.sem_cast in Hsop.
          simpl in Hsop.
          DestructCases;
            try match goal with |- context [if ?x then _ else _] => destruct x end;
            simpl; auto.
      + destruct (tx ==b bool_id); try discriminate.
  Qed.

  Lemma sem_cast_same:
    forall m v t,
      wt_cvalue v t ->
      Cop.sem_cast v (cltype t) (cltype t) m = Some v.
  Proof.
    intros * WTv.
    apply Cop.cast_val_casted.
    destruct (wt_cvalue_not_vundef_nor_vptr _ _ WTv) as (Hnun & Hnptr).
    pose proof (wt_cvalue_good_bool _ _ WTv) as Hgb.
    apply wt_cvalue_wt_val_cltype in WTv.
    destruct v.
    - tauto.
    - inv WTv; try match goal with H:_ = cltype t |- _ =>
                                   destruct t; now inv H end.
      constructor.
      match goal with H:Ctypes.Tint ?sz ?sg _ = cltype t |- _ =>
        rewrite <-H in Hgb; destruct sz, sg; auto
      end; destruct (good_bool_zero_or_one _ _ _ _ Hgb);
        try subst; auto.
    - inv WTv. apply Cop.val_casted_long.
      + match goal with H:Ctypes.Tpointer _ _ = cltype t |- _
                        => destruct t; inv H end.
      + match goal with H:Ctypes.Tvoid = cltype t |- _ => destruct t; inv H end.
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

  Lemma binop_always_returns_bool_spec:
    forall ce bop v1 t1 v2 t2 m v,
      binop_always_returns_bool bop = true ->
      Cop.sem_binary_operation ce bop v1 t1 v2 t2 m = Some v ->
      v = Values.Vint (enumtag_to_int (enumtag_of_cvalue v)).
  Proof.
    intros * Hbop Sem.
    cut (v = Values.Vtrue \/ v = Values.Vfalse).
    - intros []; subst; simpl;
        (rewrite Int.unsigned_one || rewrite Int.unsigned_zero); auto.
    - destruct bop; simpl in *; try discriminate;
        eapply sem_cmp_true_or_false; eauto.
  Qed.

  Lemma enumtag_to_int_0:
    enumtag_to_int 0%nat = Int.zero.
  Proof. reflexivity. Qed.

  Lemma enumtag_to_int_1:
    enumtag_to_int 1%nat = Int.one.
  Proof. reflexivity. Qed.

  Definition enumtag_cltype (n: nat) : Ctypes.type :=
    Ctypes.Tint (intsize_of_enumtag n) Ctypes.Unsigned Ctypes.noattr.

  Fact enumtag_cltype_ctype:
    forall n,
      enumtag_cltype n = cltype (enumtag_ctype n).
  Proof. reflexivity. Qed.

  Definition memory_chunk_of_enumtag (n: nat) : AST.memory_chunk :=
    if n <=? 2 ^ 8 then AST.Mint8unsigned
    else if n <=? 2 ^ 16 then AST.Mint16unsigned
         else AST.Mint32.

  Definition type_to_chunk (ty: type) : AST.memory_chunk :=
    match ty with
    | Tprimitive ty => type_chunk ty
    | Tenum _ n => memory_chunk_of_enumtag (List.length n)
    end.

  Lemma memory_chunk_of_enumtag_spec:
    forall n,
      n <= 2 ^ 8 /\ memory_chunk_of_enumtag n = AST.Mint8unsigned
      \/ 2 ^ 8 < n <= 2 ^ 16 /\ memory_chunk_of_enumtag n = AST.Mint16unsigned
      \/ 2 ^ 16 < n /\ memory_chunk_of_enumtag n = AST.Mint32.
  Proof.
    unfold memory_chunk_of_enumtag; intro.
    destruct (n <=? _) eqn: E.
    - apply Nat.leb_le in E; auto.
    - apply Nat.leb_gt in E.
      destruct (n <=? _) eqn: E'.
      + apply Nat.leb_le in E'; auto.
      + apply Nat.leb_gt in E'; auto.
  Qed.

  Lemma intsize_of_enumtag_spec:
    forall n,
      n <= 2 ^ 8 /\ intsize_of_enumtag n = Ctypes.I8
      \/ 2 ^ 8 < n <= 2 ^ 16 /\ intsize_of_enumtag n = Ctypes.I16
      \/ 2 ^ 16 < n /\ intsize_of_enumtag n = Ctypes.I32.
  Proof.
    unfold intsize_of_enumtag; intro.
    destruct (n <=? _) eqn: E.
    - apply Nat.leb_le in E; auto.
    - apply Nat.leb_gt in E.
      destruct (n <=? _) eqn: E'.
      + apply Nat.leb_le in E'; auto.
      + apply Nat.leb_gt in E'; auto.
  Qed.

  Lemma intsize_memory_chunk_of_enumtag_spec:
    forall n,
      n <= 2 ^ 8
      /\ intsize_of_enumtag n = Ctypes.I8
      /\ memory_chunk_of_enumtag n = AST.Mint8unsigned
      \/
      2 ^ 8 < n <= 2 ^ 16
      /\ intsize_of_enumtag n = Ctypes.I16
      /\ memory_chunk_of_enumtag n = AST.Mint16unsigned
      \/
      2 ^ 16 < n
      /\ intsize_of_enumtag n = Ctypes.I32
      /\ memory_chunk_of_enumtag n = AST.Mint32.
  Proof.
    unfold intsize_of_enumtag, memory_chunk_of_enumtag; intro.
    destruct (n <=? _) eqn: E.
    - apply Nat.leb_le in E; auto.
    - apply Nat.leb_gt in E.
      destruct (n <=? _) eqn: E'.
      + apply Nat.leb_le in E'; auto.
      + apply Nat.leb_gt in E'; auto.
  Qed.

  Lemma sem_cast_binarith_enumtag_cltype_l:
    forall v n1 n2 m,
      Cop.sem_cast (Values.Vint v) (enumtag_cltype n1)
                   (Cop.binarith_type (Cop.classify_binarith (enumtag_cltype n1) (enumtag_cltype n2))) m
      = Some (Values.Vint v).
  Proof.
    intros.
    simpl. unfold enumtag_cltype.
    destruct (intsize_of_enumtag_spec n1) as [(Hn1 & E1)|[(Hn1 & E1)|(Hn1 & E1)]],
                                             (intsize_of_enumtag_spec n2) as [(Hn2 & E2)|[(Hn2 & E2)|(Hn2 & E2)]];
      rewrite E1; try rewrite E2; simpl;
        unfold Cop.sem_cast; simpl; destruct Archi.ptr64; auto.
  Qed.

  Lemma sem_cast_binarith_enumtag_cltype_r:
    forall v n1 n2 m,
      Cop.sem_cast (Values.Vint v) (enumtag_cltype n2)
                   (Cop.binarith_type (Cop.classify_binarith (enumtag_cltype n1) (enumtag_cltype n2))) m
      = Some (Values.Vint v).
  Proof.
    intros.
    simpl. unfold enumtag_cltype.
    destruct (intsize_of_enumtag_spec n1) as [(Hn1 & E1)|[(Hn1 & E1)|(Hn1 & E1)]],
                                             (intsize_of_enumtag_spec n2) as [(Hn2 & E2)|[(Hn2 & E2)|(Hn2 & E2)]];
      rewrite E1; try rewrite E2; simpl;
        unfold Cop.sem_cast; simpl; destruct Archi.ptr64; auto.
  Qed.

  Lemma sem_binop_bool_spec:
    forall ce bop c1 c2 m c n1 n2,
      c1 < n1 ->
      c2 < n2 ->
      sem_binop_bool bop c1 c2 = Some c ->
      Cop.sem_binary_operation ce bop
                               (Values.Vint (enumtag_to_int c1)) (enumtag_cltype n1)
                               (Values.Vint (enumtag_to_int c2)) (enumtag_cltype n2) m =
      Some (Values.Vint (enumtag_to_int c)).
  Proof.
    intros * ?? Sem.
    destruct bop; simpl in *; try discriminate;
      unfold Cop.sem_and, Cop.sem_or, Cop.sem_xor, Cop.sem_cmp, Cop.sem_binarith, Cop.classify_cmp;
      rewrite ? sem_cast_binarith_enumtag_cltype_l, ? sem_cast_binarith_enumtag_cltype_r; simpl;
    destruct (intsize_of_enumtag_spec n1) as [(Hn1 & E1)|[(Hn1 & E1)|(Hn1 & E1)]],
                                             (intsize_of_enumtag_spec n2) as [(Hn2 & E2)|[(Hn2 & E2)|(Hn2 & E2)]];
      rewrite E1; try rewrite E2; simpl;
        do 2 f_equal;
        destruct c1 as [|[]], c2 as [|[]]; inv Sem;
          repeat (rewrite enumtag_to_int_0 || rewrite enumtag_to_int_1); auto.
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

  Lemma truth_table_wt_value:
    forall c1 c2 n1 n2 n3 n4 c,
      n1 <= 1 ->
      n2 <= 1 ->
      n3 <= 1 ->
      n4 <= 1 ->
      truth_table c1 c2 n1 n2 n3 n4 = Some c ->
      wt_value (Venum c) bool_type.
  Proof.
    intros * ???? TT.
    constructor; simpl.
    destruct c1 as [|[]], c2 as [|[]]; simpl in *; inv TT; lia.
  Qed.

  Lemma pres_sem_binop:
    forall bop ty1 ty2 ty v1 v2 v,
      type_binop bop ty1 ty2 = Some ty ->
      sem_binop bop v1 ty1 v2 ty2 = Some v ->
      wt_value v1 ty1 ->
      wt_value v2 ty2 ->
      wt_value v ty.
  Proof.
    unfold type_binop, sem_binop.
    intros * Hty Hsem Hwt1 Hwt2.
    inversion Hwt1 as [?? Hwt1'|? t1 n1]; inversion Hwt2 as [?? Hwt2'|? t2 n2]; subst;
      try discriminate.
    (* Scalar - Scalar *)
    - destruct (binop_always_returns_bool bop) eqn: Hbop;
        apply option_map_inv in Hsem as (c & Hsem & ?); subst.
      (* Binary comparisons always return a bool (zero or one). *)
      + inv Hty.
        constructor.
        apply option_map_inv in Hsem as (cv & Hsem & ?); subst.
        destruct bop; try discriminate Hbop;
          unfold Cop.sem_binary_operation in Hsem;
          destruct (sem_cmp_true_or_false _ _ _ _ _ _ _ Hsem); subst; simpl;
            (rewrite Int.unsigned_one || rewrite Int.unsigned_zero); simpl; lia.
      + destruct (Ctyping.type_binop bop (cltype _) (cltype _)) as [ct'|] eqn: E;
          simpl in *; try discriminate.
        apply option_map_inv in Hty as (ty' & Hty & ?); subst.
        constructor.
        pose proof (binop_never_bool _ _ _ _ E) as Hnbool.
        pose proof (wt_cvalue_not_vundef_nor_vptr _ _ Hwt1') as (Hnun1 & Hnptr1).
        pose proof (wt_cvalue_not_vundef_nor_vptr _ _ Hwt2') as (Hnun2 & Hnptr2).
        apply wt_cvalue_wt_val_cltype in Hwt1'.
        apply wt_cvalue_wt_val_cltype in Hwt2'.
        pose proof (Ctyping.pres_sem_binop _ _ _ _ _ _ _ _ _ E Hsem Hwt1' Hwt2')
          as Hwt.
        cut (c <> Values.Vundef
             /\ (forall b ofs, c <> Values.Vptr b ofs)
             /\ good_bool c ct').
      { destruct 1 as (Hnun' & Hnptr' & Hgb); eauto using typecl_wt_val_wt_cvalue. }
      destruct bop; simpl in Hsem; try discriminate Hbop.
      * (* add *)
        unfold Cop.sem_add, Cop.sem_binarith in Hsem.
        rewrite classify_add_cltypes in Hsem.
        DestructCases; repeat split; try discriminate; try ContradictNotVptr; auto.
      * (* sub *)
        unfold Cop.sem_sub, Cop.sem_binarith in Hsem.
        rewrite classify_sub_cltypes in Hsem.
        DestructCases; repeat split; try discriminate; try ContradictNotVptr; auto.
      * (* mul *)
        unfold Cop.sem_mul, Cop.sem_binarith in Hsem.
        DestructCases; repeat split; try discriminate; try ContradictNotVptr; auto.
      * (* div *)
        unfold Cop.sem_div, Cop.sem_binarith in Hsem.
        DestructCases; repeat split; try discriminate; try ContradictNotVptr; auto.
      * (* mod *)
        unfold Cop.sem_mod, Cop.sem_binarith in Hsem.
        DestructCases; repeat split; try discriminate; try ContradictNotVptr; auto.
      * (* and *)
        unfold Cop.sem_and, Cop.sem_binarith in Hsem.
        DestructCases; repeat split; try discriminate; try ContradictNotVptr; auto.
      * (* or *)
        unfold Cop.sem_or, Cop.sem_binarith in Hsem.
        DestructCases; repeat split; try discriminate; try ContradictNotVptr; auto.
      * (* xor *)
        unfold Cop.sem_xor, Cop.sem_binarith in Hsem.
        DestructCases; repeat split; try discriminate; try ContradictNotVptr; auto.
      * (* shl *)
        unfold Cop.sem_shl, Cop.sem_shift in Hsem.
        DestructCases; repeat split; try discriminate; try ContradictNotVptr; auto.
      * (* shr *)
        unfold Cop.sem_shr, Cop.sem_shift in Hsem.
        DestructCases; repeat split; try discriminate; try ContradictNotVptr; auto.

    (* Enum - Enum *)
    - destruct ((t1 ==b bool_id) && (t2 ==b bool_id)); simpl in *.
      + apply option_map_inv in Hsem as (c & Hsem & ?); subst.
        destruct bop; simpl in *; try discriminate; inv Hty;
          eapply truth_table_wt_value with (5:=Hsem); eauto.
      + destruct bop; try discriminate; inv Hty; inv Hsem; constructor;
          cases; simpl; lia.
  Qed.

  Lemma cvalue_dec: forall v1 v2 : cvalue, {v1 = v2} + {v1 <> v2}.
  Proof.
    apply Values.Val.eq.
  Qed.

  Lemma ctype_dec: forall t1 t2 : ctype, {t1 = t2} + {t1 <> t2}.
  Proof.
    decide equality; (apply Ctyping.signedness_eq
                      || apply Ctyping.intsize_eq
                      || apply Ctyping.floatsize_eq).
  Qed.

  Lemma cconst_dec: forall c1 c2 : cconst, {c1 = c2} + {c1 <> c2}.
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
    apply ctype_dec.
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

  Lemma wt_cvalue_load_result:
    forall ty v,
      wt_cvalue v ty ->
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

  Open Scope string_scope.

  Definition string_of_ctype (ty: ctype) : String.string :=
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

  (* External functions *)

  Definition sem_extern f (tyins : list ctype) xs (tyout : ctype) y :=
    forall ge mem,
      Events.external_functions_sem
        (pos_to_str f)
        {| AST.sig_args := List.map (fun cty => Ctypes.typ_of_type (cltype cty)) tyins;
           AST.sig_res := Ctypes.rettype_of_type (cltype tyout);
           AST.sig_cc := AST.cc_default |}
        ge xs mem nil y mem
      /\ wt_cvalue y tyout.

  Lemma sem_extern_det : forall f tyins ins tyout out1 out2,
      sem_extern f tyins ins tyout out1 ->
      sem_extern f tyins ins tyout out2 ->
      out1 = out2.
  Proof.
    unfold sem_extern.
    intros * Hext1 Hext2.
    specialize (Hext1 (@Globalenvs.Genv.to_senv True True (Globalenvs.Genv.empty_genv _ _ nil)) Memory.Mem.empty).
    specialize (Hext2 (@Globalenvs.Genv.to_senv True True (Globalenvs.Genv.empty_genv _ _ nil)) Memory.Mem.empty).
    destruct_conjs.
    remember (AST.mksignature _ _ _) as sig.
    specialize (Events.external_functions_properties (pos_to_str f) sig) as [].
    eapply ec_determ; eauto.
  Qed.

  Lemma pres_sem_extern:
    forall f tyins vins tyout vout,
      List.Forall2 wt_cvalue vins tyins ->
      sem_extern f tyins vins tyout vout ->
      wt_cvalue vout tyout.
  Proof.
    unfold sem_extern.
    intros * Hin Hext.
    specialize (Hext (@Globalenvs.Genv.to_senv True True (Globalenvs.Genv.empty_genv _ _ nil)) Memory.Mem.empty) as (Hext&Hwt); auto.
  Qed.
End Op.

Global Hint Resolve cltype_access_by_value cltype_align wt_cvalue_load_result sem_cast_same : core.

Module OpAux := OperatorsAux Ids Op.
Import OpAux.

Definition value_to_cvalue (v: value) : cvalue :=
  match v with
  | Vscalar v => v
  | Venum n => Values.Vint (enumtag_to_int n)
  end.


From Velus Require Import CommonTyping.
From Velus Require Import Clocks.

Lemma wt_value_load_result:
  forall ty v,
    wt_value v ty ->
    value_to_cvalue v = Values.Val.load_result (type_to_chunk ty) (value_to_cvalue v).
Proof.
  inversion 1; subst; simpl; auto.
  destruct (memory_chunk_of_enumtag_spec (Datatypes.length tn)) as [(Hn & E)|[(Hn & E)|(Hn & E)]];
    rewrite E; unfold enumtag_to_int; simpl; auto;
      unfold Int.zero_ext; rewrite Zbits.Zzero_ext_mod, Z.mod_small, Int.repr_unsigned; auto; try lia;
        rewrite Int.unsigned_repr.
  - replace 8%Z with (Z.of_nat 8); auto.
    rewrite <-Coqlib.two_power_nat_two_p, Zpower.two_power_nat_correct.
    replace 2%Z with (Z.of_nat 2); auto.
    rewrite <-Nat2Z_inj_pow; lia.
  - split; try lia.
    transitivity (Z.of_nat (2 ^ 8)); try lia.
    rewrite Nat2Z_inj_pow, <-Zpower.two_power_nat_correct, Coqlib.two_power_nat_two_p.
    apply Int.two_p_range.
    unfold Int.zwordsize; simpl; lia.
  - replace 16%Z with (Z.of_nat 16); auto.
    rewrite <-Coqlib.two_power_nat_two_p, Zpower.two_power_nat_correct.
    replace 2%Z with (Z.of_nat 2); auto.
    rewrite <-Nat2Z_inj_pow; lia.
  - split; try lia.
    transitivity (Z.of_nat (2 ^ 16)); try lia.
    rewrite Nat2Z_inj_pow, <-Zpower.two_power_nat_correct, Coqlib.two_power_nat_two_p.
    apply Int.two_p_range.
    unfold Int.zwordsize; simpl; lia.
Qed.
Global Hint Resolve wt_value_load_result : typing.

Lemma wt_value_not_vundef_nor_vptr:
  forall v ty,
    wt_value v ty ->
    value_to_cvalue v <> Values.Vundef
    /\ forall b ofs, value_to_cvalue v <> Values.Vptr b ofs.
Proof.
  inversion_clear 1; simpl.
  - eapply wt_cvalue_not_vundef_nor_vptr; eauto.
  - split; discriminate.
Qed.

Definition translate_type (ty: type) : Ctypes.type :=
  match ty with
  | Tprimitive t => cltype t
  | Tenum _ tn => enumtag_cltype (Datatypes.length tn)
  end.

Lemma translate_type_align:
  forall gcenv ty,
    (Memdata.align_chunk (type_to_chunk ty) | Ctypes.alignof gcenv (translate_type ty))%Z.
Proof.
  destruct ty as [|]; simpl; auto.
  destruct (intsize_memory_chunk_of_enumtag_spec (Datatypes.length l)) as [(Hn & E & E')|[(Hn & E & E')|(Hn & E & E')]];
    rewrite E, E'; simpl; auto.
Qed.

Lemma translate_type_access_by_value:
  forall ty,
    Ctypes.access_mode (translate_type ty) = Ctypes.By_value (type_to_chunk ty).
Proof.
  destruct ty as [|]; simpl; auto.
  destruct (intsize_memory_chunk_of_enumtag_spec (Datatypes.length l)) as [(Hn & E & E')|[(Hn & E & E')|(Hn & E & E')]];
    rewrite E, E'; simpl; auto.
Qed.

Lemma sizeof_translate_type_chunk:
  forall gcenv ty,
    Ctypes.sizeof gcenv (translate_type ty) = Memdata.size_chunk (type_to_chunk ty).
Proof.
  destruct ty as [|]; simpl; auto using sizeof_cltype_chunk.
  destruct (intsize_memory_chunk_of_enumtag_spec (Datatypes.length l)) as [(Hn & E & E')|[(Hn & E & E')|(Hn & E & E')]];
    rewrite E, E'; simpl; auto.
Qed.

Global Hint Resolve translate_type_access_by_value translate_type_align : clight.

Lemma translate_type_not_void:
  forall t,
    translate_type t <> Ctypes.Tvoid.
Proof.
  intros [[]|[]]; simpl; discriminate.
Qed.
Global Hint Resolve translate_type_not_void : clight.

Lemma sem_binary_operation_any_cenv_mem':
  forall op v1 ty1 v2 ty2 M1 M2 cenv1 cenv2,
    (forall b ofs, v1 <> Values.Vptr b ofs) ->
    (forall b ofs, v2 <> Values.Vptr b ofs) ->
    Cop.sem_binary_operation cenv1 op v1 (translate_type ty1) v2 (translate_type ty2) M1
    = Cop.sem_binary_operation cenv2 op v1 (translate_type ty1) v2 (translate_type ty2) M2.
Proof.
  intros; destruct ty1 as [|[]], ty2 as [|[]]; simpl; rewrite ? enumtag_cltype_ctype;
    apply sem_binary_operation_any_cenv_mem; auto.
Qed.

Lemma sem_cast_same':
  forall m v t,
    wt_value v t ->
    Cop.sem_cast (value_to_cvalue v) (translate_type t) (translate_type t) m =
    Some (value_to_cvalue v).
Proof.
  inversion_clear 1; simpl; auto.
  rewrite ? enumtag_cltype_ctype; auto.
  apply sem_cast_same.
  constructor; auto;
    destruct (intsize_of_enumtag_spec (Datatypes.length tn)) as [(Hn & E)|[(Hn & E)|(Hn & E)]];
    rewrite E; try discriminate;
      unfold enumtag_to_int; simpl; auto;
        unfold Int.zero_ext; rewrite Zbits.Zzero_ext_mod, Z.mod_small, Int.repr_unsigned; auto; try lia;
          rewrite Int.unsigned_repr.
  - replace 8%Z with (Z.of_nat 8); auto.
    rewrite <-Coqlib.two_power_nat_two_p, Zpower.two_power_nat_correct.
    replace 2%Z with (Z.of_nat 2); auto.
    rewrite <-Nat2Z_inj_pow; lia.
  - split; try lia.
    transitivity (Z.of_nat (2 ^ 8)); try lia.
    rewrite Nat2Z_inj_pow, <-Zpower.two_power_nat_correct, Coqlib.two_power_nat_two_p.
    apply Int.two_p_range.
    unfold Int.zwordsize; simpl; lia.
  - replace 16%Z with (Z.of_nat 16); auto.
    rewrite <-Coqlib.two_power_nat_two_p, Zpower.two_power_nat_correct.
    replace 2%Z with (Z.of_nat 2); auto.
    rewrite <-Nat2Z_inj_pow; lia.
  - split; try lia.
    transitivity (Z.of_nat (2 ^ 16)); try lia.
    rewrite Nat2Z_inj_pow, <-Zpower.two_power_nat_correct, Coqlib.two_power_nat_two_p.
    apply Int.two_p_range.
    unfold Int.zwordsize; simpl; lia.
Qed.
Global Hint Resolve sem_cast_same' : clight.

Lemma sem_switch_arg_enum:
  forall c tx tn,
    Cop.sem_switch_arg (value_to_cvalue (Venum c)) (translate_type (Tenum tx tn)) =
    Some (Int.unsigned (Int.repr (Z.of_nat c))).
Proof.
  intros *.
  unfold Cop.sem_switch_arg; simpl; auto.
Qed.
Global Hint Resolve sem_switch_arg_enum : clight.

Definition string_of_type (ty: type) : String.string :=
  match ty with
  | Tprimitive t => string_of_ctype t
  | Tenum t _ => pos_to_str t
  end.

From Velus Require Import IndexedStreams.
From Velus Require Import CoindStreams.
From Velus Require Import Obc.

Module ComTyp := CommonTypingFun Ids Op OpAux.
Module Cks := ClocksFun          Ids Op OpAux.
Module IStr := IndexedStreamsFun Ids Op OpAux Cks.
Module CStr := CoindStreamsFun   Ids Op OpAux Cks.
Module Obc  := ObcFun            Ids Op OpAux ComTyp.
