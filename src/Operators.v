From Coq Require Import PeanoNat.
From Coq Require Import List.
From Velus Require Import Common.
From Coq Require Export Classes.EquivDec.

Import List.ListNotations.
Open Scope list_scope.

Module Type OPERATORS.

  (* Concrete types and values *)

  Parameter cvalue : Type.
  Parameter ctype  : Type.
  Parameter cconst : Type.

  (* Enums *)

  Definition enumtag := nat.

  (* Axiom enumtag_of_cvalue: cvalue -> enumtag. *)
  (* Axiom cvalue_of_enumtag: enumtag -> cvalue. *)
  (* Axiom enumtag_ctype: ctype. *)

  (* Axiom enumtag_of_cvalue_lte: *)
  (*   forall n, enumtag_of_cvalue (cvalue_of_enumtag n) <= n. *)

  (* Vélus types and values *)

  Inductive value :=
  | Vscalar : cvalue -> value
  | Venum   : enumtag -> value.

  Inductive type :=
  | Tprimitive : ctype -> type
  | Tenum      : ident -> list ident -> type.

  Inductive const :=
  | Const: cconst -> const
  | Enum : enumtag -> const.

  (* Constants *)

  Parameter ctype_cconst : cconst -> ctype.
  Parameter sem_cconst  : cconst -> cvalue.
  Parameter init_ctype  : ctype -> cconst.

  (* Operations *)

  Parameter unop  : Type.
  Parameter binop : Type.

  Parameter sem_unop  : unop -> value -> type -> option value.
  Parameter sem_binop : binop -> value -> type -> value -> type -> option value.

  (* External functions *)

  Parameter sem_extern : (* extern_env ->  *) ident -> list ctype -> list cvalue -> ctype -> cvalue -> Prop.

  Axiom sem_extern_det : forall f tyins ins tyout out1 out2,
      sem_extern f tyins ins tyout out1 ->
      sem_extern f tyins ins tyout out2 ->
      out1 = out2.

  (* Typing *)

  Parameter type_unop  : unop -> type -> option type.
  Parameter type_binop : binop -> type -> type -> option type.

  (* Parameter type_extern : extern_type -> list ctype -> option ctype. *)

  Parameter wt_cvalue : cvalue -> ctype -> Prop.

  Axiom wt_cvalue_cconst : forall c, wt_cvalue (sem_cconst c) (ctype_cconst c).

  Axiom wt_init_ctype : forall ty, wt_cvalue (sem_cconst (init_ctype ty)) ty.
  Axiom ctype_init_ctype : forall ty, ctype_cconst (init_ctype ty) = ty.

  Inductive wt_value: value -> type -> Prop :=
    | WTVScalarPrimitive: forall v t,
        wt_cvalue v t ->
        wt_value (Vscalar v) (Tprimitive t)
    | WTVEnum: forall v tx tn,
        v < length tn ->
        wt_value (Venum v) (Tenum tx tn).

  Conjecture pres_sem_unop:
    forall op ty1 ty v1 v,
      type_unop op ty1 = Some ty ->
      sem_unop op v1 ty1 = Some v ->
      wt_value v1 ty1 ->
      wt_value v ty.

  Conjecture pres_sem_binop:
    forall op ty1 ty2 ty v1 v2 v,
      type_binop op ty1 ty2 = Some ty ->
      sem_binop op v1 ty1 v2 ty2 = Some v ->
      wt_value v1 ty1 ->
      wt_value v2 ty2 ->
      wt_value v ty.

  Conjecture pres_sem_extern:
    forall f tyins vins tyout vout,
      Forall2 wt_cvalue vins tyins ->
      sem_extern f tyins vins tyout vout ->
      wt_cvalue vout tyout.

  (* Decidability of elements *)

  Axiom cvalue_dec   : forall v1  v2  : cvalue,    {v1 = v2}  +  {v1 <> v2}.
  Axiom ctype_dec  : forall t1  t2  : ctype,   {t1 = t2}  +  {t1 <> t2}.
  Axiom cconst_dec : forall c1  c2  : cconst,  {c1 = c2}  +  {c1 <> c2}.
  Axiom unop_dec  : forall op1 op2 : unop,  {op1 = op2} + {op1 <> op2}.
  Axiom binop_dec : forall op1 op2 : binop, {op1 = op2} + {op1 <> op2}.

  (* Simple characterization of unary/binary operators failure cases.
   * [check_unop], [check_binop] return
   * - [true] if the operator cannot fail with the values possibly provided,
       if no value is given the operator should never fail
   * - [false] otherwise
   *)

  Parameter check_unop : unop -> option value -> type -> bool.

  Conjecture check_unop_correct :
    forall op ov ty,
      check_unop op ov ty = true ->
      type_unop op ty <> None ->
      forall v,
      wt_value v ty ->
      match ov with
      | Some v' => v' = v
      | _ => True
      end ->
      sem_unop op v ty <> None.

  Parameter check_binop : binop -> option value -> type -> option value -> type -> bool.

  Conjecture check_binop_correct :
    forall op ov1 ty1 ov2 ty2,
      check_binop op ov1 ty1 ov2 ty2 = true ->
      type_binop op ty1 ty2 <> None ->
      forall v1 v2,
      wt_value v1 ty1 ->
      wt_value v2 ty2 ->
      match ov1 with
      | Some v => v = v1
      | _ => True
      end ->
      match ov2 with
      | Some v => v = v2
      | _ => True
      end ->
      sem_binop op v1 ty1 v2 ty2 <> None.

End OPERATORS.

Module Type OPERATORS_AUX
       (Import Ids : IDS)
       (Import Ops : OPERATORS).
  Close Scope equiv_scope.

  Global Instance: EqDec cvalue eq := { equiv_dec := cvalue_dec }.
  Global Instance: EqDec ctype  eq := { equiv_dec := ctype_dec  }.
  Global Instance: EqDec cconst eq := { equiv_dec := cconst_dec }.
  Global Instance: EqDec unop   eq := { equiv_dec := unop_dec   }.
  Global Instance: EqDec binop  eq := { equiv_dec := binop_dec  }.

  Definition false_tag : enumtag := 0.
  Definition true_tag : enumtag := 1.

  Lemma enumtag_eqb_eq : forall (x y : enumtag),
      (x ==b y) = true <-> x = y.
  Proof.
    setoid_rewrite equiv_decb_equiv. reflexivity.
  Qed.

  Lemma enumtag_eqb_neq : forall (x y : enumtag),
      (x ==b y) = false <-> x <> y.
  Proof.
    setoid_rewrite <-Bool.not_true_iff_false.
    setoid_rewrite equiv_decb_equiv. reflexivity.
  Qed.

  Lemma value_dec:
    forall v1 v2 : value,
      {v1 = v2} + {v1 <> v2}.
  Proof.
    repeat  decide equality.
    apply cvalue_dec.
  Qed.

  Definition sem_const (c0: const) : value :=
    match c0 with
    | Const c0 => Vscalar (sem_cconst c0)
    | Enum c   => Venum c
    end.


  Definition bool_velus_type := Tenum bool_id [false_id; true_id].

  Definition type_dec (t1 t2: type) : {t1 = t2} + {t1 <> t2}.
    repeat decide equality.
    apply ctype_dec.
  Defined.

  Global Instance: EqDec type eq := { equiv_dec := type_dec }.

  (** A synchronous [value] is either an absence or a present constant *)

  Inductive synchronous (A : Type) :=
  | absent
  | present (v: A).

  Arguments absent {_}.
  Arguments present {_}.

  Definition svalue := synchronous value.

  Definition svalue_dec (v1 v2: svalue) : {v1 = v2} + {v1 <> v2}.
    repeat decide equality.
    apply cvalue_dec.
  Defined.

  Global Instance: EqDec svalue eq := { equiv_dec := svalue_dec }.

  Lemma not_absent_bool:
    forall (x : svalue), x <> absent <-> x <>b absent = true.
  Proof.
    unfold nequiv_decb.
    setoid_rewrite Bool.negb_true_iff.
    split; intro Hx.
    - destruct x. now contradiction Hx.
      now apply not_equiv_decb_equiv.
    - destruct x. now apply not_equiv_decb_equiv.
      apply not_equiv_decb_equiv in Hx; auto.
  Qed.

  Lemma neg_eq_svalue:
    forall (x y: svalue),
      negb (x <>b y) = (x ==b y).
  Proof.
    unfold nequiv_decb; setoid_rewrite Bool.negb_involutive; auto.
  Qed.

  Lemma svalue_eqb_eq:
    forall (x y: svalue), x ==b y = true <-> x = y.
  Proof.
    setoid_rewrite equiv_decb_equiv; reflexivity.
  Qed.

  Lemma decidable_eq_svalue:
    forall (x y: svalue),
      Decidable.decidable (x = y).
  Proof.
    intros; unfold Decidable.decidable.
    setoid_rewrite <-svalue_eqb_eq.
    destruct (x ==b y); auto.
  Qed.

  Inductive wt_type (types: list type): type -> Prop :=
  | WTTPrim: forall cty,
      wt_type types (Tprimitive cty)
  | WTTEnum: forall tx tn,
      In (Tenum tx tn) types ->
      0 < length tn ->
      NoDup tn ->
      wt_type types (Tenum tx tn).

  Inductive wt_const (enums: list type): const -> type -> Prop :=
  | WTCConst: forall c,
      wt_const enums (Const c) (Tprimitive (ctype_cconst c))
  | WTCEnum: forall c tx tn,
      In (Tenum tx tn) enums ->
      c < length tn ->
      wt_const enums (Enum c) (Tenum tx tn).

  Definition wt_values vs (xts: list (ident * type))
    := List.Forall2 (fun v xt => wt_value v (snd xt)) vs xts.

  Lemma wt_value_const:
    forall enums c t,
      wt_const enums c t ->
      wt_value (sem_const c) t.
  Proof.
    inversion 1; subst; constructor; auto.
    apply wt_cvalue_cconst.
  Qed.

  Definition wt_option_value (vo: option value) (ty: type) : Prop :=
    match vo with
    | None => True
    | Some v => wt_value v ty
    end.

  Definition value_to_bool (v : value) :=
    match v with
    | Venum tag => Some (tag ==b true_tag)
    | _ => None
    end.

  Definition svalue_to_bool (v : svalue) :=
    match v with
    | absent => Some false
    | present v => value_to_bool v
    end.

  Definition wt_svalue (v: svalue) (ty: type) : Prop :=
    match v with
    | absent => True
    | present v => wt_value v ty
    end.

End OPERATORS_AUX.

Module OperatorsAux
       (Import Ids : IDS)
       (Import Ops : OPERATORS) <: OPERATORS_AUX Ids Ops.
  Include OPERATORS_AUX Ids Ops.
End OperatorsAux.
