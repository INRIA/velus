Require Import Common.

Module Type OPERATORS.

  (* Types *)

  Parameter val : Type.
  Parameter type : Type.
  Parameter const : Type.

  (* Booleans *)

  Parameter true_val  : val.
  Parameter false_val : val.
  Axiom true_not_false_val : true_val <> false_val.

  Parameter bool_type : type.

  (* Constants *)

  Parameter type_const : const -> type.
  Parameter sem_const  : const -> val.

  (* Operations *)

  Parameter unop  : Type.
  Parameter binop : Type.

  Parameter sem_unop  : unop -> val -> type -> option val.
  Parameter sem_binop : binop -> val -> type -> val -> type -> option val.

  (* Typing *)

  Parameter type_unop  : unop -> type -> option type.
  Parameter type_binop : binop -> type -> type -> option type.

  Parameter wt_val : val -> type -> Prop.

  Axiom wt_val_true  : wt_val true_val bool_type.
  Axiom wt_val_false : wt_val false_val bool_type.
  Axiom wt_val_const : forall c, wt_val (sem_const c) (type_const c).

  Axiom pres_sem_unop:
    forall op ty1 ty v1 v,
      type_unop op ty1 = Some ty ->
      sem_unop op v1 ty1 = Some v ->
      wt_val v1 ty1 ->
      wt_val v ty.

  Axiom pres_sem_binop:
    forall op ty1 ty2 ty v1 v2 v,
      type_binop op ty1 ty2 = Some ty ->
      sem_binop op v1 ty1 v2 ty2 = Some v ->
      wt_val v1 ty1 ->
      wt_val v2 ty2 ->
      wt_val v ty.

  (* Decidability of elements *)

  Axiom val_dec   : forall v1  v2  : val,    {v1 = v2}  +  {v1 <> v2}.
  Axiom type_dec  : forall t1  t2  : type,   {t1 = t2}  +  {t1 <> t2}.
  Axiom const_dec : forall c1  c2  : const,  {c1 = c2}  +  {c1 <> c2}.
  Axiom unop_dec  : forall op1 op2 : unop,  {op1 = op2} + {op1 <> op2}.
  Axiom binop_dec : forall op1 op2 : binop, {op1 = op2} + {op1 <> op2}.

End OPERATORS.

Module Type OPERATORS_AUX (Import Ops : OPERATORS).
  Require Export Coq.Classes.EquivDec.
  Close Scope equiv_scope.

  Instance: EqDec val   eq := { equiv_dec := val_dec   }.
  Instance: EqDec type  eq := { equiv_dec := type_dec  }.
  Instance: EqDec const eq := { equiv_dec := const_dec }.
  Instance: EqDec unop  eq := { equiv_dec := unop_dec  }.
  Instance: EqDec binop eq := { equiv_dec := binop_dec }.

  Definition val_to_bool (v: val) : option bool :=
    if equiv_decb v true_val then Some true
    else if equiv_decb v false_val then Some false
         else None.

  Lemma val_to_bool_true:
    val_to_bool true_val = Some true.
  Proof.
    unfold val_to_bool. now rewrite equiv_decb_refl.
  Qed.

  Lemma val_to_bool_false:
    val_to_bool false_val = Some false.
  Proof.
    unfold val_to_bool.
    assert (equiv_decb false_val true_val = false) as Hne.
    apply not_equiv_decb_equiv.
    now intro HH; apply true_not_false_val; rewrite HH.
    now rewrite Hne, equiv_decb_refl.
  Qed.

  Lemma val_to_bool_true':
    forall v,
      val_to_bool v = Some true <-> v = true_val.
  Proof.
    intro; split; intro HH.
    2:now subst; apply val_to_bool_true.
    destruct (equiv_dec v true_val); [assumption|].
    apply not_equiv_decb_equiv in c.
    unfold val_to_bool in HH; rewrite c in HH.
    now destruct (equiv_decb v false_val).
  Qed.

  Lemma val_to_bool_false':
    forall v,
      val_to_bool v = Some false <-> v = false_val.
  Proof.
    intro; split; intro HH.
    2:now subst; apply val_to_bool_false.
    destruct (equiv_dec v false_val); [assumption|].
    apply not_equiv_decb_equiv in c.
    unfold val_to_bool in HH; rewrite c in HH.
    now destruct (equiv_decb v true_val).
  Qed.

  Definition wt_vals vs (xts: list (ident * type))
    := List.Forall2 (fun v xt => wt_val v (snd xt)) vs xts.

 (** A synchronous [value] is either an absence or a present constant *)

  Inductive value :=
  | absent
  | present (c : val).
  Implicit Type v : value.

  Definition value_dec (v1 v2: value) : {v1 = v2} + {v1 <> v2}.
    decide equality. apply val_dec.
  Defined.

  Instance: EqDec value eq := { equiv_dec := value_dec }.

End OPERATORS_AUX.

Module OperatorsAux (Import Ops : OPERATORS) <: OPERATORS_AUX Ops.
  Include OPERATORS_AUX Ops.
End OperatorsAux.
