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

  (* Decidability of elements *)
  
  Axiom val_dec   : forall v1 v2 : val, {v1 = v2} + {v1 <> v2}.
  Axiom type_dec  : forall t1 t2 : type, {t1 = t2} + {t1 <> t2}.
  Axiom const_dec : forall c1 c2 : const, {c1 = c2} + {c1 <> c2}.
  Axiom unop_dec  : forall op1 op2 : unop, {op1 = op2} + {op1 <> op2}.
  Axiom binop_dec : forall op1 op2 : binop, {op1 = op2} + {op1 <> op2}.

End OPERATORS.

Module Type OPERATORS_AUX (Import Ops : OPERATORS).
  Require Export Coq.Classes.EquivDec.
  Close Scope equiv_scope.

  Instance: EqDec val eq   := { equiv_dec := val_dec   }.
  Instance: EqDec type eq  := { equiv_dec := type_dec  }.
  Instance: EqDec const eq := { equiv_dec := const_dec }.
  Instance: EqDec unop eq  := { equiv_dec := unop_dec  }.
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
  
End OPERATORS_AUX.

Module OperatorsAux (Import Ops : OPERATORS) <: OPERATORS_AUX Ops.
  Include OPERATORS_AUX Ops.
End OperatorsAux.

