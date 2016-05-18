Require Import PArith.
Require Import Rustre.Nelist.
Require Import List.
Import List.ListNotations.
Open Scope positive.
Open Scope list.

Require Import Rustre.Common.
Require Import Rustre.Dataflow.Syntax.
Require Import Rustre.Minimp.Syntax.
Require Import Rustre.Translation.
Require Import Rustre.Minimp.FuseIfte.

Require Import Rustre.Dataflow.Memories.
Require Import Rustre.Dataflow.WellFormed.
Require Import Rustre.Dataflow.WellFormed.Decide.

(* Common notations *)
Class Assignment T U V := {assign : ident -> T -> U -> V}.
Notation "x '::=' y" := (assign x _ y) (at level 47, no associativity).
Class OpCall T U := {opcall : operator -> T -> U}.
Notation "f '<' nel '>'" := (opcall f nel) (at level 46, format "f '<' nel '>'").
Notation "x :,: y" := (necons x y) (at level 30, right associativity).
Notation "x '§'" := (nebase x) (at level 30).

(* Dataflow notations *)
Coercion Cint : BinInt.Z >-> const.
Coercion Cbool : bool >-> const.
Coercion Evar : ident >-> lexp.
Coercion Eexp : lexp >-> cexp.
Coercion Econst : const >-> lexp.

Notation "x 'on' ck" := (Con x ck) (at level 44).
(*Notation "x 'when' C ( ck )" := (Ewhen x ck C) (at level 45, left associativity, format "x  'when'  C ( ck )").*)
Notation "x 'when' ck" := (Ewhen x ck true) (at level 45, left associativity).
Notation "x 'whenot' ck" := (Ewhen x ck false) (at level 45, left associativity).
Notation "x '::=' v 'fby' y" := (EqFby x _ v y) (at level 47).
Notation "x '::=' f '(|' nel '|)'" := (EqApp x _ f nel) (at level 47, format "x  '::='  f '(|' nel '|)'").
Instance EqDef_Assign : Assignment clock cexp equation := {assign := EqDef}.
Instance Eop_OpCall : OpCall lexps lexp := {opcall := Eop}.

(* Imperative notations *)
Coercion Const : const >-> exp.

Instance Assign_Assign : Assignment unit exp stmt := {assign := fun x (_ : unit) => Assign x}.
Instance AssignSt_Assign : Assignment unit exp stmt := {assign := fun x (_ : unit) => AssignSt x}.
Instance Op_OpCall : OpCall (nelist exp) exp := {opcall := Op}.
Notation "stmt1 ;; stmt2" := (Comp stmt1 stmt2) (at level 48, right associativity).
Notation "'If' b 'Then' t 'Else' f" := (Ifte b t f) (at level 47, t at level 47, f at level 47).
Notation "x '::=' class '(' obj ').step(' args ')'" := (Step_ap x class obj args) (at level 47).
Notation " class '(' obj ').reset()'" := (Reset_ap class obj) (at level 47).

(** Examples from paper *)

Section CodegenPaper.

  Require Import Nelist.

  Definition Plus : operator := existT arrows (Tcons Tint (Tcons Tint (Tout Tint))) BinInt.Z.add.
  Definition op_plus (x: lexp) (y: lexp) : lexp := Eop Plus (necons x (nebase y)).
  Notation "x ':+' y" := (op_plus x y) (at level 47).
  Opaque Plus.

  Definition Ifte_int : operator :=
    existT arrows (Tcons Tbool (Tcons Tint (Tcons Tint (Tout Tint))))
             (fun (x : bool) t f => if x then t else f).
  Definition op_ifte (x: lexp) (t: lexp) (f: lexp) : lexp :=
    Eop Ifte_int (necons x (necons t (nebase f))).
  Opaque Ifte_int.

  Definition Disj : operator :=
    existT arrows (Tcons Tbool (Tcons Tbool (Tout Tbool))) orb.
  Definition op_disj (x: lexp) (y: lexp) : lexp := Eop Disj (necons x (nebase y)).
  Notation "x ':||' y" := (op_disj x y) (at level 47).
  Opaque Disj.

  (* Node names *)
  Definition n_count       : ident := 1.
  Definition n_avgvelocity : ident := n_count + 1.

  (*
  node count (ini, inc: int; restart: bool) returns (n: int)
    var c: int; f: bool;
  let
    n = if f or restart then ini else c + inc;
    f = true fby false;
    c = 0 fby n;
  tel
  *)

  (* counter: variable names *)
  Definition ini       : ident := 1.
  Definition inc       : ident := 2.
  Definition restart   : ident := 3.
  Definition n         : ident := 4.
  Definition f         : ident := 5.
  Definition c         : ident := 6.

  Example count_eqns : list equation :=
    [
      EqFby c Cbase (Cint 0) (Evar n);
      EqFby f Cbase (Cbool true) (Cbool false);
      EqDef n Cbase (Eexp (op_ifte (op_disj (Evar f) (Evar restart))
                                   (Evar ini)
                                   (op_plus (Evar c) (Evar inc))))
    ].
  (* Print count_eqns. *)

  Definition Div : operator := existT arrows (Tcons Tint (Tcons Tint (Tout Tint))) BinInt.Z.div.
  Definition op_div (x: lexp) (y: lexp) : lexp := Eop Div (necons x (nebase y)).
  Notation "x ':/' y" := (op_div x y) (at level 49).
  Opaque Div.

  Lemma count_eqns_well_sch :
    Is_well_sch (PS.add f (PS.singleton c))
                (ini :,: inc :,: restart§) count_eqns.
  Proof. apply Is_well_sch_by_refl; reflexivity. Qed.

  Example count : node :=
    mk_node n_count (necons ini (necons inc (nebase restart))) n count_eqns.

  Example count_prog :=
    {|
      c_name := n_count;
      c_input := ini :,: inc :,: restart §;
      c_output := n;
      c_mems := [f; c];
      c_objs := [];
      c_step := Assign n
                  (Op Ifte_int
                      (Op Disj (State f :,: Var restart §)
                          :,: Var ini :,: Op Plus (State c :,: Var inc §) §));;
                AssignSt f false;;
                AssignSt c (Var n);;
                Skip;
      c_reset := AssignSt f true;;
                 AssignSt c 0%Z;;
                 Skip
    |}.

  Remark count_prog_good: translate_node count = count_prog.
  Proof eq_refl.

  Remark count_prog_step_fuse:
    fuse (c_step count_prog) =
         Assign n (Op Ifte_int
                      (Op Disj (State f :,: Var restart §) :,: Var ini
                          :,: Op Plus (State c :,: Var inc §) §));;
         AssignSt f false;;
         AssignSt c (Var n).
  Proof eq_refl.

  Remark count_prog_reset_fuse:
    fuse (c_reset count_prog) = AssignSt f true;; AssignSt c 0%Z.
  Proof eq_refl.

(*
  node avgvelocity (delta: int; sec: bool) returns (v: int)
    var r, t, h: int;
  let
    r = count(0, delta, false);
    t = count(1 when sec, 1 when sec, false when sec);
    v = merge sec ((r when sec) / t) (h whenot sec);
    h = 0 fby v;
  tel
*)

  (* avgvelocity: variable names *)
  Definition delta  : ident := 1.
  Definition sec    : ident := 2.
  Definition r      : ident := 3.
  Definition t      : ident := 4.
  Definition v      : ident := 5.
  Definition h      : ident := 6.

  Example avgvelocity_eqns : list equation :=
    [
      EqFby h Cbase (Cint 0) (Evar v);
      EqDef v Cbase
              (Emerge sec
                      (Eexp (op_div (Ewhen (Evar r) sec true) (Evar t)))
                      (Eexp (Ewhen (Evar h) sec false)));
      EqApp t (Con Cbase sec true) n_count
                  (necons (Ewhen (Econst (Cint 1)) sec true)
                  (necons (Ewhen (Econst (Cint 1)) sec true)
                  (nebase (Ewhen (Econst (Cbool false)) sec true))));
      EqApp r Cbase n_count (necons (Econst (Cint 0))
                            (necons (Evar delta)
                            (nebase (Econst (Cbool false)))))
    ].
  (* Print avgvelocity_eqns. *)

  Lemma avgvelocity_eqns_Well_sch :
    Is_well_sch (PS.singleton h) (delta :,: sec§) avgvelocity_eqns.
  Proof. apply Is_well_sch_by_refl; reflexivity. Qed.

  Example avgvelocity : node :=
    mk_node n_avgvelocity (delta :,: sec§) v avgvelocity_eqns.

  Example avgvelocity_prog :=
    {|
      c_name := n_avgvelocity;
      c_input := delta :,: sec §;
      c_output := v;
      c_mems := [h];
      c_objs := [{| obj_inst := r; obj_class := n_count |};
                 {| obj_inst := t; obj_class := n_count |}];
      c_step := Step_ap r n_count r ((Const 0%Z) :,: Var delta :,: (Const false) §);;
                Ifte (Var sec)
                     (Step_ap t n_count t ((Const 1%Z) :,: (Const 1%Z) :,: (Const false) §))
                Skip;;
                Ifte (Var sec)
                     (Assign v (Op Div (Var r :,: Var t §)))
                     (Assign v (State h));;
                AssignSt h (Var v);;
                Skip;
      c_reset := Reset_ap n_count r;;
                 Reset_ap n_count t;;
                 AssignSt h 0%Z;;
                 Skip
    |}.

  Remark avgvelocity_prog_good: translate_node avgvelocity = avgvelocity_prog.
  Proof eq_refl.

  Remark avgvelocity_prog_step_fuse:
    fuse (c_step avgvelocity_prog) =
         Step_ap r n_count r ((Const 0%Z) :,: Var delta :,: (Const false) §);;
         Ifte (Var sec)
              (Step_ap t n_count t ((Const 1%Z) :,: (Const 1%Z) :,: (Const false) §);;
               Assign v (Op Div (Var r :,: Var t §)))
              (Assign v (State h));;
         AssignSt h (Var v).
  Proof eq_refl.

  Remark avgvelocity_prog_reset_fuse:
    fuse (c_reset avgvelocity_prog) = Reset_ap n_count r;;
                                      Reset_ap n_count t;;
                                      AssignSt h 0%Z.
  Proof eq_refl.

End CodegenPaper.

