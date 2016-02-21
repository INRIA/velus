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

Require Import Rustre.Dataflow.Memories.
Require Import Rustre.Dataflow.WellFormed.
Require Import Rustre.Dataflow.WellFormed.Decide.

(* Common notations *)
Class Assignment T U V := {assign : ident -> T -> U -> V}.
Notation "x '::=' y" := (assign x _ y) (at level 47, no associativity).
Class OpCall T U := {opcall : operator -> T -> U}.
Notation "f '<' nel '>'" := (opcall f nel) (at level 46, format "f '<' nel '>'").
Notation "x , y" := (necons x y) (at level 30, right associativity).
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
Coercion Var : ident >-> exp.
Coercion State : ident >-> exp.
Coercion Const : const >-> exp.

Instance Assign_Assign : Assignment unit exp stmt := {assign := fun x (_ : unit) => Assign x}.
Instance AssignSt_Assign : Assignment unit exp stmt := {assign := fun x (_ : unit) => AssignSt x}.
Instance Op_OpCall : OpCall (nelist exp) exp := {opcall := Op}.
Notation "stmt1 ;; stmt2" := (Comp stmt1 stmt2) (at level 48, right associativity).
Notation "'If' b 'Then' t 'Else' f" := (Ifte b t f) (at level 47, t at level 47, f at level 47).
Notation "x '::=' class '(' obj ').step(' args ')'" := (Step_ap x class obj args) (at level 47).
Notation " class '(' obj ').reset()'" := (Reset_ap class obj) (at level 47).

(* TODO: not properly clocked... *)
Example eqns1 : list equation :=
  [
    EqFby 3 (Con Cbase 1 false) (Cint 0) (Evar 2);
    assign 4 Cbase (Emerge 1 (Eexp (Evar 2)) (Eexp (Evar 3)));
    assign 2 (Con Cbase 1 true) (Eexp (Ewhen (Econst (Cint 7)) 1 true))
            
(*   ;EqDef 1 (CAexp Cbase (Eexp (Econst (Cbool true)))) *)
  ].
Print eqns1.

Example node1 : node :=
  mk_node 1 (nebase 1) 4 eqns1.


Example eqns2 : list equation :=
  [
    EqFby 3 Cbase (Cint 0) (Evar 2);
    EqApp 4 Cbase 1 (nebase (Evar 3));
    EqApp 2 Cbase 1 (nebase (Evar 1))
  ].
Print eqns2.

Example node2 : node :=
  mk_node 2 (nebase 1) 4 eqns2.

(** Scheduling *)

Example eqn1_well_sch: Is_well_sch (memories eqns1) (1§) eqns1.
Proof.
  assert (well_sch (memories eqns1) (1§) eqns1 = true) as HW by apply eq_refl.
  pose proof (well_sch_spec (memories eqns1) (1§) eqns1) as HS.
  rewrite HW in HS.
  assumption.
Qed.

Example eqn2_well_sch: Is_well_sch (memories eqns2) (1§) eqns2.
Proof.
  assert (well_sch (memories eqns2) (1§) eqns2 = true) as HW by apply eq_refl.
  pose proof (well_sch_spec (memories eqns2) (1§) eqns2) as HS.
  rewrite HW in HS.
  assumption.
Qed.

(** Translation *)

(* Eval cbv in (translate_node node1). *)

Example prog1 : stmt :=
  Comp (Ifte (Var 1) (Assign 2 (Const (Cint 7))) Skip)
       (Comp (Ifte (Var 1) (Assign 4 (Var 2))
                   (Assign 4 (State 3)))
             (Comp (Ifte (Var 1) Skip (AssignSt 3 (Var 2)))
                   Skip)).
Print prog1.
(* If 1 Then Assign 2 7%Z Else Skip;;
   If 1 Then Assign 4 2 Else Assign 4 3;;
   If 1 Then Skip Else AssignSt 3 2;; Skip *)

Remark prog1_good : (translate_node node1).(c_step) = prog1.
Proof eq_refl.

Example reset1 : stmt :=
  translate_reset_eqns eqns1.

(* Eval cbv in (translate_node node2). *)

Example class2 : class :=
  {|
    c_name := 2;
    c_input := nebase 1;
    c_output := 4;
    c_mems := [3];
    c_objs := [{| obj_inst := 2; obj_class := 1 |};
                {| obj_inst := 4; obj_class := 1 |}];
    c_step := Comp (Step_ap 2 1 2 (nebase (Var 1)))
                   (Comp (Step_ap 4 1 4 (nebase (State 3)))
                         (Comp (AssignSt 3 (Var 2))
                               Skip));
    c_reset := Comp (Reset_ap 1 2)
                    (Comp (Reset_ap 1 4)
                          (Comp (AssignSt 3 (Const (Cint 0)))
                                Skip))
  |}.
Print class2.

Remark prog2_good : translate_node node2 = class2.
Proof eq_refl.

(** Optimization *)

Require Import Rustre.Minimp.FuseIfte.

Example prog1' : stmt :=
  Ifte (Var 1)
       (Comp (Assign 2 (Const (Cint 7)))
             (Assign 4 (Var 2)))
       (Comp (Assign 4 (State 3))
             (AssignSt 3 (Var 2))).
Print prog1'.
(* If 1 Then (Assign 2 7%Z;; Assign 4 2) Else (Assign 4 3;; AssignSt 3 2) *)

Remark prog1'_is_fused: (ifte_fuse prog1 = prog1').
Proof eq_refl.

(* TODO: Show correctness of prog1' *)

(** Examples from paper *)

Section CodegenPaper.

  Require Import Nelist.


  Definition Plus : operator := existT arrows (Tcons Tint (Tcons Tint (Tout Tint))) BinInt.Z.add.
  Definition op_plus (x: lexp) (y: lexp) : lexp := Eop Plus (necons x (nebase y)).
  Notation "x ':+' y" := (op_plus x y) (at level 47).

  Definition Ifte_int : operator :=
    existT arrows (Tcons Tbool (Tcons Tint (Tcons Tint (Tout Tint))))
             (fun (x : bool) t f => if x then t else f).
  Definition op_ifte (x: lexp) (t: lexp) (f: lexp) : lexp :=
    Eop Ifte_int (necons x (necons t (nebase f))).




  (* Node names *)
  Definition n_counter     : ident := 1.
  Definition n_altcounters : ident := n_counter + 1.

(*
  node counter (initial, increment: int; restart: bool) returns (n: int)
  var c: int;
  let
    n = if restart then initial else c + increment;
    c = 0 fby n;
  tel

 *)

  (* counter: variable names *)
  Definition initial   : ident := 1.
  Definition increment : ident := 2.
  Definition restart   : ident := 3.
  Definition n         : ident := 4.
  Definition c         : ident := 5.

  Example counter_eqns : list equation :=
    [
      EqFby c Cbase (Cint 0) (Evar n);
      EqDef n Cbase (Eexp (op_ifte (Evar restart)
                                   (Evar initial)
                                   (op_plus (Evar c) (Econst (Cint 1)))))
    ].
  Print counter_eqns.
  (* TODO: show that these equations Is_well_sch and Well_clocked;
           need multiple inputs *)

  Lemma counter_eqns_well_sch : Is_well_sch (PS.singleton c) (initial, increment, restart§) counter_eqns.
  Proof.
  unfold counter_eqns. constructor. constructor. constructor.
  - intros i Hi. split.
    + intros _ Habs. inversion Habs.
    + intros Hic. right. inv Hi; inv H. inv H2. inv H1; inv H0.
      * do 2 constructor 2. constructor.
      * inv H1. now constructor.
      * inv H1. inv H0. inv H2.
        { inv H0. elim Hic. PSdec.fsetdec. }
        { inv H0. inv H1. }
  - intro Habs. inv Habs.
  - intros i Hi. split.
    + intros Hic Habs. inv Habs.
      * inv H0. inv Hic.
      * inv H0.
    + intro Hic. inv Hi; inv H. left. do 2 constructor.
  - intro Habs. inv Habs; inv H0.
  Qed.

  (* TODO: multiple inputs: initial, increment, restart -> LR: done? *)
  Example counter : node :=
    mk_node n_counter (necons initial (necons increment (nebase restart))) n counter_eqns.

  Eval cbv in translate_node counter.
  Eval cbv in ifte_fuse (c_step (translate_node counter)).
  Eval cbv in ifte_fuse (c_reset (translate_node counter)).


(*
  node altcounters (b: bool) returns (y: int)
  var n1, n2: int;
  let
    n1 = counter(0, 1, false);
    n2 = counter(0 whenot b, −1 whenot b, false whenot b);
    y = merge b (n1 when b) n2;
  tel
*)

  (* altcounters: variable names *)
  Definition b  : ident := 1.
  Definition n1 : ident := 2.
  Definition n2 : ident := 3.
  Definition y  : ident := 4.

  Example altcounters_eqns : list equation :=
    [
      EqDef y Cbase
              (Emerge b
                      (Eexp (Ewhen (Evar n1) b true))
                      (Eexp (Evar n2)));
      EqApp n2 (Con Cbase b false) n_counter 
               (necons (Ewhen (Econst (Cint 0)) b false)
               (necons (Ewhen (Econst (Cint (-1))) b false)
               (nebase (Ewhen (Econst (Cbool false)) b false))));
      EqApp n1 Cbase n_counter (necons (Econst (Cint 1))
                               (necons (Econst (Cbool false))
                               (nebase (Econst (Cint 0)))))
    ].
  Print altcounters_eqns.

  (* TODO: show that these equations Is_well_sch and Well_clocked;
           need multiple inputs *)

  Lemma altcounters_eqns_Well_sch : Is_well_sch PS.empty (b§) altcounters_eqns.
  Proof.
  constructor. constructor. constructor. constructor.
  - intros i Hi. split.
    + intros _ Habs. inv Habs.
    + intros _. right. inv Hi; inv H; inv H1; inv H0; inv H1.
  - intro Habs. inv Habs.
  - intros i Hi. split.
    + intros Habs _. PSdec.fsetdec.
    + intros _. inv Hi; inv H; intuition.
      * inv H1; inv H2 || right; constructor.
      * inv H1; inv H0; try inv H1; try inv H2; right; constructor.
      * right; constructor.
      * inv H2.
  - intro Habs. inv Habs; inv H0.
  - intros i Hi. split.
    + intros Habs _. PSdec.fsetdec.
    + intros _. inv Hi; inv H.
      * right; constructor.
      * inv H2; inv H1; try (now right; constructor); [].
        left. constructor 2. inv H2. do 2 constructor.
      * inv H2. inv H1. repeat constructor.
  - intro Habs. inv Habs; inv H0; inv H1.
  Qed.

  Example altcounters : node :=
    mk_node n_altcounters (nebase b) y altcounters_eqns.

  Eval cbv in translate_node altcounters.
  Eval cbv in ifte_fuse (c_step (translate_node altcounters)).

End CodegenPaper.
