Require Import PArith.
Require Import List.
Import List.ListNotations.
Open Scope positive.
Open Scope list.

Require Import Rustre.Common.
Require Import Rustre.Dataflow.Syntax.

Require Import Rustre.Dataflow.Memories.
Require Import Rustre.Dataflow.WellFormed.
Require Import Rustre.Dataflow.WellFormed.Decide.

Require Import Rustre.Minimp.Syntax.
Require Import Rustre.Translation.

(* TODO: not properly clocked... *)
Example eqns1 : list equation :=
  [
    EqFby 3 (Cint 0) (LAexp (Con Cbase 1 false) (Evar 2));
    EqDef 4 (CAexp Cbase (Emerge 1 (Eexp (Evar 2))
                                   (Eexp (Evar 3))));
    EqDef 2 (CAexp (Con Cbase 1 true)
                   (Eexp (Ewhen (Econst (Cint 7)) 1 true))
            )
(*   ;EqDef 1 (CAexp Cbase (Eexp (Econst (Cbool true)))) *)
  ].

Example node1 : node :=
  mk_node 1 1 4 eqns1.


Example eqns2 : list equation :=
  [
    EqFby 3 (Cint 0) (LAexp Cbase (Evar 2));
    EqApp 4 1 (LAexp Cbase (Evar 3));
    EqApp 2 1 (LAexp Cbase (Evar 1))
  ].

Example node2 : node :=
  mk_node 2 1 4 eqns2.

(** Scheduling *)

Example eqn1_well_sch: Is_well_sch (memories eqns1) 1 eqns1.
Proof.
  assert (well_sch (memories eqns1) 1 eqns1 = true) as HW by apply eq_refl.
  pose proof (well_sch_spec (memories eqns1) 1 eqns1) as HS.
  rewrite HW in HS.
  assumption.
Qed.

Example eqn2_well_sch: Is_well_sch (memories eqns2) 1 eqns2.
Proof.
  assert (well_sch (memories eqns2) 1 eqns2 = true) as HW by apply eq_refl.
  pose proof (well_sch_spec (memories eqns2) 1 eqns2) as HS.
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

Remark prog1_good : (translate_node node1).(c_step) = prog1.
Proof eq_refl.

Example reset1 : stmt :=
  translate_reset_eqns eqns1.


(* Eval cbv in (translate_node node2). *)

Example class2 : class :=
  {|
    c_name := 2;
    c_input := 1;
    c_output := 4;
    c_mems := [3];
    c_objs := [{| obj_inst := 2; obj_class := 1 |};
                {| obj_inst := 4; obj_class := 1 |}];
    c_step := Comp (Step_ap 2 1 2 (Var 1))
                   (Comp (Step_ap 4 1 4 (State 3))
                         (Comp (AssignSt 3 (Var 2))
                               Skip));
    c_reset := Comp (Reset_ap 1 2)
                    (Comp (Reset_ap 1 4)
                          (Comp (AssignSt 3 (Const (Cint 0)))
                                Skip))
  |}.

Remark prog2_good : translate_node node2 = class2.
Proof eq_refl.

