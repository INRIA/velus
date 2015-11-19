Require Import Rustre.Common.
Require Import PArith.
Import List.ListNotations.
Open Scope list_scope.
Open Scope positive.

Require Import Rustre.Dataflow.Example.
Require Import Rustre.Minimp.Syntax.
Require Import Rustre.Translation.

(**

  Define and translate a simple node. 

 *)


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
