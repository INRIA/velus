Require Import PArith.
Require Import List.
Import List.ListNotations.
Open Scope positive.
Open Scope list.

Require Import Rustre.Common.
Require Import Rustre.Dataflow.Syntax.

Example eqns1 : list equation :=
  [
    EqFby 3 (Cint 0) (LAexp (Con Cbase 1 false) (Evar 2));
    EqDef 4 (CAexp Cbase (Emerge 1 (Eexp (Evar 2))
                                   (Eexp (Evar 3))));
    EqDef 2 (CAexp (Con Cbase 1 true) (Eexp (Econst (Cint 7))))
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
