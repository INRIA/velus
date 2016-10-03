Require Import Operators.
Require Export Dataflow.Stream.
Require Export Dataflow.Syntax.
Require Export Dataflow.IsFree.
Require Export Dataflow.IsVariable.
Require Export Dataflow.IsDefined.
Require Export Dataflow.Memories.
Require Export Dataflow.Semantics.
Require Export Dataflow.MemSemantics.
Require Export Dataflow.WellFormed.
Require Export Dataflow.Ordered.
Require Export Dataflow.NoDup.
Require Export Dataflow.Clocking.
Require Export Dataflow.Typing.

Require Import Rustre.Common.
Require Import Dataflow.IsVariable.Decide.
Require Import Dataflow.IsDefined.Decide.
Require Export Dataflow.Clocking.Parents.
Require Export Dataflow.Clocking.Properties.

Module Type DATAFLOW
       (Ids : IDS)
       (Op  : OPERATORS)
       (OpAux: OPERATORS_AUX Op).
  Declare Module Export Syn: SYNTAX Ids Op.
  Declare Module Export Str: STREAM Op.
  Declare Module Export Ord: ORDERED Ids Op Syn.
  Declare Module Export IsF: ISFREE Ids Op Syn.
  Declare Module Export Sem: SEMANTICS Ids Op OpAux Syn Str Ord.
  Declare Module Export Typ: TYPING Ids Op Syn.
  Declare Module Export Mem: MEMORIES Ids Op Syn.
  Declare Module Export IsD: ISDEFINED Ids Op Syn Mem.
  Declare Module Export IsV: ISVARIABLE Ids Op Syn Mem IsD.
  Declare Module Export NoD: NODUP Ids Op Syn Mem IsD IsV.
  Declare Module Export WeF: WELLFORMED Ids Op Syn IsF Ord Mem IsD IsV NoD.
  Declare Module Export MemSem: MEMSEMANTICS Ids Op OpAux Syn Str Ord Mem IsF IsD Sem IsV NoD WeF.     
  Declare Module Export IsVDec: IsVariable.Decide.DECIDE Ids Op Syn Mem IsD IsV.
  Declare Module Export IsDDec: IsDefined.Decide.DECIDE Ids Op Syn Mem IsD.
  Declare Module Export Clo: CLOCKING Ids Op Syn.
  Declare Module Export Par: PARENTS Ids Op Syn Clo.
  Declare Module Export Pro: PROPERTIES Ids Op Syn IsF Clo Mem IsD Par.
End DATAFLOW.

