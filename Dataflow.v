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

Require Import Rustre.Common.
Require Import Dataflow.IsVariable.Decide.
Require Import Dataflow.IsDefined.Decide.
Require Export Dataflow.Clocking.Parents.
Require Export Dataflow.Clocking.Properties.

Module Type DATAFLOW (Op: OPERATORS) (OpAux: OPERATORS_AUX Op).
  Declare Module Export Syn: SYNTAX Op.
  Declare Module Export Str: STREAM Op.
  Declare Module Export Ord: ORDERED Op Syn.
  Declare Module Export IsF: ISFREE Op Syn.
  Declare Module Export Sem: SEMANTICS Op OpAux Syn Str Ord.
  Declare Module Export Mem: MEMORIES Op Syn.
  Declare Module Export IsD: ISDEFINED Op Syn Mem.
  Declare Module Export IsV: ISVARIABLE Op Syn Mem IsD.
  Declare Module Export NoD: NODUP Op Syn Mem IsD IsV.
  Declare Module Export WeF: WELLFORMED Op Syn IsF Ord Mem IsD IsV NoD.
  Declare Module Export MemSem: MEMSEMANTICS Op OpAux Syn Str Ord Mem IsF IsD Sem IsV NoD WeF.     
  Declare Module Export IsVDec: IsVariable.Decide.DECIDE Op Syn Mem IsD IsV.
  Declare Module Export IsDDec: IsDefined.Decide.DECIDE Op Syn Mem IsD.
  Declare Module Export Clo: CLOCKING Op Syn.
  Declare Module Export Par: PARENTS Op Syn Clo.
  Declare Module Export Pro: PROPERTIES Op Syn IsF Clo Mem IsD Par.
End DATAFLOW.