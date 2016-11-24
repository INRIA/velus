Require Import Operators.
Require Export NLustre.Stream.
Require Export NLustre.Syntax.
Require Export NLustre.IsFree.
Require Export NLustre.IsVariable.
Require Export NLustre.IsDefined.
Require Export NLustre.Memories.
Require Export NLustre.Semantics.
Require Export NLustre.MemSemantics.
Require Export NLustre.WellFormed.
Require Export NLustre.Ordered.
Require Export NLustre.NoDup.
Require Export NLustre.Clocking.
Require Export NLustre.Typing.

Require Import Velus.Common.
Require Import NLustre.IsVariable.Decide.
Require Import NLustre.IsDefined.Decide.
Require Import NLustre.WellFormed.Decide.
Require Import NLustre.IsFree.Decide.
Require Export NLustre.Clocking.Parents.
Require Export NLustre.Clocking.Properties.

Module Type NLUSTRE
       (Ids : IDS)
       (Op  : OPERATORS)
       (OpAux: OPERATORS_AUX Op).
  Declare Module Export Syn: SYNTAX Ids Op.
  Declare Module Export Str: STREAM Op.
  Declare Module Export Ord: ORDERED Ids Op Syn.
  Declare Module Export IsF: ISFREE Ids Op Syn.
  Declare Module Export IsFDec: IsFree.Decide.DECIDE Ids Op Syn IsF.
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
  Declare Module Export IsWFDec: WellFormed.Decide.DECIDE Ids Op Syn IsF IsFDec
                                     Ord Mem IsD IsV IsDDec IsVDec NoD WeF.
  Declare Module Export Clo: CLOCKING Ids Op Syn.
  Declare Module Export Par: PARENTS Ids Op Syn Clo.
  Declare Module Export Pro: PROPERTIES Ids Op Syn IsF Clo Mem IsD Par.
End NLUSTRE.

Module NLustreFun
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       <: NLUSTRE Ids Op OpAux.
  Module Export Syn := SyntaxFun Ids Op.
  Module Export Str := StreamFun Op.
  Module Export Ord := OrderedFun Ids Op Syn.
  Module Export IsF := IsFreeFun Ids Op Syn.
  Module Export IsFDec := IsFree.Decide.DecideFun Ids Op Syn IsF.
  Module Export Sem := SemanticsFun Ids Op OpAux Syn Str Ord.
  Module Export Typ := TypingFun Ids Op Syn.
  Module Export Mem := MemoriesFun Ids Op Syn.
  Module Export IsD := IsDefinedFun Ids Op Syn Mem.
  Module Export IsV := IsVariableFun Ids Op Syn Mem IsD.
  Module Export NoD := NoDupFun Ids Op Syn Mem IsD IsV.
  Module Export WeF := WellFormedFun Ids Op Syn IsF Ord Mem IsD IsV NoD.
  Module Export MemSem := MemSemanticsFun Ids Op OpAux Syn Str Ord Mem IsF IsD Sem IsV NoD WeF.     
  Module Export IsVDec := IsVariable.Decide.DecideFun Ids Op Syn Mem IsD IsV.
  Module Export IsDDec := IsDefined.Decide.DecideFun Ids Op Syn Mem IsD.
  Module Export IsWFDec := WellFormed.Decide.DecideFun Ids Op Syn IsF IsFDec Ord
                                             Mem IsD IsV IsDDec IsVDec NoD WeF.
  Module Export Clo := ClockingFun Ids Op Syn.
  Module Export Par := ParentsFun Ids Op Syn Clo.
  Module Export Pro := PropertiesFun Ids Op Syn IsF Clo Mem IsD Par.
End NLustreFun.

