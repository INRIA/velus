Require Import Operators.
Require Import Clocks.
Require Export NLustre.Stream.
Require Export NLustre.NLSyntax.
Require Export NLustre.IsFree.
Require Export NLustre.IsVariable.
Require Export NLustre.IsDefined.
Require Export NLustre.Memories.
Require Export NLustre.NLSemantics.
Require Export NLustre.MemSemantics.
Require Export NLustre.WellFormed.
Require Export NLustre.Ordered.
Require Export NLustre.NoDup.
Require Export NLustre.Clocking.
Require Export NLustre.NLTyping.

Require Import Velus.Common.

Module Type NLUSTRE
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Clks  : CLOCKS Ids).
  Declare Module Export Syn: NLSYNTAX Ids Op Clks.
  Declare Module Export Str: STREAM Op.
  Declare Module Export Ord: ORDERED Ids Op Clks Syn.
  Declare Module Export IsF: ISFREE Ids Op Clks Syn.
  Declare Module Export Sem: NLSEMANTICS Ids Op OpAux Clks Syn Str Ord.
  Declare Module Export Typ: NLTYPING Ids Op Clks Syn.
  Declare Module Export Mem: MEMORIES Ids Op Clks Syn.
  Declare Module Export IsD: ISDEFINED Ids Op Clks Syn Mem.
  Declare Module Export IsV: ISVARIABLE Ids Op Clks Syn Mem IsD.
  Declare Module Export NoD: NODUP Ids Op Clks Syn Mem IsD IsV.
  Declare Module Export WeF: WELLFORMED Ids Op Clks Syn IsF Ord Mem IsD IsV NoD.
  Declare Module Export MemSem: MEMSEMANTICS Ids Op OpAux Clks Syn Str Ord Mem
                                    IsF IsD Sem IsV NoD WeF.     
  Declare Module Export Clo: CLOCKING Ids Op Clks Syn IsF Mem IsD.
End NLUSTRE.

Module NLustreFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Clks  : CLOCKS Ids)
       <: NLUSTRE Ids Op OpAux Clks.
  Module Export Syn := NLSyntaxFun    Ids Op Clks.
  Module Export Str := StreamFun          Op.
  Module Export Ord := OrderedFun     Ids Op Clks Syn.
  Module Export IsF := IsFreeFun      Ids Op Clks Syn.
  Module Export Sem := NLSemanticsFun Ids Op OpAux Clks Syn Str Ord.
  Module Export Typ := NLTypingFun    Ids Op Clks Syn.
  Module Export Mem := MemoriesFun    Ids Op Clks Syn.
  Module Export IsD := IsDefinedFun   Ids Op Clks Syn Mem.
  Module Export IsV := IsVariableFun  Ids Op Clks Syn Mem IsD.
  Module Export NoD := NoDupFun       Ids Op Clks Syn Mem IsD IsV.
  Module Export WeF := WellFormedFun  Ids Op Clks Syn IsF Ord Mem IsD IsV NoD.
  Module Export MemSem := MemSemanticsFun Ids Op OpAux Clks Syn Str Ord Mem IsF
                            IsD Sem IsV NoD WeF.     
  Module Export Clo := ClockingFun    Ids Op Clks Syn IsF Mem IsD.
End NLustreFun.

