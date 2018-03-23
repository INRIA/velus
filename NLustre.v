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
Require Export NLustre.NLClocking.
Require Export NLustre.NLTyping.
Require Export NLustre.NLSchedule.

Require Import Velus.Common.

Module Type NLUSTRE
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Clks  : CLOCKS Ids).
  Declare Module Export Syn: NLSYNTAX        Ids Op       Clks.
  Declare Module Export Str: STREAM              Op OpAux.
  Declare Module Export Ord: ORDERED         Ids Op       Clks Syn.
  Declare Module Export IsF: ISFREE          Ids Op       Clks Syn.
  Declare Module Export Sem: NLSEMANTICS     Ids Op OpAux Clks Syn Str Ord.
  Declare Module Export Typ: NLTYPING        Ids Op       Clks Syn.
  Declare Module Export Mem: MEMORIES        Ids Op       Clks Syn.
  Declare Module Export IsD: ISDEFINED       Ids Op       Clks Syn             Mem.
  Declare Module Export IsV: ISVARIABLE      Ids Op       Clks Syn             Mem IsD.
  Declare Module Export NoD: NODUP           Ids Op       Clks Syn             Mem IsD IsV.
  Declare Module Export WeF: WELLFORMED      Ids Op       Clks Syn     Ord     Mem IsD IsV IsF NoD.
  Declare Module Export MemSem: MEMSEMANTICS Ids Op OpAux Clks Syn Str Ord Sem Mem IsD IsV IsF NoD WeF.
  Declare Module Export Clo: NLCLOCKING      Ids Op       Clks Syn             Mem IsD     IsF.

  Declare Module Scheduler: NLSCHEDULE       Ids Op OpAux Clks Syn Str Ord Sem Mem IsD     IsF          Typ Clo.

End NLUSTRE.

Module NLustreFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Clks  : CLOCKS Ids)
       <: NLUSTRE Ids Op OpAux Clks.
  Module Export Syn := NLSyntaxFun        Ids Op       Clks.
  Module Export Str := StreamFun              Op OpAux.
  Module Export Ord := OrderedFun         Ids Op       Clks Syn.
  Module Export IsF := IsFreeFun          Ids Op       Clks Syn.
  Module Export Sem := NLSemanticsFun     Ids Op OpAux Clks Syn Str Ord.
  Module Export Typ := NLTypingFun        Ids Op       Clks Syn.
  Module Export Mem := MemoriesFun        Ids Op       Clks Syn.
  Module Export IsD := IsDefinedFun       Ids Op       Clks Syn             Mem.
  Module Export IsV := IsVariableFun      Ids Op       Clks Syn             Mem IsD.
  Module Export NoD := NoDupFun           Ids Op       Clks Syn             Mem IsD IsV.
  Module Export WeF := WellFormedFun      Ids Op       Clks Syn     Ord     Mem IsD IsV IsF NoD.
  Module Export MemSem := MemSemanticsFun Ids Op OpAux Clks Syn Str Ord Sem Mem IsD IsV IsF NoD WeF.
  Module Export Clo := NLClockingFun      Ids Op       Clks Syn             Mem IsD     IsF.

  Module Scheduler := NLScheduleFun       Ids Op OpAux Clks Syn Str Ord Sem Mem IsD IsF              Typ Clo.

End NLustreFun.
