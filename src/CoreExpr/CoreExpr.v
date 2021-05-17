From Velus Require Export Operators.
From Velus Require Export CommonTyping.
From Velus Require Export Clocks.
From Velus Require Export IndexedStreams.
From Velus Require Export CoreExpr.CESyntax.
From Velus Require Export CoreExpr.CEIsFree.
From Velus Require Export CoreExpr.CESemantics.
From Velus Require Export CoreExpr.CEClocking.
From Velus Require Export CoreExpr.CEClockingSemantics.
From Velus Require Export CoreExpr.CETyping.
From Velus Require Export CoreExpr.CETypingSemantics.
From Velus Require Export CoreExpr.CEProperties.
From Velus Require Export CoreExpr.CEInterpreter.

From Velus Require Import Common.

Module Type COREEXPR
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX  Ids Op)
       (ComTyp: COMMONTYPING   Ids Op OpAux)
       (Cks   : CLOCKS         Ids Op OpAux)
       (Str   : INDEXEDSTREAMS Ids Op OpAux Cks).
  Declare Module Export Syn    : CESYNTAX            Ids Op OpAux Cks.
  Declare Module Export IsF    : CEISFREE            Ids Op OpAux Cks Syn.
  Declare Module Export Sem    : CESEMANTICS         Ids Op OpAux Cks Syn Str.
  Declare Module Export Typ    : CETYPING            Ids Op OpAux Cks Syn.
  Declare Module Export TypSem : CETYPINGSEMANTICS   Ids Op OpAux ComTyp Cks Syn IsF Str Sem Typ.
  Declare Module Export Clo    : CECLOCKING          Ids Op OpAux Cks Syn.
  Declare Module Export CloSem : CECLOCKINGSEMANTICS Ids Op OpAux Cks Syn Str Sem     Clo.
  Declare Module Export Props  : CEPROPERTIES        Ids Op OpAux Cks Syn Str Sem Typ        IsF.
  Declare Module Export Interp : CEINTERPRETER       Ids Op OpAux Cks Syn Str Sem.
End COREEXPR.

Module CoreExprFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX  Ids Op)
       (ComTyp: COMMONTYPING   Ids Op OpAux)
       (Cks   : CLOCKS         Ids Op OpAux)
       (Str   : INDEXEDSTREAMS Ids Op OpAux Cks)
<: COREEXPR Ids Op OpAux ComTyp Cks Str.
  Module Export Syn    := CESyntaxFun            Ids Op OpAux Cks.
  Module Export IsF    := CEIsFreeFun            Ids Op OpAux Cks Syn.
  Module Export Sem    := CESemanticsFun         Ids Op OpAux Cks Syn Str.
  Module Export Typ    := CETypingFun            Ids Op OpAux Cks Syn.
  Module Export TypSem := CETypingSemanticsFun   Ids Op OpAux ComTyp Cks Syn IsF Str Sem Typ.
  Module Export Clo    := CEClockingFun          Ids Op OpAux Cks Syn.
  Module Export CloSem := CEClockingSemanticsFun Ids Op OpAux Cks Syn Str Sem     Clo.
  Module Export Props  := CEProperties           Ids Op OpAux Cks Syn Str Sem Typ     IsF.
  Module Export Interp := CEInterpreterFun       Ids Op OpAux Cks Syn Str Sem.
End CoreExprFun.
