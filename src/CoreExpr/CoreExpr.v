From Velus Require Export Operators.
From Velus Require Export Clocks.
From Velus Require Export CoreExpr.Stream.
From Velus Require Export CoreExpr.CESyntax.
From Velus Require Export CoreExpr.CEIsFree.
From Velus Require Export CoreExpr.CESemantics.
From Velus Require Export CoreExpr.CEClocking.
From Velus Require Export CoreExpr.CEClockingSemantics.
From Velus Require Export CoreExpr.CETyping.
From Velus Require Export CoreExpr.CEInterpreter.

From Velus Require Import Common.

Module Type COREEXPR
       (Ids    : IDS)
       (Op     : OPERATORS)
       (OpAux  : OPERATORS_AUX Op)
       (Str    : STREAM        Op OpAux).
  Declare Module Export Syn    : CESYNTAX                Op.
  Declare Module Export IsF    : CEISFREE            Ids Op       Syn.
  Declare Module Export Sem    : CESEMANTICS         Ids Op OpAux Syn Str.
  Declare Module Export Typ    : CETYPING            Ids Op       Syn.
  Declare Module Export Clo    : CECLOCKING          Ids Op       Syn.
  Declare Module Export CloSem : CECLOCKINGSEMANTICS Ids Op OpAux Syn Str Sem     Clo.
  Declare Module Export Interp : CEINTERPRETER       Ids Op OpAux Syn Str Sem Typ Clo IsF.
End COREEXPR.

Module CoreExprFun
       (Ids    : IDS)
       (Op     : OPERATORS)
       (OpAux  : OPERATORS_AUX Op)
       (Str    : STREAM        Op OpAux)
<: COREEXPR Ids Op OpAux Str.
  Module Export Syn    := CESyntaxFun                Op.
  Module Export IsF    := CEIsFreeFun            Ids Op       Syn.
  Module Export Sem    := CESemanticsFun         Ids Op OpAux Syn Str.
  Module Export Typ    := CETypingFun            Ids Op       Syn.
  Module Export Clo    := CEClockingFun          Ids Op       Syn.
  Module Export CloSem := CEClockingSemanticsFun Ids Op OpAux Syn Str Sem     Clo.
  Module Export Interp := CEInterpreterFun       Ids Op OpAux Syn Str Sem Typ Clo IsF.
End CoreExprFun.
