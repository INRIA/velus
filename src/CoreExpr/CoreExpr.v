Require Export Operators.
Require Export Clocks.
Require Export CoreExpr.Stream.
Require Export CoreExpr.CESyntax.
Require Export CoreExpr.CEIsFree.
Require Export CoreExpr.CESemantics.
Require Export CoreExpr.CEClocking.
Require Export CoreExpr.CEClockingSemantics.
Require Export CoreExpr.CETyping.
Require Export CoreExpr.CEInterpreter.

Require Import Velus.Common.Common.

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
  Declare Module Export CloSem : CECLOCKINGSEMANTICS Ids Op OpAux Syn Str Sem Clo.
  Declare Module Export Interp : CEINTERPRETER       Ids Op OpAux Syn Str Sem.
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
  Module Export CloSem := CEClockingSemanticsFun Ids Op OpAux Syn Str Sem Clo.
  Module Export Interp := CEInterpreterFun       Ids Op OpAux Syn Str Sem.
End CoreExprFun.
