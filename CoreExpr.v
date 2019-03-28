Require Export Operators.
Require Export Clocks.
Require Export CoreExpr.Stream.
Require Export CoreExpr.CESyntax.
Require Export CoreExpr.CEIsFree.
Require Export CoreExpr.CESemantics.
Require Export CoreExpr.CEClocking.
Require Export CoreExpr.CETyping.

Require Import Velus.Common.

Module Type COREEXPR
       (Ids    : IDS)
       (Op     : OPERATORS)
       (OpAux  : OPERATORS_AUX Op)
       (Clks   : CLOCKS Ids)
       (Str    : STREAM        Op OpAux).

  Declare Module Export Syn : CESYNTAX        Op.
  Declare Module Export IsF : CEISFREE    Ids Op       Clks Syn.
  Declare Module Export Sem : CESEMANTICS Ids Op OpAux Clks Syn Str.
  Declare Module Export Typ : CETYPING    Ids Op       Clks Syn.
  Declare Module Export Clo : CECLOCKING  Ids Op       Clks Syn.

End COREEXPR.

Module CoreExprFun
       (Ids    : IDS)
       (Op     : OPERATORS)
       (OpAux  : OPERATORS_AUX Op)
       (Clks   : CLOCKS Ids)
       (Str    : STREAM        Op OpAux)
<: COREEXPR Ids Op OpAux Clks Str.
  Module Export Syn := CESyntaxFun        Op.
  Module Export IsF := CEIsFreeFun    Ids Op       Clks Syn.
  Module Export Sem := CESemanticsFun Ids Op OpAux Clks Syn Str.
  Module Export Typ := CETypingFun    Ids Op       Clks Syn.
  Module Export Clo := CEClockingFun  Ids Op       Clks Syn.
End CoreExprFun.
