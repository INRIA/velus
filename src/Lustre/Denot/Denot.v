From Velus Require Import Lustre.LSyntax.
From Velus Require Import Lustre.LTyping.
From Velus Require Import Lustre.LClocking.
From Velus Require Import Lustre.LOrdered.
From Velus Require Import Lustre.LCausality.
From Velus Require Import Lustre.LSemantics.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Common Operators Clocks CoindStreams.

From Velus Require Export Lustre.Denot.Restr.
From Velus Require Export Lustre.Denot.CheckOp.
From Velus Require Export Lustre.Denot.SD.
From Velus Require Export Lustre.Denot.InftyProof.
From Velus Require Export Lustre.Denot.OpErr.
From Velus Require Export Lustre.Denot.Safe.
From Velus Require Export Lustre.Denot.Abs.
From Velus Require Export Lustre.Denot.Lp.
From Velus Require Export Lustre.Denot.SDtoRel.
(* FIMXE: ResetLs is not part of the functor *)
From Velus Require Export Lustre.Denot.ResetLs.

(** We put Restr and CheckOp in separate modules for extraction, we don't want
    to extract the CPO library, which causes compilation error (DS_bot). *)

Module Type LDENOT
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS        Ids Op OpAux)
       (Senv  : STATICENV     Ids Op OpAux Cks)
       (Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
       (Typ   : LTYPING       Ids Op OpAux Cks Senv Syn)
       (Cl    : LCLOCKING     Ids Op OpAux Cks Senv Syn)
       (Caus  : LCAUSALITY    Ids Op OpAux Cks Senv Syn)
       (Lord  : LORDERED      Ids Op OpAux Cks Senv Syn)
       (Str   : COINDSTREAMS  Ids Op OpAux Cks)
       (Sem   : LSEMANTICS    Ids Op OpAux Cks Senv Syn Lord Str)
       (Restr : LRESTR        Ids Op OpAux Cks Senv Syn)
       (CheckOp  : CHECKOP    Ids Op OpAux Cks Senv Syn).

    Declare Module Export Sd    : SD         Ids Op OpAux Cks Senv Syn Lord.
    Declare Module Export Inf   : LDENOTINF  Ids Op OpAux Cks Senv Syn Typ Caus Lord Restr Sd.
    Declare Module Export OpErr : OP_ERR        Ids Op OpAux Cks Senv Syn Typ Restr Lord Sd CheckOp.
    Declare Module Export Safe  : LDENOTSAFE Ids Op OpAux Cks Senv Syn Typ Restr Cl Lord Sd CheckOp OpErr.
    Declare Module Export Abs   : ABS_INDEP  Ids Op OpAux Cks Senv Syn Typ Lord Sd.
    Declare Module Export Lp    : LP         Ids Op OpAux Cks Senv Syn Typ Lord Sd.
    Declare Module Export SdR   : SDTOREL Ids Op OpAux Cks Senv Syn Typ Cl Caus Lord Str Sem Sd Restr Inf CheckOp OpErr Safe Abs Lp.

End LDENOT.

Module LdenotFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS        Ids Op OpAux)
       (Senv  : STATICENV     Ids Op OpAux Cks)
       (Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
       (Typ   : LTYPING       Ids Op OpAux Cks Senv Syn)
       (Cl    : LCLOCKING     Ids Op OpAux Cks Senv Syn)
       (Caus  : LCAUSALITY    Ids Op OpAux Cks Senv Syn)
       (Lord  : LORDERED      Ids Op OpAux Cks Senv Syn)
       (Str   : COINDSTREAMS  Ids Op OpAux Cks)
       (Sem   : LSEMANTICS Ids Op OpAux Cks Senv Syn Lord Str)
       (Restr : LRESTR        Ids Op OpAux Cks Senv Syn)
       (CheckOp  : CHECKOP    Ids Op OpAux Cks Senv Syn)
<: LDENOT Ids Op OpAux Cks Senv Syn Typ Cl Caus Lord Str Sem Restr CheckOp.
  Module Export Sd := SdFun Ids Op OpAux Cks Senv Syn Lord.
  Module Export Inf := LDenotInfFun Ids Op OpAux Cks Senv Syn Typ Caus Lord Restr Sd.
  Module Export OpErr := OpErrFun Ids Op OpAux Cks Senv Syn Typ Restr Lord Sd CheckOp.
  Module Export Safe := LdenotsafeFun Ids Op OpAux Cks Senv Syn Typ Restr Cl Lord Sd CheckOp OpErr.
  Module Export Abs := AbsIndepFun Ids Op OpAux Cks Senv Syn Typ Lord Sd.
  Module Export Lp := LpFun Ids Op OpAux Cks Senv Syn Typ Lord Sd.
  Module Export SdR := SdtorelFun Ids Op OpAux Cks Senv Syn Typ Cl Caus Lord Str Sem Sd Restr Inf CheckOp OpErr Safe Abs Lp.
End LdenotFun.
