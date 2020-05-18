From Velus Require Import Common Ident.
From Velus Require Import Operators Environment.
From Velus Require Import CoindStreams.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LTyping Lustre.LClocking Lustre.LSemantics.
From Velus Require Import Lustre.Normalization.Normalization Lustre.Normalization.Specification Lustre.Normalization.FullNorm.
From Velus Require Import Lustre.Normalization.NTyping (* Lustre.Normalization.Correctness *).
From Velus Require Import Lustre.Normalization.Idempotence.

Local Set Warnings "-masking-absolute-name".
Module Type LNORMALIZATION
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Str : COINDSTREAMS Op OpAux)
       (Import Syn : LSYNTAX Ids Op)
       (Import Typ : LTYPING Ids Op Syn)
       (Import Clo : LCLOCKING Ids Op Syn)
       (Import Lord : LORDERED Ids Op Syn)
       (Import Sem : LSEMANTICS Ids Op OpAux Syn Lord Str).
  Declare Module Norm : FULLNORM Ids Op OpAux Syn.
  (* Declare Module Export Correct : CORRECTNESS Ids Op OpAux Str Syn Typ Clo Lord Sem Norm. *)
  Declare Module Idempotence : IDEMPOTENCE Ids Op OpAux Syn Norm.
End LNORMALIZATION.

Module LNormalizationFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Str : COINDSTREAMS Op OpAux)
       (Syn : LSYNTAX Ids Op)
       (Typ : LTYPING Ids Op Syn)
       (Clo : LCLOCKING Ids Op Syn)
       (Lord : LORDERED Ids Op Syn)
       (Sem : LSEMANTICS Ids Op OpAux Syn Lord Str)
       <: LNORMALIZATION Ids Op OpAux Str Syn Typ Clo Lord Sem.
  Module Norm := FullNormFun Ids Op OpAux Syn.
  (* Module Export Correct := CorrectnessFun Ids Op OpAux Str Syn Typ Clo Lord Sem Norm. *)
  Module Idempotence := IdempotenceFun Ids Op OpAux Syn Norm.
End LNormalizationFun.
