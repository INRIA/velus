From Velus Require Import Common Ident.
From Velus Require Import Operators Environment.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Import Lustre.Lustre.
From Velus Require Import CoreExpr.CoreExpr.
From Velus Require Import NLustre.NLustre.
From Velus Require Import Transcription.Tr.
From Velus Require Import Transcription.TrTyping Transcription.TrClocking Transcription.Correctness.
From Velus Require Import Transcription.Completeness.

Local Set Warnings "-masking-absolute-name".
Module Type TRANSCRIPTION
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (CStr : COINDSTREAMS Op OpAux)
       (IStr : INDEXEDSTREAMS Op OpAux)
       (L : LUSTRE Ids Op OpAux CStr)
       (CE : COREEXPR Ids Op OpAux IStr)
       (NL : NLUSTRE Ids Op OpAux CStr IStr CE).
  Declare Module Export Tr : TR Ids Op OpAux L.Syn CE.Syn NL.Syn.
  Declare Module Export Typing : TRTYPING Ids Op OpAux L.Syn L.Typ L.Norm.Norm.Untuple CE.Syn CE.Typ NL.Syn NL.Ord NL.Typ Tr.
  Declare Module Export Clocking : TRCLOCKING Ids Op OpAux L.Syn L.Clo CE.Syn NL.Syn NL.Ord NL.Mem NL.IsD CE.IsF NL.IsF CE.Clo NL.Clo Tr.
  Declare Module Export Correctness : CORRECTNESS Ids Op OpAux L.Syn CE.Syn NL.Syn Tr L.Typ L.Clo L.Cau NL.Ord L.Ord CStr L.Sem L.ClSem NL.CoindSem.
  Declare Module Export Completeness : COMPLETENESS Ids Op OpAux CStr L.Syn L.Norm.Norm CE.Syn NL.Syn Tr.
End TRANSCRIPTION.

Module TranscriptionFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (CStr : COINDSTREAMS Op OpAux)
       (IStr : INDEXEDSTREAMS Op OpAux)
       (L : LUSTRE Ids Op OpAux CStr)
       (CE : COREEXPR Ids Op OpAux IStr)
       (NL : NLUSTRE Ids Op OpAux CStr IStr CE)
       <: TRANSCRIPTION Ids Op OpAux CStr IStr L CE NL.
  Module Export Tr := TrFun Ids Op OpAux L.Syn CE.Syn NL.Syn.
  Module Export Typing := TrTypingFun Ids Op OpAux L.Syn L.Typ L.Norm.Norm.Untuple CE.Syn CE.Typ NL.Syn NL.Ord NL.Typ Tr.
  Module Export Clocking := TrClockingFun Ids Op OpAux L.Syn L.Clo CE.Syn NL.Syn NL.Ord NL.Mem NL.IsD CE.IsF NL.IsF CE.Clo NL.Clo Tr.
  Module Export Correctness := CorrectnessFun Ids Op OpAux L.Syn CE.Syn NL.Syn Tr L.Typ L.Clo L.Cau NL.Ord L.Ord CStr L.Sem L.ClSem NL.CoindSem.
  Module Export Completeness := CompletenessFun Ids Op OpAux CStr L.Syn L.Norm.Norm CE.Syn NL.Syn Tr.
End TranscriptionFun.
