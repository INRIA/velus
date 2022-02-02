From Velus Require Import Common Ident.
From Velus Require Import Operators Environment.
From Velus Require Import CoindStreams IndexedStreams CoindToIndexed.
From Velus Require Import Lustre.Lustre.
From Velus Require Import CoreExpr.CoreExpr.
From Velus Require Import NLustre.NLustre.
From Velus Require Import Transcription.Tr.
From Velus Require Import Transcription.TrTyping Transcription.TrClocking Transcription.Correctness.
From Velus Require Import Transcription.Completeness.
From Velus Require Import Transcription.TrNormalArgs.

Module Type TRANSCRIPTION
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (ComTyp: COMMONTYPING   Ids Op OpAux)
       (Cks : CLOCKS Ids Op OpAux)
       (CStr : COINDSTREAMS Ids Op OpAux Cks)
       (IStr : INDEXEDSTREAMS Ids Op OpAux Cks)
       (CIStr : COINDTOINDEXED Ids Op OpAux Cks CStr IStr)
       (L : LUSTRE Ids Op OpAux Cks CStr)
       (CE : COREEXPR Ids Op OpAux ComTyp Cks IStr)
       (NL : NLUSTRE Ids Op OpAux ComTyp Cks CStr IStr CIStr CE).
  Declare Module Export Tr : TR Ids Op OpAux Cks L.Senv L.Syn CE.Syn NL.Syn.
  Declare Module Export Typing : TRTYPING Ids Op OpAux Cks L.Senv L.Syn L.Typ CE.Syn CE.Typ NL.Syn NL.Ord NL.Typ Tr.
  Declare Module Export Clocking : TRCLOCKING Ids Op OpAux Cks L.Senv L.Syn L.Typ L.Clo CE.Syn NL.Syn NL.Ord NL.Mem NL.IsD CE.Clo NL.Clo Tr.
  Declare Module Export Correctness : CORRECTNESS Ids Op OpAux Cks L.Senv L.Syn CE.Syn NL.Syn Tr L.Typ L.Clo L.Cau NL.Ord L.Ord CStr L.Sem L.CkSem L.Norm.Norm NL.CoindSem.
  Declare Module Export Completeness : COMPLETENESS Ids Op OpAux Cks L.Senv L.Syn L.Typ L.Norm.Norm CE.Syn NL.Syn Tr.
  Declare Module Export NormalArgs : TRNORMALARGS Ids Op OpAux Cks L.Senv L.Syn L.Ord L.Norm.Norm CE.Syn CE.Typ NL.Syn NL.Ord NL.Typ NL.Norm Tr.
End TRANSCRIPTION.

Module TranscriptionFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (ComTyp: COMMONTYPING   Ids Op OpAux)
       (Cks : CLOCKS Ids Op OpAux)
       (CStr : COINDSTREAMS Ids Op OpAux Cks)
       (IStr : INDEXEDSTREAMS Ids Op OpAux Cks)
       (CIStr : COINDTOINDEXED Ids Op OpAux Cks CStr IStr)
       (L : LUSTRE Ids Op OpAux Cks CStr)
       (CE : COREEXPR Ids Op OpAux ComTyp Cks IStr)
       (NL : NLUSTRE Ids Op OpAux ComTyp Cks CStr IStr CIStr CE)
       <: TRANSCRIPTION Ids Op OpAux ComTyp Cks CStr IStr CIStr L CE NL.
  Module Export Tr := TrFun Ids Op OpAux Cks L.Senv L.Syn CE.Syn NL.Syn.
  Module Export Typing := TrTypingFun Ids Op OpAux Cks L.Senv L.Syn L.Typ CE.Syn CE.Typ NL.Syn NL.Ord NL.Typ Tr.
  Module Export Clocking := TrClockingFun Ids Op OpAux Cks L.Senv L.Syn L.Typ L.Clo CE.Syn NL.Syn NL.Ord NL.Mem NL.IsD CE.Clo NL.Clo Tr.
  Module Export Correctness := CorrectnessFun Ids Op OpAux Cks L.Senv L.Syn CE.Syn NL.Syn Tr L.Typ L.Clo L.Cau NL.Ord L.Ord CStr L.Sem L.CkSem L.Norm.Norm NL.CoindSem.
  Module Export Completeness := CompletenessFun Ids Op OpAux Cks L.Senv L.Syn L.Typ L.Norm.Norm CE.Syn NL.Syn Tr.
  Module Export NormalArgs := TrNormalArgsFun Ids Op OpAux Cks L.Senv L.Syn L.Ord L.Norm.Norm CE.Syn CE.Typ NL.Syn NL.Ord NL.Typ NL.Norm Tr.
End TranscriptionFun.
