From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import CoindStreams.
From Velus Require Import Lustre.Lustre.

From Velus Require Import Normalization.Norm.

Module Type NORMALIZATION
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Str : COINDSTREAMS Op OpAux)
       (Lus : LUSTRE Ids Op OpAux Str).
  Declare Module Export Norm : NORM Ids Op Lus.Syn Lus.Typ.
End NORMALIZATION.

Module NormalizationFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Str : COINDSTREAMS Op OpAux)
       (Lus : LUSTRE Ids Op OpAux Str).
  Module Export Norm := NormFun Ids Op Lus.Syn Lus.Typ.
End NormalizationFun.
