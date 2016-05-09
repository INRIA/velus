Require Import Rustre.Common.
Require Import Rustre.Dataflow.Syntax.
Require Import Rustre.Interface.
Require Import Rustre.DF2MP.Translation.
Require Import Rustre.MP2CL.Translation.

Module Import SynDF := Dataflow.Syntax.SyntaxFun Op.
Module Import DF2MPTrans := TranslationFun Op SynDF MP2CL.Translation.Syn.

Definition compile (g: global) (main_node: ident) :=
  MP2CL.Translation.translate (DF2MPTrans.translate g) main_node.