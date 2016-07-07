Require Import Rustre.Common.
Require Import Rustre.Dataflow.
Require Import Rustre.Dataflow.IsFree.Decide.
Require Import Rustre.Dataflow.WellFormed.Decide.
Require Import Rustre.Interface.
Require Import Rustre.DataflowToMinimp.Translation.
Require Import Rustre.MinimpToClight.Translation.
Require Import Rustre.Minimp.FuseIfte.

Require Import common.Errors.

Module Import SynDF := Dataflow.Syntax.SyntaxFun Op.
Module Import SynMP := MinimpToClight.Translation.Syn.
Module Import DF2MPTrans := TranslationFun Op SynDF SynMP.

Module Import IsF := IsFreeFun Op SynDF.
Module Import IsFDec := Dataflow.IsFree.Decide.DecideFun Op SynDF IsF.
Module Import Ord := OrderedFun Op SynDF.
Module Import Mem := MemoriesFun Op SynDF.
Module Import IsD := IsDefinedFun Op SynDF Mem.
Module Import IsV := IsVariableFun Op SynDF Mem IsD.
Module Import NoD := NoDupFun Op SynDF Mem IsD IsV.
Module Import Wef := WellFormedFun Op SynDF IsF Ord Mem IsD IsV NoD.
Module Import WefD := Dataflow.WellFormed.Decide.DecideFun Op SynDF IsF IsFDec Ord Mem IsD IsV NoD Wef.

Module Import SemMP := Rustre.Minimp.Semantics.SemanticsFun Op SynMP.
Module Import Equ := Rustre.Minimp.Equiv.EquivFun Op SynMP SemMP.
Module Import FuseIFTE := FuseIfteFun Op SynDF MinimpToClight.Translation.Syn SemMP Equ.

Require Import String.

Open Scope error_monad_scope.

Definition is_well_sch (res: Errors.res unit) (n: node) :=
  match res with
  | OK _ =>
    let eqs := n.(n_eqs) in
    let ni := Nelist.map_fst n.(n_input) in
    if well_sch (memories eqs) ni eqs then OK tt
    else Error (Errors.msg ("node " ++ pos_to_str n.(n_name) ++ " is not well scheduled."))
  | _ => res
  end.

Definition fuse (c: class): class :=
  match c with
    mk_class name ins out vars mems objs step reset =>
    mk_class name ins out vars mems objs (ifte_fuse step) (ifte_fuse reset)
  end.

Definition compile (g: global) (main_node: ident) :=
  do _ <- (List.fold_left is_well_sch g (OK tt));
  MinimpToClight.Translation.translate (List.map fuse (DF2MPTrans.translate g)) main_node.
