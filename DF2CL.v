Require Import Rustre.Common.
Require Import Rustre.Dataflow.
Require Import Rustre.Dataflow.IsFree.Decide.
Require Import Rustre.Dataflow.WellFormed.Decide.
Require Import Rustre.Interface.
Require Import Rustre.DF2MP.Translation.
Require Import Rustre.MP2CL.Translation.

Require Import common.Errors.

Module Import SynDF := Dataflow.Syntax.SyntaxFun Op.
Module Import DF2MPTrans := TranslationFun Op SynDF MP2CL.Translation.Syn.

Module Import IsF := IsFreeFun Op SynDF.
Module Import IsFDec := Dataflow.IsFree.Decide.DecideFun Op SynDF IsF.
Module Import Ord := OrderedFun Op SynDF.
Module Import Mem := MemoriesFun Op SynDF.
Module Import IsD := IsDefinedFun Op SynDF Mem.
Module Import IsV := IsVariableFun Op SynDF Mem IsD.
Module Import NoD := NoDupFun Op SynDF Mem IsD IsV.
Module Import Wef := WellFormedFun Op SynDF IsF Ord Mem IsD IsV NoD.
Module Import WefD := Dataflow.WellFormed.Decide.DecideFun Op SynDF IsF IsFDec Ord Mem IsD IsV NoD Wef.

Require Import String.

Definition is_well_sch (res: Errors.res unit) (n: node) :=
  match res with
  | OK _ =>
    let eqs := n.(n_eqs) in
    let ni := Nelist.nefst n.(n_input) in
    if well_sch (memories eqs) ni eqs then OK tt
    else Error (Errors.msg ("node " ++ pos_to_str n.(n_name) ++ " is not well scheduled."))
  | _ => res
  end.

Open Scope error_monad_scope.

Definition compile (g: global) (main_node: ident) :=
  do _ <- (List.fold_left is_well_sch g (OK tt));
  MP2CL.Translation.translate (DF2MPTrans.translate g) main_node.