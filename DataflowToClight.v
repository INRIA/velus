Require Import Rustre.Common.
Require Import Rustre.Dataflow.
Require Import Rustre.Dataflow.IsFree.Decide.
Require Import Rustre.Dataflow.WellFormed.Decide.
Require Import Rustre.ObcToClight.Interface.
Require Import Rustre.DataflowToObc.Translation.
Require Import Rustre.ObcToClight.Translation.
Require Import Rustre.Obc.FuseIfte.

Require Import common.Errors.
Require Import Rustre.Operators.
Require Import Rustre.Ident.

Module Export OpAux := OperatorsAux Op.

Module Import SynDF := Dataflow.Syntax.SyntaxFun Ids Op.
Module Import SynObc := ObcToClight.Translation.Syn.
Module Import Mem := Dataflow.Memories.MemoriesFun Ids Op SynDF.
Module Import DF2ObcTrans := TranslationFun Ids Op OpAux SynDF SynObc Mem.

Module Import IsF := IsFreeFun Ids Op SynDF.
Module Import IsFDec := Dataflow.IsFree.Decide.Decide Ids Op SynDF IsF.
Module Import Ord := OrderedFun Ids Op SynDF.
Module Import IsD := IsDefined Ids Op SynDF Mem.
Module Import IsV := IsVariableFun Ids Op SynDF Mem IsD.
Module Import IsDDec := IsDefined.Decide.Decide Ids Op SynDF Mem IsD.
Module Import IsVDec := IsVariable.Decide.Decide Ids Op SynDF Mem IsD IsV.
Module Import NoD := NoDupFun Ids Op SynDF Mem IsD IsV.
Module Import Wef := WellFormedFun Ids Op SynDF IsF Ord Mem IsD IsV NoD.
Module Import WefD := Dataflow.WellFormed.Decide.Decide
                        Ids Op SynDF IsF IsFDec Ord Mem IsD IsV IsDDec IsVDec NoD Wef.

Module Import SemObc := Rustre.Obc.Semantics.SemanticsFun Ids Op OpAux SynObc.
Module Import Equ := Rustre.Obc.Equiv.EquivFun Ids Op OpAux SynObc SemObc.
Module Import FuseIFTE := FuseIfteFun Ids Op OpAux SynDF SynObc SemObc Equ.

Require Import String.

Open Scope error_monad_scope.

Definition is_well_sch (res: Errors.res unit) (n: node) :=
  match res with
  | OK _ =>
    let eqs := n.(n_eqs) in
    let ni := List.map fst n.(n_in) in
    if well_sch (memories eqs) ni eqs then OK tt
    else Error (Errors.msg ("node " ++ pos_to_str n.(n_name) ++ " is not well scheduled."))
  | _ => res
  end.


Definition fuse_method (m: method): method :=
  match m with
    mk_method name ins vars out body nodup good =>
    mk_method name ins vars out (fuse body) nodup good 
  end.

Lemma map_m_name_fuse_methods:
  forall methods,
    List.map m_name (List.map fuse_method methods) = List.map m_name methods.
Proof.
  intro ms; induction ms as [|m ms]; auto.
  simpl. rewrite IHms.
  now destruct m.
Qed.
  
Lemma NoDup_m_name_fuse_methods:
  forall methods,
    List.NoDup (List.map m_name methods) ->
    List.NoDup (List.map m_name (List.map fuse_method methods)).
Proof.
  intros; now rewrite map_m_name_fuse_methods.
Qed.

Definition fuse_class (c: class): class :=
  match c with
    mk_class name mems objs methods nodup nodupm =>
    mk_class name mems objs (List.map fuse_method methods) nodup
             (NoDup_m_name_fuse_methods _ nodupm)
  end.

Definition compile (g: global) (main_node: ident) :=
  do _ <- (List.fold_left is_well_sch g (OK tt));
  ObcToClight.Translation.translate (List.map fuse_class (DF2ObcTrans.translate g)) main_node.
