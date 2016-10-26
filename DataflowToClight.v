Require Import Rustre.Common.
Require Import Rustre.Ident.
Require Import Rustre.ObcToClight.Translation.

Require Import common.Errors.

Require Import Rustre.Instantiator.
Import DF.Syn.
Import WeFDec.
Import DF.Mem.
Import Obc.Syn.
Import Fus.
Import Trans.

Require Import String.

Open Scope error_monad_scope.

Definition is_well_sch (res: res unit) (n: node) :=
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
  ObcToClight.Translation.translate (List.map fuse_class (Trans.translate g)) main_node.
