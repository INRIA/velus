Require Import Coq.FSets.FMapPositive.
Require Import PArith.
Require Import Rustre.Nelist.
Require Import Rustre.Common.
Require Import Rustre.Minimp.Syntax.
Require Import Rustre.Dataflow.Syntax.
Require Import Rustre.Dataflow.Memories.

Import List.ListNotations.
Open Scope positive.
Open Scope list.
Require Import Nelist.


(** * Translation *)

(** ** Identification of node instances *)

(** 

Each node application in CoreDF turns into a method call in the
imperative setting. This means that, upon initializing a node, one
must declare a new instance for each its application.

Remark: it is necessary to distinguish different instantiations of the
same node (i.e., different objects of the same class). This is done in
Auger's thesis in the language LSNI, where node applications are
assigned unique identifiers. His context is richer, in particular,
because the result of a node application may be assigned to a
pattern-tuple containing multiple identifiers.

Here, we take advantage of the fact that the result of a node
application is assigned to a single variable. We use the name of that
variable to identify the instance.  *)

Definition gather_eq (acc: list ident * list obj_dec) (eq: equation) :=
  match eq with
  | EqDef _ _ _ => acc
  | EqApp x _ f _ => (fst acc, mk_obj_dec x f :: snd acc)
  | EqFby x _ v0 _ => (x::fst acc, snd acc)
  end.

Definition gather_eqs (eqs: list equation) : (list ident * list obj_dec) :=
  List.fold_left gather_eq eqs ([], []).

(** ** Translation *)

Section Translate.

Variable memories : PS.t.

(* =tovar= *)
Definition tovar (x: ident) : exp :=
  if PS.mem x memories then State x else Var x.
(* =end= *)

(* =control= *)
Fixpoint Control (ck: clock) (s: stmt) : stmt :=
  match ck with
  | Cbase => s
  | Con ck x true  => Control ck (Ifte (tovar x) s Skip)
  | Con ck x false => Control ck (Ifte (tovar x) Skip s)
  end.
(* =end= *)

(* =translate_lexp= *)
Fixpoint translate_lexp (e : lexp) : exp :=
  match e with
  | Econst c => Const c
  | Evar x => if PS.mem x memories then State x else Var x
  | Ewhen e c x => translate_lexp e
  | Eop op es => Op op (Nelist.map translate_lexp es)
  end.
(* =end= *)

(* =translate_cexp= *)
Fixpoint translate_cexp (x: ident) (e: cexp) : stmt :=
  match e with
  | Emerge y t f => Ifte (tovar y) (translate_cexp x t) (translate_cexp x f)
  | Eexp l =>        Assign x (translate_lexp l)
  end.
(* =end= *)

(* =translate_eqn= *)
Definition translate_eqn (eqn: equation) : stmt :=
  match eqn with
  | EqDef x ck ce   => Control ck (translate_cexp x ce)
  | EqApp x ck f les => Control ck (Step_ap x f x (map translate_lexp les))
  | EqFby x ck v le => Control ck (AssignSt x (translate_lexp le))
  end.
(* =end= *)

(** Remark: eqns ordered in reverse order of execution for coherence with
       [Is_well_sch]. *)

(* =translate_eqns= *)
Definition translate_eqns (eqns: list equation) : stmt :=
  List.fold_left (fun i eq => Comp (translate_eqn eq) i) eqns Skip.
(* =end= *)

End Translate.

(* =translate_reset_eqn= *)
Definition translate_reset_eqn (s: stmt) (eqn: equation) : stmt :=
  match eqn with
  | EqDef _ _ _ => s
  | EqFby x _ v0 _ => Comp (AssignSt x (Const v0)) s
  | EqApp x _ f _ => Comp (Reset_ap f x) s
  end.
(* =end= *)

(* =translate_reset_eqns= *)
Definition translate_reset_eqns (eqns: list equation): stmt :=
  List.fold_left translate_reset_eqn eqns Skip.
(* =end= *)

Definition ps_from_list (l: list ident) : PS.t :=
  List.fold_left (fun s i=>PS.add i s) l PS.empty.

(* =translate_node= *)
Definition translate_node (n: node): class :=
  let names := gather_eqs n.(n_eqs) in
  let mems := ps_from_list (fst names) in
  mk_class n.(n_name)
           n.(n_input)
           n.(n_output)
           (fst names)
           (snd names)
           (translate_eqns mems n.(n_eqs))
           (translate_reset_eqns n.(n_eqs)).
(* =end= *)

(* =translate= *)
Definition translate (G: global) : program :=
  List.map translate_node G.
(* =end= *)


(** ** Properties *)


Lemma ps_from_list_pre_spec:
  forall x l S, (List.In x l \/ PS.In x S)
                <->
                PS.In x (List.fold_left (fun s i=>PS.add i s) l S).
Proof.
  induction l as [|l ls IH].
  - firstorder.
  - split; intro HH.
    + firstorder.
    + apply IH in HH.
      destruct HH as [HH|HH]; try apply PS.add_spec in HH; firstorder.
Qed.

Lemma ps_from_list_spec:
  forall x l, List.In x l <-> PS.In x (ps_from_list l).
Proof.
  unfold ps_from_list.
  intros.
  rewrite <- ps_from_list_pre_spec with (S:=PS.empty).
  split; try intros [H | H]; try tauto.
  apply not_In_empty in H; contradiction.
Qed.


