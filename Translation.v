Require Import Coq.FSets.FMapPositive.
Require Import PArith.
Require Import Rustre.Common.
Require Import Rustre.Minimp.Syntax.
Require Import Rustre.Dataflow.Syntax.
Require Import Rustre.Dataflow.Memories.

Import List.ListNotations.
Open Scope positive.
Open Scope list.

(** * Translation *)

(** ** Identification of node instances *)

(*
   Note: it is necessary to distinguish different instantiations of
         the same node (i.e., different objects of the same class).

         This is done in Auger's thesis in the language LSNI, where
         node applications are assigned unique identifiers. His context
         is richer, in particular, because the result of a node application
         may be assigned to a pattern-tuple containing multiple identifiers.

         Here, we take advantage of the fact that the result of a node
         application is assigned to a single variable. We use the name of
         that variable to identify the instance.
 *)

Definition gather_eq (acc: list ident * list obj_dec) (eq: equation) :=
  match eq with
  | EqDef _ _ => acc
  | EqApp x f _ => (fst acc, mk_obj_dec x f :: snd acc)
  | EqFby x v0 _ => (x::fst acc, snd acc)
  end.

Definition gather_eqs (eqs: list equation) : (list ident * list obj_dec) :=
  List.fold_left gather_eq eqs ([], []).

(** ** Translation *)

Section Translate.

  Variable memories : PS.t.

  Definition tovar (x: ident) : exp :=
    if PS.mem x memories then State x else Var x.

  Fixpoint Control (ck: clock)(s: stmt): stmt :=
    match ck with
    | Cbase => s
    | Con ck x true  => Control ck (Ifte (tovar x) s Skip)
    | Con ck x false => Control ck (Ifte (tovar x) Skip s)
    end.

  Fixpoint translate_lexp (e: lexp): exp :=
    match e with
    | Econst c => Const c
    | Evar x => if PS.mem x memories then State x else Var x
    | Ewhen e c x => translate_lexp e
    end.
  
  Definition translate_laexp (lae: laexp): exp :=
    match lae with
      | LAexp ck e => translate_lexp e
    end.

  Fixpoint translate_cexp (x: ident)(e : cexp) {struct e}: stmt :=
    match e with
    | Emerge y t f => Ifte (tovar y) (translate_cexp x t) (translate_cexp x f)
    | Eexp l => Assign x (translate_lexp l)
    end.

  Definition translate_caexp (x: ident)(ae : caexp): stmt :=
    match ae with
      | CAexp ck e => translate_cexp x e
    end.

  Definition translate_eqn (eqn: equation): stmt :=
    match eqn with
    | EqDef x (CAexp ck ce) =>
      Control ck (translate_cexp x ce)
    | EqApp x f (LAexp ck le) =>
      Control ck (Step_ap x f x (translate_lexp le))
    | EqFby x v (LAexp ck le) =>
      Control ck (AssignSt x (translate_lexp le))
    end.

  (* NB: eqns ordered in reverse order of execution for coherence
         with Is_well_sch. *)
  Definition translate_eqns (eqns: list equation): stmt :=
    List.fold_left (fun i eq => Comp (translate_eqn eq) i) eqns Skip.

End Translate.

Definition translate_reset_eqn (s: stmt) (eqn: equation): stmt :=
  match eqn with
  | EqDef _ _ => s
  | EqFby x v0 _ => Comp (AssignSt x (Const v0)) s
  | EqApp x f _ => Comp (Reset_ap f x) s
  end.

Definition ps_from_list (l: list ident) : PS.t :=
  List.fold_left (fun s i=>PS.add i s) l PS.empty.

Definition translate_reset_eqns (eqns: list equation): stmt :=
  List.fold_left translate_reset_eqn eqns Skip.

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

Definition translate (G: global) : program :=
  List.map translate_node G.


(** ** Misc. lemmas *)


Lemma ps_from_list_pre_spec:
  forall x l S, (List.In x l \/ PS.In x S)
                <->
                PS.In x (List.fold_left (fun s i=>PS.add i s) l S).
Proof.
  (* TODO: How to use auto to do this whole proof? *)
  induction l as [|l ls IH].
  split; intro HH;
    [ destruct HH as [HH|HH]; [ apply List.in_nil in HH; contradiction | auto]
    | auto ].
  split; intro HH.
  - apply IH.
    destruct HH as [HH|HH].
    apply List.in_inv in HH.
    destruct HH as [HH|HH].
    rewrite HH.
    right; apply PS.add_spec.
    intuition.
    intuition.
    right; apply PS.add_spec; intuition.
  - apply IH in HH.
    destruct HH as [HH|HH].
    left; apply List.in_cons; exact HH.
    apply PS.add_spec in HH.
    destruct HH as [HH|HH].
    rewrite HH; intuition.
    intuition.
Qed.

Lemma ps_from_list_spec:
  forall x l, List.In x l <-> PS.In x (ps_from_list l).
Proof.
  unfold ps_from_list.
  intros.
  rewrite <- ps_from_list_pre_spec with (S:=PS.empty).
  intuition.
  match goal with
  | H:PS.In _ PS.empty |- _ => apply not_In_empty in H; contradiction
  end.
Qed.


