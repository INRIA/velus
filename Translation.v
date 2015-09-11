Require Import Coq.FSets.FMapPositive.
Require Import PArith.
Require Import Rustre.Common.
Require Import Rustre.Minimp.
Require Import Rustre.DataflowSyntax.

Import List.ListNotations.
Open Scope positive.
Open Scope list.

(** * Translation *)

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

Section Translate.

  Variable memories : PS.t.

  Definition tovar (x: ident) : exp :=
    if PS.mem x memories then State x else Var x.

  Fixpoint Control (ck: clock)(s: stmt): stmt :=
    match ck with
    | Cbase => s
    | Con ck x true => Ifte (tovar x) (Control ck s) Skip
    | Con ck x false => Ifte (tovar x) Skip (Control ck s)
    end.

  Fixpoint translate_lexp (e: lexp): exp :=
    match e with
    | Econst c => Const c
    | Evar x => if PS.mem x memories then State x else Var x
    | Ewhen ae c x => translate_laexp ae
    end
  with translate_laexp (lae: laexp): exp :=
         match lae with
         | LAexp ck e => translate_lexp e
         end.

  Fixpoint translate_cexp (x: ident)(e : cexp) {struct e}: stmt :=
    match e with
    | Emerge y t f => Ifte (tovar y) (translate_caexp x t) (translate_caexp x f)
    | Eexp l => Assign x (translate_lexp l)
    end
  with translate_caexp (x: ident)(ae : caexp): stmt :=
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

Definition ps_from_list (l: list ident) : PS.t :=
  List.fold_left (fun s i=>PS.add i s) l PS.empty.

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

Definition translate_reset_eqn (s: stmt) (eqn: equation): stmt :=
  match eqn with
  | EqDef _ _ => s
  | EqFby x v0 _ => Comp (AssignSt x (Const v0)) s
  | EqApp x f _ => Comp (Reset_ap f x) s
  end.

Definition translate_reset_eqns (eqns: list equation): stmt :=
  List.fold_left translate_reset_eqn eqns Skip.

Definition translate_node (n: node): class :=
  let names := gather_eqs n.(n_eqs) in
  let mems := ps_from_list (fst names) in
  mk_class n.(n_name)
           n.(n_input).(v_name)
           n.(n_output).(v_name)
           (fst names)
           (snd names)
           (translate_eqns mems n.(n_eqs))
           (translate_reset_eqns n.(n_eqs)).

(* Define and translate a simple node. *)
Section TestTranslate.

  Example eqns1 : list equation :=
    [
      EqFby 3 (Cint 0) (LAexp (Con Cbase 1 false) (Evar 2));
      EqDef 4 (CAexp Cbase (Emerge 1 (CAexp (Con Cbase 1 true) (Eexp (Evar 2)))
                                   (CAexp (Con Cbase 1 false) (Eexp (Evar 3)))));
      EqDef 2 (CAexp (Con Cbase 1 true) (Eexp (Econst (Cint 7))))
(*   ;EqDef 1 (CAexp Cbase (Eexp (Econst (Cbool true)))) *)
    ].

  Example node1 : node :=
    mk_node 1 (mk_var 1 Cbase) (mk_var 4 Cbase) eqns1.

  (* Eval cbv in (translate_node node1). *)

  Example prog1 : stmt :=
    Comp (Ifte (Var 1) (Assign 2 (Const (Cint 7))) Skip)
   (Comp (Ifte (Var 1) (Assign 4 (Var 2))
                       (Assign 4 (State 3)))
   (Comp (Ifte (Var 1) Skip (AssignSt 3 (Var 2)))
                       Skip)).

  Remark prog1_good : (translate_node node1).(c_step) = prog1.
  Proof eq_refl.

  Example reset1 : stmt :=
    translate_reset_eqns eqns1.

  Example eqns2 : list equation :=
    [
      EqFby 3 (Cint 0) (LAexp Cbase (Evar 2));
      EqApp 4 1 (LAexp Cbase (Evar 3));
      EqApp 2 1 (LAexp Cbase (Evar 1))
    ].

  Example node2 : node :=
    mk_node 2 (mk_var 1 Cbase) (mk_var 4 Cbase) eqns2.

  Eval cbv in (translate_node node2).

  Example class2 : class :=
    {|
      c_name := 2;
      c_input := 1;
      c_output := 4;
      c_mems := [3];
      c_objs := [{| obj_inst := 2; obj_class := 1 |};
                  {| obj_inst := 4; obj_class := 1 |}];
      c_step := Comp (Step_ap 2 1 2 (Var 1))
               (Comp (Step_ap 4 1 4 (State 3))
               (Comp (AssignSt 3 (Var 2))
               Skip));
      c_reset := Comp (Reset_ap 1 2)
                (Comp (Reset_ap 1 4)
                (Comp (AssignSt 3 (Const (Cint 0)))
                 Skip))
    |}.

  Remark prog2_good : translate_node node2 = class2.
  Proof eq_refl.

End TestTranslate.

