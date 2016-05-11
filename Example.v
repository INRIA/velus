Require Import PArith.
Require Import Rustre.Nelist.
Require Import List.
Import List.ListNotations.
Open Scope positive.
Open Scope list.

Require Import Rustre.Common.
Require Import Rustre.Dataflow.Syntax.
Require Import Rustre.Minimp.Syntax.
Require Import Rustre.Translation.

Require Import Rustre.Dataflow.Memories.
Require Import Rustre.Dataflow.WellFormed.
Require Import Rustre.Dataflow.WellFormed.Decide.

(* Common notations *)
Class Assignment T U V := {assign : ident -> T -> U -> V}.
Notation "x '::=' y" := (assign x _ y) (at level 47, no associativity).
Class OpCall T U := {opcall : operator -> T -> U}.
Notation "f '<' nel '>'" := (opcall f nel) (at level 46, format "f '<' nel '>'").
Notation "x :,: y" := (necons x y) (at level 30, right associativity).
Notation "x '§'" := (nebase x) (at level 30).

(* Dataflow notations *)
Coercion Cint : BinInt.Z >-> const.
Coercion Cbool : bool >-> const.
Coercion Evar : ident >-> lexp.
Coercion Eexp : lexp >-> cexp.
Coercion Econst : const >-> lexp.

Notation "x 'on' ck" := (Con x ck) (at level 44).
(*Notation "x 'when' C ( ck )" := (Ewhen x ck C) (at level 45, left associativity, format "x  'when'  C ( ck )").*)
Notation "x 'when' ck" := (Ewhen x ck true) (at level 45, left associativity).
Notation "x 'whenot' ck" := (Ewhen x ck false) (at level 45, left associativity).
Notation "x '::=' v 'fby' y" := (EqFby x _ v y) (at level 47).
Notation "x '::=' f '(|' nel '|)'" := (EqApp x _ f nel) (at level 47, format "x  '::='  f '(|' nel '|)'").
Instance EqDef_Assign : Assignment clock cexp equation := {assign := EqDef}.
Instance Eop_OpCall : OpCall lexps lexp := {opcall := Eop}.

(* Imperative notations *)
Coercion Var : ident >-> exp.
Coercion State : ident >-> exp.
Coercion Const : const >-> exp.

Instance Assign_Assign : Assignment unit exp stmt := {assign := fun x (_ : unit) => Assign x}.
Instance AssignSt_Assign : Assignment unit exp stmt := {assign := fun x (_ : unit) => AssignSt x}.
Instance Op_OpCall : OpCall (nelist exp) exp := {opcall := Op}.
Notation "stmt1 ;; stmt2" := (Comp stmt1 stmt2) (at level 48, right associativity).
Notation "'If' b 'Then' t 'Else' f" := (Ifte b t f) (at level 47, t at level 47, f at level 47).
Notation "x '::=' class '(' obj ').step(' args ')'" := (Step_ap x class obj args) (at level 47).
Notation " class '(' obj ').reset()'" := (Reset_ap class obj) (at level 47).

(* TODO: not properly clocked... *)
Example eqns1 : list equation :=
  [
    EqFby 3 (Con Cbase 1 false) (Cint 0) (Evar 2);
    assign 4 Cbase (Emerge 1 (Eexp (Evar 2)) (Eexp (Evar 3)));
    assign 2 (Con Cbase 1 true) (Eexp (Ewhen (Econst (Cint 7)) 1 true))

(*   ;EqDef 1 (CAexp Cbase (Eexp (Econst (Cbool true)))) *)
  ].
Print eqns1.

Example node1 : node :=
  mk_node 1 (nebase 1) 4 eqns1.


Example eqns2 : list equation :=
  [
    EqFby 3 Cbase (Cint 0) (Evar 2);
    EqApp 4 Cbase 1 (nebase (Evar 3));
    EqApp 2 Cbase 1 (nebase (Evar 1))
  ].
Print eqns2.

Example node2 : node :=
  mk_node 2 (nebase 1) 4 eqns2.

(** Scheduling *)

Example eqn1_well_sch: Is_well_sch (memories eqns1) (1§) eqns1.
Proof.
  assert (well_sch (memories eqns1) (1§) eqns1 = true) as HW by apply eq_refl.
  pose proof (well_sch_spec (memories eqns1) (1§) eqns1) as HS.
  rewrite HW in HS.
  assumption.
Qed.

Example eqn2_well_sch: Is_well_sch (memories eqns2) (1§) eqns2.
Proof.
  assert (well_sch (memories eqns2) (1§) eqns2 = true) as HW by apply eq_refl.
  pose proof (well_sch_spec (memories eqns2) (1§) eqns2) as HS.
  rewrite HW in HS.
  assumption.
Qed.


(** Translation *)

(* Eval cbv in (translate_node node1). *)

Example prog1 : stmt :=
  Comp (Ifte (Var 1) (Assign 2 (Const (Cint 7))) Skip)
       (Comp (Ifte (Var 1) (Assign 4 (Var 2))
                   (Assign 4 (State 3)))
             (Comp (Ifte (Var 1) Skip (AssignSt 3 (Var 2)))
                   Skip)).
Print prog1.
(* If 1 Then Assign 2 7%Z Else Skip;;
   If 1 Then Assign 4 2 Else Assign 4 3;;
   If 1 Then Skip Else AssignSt 3 2;; Skip *)

Remark prog1_good : (translate_node node1).(c_step) = prog1.
Proof eq_refl.

Example reset1 : stmt :=
  translate_reset_eqns eqns1.

(* Eval cbv in (translate_node node2). *)

Example class2 : class :=
  {|
    c_name := 2;
    c_input := nebase 1;
    c_output := 4;
    c_mems := [3];
    c_objs := [{| obj_inst := 2; obj_class := 1 |};
                {| obj_inst := 4; obj_class := 1 |}];
    c_step := Comp (Step_ap 2 1 2 (nebase (Var 1)))
                   (Comp (Step_ap 4 1 4 (nebase (State 3)))
                         (Comp (AssignSt 3 (Var 2))
                               Skip));
    c_reset := Comp (Reset_ap 1 2)
                    (Comp (Reset_ap 1 4)
                          (Comp (AssignSt 3 (Const (Cint 0)))
                                Skip))
  |}.
Print class2.

Remark prog2_good : translate_node node2 = class2.
Proof eq_refl.

(** Optimization *)

Require Import Rustre.Minimp.FuseIfte.

Example prog1' : stmt :=
  Ifte (Var 1)
       (Comp (Assign 2 (Const (Cint 7)))
             (Assign 4 (Var 2)))
       (Comp (Assign 4 (State 3))
             (AssignSt 3 (Var 2))).
Print prog1'.
(* If 1 Then (Assign 2 7%Z;; Assign 4 2) Else (Assign 4 3;; AssignSt 3 2) *)

Remark prog1'_is_fused: (ifte_fuse prog1 = prog1').
Proof eq_refl.

(* TODO: Show correctness of prog1' *)

(** Examples from paper *)

Section CodegenPaper.

  Require Import Nelist.


  Definition Plus : operator := existT arrows (Tcons Tint (Tcons Tint (Tout Tint))) BinInt.Z.add.
  Definition op_plus (x: lexp) (y: lexp) : lexp := Eop Plus (necons x (nebase y)).
  Notation "x ':+' y" := (op_plus x y) (at level 47).
  Opaque Plus.

  Definition Ifte_int : operator :=
    existT arrows (Tcons Tbool (Tcons Tint (Tcons Tint (Tout Tint))))
             (fun (x : bool) t f => if x then t else f).
  Definition op_ifte (x: lexp) (t: lexp) (f: lexp) : lexp :=
    Eop Ifte_int (necons x (necons t (nebase f))).
  Opaque Ifte_int.

  Definition Disj : operator :=
    existT arrows (Tcons Tbool (Tcons Tbool (Tout Tbool))) orb.
  Definition op_disj (x: lexp) (y: lexp) : lexp := Eop Disj (necons x (nebase y)).
  Notation "x ':||' y" := (op_disj x y) (at level 47).
  Opaque Disj.

  (* Node names *)
  Definition n_count       : ident := 1.
  Definition n_avgvelocity : ident := n_count + 1.

  (*
  node count (initial, inc: int; restart: bool) returns (n: int)
    var c: int; f: bool;
  let
    n = if f or restart then initial else c + inc;
    f = true fby false;
    c = 0 fby n;
  tel
  *)

  (* counter: variable names *)
  Definition initial   : ident := 1.
  Definition inc       : ident := 2.
  Definition restart   : ident := 3.
  Definition n         : ident := 4.
  Definition f         : ident := 5.
  Definition c         : ident := 6.

  Example count_eqns : list equation :=
    [
      EqFby c Cbase (Cint 0) (Evar n);
      EqFby f Cbase (Cbool true) (Cbool false);
      EqDef n Cbase (Eexp (op_ifte (op_disj (Evar f) (Evar restart))
                                   (Evar initial)
                                   (op_plus (Evar c) (Econst (Cint 1)))))
    ].
  Print count_eqns.
  (* TODO: show that these equations Is_well_sch and Well_clocked;
           need multiple inputs *)

  Definition Div : operator := existT arrows (Tcons Tint (Tcons Tint (Tout Tint))) BinInt.Z.div.
  Definition op_div (x: lexp) (y: lexp) : lexp := Eop Div (necons x (nebase y)).
  Notation "x ':/' y" := (op_div x y) (at level 49).
  Opaque Div.

  (* XXX: prove by reflection, god damnit *)
  Ltac invert :=
    (* Invertible rules, yeah! *)
    repeat progress
           match goal with
             | H: PS.In _ (PS.singleton _) |- _ =>
               apply PSP.Dec.F.singleton_1 in H
             | H: ~ PS.In ?c (PS.singleton ?c) |- _ =>
               now (exfalso; apply H; PSdec.fsetdec)
             | H: IsFree.Is_free_in_lexp _ (Econst _) |- _ =>
               now (exfalso; inv H)


             | |- Is_well_sch _ _ _ => constructor
             | |- ~ _ => intro
             | |- _ /\ _  => split
             | |- _ -> _ => intros

             | |- PS.In ?x (PS.add ?x _) => apply PSF.add_1; reflexivity
             | |- PS.In ?x (PS.add _ (PS.singleton ?x)) => apply PSF.add_2; reflexivity

             | H: context[ op_ifte _ _ _ ] |- _ => unfold op_ifte in H
             | H: context[ op_plus _ _ ] |- _ => unfold op_plus in H
             | H: context[ op_div _ _ ] |- _ => unfold op_div in H
             | H: context[ op_disj _ _ ] |- _ => unfold op_disj in H
             | [ i : ident , H : ?i = _ |- _ ] => subst i
             | i: ident , H: _ = ?i |- _ => subst i

             | H: IsFree.Is_free_in_eq _ (EqDef _ _ _) |- _ => inv H
             | H: IsFree.Is_free_in_eq _ (EqFby _ _ _ _) |- _ => inv H
             | H: IsFree.Is_free_in_eq _ (EqApp _ _ _ _) |- _ => inv H

             | H: IsFree.Is_free_in_caexp _ _ _ |- _ => inversion H; clear H

             | H: IsFree.Is_free_in_cexp _ (Emerge _ _ _) |- _ => inversion H; clear H
             | H: IsFree.Is_free_in_cexp _ (Eexp _) |- _ => inv H

             | H: IsFree.Is_free_in_lexp _ (Ewhen _ _ _) |- _ => inversion H; clear H
             | H: IsFree.Is_free_in_lexp _ (Eop _ _) |- _ => inv H
             | H: IsFree.Is_free_in_lexp ?x (Evar ?y) |- _ =>
               assert (x = y) by (inv H; eauto); clear H

             | H: IsFree.Is_free_in_clock _ Cbase |- _ => now (exfalso; inv H)
             | H: IsFree.Is_free_in_clock _ (Con _ _ _) |- _ => inversion H; clear H
             | H: IsFree.Is_free_in_laexp _ _ _ |- _ => inversion H; clear H
             | H: IsFree.Is_free_in_laexps _ _ (nebase _) |- _ => inv H
             | H: IsFree.Is_free_in_laexps _ _ (necons _ _) |- _ => inv H

             | H: IsDefined.Is_defined_in_eqs _ [] |- _ => inv H
             | H: IsDefined.Is_defined_in_eqs _ (_ :: _) |- _ => inv H

             | H: IsDefined.Is_defined_in_eq _ (EqDef _ _ _) |- _ => inv H
             | H: IsDefined.Is_defined_in_eq _ (EqFby _ _ _ _) |- _ => inv H
             | H: IsDefined.Is_defined_in_eq _ (EqApp _ _ _ _) |- _ => inv H

             | H: List.Exists _ [] |- _ => inv H
             | H: List.Exists _ (_ :: _) |- _ => inv H

             | H: Exists _ (nebase _) |- _ => inv H
             | H: Exists _ (necons _ _) |- _ => inv H

             | H: ~PS.In ?x (PS.add ?x _) |- _ => exfalso; apply H
             | H: ~PS.In ?x (PS.add _ (PS.singleton ?x)) |- _ => exfalso; apply H
             | H: PS.In _ (PS.add _ _) |- _ => inv H
           end.

  Ltac commit :=
    try solve [ right;
                simpl; auto
              | left; constructor 2; repeat constructor
              | left; repeat constructor
              | auto ].

  Ltac is_well_sch := invert; commit.

  Lemma count_eqns_well_sch :
    Is_well_sch (PS.add f (PS.singleton c))
                (initial :,: inc :,: restart§) count_eqns.
  Proof.
    is_well_sch.
  Qed.

  Example count : node :=
    mk_node n_count (necons initial (necons inc (nebase restart))) n count_eqns.

  Eval cbv in translate_node count.
  Eval cbv in ifte_fuse (c_step (translate_node count)).
  Eval cbv in ifte_fuse (c_reset (translate_node count)).

(*
  node avgvelocity (delta: int; sec: bool) returns (v: int)
    var r, t, h: int;
  let
    r = count(0, delta, false);
    t = count(1 when sec, 1 when sec, false when sec);
    v = merge sec ((r when sec) / t) (h whenot sec);
    h = 0 fby v;
  tel
*)

  (* avgvelocity: variable names *)
  Definition delta  : ident := 1.
  Definition sec    : ident := 2.
  Definition r      : ident := 3.
  Definition t      : ident := 4.
  Definition v      : ident := 5.
  Definition h      : ident := 6.

  Example avgvelocity_eqns : list equation :=
    [
      EqFby h Cbase (Cint 0) (Evar v);
      EqDef v Cbase
              (Emerge sec
                      (Eexp (op_div (Ewhen (Evar r) sec true) (Evar t)))
                      (Eexp (Ewhen (Evar h) sec false)));
      EqApp t (Con Cbase sec true) n_count
                  (necons (Ewhen (Econst (Cint 1)) sec true)
                  (necons (Ewhen (Econst (Cint 1)) sec true)
                  (nebase (Ewhen (Econst (Cbool false)) sec true))));
      EqApp r Cbase n_count (necons (Econst (Cint 0))
                            (necons (Evar delta)
                            (nebase (Econst (Cbool false)))))
    ].
  Print avgvelocity_eqns.

  Lemma avgvelocity_eqns_Well_sch :
    Is_well_sch (PS.singleton h) (delta :,: sec§) avgvelocity_eqns.
  Proof.
    is_well_sch.
  Qed.

  Example avgvelocity : node :=
    mk_node n_avgvelocity (delta :,: sec§) v avgvelocity_eqns.

  Eval cbv in translate_node avgvelocity.
  Eval cbv in ifte_fuse (c_step (translate_node avgvelocity)).

End CodegenPaper.
