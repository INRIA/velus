From Coq Require Import PArith.
From Velus Require Import Nelist.
From Coq Require Import List.
Import List.ListNotations.
Open Scope positive.
Open Scope list.

From Velus Require Import Common.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import Obc.ObcSyntax.
From Velus Require Import Translation.
From Velus Require Import Obc.FuseIfte.

From Velus Require Import NLustre.Memories.
From Velus Require Import NLustre.WellFormed.
From Velus Require Import NLustre.WellFormed.Decide.


(* Common notations *)
Class Assignment U V := {assign : ident -> U -> V}.
Notation "x '::=' y" := (assign x y) (at level 47, no associativity, only parsing).
Class OpCall T U := {opcall : operator -> T -> U}.
Notation "f '<' nel '>'" := (opcall f nel) (at level 46, only parsing, format "f '<' nel '>'").
Notation "x :,: y" := (necons x y) (at level 30, right associativity, only parsing).
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
Notation "x '::=' v 'fby' y" := (EqFby x Cbase (v : const) (y : lexp)) 
                                  (at level 47, v at next level). 
Notation "x '::=' f '(|' nel '|)'" := (EqApp x Cbase f nel) 
                                        (at level 47, f, nel at next level, format "x  '::='  f '(|' nel '|)'").
Notation "x '::=' f '(|' nel '|)' '@' ck" := (EqApp x ck f nel) 
                                        (at level 47, f, nel at next level).

Instance EqDef_CAssign : Assignment cexp equation := {assign := (fun i => EqDef i Cbase)}.
Instance EqDef_EAssign : Assignment lexp equation := {assign := (fun i e => EqDef i Cbase (Eexp e))}.
Instance Eop_OpCall : OpCall lexps lexp := {opcall := Eop}.

(* Imperative notations *)
Coercion Const : const >-> exp.
Coercion Var : ident >-> exp.

Class IFTE U V := {ifte : U -> V -> V -> V}.
Notation "'If' b 'Then' t 'Else' f" := (ifte b t f) (at level 47, t at level 47, f at level 47).

Instance Assign_Assign : Assignment exp stmt := {assign := Assign}.
(* Instance AssignSt_Assign : Assignment exp stmt := {assign := AssignSt}. *)
Notation "'state(|' x '|)::='  y" := (AssignSt x y) (at level 47).
Instance Op_OpCall : OpCall (nelist exp) exp := {opcall := Op}.
Notation "stmt1 ;; stmt2" := (Comp stmt1 stmt2) (at level 48, right associativity).
Instance IFTE_imp : IFTE exp stmt := {ifte := Ifte}.
Instance IFTE_impVar : IFTE ident stmt := {ifte := fun i => Ifte (Var i) }.

Notation "x '::=' class '(|' obj '|).step(' args ')'" := (Step_ap x class obj args)
    (at level 47, class, obj, args at next level).
Notation " class '(|' obj '|).reset()'" := (Reset_ap class obj)
                                                 (at level 47, obj at next level).

Print Grammar constr.

(** Examples from paper *)

Section CodegenPaper.

  Require Import Nelist.

  Definition Plus : operator := existT arrows (Tcons Tint (Tcons Tint (Tout Tint))) BinInt.Z.add.
  Opaque Plus.

  Class NPlus U := {plus : U -> U -> U}.
  Notation "x ':+' y" := (plus x y) (at level 47).

  Instance NPlus_lexp : NPlus lexp := {plus := fun x y => Eop Plus (necons x (nebase y))}.
  Instance NPlus_exp : NPlus exp := {plus := fun x y => Op Plus (necons x (nebase y))}.

  Definition Ifte_int : operator :=
    existT arrows (Tcons Tbool (Tcons Tint (Tcons Tint (Tout Tint))))
             (fun (x : bool) t f => if x then t else f).
  Definition op_ifte (x: lexp) (t: lexp) (f: lexp) : lexp :=
    Eop Ifte_int (necons x (necons t (nebase f))).
  Opaque Ifte_int.

  Instance IFTE_lustre : IFTE lexp lexp := {ifte := op_ifte}.
  Instance IFTE_impOp : IFTE exp exp := {ifte := fun x t f => Op Ifte_int (necons x (necons t (nebase f)))}.

  Definition Disj : operator :=
    existT arrows (Tcons Tbool (Tcons Tbool (Tout Tbool))) orb.
  Opaque Disj.

  Class NDisj U := {disj : U -> U -> U}.
  Notation "x ':||' y" := (disj x y) (at level 47).

  Instance NDisj_lexp : NDisj lexp := {disj := fun x y => Eop Disj (necons x (nebase y))}.
  Instance NDisj_exp : NDisj exp := {disj := fun x y => Op Disj (necons x (nebase y))}.

  (* Node names *)
  Definition n_count       : ident := 1.
  Definition n_avgvelocity : ident := n_count + 1.

  (*
  node count (ini, inc: int; restart: bool) returns (n: int)
    var c: int; f: bool;
  let
    n = if f or restart then ini else c + inc;
    f = true fby false;
    c = 0 fby n;
  tel
  *)

  (* counter: variable names *)
  Definition ini       : ident := 1.
  Definition inc       : ident := 2.
  Definition restart   : ident := 3.
  Definition n         : ident := 4.
  Definition f         : ident := 5.
  Definition c         : ident := 6.

  Example count_eqns : list equation :=
    [
      c ::= 0%Z fby n ;
      f ::= true fby false;
      n ::= If ((f : lexp) :|| restart) 
            Then (ini : lexp)
            Else ((c : lexp) :+ inc)
    ].
  (* Print count_eqns. *)

  Definition Div : operator := existT arrows (Tcons Tint (Tcons Tint (Tout Tint))) BinInt.Z.div.
  Opaque Div.

  Class NDiv U := {div : U -> U -> U}.
  Notation "x ':/' y" := (div x y) (at level 47).

  Instance NDiv_lexp : NDiv lexp := {div := fun x y => Eop Div (necons x (nebase y))}.
  Instance NDiv_imp : NDiv exp := {div := fun x y => Op Div (necons x (nebase y))}.


  Lemma count_eqns_well_sch :
    Is_well_sch (PS.add f (PS.singleton c))
                (ini :,: inc :,: restart§) count_eqns.
  Proof. apply Is_well_sch_by_refl; reflexivity. Qed.

  Example count : node :=
    mk_node n_count (necons ini (necons inc (nebase restart))) n count_eqns.

  Example count_prog :=
    {|
      c_name := n_count;
      c_input := ini :,: inc :,: restart §;
      c_output := n;
      c_mems := [f; c];
      c_objs := [];
      c_step := n ::=
                  (If (State f) :|| restart
                  Then (ini : exp)
                  Else ((State c) :+ inc));;
                state(| f |)::= false;;
                state(| c |)::= n;;
                Skip;
      c_reset := state(| f |)::= true;;
                 state(| c |)::= 0%Z;;
                 Skip
    |}.
  

  Remark count_prog_good: translate_node count = count_prog.
  Proof eq_refl.

  Remark count_prog_step_fuse:
    fuse (c_step count_prog) =
         n ::= (If (State f) :|| restart
                Then (ini : exp)
                Else ((State c) :+ inc));;
         state(| f |)::= false;;
         state(| c |)::= n.
  Proof eq_refl.

  Remark count_prog_reset_fuse:
    fuse (c_reset count_prog) = state(| f |)::= true;; state(| c |)::= 0%Z.
  Proof eq_refl.

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
      h ::= 0%Z fby v;
      v ::= (Emerge sec
                    (Ewhen r sec true :/ t)
                    (Ewhen h sec false));
      t ::= n_count (| (Ewhen 1%Z sec true) :,:
                       (Ewhen 1%Z sec true) :,:
                       (Ewhen false sec true) § |) 
        @  (Con Cbase sec true);
      r ::= n_count (| (0%Z : lexp) :,: (delta : lexp) :,: (false : lexp) § |)
    ].
  (* Print avgvelocity_eqns. *)

  Lemma avgvelocity_eqns_Well_sch :
    Is_well_sch (PS.singleton h) (delta :,: sec§) avgvelocity_eqns.
  Proof. apply Is_well_sch_by_refl; reflexivity. Qed.

  Example avgvelocity : node :=
    mk_node n_avgvelocity (delta :,: sec§) v avgvelocity_eqns.

Print Grammar constr.

  Example avgvelocity_prog :=
    {|
      c_name := n_avgvelocity;
      c_input := delta :,: sec §;
      c_output := v;
      c_mems := [h];
      c_objs := [{| obj_inst := r; obj_class := n_count |};
                 {| obj_inst := t; obj_class := n_count |}];
      c_step := (r ::= n_count (| r |).step((0%Z : exp) :,: 
                                            (delta : exp) :,: 
                                            (false : exp) §));;
                If sec
                Then (t ::= n_count (| t |).step((1%Z : exp) :,: 
                                                 (1%Z : exp) :,: 
                                                 (false : exp) §))
                Else Skip;;
                If sec
                Then v ::=  ((r : exp) :/ (t : exp))
                 Else v ::= (State h);;
                state(| h |)::= v;;
                Skip;
      c_reset := n_count (| r |).reset() ;;
                 n_count (| t |).reset();;
                 state(| h |)::= 0%Z;;
                 Skip
    |}.

  Remark avgvelocity_prog_good: translate_node avgvelocity = avgvelocity_prog.
  Proof eq_refl.

  Remark avgvelocity_prog_step_fuse:
    fuse (c_step avgvelocity_prog) =
         r ::= n_count (| r |).step((0%Z : exp) :,: 
                                    (delta : exp) :,: 
                                    (false : exp) §);;
         If sec
         Then (t ::= n_count (| t |).step((1%Z : exp) :,: 
                                          (1%Z : exp) :,: 
                                          (false : exp) §);;
              v ::= ((r : exp) :/ (t : exp))) 
         Else v ::= State h;;
         state(| h |)::= v.
  Proof eq_refl.

  Remark avgvelocity_prog_reset_fuse:
    fuse (c_reset avgvelocity_prog) = n_count (| r |).reset();;
                                      n_count (| t |).reset();;
                                      state(| h |)::= 0%Z.
  Proof eq_refl.

End CodegenPaper.

