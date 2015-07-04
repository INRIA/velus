Require Import Coq.FSets.FMapPositive.
Require Import PArith.
Require Import Rustre.Common.
Require Import Rustre.Minimp.
Require Import Rustre.DataflowSyntax.


(** * Translation *)

Record state : Set := mk_state {
  st_sym : BinNums.positive;  (** symbol generator *)
  st_mem : list ident;        (* m *)
  st_objs : list obj_dec;     (* j *)
  st_instrs : stmt            (* L *)
}.

Definition Compiler (A : Type): Type
  := state -> state * A.

Definition retc {A}(a: A): Compiler A :=
  fun s => (s, a).
Notation "ret!" := (retc).

Definition bind {A B} (c : Compiler A) (f : A -> Compiler B) : Compiler B :=
  fun s => let (s', a) := c s in
           f a s'.
Notation "x <- c ; f" := (bind c (fun x => f))
    (right associativity, at level 84, c1 at next level).

Definition add_instr (stmt: stmt): Compiler unit :=
  fun s =>
    (mk_state s.(st_sym) s.(st_mem)
              s.(st_objs) (Comp stmt s.(st_instrs)), 
     tt).

Definition add_mem (m: ident): Compiler unit :=
  fun s =>
    (mk_state s.(st_sym) (m :: s.(st_mem))
              s.(st_objs) s.(st_instrs),
     tt).

Definition gensym: Compiler ident :=
  fun s =>
    let fresh := s.(st_sym) in
    (mk_state (Pos.succ fresh) s.(st_mem) s.(st_objs) s.(st_instrs),
     fresh).
    

Definition add_obj (o: obj_dec): Compiler unit :=
  fun s => 
    (mk_state s.(st_sym) 
              s.(st_mem)
              (o :: s.(st_objs)) 
              s.(st_instrs),
     tt).

Definition new_obj (cls: ident): Compiler ident :=
  o <- gensym;
  let obj := mk_obj_dec o cls in
  _ <- add_obj obj ;
  ret! o.

Definition runCompiler (c: Compiler unit): state :=
  let empty_s := mk_state 1 nil nil Skip in
  fst (c empty_s).


Fixpoint translate_lexp (e: lexp): exp :=
  match e with
    | Econst c => Const c
    | Evar x => Var x
    | Ewhen ae c x => translate_laexp ae
  end
with translate_laexp (lae: laexp): exp :=
  match lae with
    | LAexp ck e => translate_lexp e
  end.

Fixpoint translate_cexp (x: ident)(e : cexp): stmt :=
  match e with
    | Emerge y t f => Ifte y (translate_caexp x t) (translate_caexp x f)
    | Eexp l => Assign x (translate_lexp l)
  end
with translate_caexp (x: ident)(ae : caexp): stmt :=
  match ae with
    | CAexp ck e => translate_cexp x e
  end.

Fixpoint Control (ck: clock)(s: stmt): stmt :=
  match ck with
    | Cbase => s
    | Con ck x true => Control ck (Ifte x s Skip)
    | Con ck x false => Control ck (Ifte x Skip s)
  end.

Definition translate_eqn (eqn: equation): Compiler unit :=
  match eqn with
    | EqDef x (CAexp ck ce) =>
      let s := Control ck (translate_cexp x ce) in
      add_instr s
    | EqApp x f (LAexp ck le) =>
      let c := translate_lexp le in
      o <- new_obj f;
      add_instr (Control ck (Step_ap x o c))
    | EqFby x v (LAexp ck le) =>
      let c := translate_lexp le in
      let s := Control ck (AssignSt x c) in
      _ <- add_mem x;
      add_instr s
  end.

Fixpoint translate_eqns (eqns: list equation): Compiler unit :=
  match eqns with
    | nil => ret! tt
    | cons eqn eqns =>
      _ <- translate_eqns eqns ;
      translate_eqn eqn
  end.

Definition translate_node (n: node): class_def :=
  let s := runCompiler (translate_eqns n.(n_eqs)) in
  mk_class n.(n_name)
           s.(st_objs)
           (mk_step_fun n.(n_input).(v_name)
                        n.(n_output).(v_name)
                        s.(st_mem)
                        s.(st_instrs)).

(* Define and translate a simple node. *)
Section TestTranslate.
  
  Import List.ListNotations.
  Open Scope positive.
  Open Scope list.

  Definition eqns1 : list equation :=
    [
      EqDef 2 (CAexp (Con Cbase 1 true) (Eexp (Econst (Cint 7))));
      EqFby 3 (Cint 0) (LAexp (Con Cbase 1 false) (Evar 2));
      EqDef 4 (CAexp Cbase (Emerge 1 (CAexp (Con Cbase 1 true) (Eexp (Evar 2)))
                                   (CAexp (Con Cbase 1 false) (Eexp (Evar 3)))))
    ].
  
  Definition node1 : node :=
    mk_node 1 (mk_var 1 Cbase) (mk_var 4 Cbase) eqns1.
  
  Eval cbv in (translate_node node1).
  
  Definition prog1 : stmt :=
    Comp (Ifte 1 (Assign 2 (Const (Cint 7)))
                 Skip)
   (Comp (Ifte 1 Skip
                 (AssignSt 3 (Var 2)))
   (Comp (Ifte 1 (Assign 4 (Var 2))
                 (Assign 4 (Var 3)))
         Skip)).

End TestTranslate.
