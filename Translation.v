Require Import Coq.FSets.FMapPositive.
Require Import PArith.
Require Import Rustre.Common.
Require Import Rustre.Minimp.
Require Import Rustre.DataflowSyntax.


(** * Translation *)

Record state : Set := mk_state {
  st_mem : list ident;        (* m *)
  st_objs : list obj_dec;     (* j *)
  st_instrs : stmt            (* L *)
}.

Fixpoint new_objs_eq (symap: (ident * PM.t obj_dec)%type) (eq: equation)
  : (ident * PM.t obj_dec)%type :=
  match eq with
  | EqApp x f _ =>
    match symap with
    | (o, map) => (Pos.succ o, PM.add x (mk_obj_dec o f) map)
    end
  | _ => symap
  end.

Definition new_objs (eqns: list equation) : PM.t obj_dec :=
  snd (List.fold_left new_objs_eq eqns (1%positive, PM.empty obj_dec)).

Section Translate.

  Variable memories : PS.t.
  (* create this using new_objs ? *)
  (* Variable objects : PM.t obj_dec. *)

  Definition tovar (x: ident) : exp :=
    if PS.mem x memories then State x else Var x.

  Fixpoint Control (ck: clock)(s: stmt): stmt :=
    match ck with
    | Cbase => s
    | Con ck x true => Control ck (Ifte (tovar x) s Skip)
    | Con ck x false => Control ck (Ifte (tovar x) Skip s)
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

  Fixpoint translate_cexp (x: ident)(e : cexp): stmt :=
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
      (* TODO: should the 2nd x reference an object declaration?
               i.e., objects x*)
      Control ck (Step_ap x x (translate_lexp le))
    | EqFby x v (LAexp ck le) =>
      Control ck (AssignSt x (translate_lexp le))
    end.

  (* NB: eqns ordered in reverse order of execution for coherence
         with Is_well_sch. *)
  Definition translate_eqns (eqns: list equation): stmt :=
    List.fold_left (fun i eq => Comp (translate_eqn eq) i) eqns Skip.

End Translate.

Definition translate_node (n: node): class_def :=
  let mems := memories n.(n_eqs) in
  let s :=
      mk_state (PS.elements mems) List.nil (translate_eqns mems n.(n_eqs)) in
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
      EqDef 4 (CAexp Cbase (Emerge 1 (CAexp (Con Cbase 1 true) (Eexp (Evar 2)))
                                   (CAexp (Con Cbase 1 false) (Eexp (Evar 3)))));
      EqFby 3 (Cint 0) (LAexp (Con Cbase 1 false) (Evar 2));
      EqDef 2 (CAexp (Con Cbase 1 true) (Eexp (Econst (Cint 7))))
    ].

  Definition node1 : node :=
    mk_node 1 (mk_var 1 Cbase) (mk_var 4 Cbase) eqns1.

  Eval cbv in (translate_node node1).

  Definition prog1 : stmt :=
    Comp (Ifte (Var 1) (Assign 2 (Const (Cint 7)))
                       Skip)
   (Comp (Ifte (Var 1) Skip
                       (AssignSt 3 (Var 2)))
   (Comp (Ifte (Var 1) (Assign 4 (Var 2))
                       (Assign 4 (State 3)))
         Skip)).

  Lemma prog1_good : (translate_node node1).(c_step).(body) = prog1.
  Proof eq_refl.

End TestTranslate.
