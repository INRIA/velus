Require Import Rustre.Common.


(** * Dataflow language *)

Inductive clock : Set :=
| Cbase : clock                          (* base clock *)
| Con : clock -> ident -> bool -> clock. (* subclock *)

Record var_dec : Set := mk_var { v_name : ident;
                                 v_clock : clock }.

(** ** Syntax *)

(* TODO: laexp: would be nicer if it were a record *)
Inductive laexp : Type :=
  | LAexp : clock -> lexp -> laexp
with lexp : Type :=
  | Econst : const -> lexp
  | Evar : ident -> lexp
  | Ewhen : laexp -> ident -> bool -> lexp.
(* External operators are missing *)

Scheme laexp_mult := Induction for laexp Sort Prop
with lexp_mult := Induction for lexp Sort Prop.

(* TODO: caexp: would be nicer if it were a record *)
Inductive caexp : Type :=
  | CAexp : clock -> cexp -> caexp
with cexp : Type :=
  | Emerge : ident -> caexp -> caexp -> cexp (* currently only binary merge *)
  | Eexp : lexp -> cexp.

Scheme caexp_mult := Induction for caexp Sort Prop
with cexp_mult := Induction for cexp Sort Prop.

(** ** Equations *)

Inductive equation : Type :=
  | EqDef : ident -> caexp -> equation
  | EqApp : ident -> ident -> laexp -> equation
  | EqFby : ident -> const -> laexp -> equation.

Record node : Type := mk_node {
  n_name : ident;
  n_input : var_dec;
  n_output : var_dec;
  n_eqs : list equation }.

(** ** Predicates *)

Require Coq.MSets.MSets.

Module PS := Coq.MSets.MSetPositive.PositiveSet.

Fixpoint freevar_lexp' (e : lexp) (fvs : PS.t) : PS.t :=
  match e with
    | Econst c => fvs
    | Evar x => PS.add x fvs
    | Ewhen ae c x => freevar_laexp' ae fvs
  end
with freevar_laexp' (lae : laexp) (fvs : PS.t) : PS.t :=
  match lae with
    | LAexp ck e => freevar_lexp' e fvs
  end.

(* Definition freevar_lexp e := freevar_lexp' e PS.empty. *)
(* Definition freevar_laexp lae := freevar_laexp' lae PS.empty. *)

Inductive freevar_lexp : lexp -> ident -> Prop :=
| FreeEvar: forall x, freevar_lexp (Evar x) x
| FreeEwhen: forall ae ck cv x,
    freevar_laexp ae x ->
    freevar_lexp (Ewhen ae ck cv) x
with freevar_laexp : laexp -> ident -> Prop :=
| freeLAexp: forall ck e x,
    freevar_lexp e x ->
    freevar_laexp (LAexp ck e) x.

Fixpoint freevar_caexp' (cae: caexp) (fvs: PS.t) : PS.t :=
  match cae with
  | CAexp ck ce => freevar_cexp' ce fvs
  end
with freevar_cexp' (ce: cexp) (fvs: PS.t) : PS.t :=
  match ce with
  | Emerge x t f => PS.add x (freevar_caexp' f (freevar_caexp' t fvs))
  | Eexp e => freevar_lexp' e fvs
  end.

(* Definition freevar_caexp cae := freevar_caexp' cae PS.empty. *)

Inductive freevar_cexp : cexp -> ident -> Prop :=
| FreeEmerge_cond: forall i t f,
    freevar_cexp (Emerge i t f) i
| FreeEmerge_true: forall i t f x,
    freevar_caexp t x ->
    freevar_cexp (Emerge i t f) x
| FreeEmerge_false: forall i t f x,
    freevar_caexp f x ->
    freevar_cexp (Emerge i t f) x
| FreeEexp: forall e x,
    freevar_lexp e x ->
    freevar_cexp (Eexp e) x
with freevar_caexp : caexp -> ident -> Prop :=
| FreeCAexp: forall ck ce x,
    freevar_cexp ce x ->
    freevar_caexp (CAexp ck ce) x.

Fixpoint memory_eq (mems: PS.t) (eq: equation) : PS.t :=
  match eq with
  | EqFby x _ _ => PS.add x mems
  | _ => mems
  end.

Definition memories (eqs: list equation) : PS.t :=
  List.fold_left memory_eq eqs PS.empty.


Fixpoint defined_eq (defs: PS.t) (eq: equation) : PS.t :=
  match eq with
  | EqDef x _   => PS.add x defs
  | EqApp x _ _ => PS.add x defs
  | EqFby x _ _ => PS.add x defs
  end.

Definition defined (eqs: list equation) : PS.t :=
  List.fold_left defined_eq eqs PS.empty.

(** The map containing global definitions. *)
Require Coq.FSets.FMapPositive.
Definition global := FSets.FMapPositive.PositiveMap.t node.

