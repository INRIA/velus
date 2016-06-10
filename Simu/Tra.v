Require cfrontend.Clight.
Require Import lib.Integers.

Require Import Rustre.Common.

Require Import Syn.

Require Import String.
Require Import List.
Import List.ListNotations.
Open Scope list_scope.

(* TRANSLATION *)
Definition type_of_inst (o: ident): typ :=
  Ctypes.Tstruct o Ctypes.noattr.
Definition pointer_of (ty: typ): typ :=
  Ctypes.Tpointer ty Ctypes.noattr.
Definition type_of_inst_p (o: ident): typ :=
  pointer_of (type_of_inst o).

Definition deref_self_field (cls x: ident) (ty: typ): Clight.expr :=
  let ty_deref_self := type_of_inst cls in
  let ty_self := pointer_of ty_deref_self in
  Clight.Efield (Clight.Ederef (Clight.Evar self_id ty_self) ty_deref_self) x ty.

Definition translate_const (c: const): typ -> Clight.expr :=
  match c with
  | Cint i => Clight.Econst_int i
  | Cfloat f => Clight.Econst_float f
  | Csingle s => Clight.Econst_single s
  | Clong l => Clight.Econst_long l
  end.

(** Straightforward expression translation *)
Definition translate_exp (cls: ident) (e: exp): Clight.expr :=
  match e with
  | Var x ty => Clight.Evar x ty  
  | State x ty =>
    deref_self_field cls x ty
  | Const c ty => translate_const c ty
  end.

(** 
Statement conversion keeps track of the produced temporaries (function calls).
[owner] represents the name of the current class.
 *)
Fixpoint translate_stmt (owner: ident) (s: stmt): Clight.statement :=
  match s with
  | Assign x e =>
    Clight.Sassign (Clight.Evar x (typeof e)) (translate_exp owner e)
  | AssignSt x e =>
    Clight.Sassign (deref_self_field owner x (typeof e)) (translate_exp owner e)
  | Comp s1 s2 =>
    Clight.Ssequence (translate_stmt owner s1) (translate_stmt owner s2)
  | Skip =>
    Clight.Sskip
  end.

Definition translate_obj_dec (obj: obj_dec): (ident * typ) :=
  match obj with
    mk_obj_dec inst cls =>
    (inst, type_of_inst cls)
  end.

Definition translate_class (c: class)
  : Ctypes.composite_definition :=
  match c with
    mk_class name mems objs _ _ =>
    let objs := List.map translate_obj_dec objs in
    let members := mems ++ objs in
    Ctypes.Composite name Ctypes.Struct members Ctypes.noattr
  end.

Definition cl_zero: Clight.expr :=
  Clight.Econst_int Int.zero Ctypes.type_int32s.
Definition return_zero (s: Clight.statement): Clight.statement :=
  Clight.Ssequence s (Clight.Sreturn (Some cl_zero)).

(** build the main function (entry point) *)
Definition make_main (body: Clight.statement) (vars: list (ident * typ))
  : AST.globdef Clight.fundef Ctypes.type :=
  let body := return_zero body in
  let main := Clight.mkfunction Ctypes.type_int32s AST.cc_default [] vars [] body in
  @AST.Gfun Clight.fundef typ (Clight.Internal main).

Definition glob_id (id: ident): ident :=
  pos_of_str ("_" ++ (pos_to_str id)).

Definition translate (p: program) (main_node: ident)
  : Errors.res Clight.program :=
  let structs := List.map translate_class p in
  match find_class main_node p with
    | Some (cls, _) =>
      let main := make_main (translate_stmt main_node cls.(c_step)) cls.(c_vars) in
      Clight.make_program structs [(main_id, main)] [] main_id
    | None => Errors.Error (Errors.msg "undefined node")
  end.
