Require cfrontend.Clight.
Require Import lib.Integers.

Require Import Rustre.Common.
Require Import Rustre.Nelist.

Require Import Syn.

Require Import String.
Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Axiom pos_of_str: string -> ident.
Axiom pos_to_str: ident -> string.
Axiom first_unused_ident: unit -> ident.

Definition self_id: ident := pos_of_str "self".
Definition main_id: ident := pos_of_str "main".
Definition step_id (id: ident): ident :=
  pos_of_str ("step_" ++ (pos_to_str id)).

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
  | State x ty => deref_self_field cls x ty
  | Const c ty => translate_const c ty
  end.

Fixpoint list_type_to_typelist (tys: list typ): Ctypes.typelist :=
  match tys with
  | [] => Ctypes.Tnil
  | ty :: tys => Ctypes.Tcons ty (list_type_to_typelist tys)
  end.

Definition funcall (f: ident) (args: list Clight.expr) : Clight.statement :=
  let tys := List.map Clight.typeof args in
  let sig := Ctypes.Tfunction (list_type_to_typelist tys) Ctypes.Tvoid AST.cc_default in
  Clight.Scall None (Clight.Evar f sig) args.

Definition assign (x: ident) (ty: typ) (e: Clight.expr): Clight.statement :=
  Clight.Sassign (Clight.Evar x ty) e.

(* Definition binded_funcall (bind temp f: ident) (ty: typ) (args: list Clight.expr) *)
(*   : Clight.statement := *)
(*    Clight.Ssequence (funcall (Some temp) f ty args) *)
(*                     (assign bind ty (Clight.Etempvar temp ty)). *)

Definition ptr_obj (owner: option ident) (cls obj: ident): Clight.expr :=
  Clight.Eaddrof
    ((match owner with
      | Some owner => deref_self_field owner
      | None => Clight.Evar
      end) obj (type_of_inst cls))
    (type_of_inst_p cls).

Definition step_call (owner: option ident) (cls obj: ident) (args: list Clight.expr)
  : Clight.statement :=
  let args := ptr_obj owner cls obj :: args in
  funcall (step_id cls) args.

Definition make_in_arg (arg: ident * typ): Clight.expr :=
  let (x, ty) := arg in
  Clight.Evar x ty.
Definition make_out_arg (arg: ident * typ): Clight.expr :=
  let (x, ty) := arg in
  Clight.Eaddrof (Clight.Evar x ty) (pointer_of ty).

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
  | Ifte e s1 s2 =>
    Clight.Sifthenelse (translate_exp owner e)
                       (translate_stmt owner s1) (translate_stmt owner s2)
  | Comp s1 s2 =>
    Clight.Ssequence (translate_stmt owner s1) (translate_stmt owner s2)
  | Step_ap ys cls x es =>
    let args := nelist2list (Nelist.map (translate_exp owner) es) in
    let outs := nelist2list (Nelist.map make_out_arg ys) in
    step_call (Some owner) cls x (args ++ outs)  
  | Skip =>
    Clight.Sskip
  end.

(* Definition return_some (s: Clight.statement) (out: ident * typ): Clight.statement := *)
(*   let (id, ty) := out in *)
(*   Clight.Ssequence s (Clight.Sreturn (Some (Clight.Evar id ty))). *)
Definition return_none (s: Clight.statement): Clight.statement :=
  Clight.Ssequence s (Clight.Sreturn None).
Definition cl_zero: Clight.expr :=
  Clight.Econst_int Int.zero Ctypes.type_int32s.
Definition return_zero (s: Clight.statement): Clight.statement :=
  Clight.Ssequence s (Clight.Sreturn (Some cl_zero)).

Definition fundef
           (ins: list (ident * typ)) (vars: list (ident * typ)) (ty: typ) (body: Clight.statement)
  : AST.globdef Clight.fundef Ctypes.type :=
  let f := Clight.mkfunction ty AST.cc_default ins vars [] body in
  @AST.Gfun Clight.fundef typ (Ctypes.Internal f).

Definition make_step
           (self: ident * typ) (ins: list (ident * typ)) (outs: list (ident * typ))
           (vars: list (ident * typ)) (body: Clight.statement)
  : AST.globdef Clight.fundef Ctypes.type :=
  let body := return_none body in
  fundef (self :: ins ++ outs) vars Ctypes.Tvoid body.

Definition translate_obj_dec (obj: obj_dec): (ident * typ) :=
  match obj with
    mk_obj_dec inst cls =>
    (inst, type_of_inst cls)
  end.

Definition make_struct (cls: ident) (members: list (ident * typ))
  : Ctypes.composite_definition :=
  Ctypes.Composite cls Ctypes.Struct members Ctypes.noattr.

Definition translate_class (c: class)
  : Ctypes.composite_definition * (ident * AST.globdef Clight.fundef Ctypes.type) :=
  match c with
    mk_class c_name c_input c_output c_vars c_mems c_objs c_step =>
    let objs := List.map translate_obj_dec c_objs in
    let members := c_mems ++ objs in
    let step := translate_stmt c_name c_step in
    let self := (self_id, type_of_inst_p c_name) in
    let cl_struct := make_struct c_name members in
    let cl_step := (step_id c_name, make_step self (nelist2list c_input) (nelist2list c_output) c_vars step) in
    (cl_struct, cl_step)
  end.

Definition glob_id (id: ident): ident :=
  pos_of_str ("_" ++ (pos_to_str id)).
Definition glob_bind (bind: ident * typ): ident * typ :=
  let (x, ty) := bind in
  (glob_id x, ty).

Definition make_main (node: ident) (f: ident) (ins: list (ident * typ)) (outs: list (ident * typ))
  : AST.globdef Clight.fundef Ctypes.type :=
  let args_in := List.map make_in_arg ins in
  let args_out := List.map make_out_arg outs in
  let step := step_call None node f (args_in ++ args_out) in
  let loop := Clight.Sloop ((* Clight.Ssequence wait *) step) Clight.Sskip in
  let body := return_zero ((* Clight.Ssequence (reset_call None node f) *) loop) in
  fundef [] [] Ctypes.type_int32s body.

Definition vardef (init volatile: bool) (x: ident * typ): ident * AST.globdef Clight.fundef Ctypes.type :=
  let (x, ty) := x in
  let ty' := Ctypes.merge_attributes ty (Ctypes.mk_attr volatile None) in
  (x, @AST.Gvar Clight.fundef _
                (AST.mkglobvar ty' (if init then [AST.Init_space Z0] else []) false volatile)).

Definition translate (p: program) (main_node: ident): Errors.res Clight.program :=
  match find_class main_node p with
  | Some (cls, _) =>
    let f := glob_id main_node in
    let ins := map glob_bind (nelist2list cls.(c_input)) in
    let outs := map glob_bind (nelist2list cls.(c_output)) in
    let main := make_main main_node f ins outs in
    let cs := List.map translate_class p in
    let f_gvar := vardef true false (f, type_of_inst main_node) in
    let o_gvars := map (vardef true true) outs in
    let i_gvars := map (vardef true true) ins in
    let (structs, steps) := split cs in
    let gdefs := f_gvar :: o_gvars ++ i_gvars ++ steps ++ [(main_id, main)] in
    Ctypes.make_program structs gdefs [] main_id                    
  | None => Errors.Error (Errors.msg "undefined node")
  end.
