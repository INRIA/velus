Require Import Rustre.Minimp.Syntax.
Require Import Rustre.Common.
Require Import Rustre.Nelist.
Require Import Rustre.Interface.

Module Import Syn := SyntaxFun Op.

Require common.AST.
Require common.Errors.
Require cfrontend.Ctypes.
Require cfrontend.Clight.
Require cfrontend.Cop.
Require driver.Compiler.

Require Import String.

(* Open Scope string_scope. *)
Open Scope list_scope.
Import List.ListNotations.

Axiom pos_of_str: String.string -> ident.
Axiom pos_to_str: ident -> String.string.

Definition example :=
  {|
    c_name := pos_of_str "count";
    c_input := nebase (pos_of_str "i");
    c_output := pos_of_str "o";
    c_mems := [pos_of_str "t"];
    c_objs := [];
    c_step := Comp (Assign (pos_of_str "o")
                           (Binop Plus
                                  (Syn.State (pos_of_str "t"))
                                  (Var (pos_of_str "i"))))
                   (AssignSt (pos_of_str "t") (Var (pos_of_str "o")));
    c_reset := AssignSt (pos_of_str "t") (Const Vzero)
  |}.

Definition cl_type := Ctypes.type.
Definition cl_typelist := Ctypes.typelist.
Definition cl_expr := Clight.expr.
Definition cl_stmt := Clight.statement.
Definition cl_bool := Ctypes.type_bool.
Definition cl_int := Ctypes.type_int32s.
Definition cl_ident := AST.ident.
Definition cl_bind := prod cl_ident cl_type.
Definition cl_globdef := AST.globdef Clight.fundef Ctypes.type.
Definition cl_structdef := Ctypes.composite_definition.

(** Common identifiers  *)
Definition main_id: ident := pos_of_str "main".
Definition step_id (id: cl_ident): ident :=
  pos_of_str (String.append "step_" (pos_to_str id)).
Definition reset_id (id: cl_ident): ident :=
  pos_of_str (String.append "reset_" (pos_to_str id)).
Definition self_id: ident := pos_of_str "self".

(** struct types  *)
Definition type_of_inst (o: cl_ident): cl_type :=
  Ctypes.Tstruct o Ctypes.noattr.
Definition type_of_inst_p (o: cl_ident): cl_type :=
  Ctypes.Tpointer (type_of_inst o) Ctypes.noattr.

(** Constants  *)
Definition cl_true: cl_expr := Clight.Econst_int one cl_bool.
Definition cl_false: cl_expr := Clight.Econst_int zero cl_bool.
Definition cl_zero: cl_expr := Clight.Econst_int zero cl_int.

Definition translate_const (c: Op.val): cl_expr :=
  Clight.Econst_int (Integers.Int.repr Z0) cl_int.

Definition translate_type (ty: base_type): cl_type :=
  match ty with
  | Tint => cl_int
  | Tbool => cl_bool
  end.

Definition translate_unop (op: Op.unary_op) (e: cl_expr): cl_expr :=
  match op with
  | Opposite => Clight.Eunop Cop.Oneg e cl_int
  | Negation => Clight.Eunop Cop.Onotbool e cl_int
  end.

Definition translate_binop (op: Op.binary_op) (e1 e2: cl_expr): cl_expr :=
  match op with
  | Plus => Clight.Ebinop Cop.Oadd e1 e2 cl_int
  | Minus => Clight.Ebinop Cop.Osub e1 e2 cl_int
  | Mult => Clight.Ebinop Cop.Omul e1 e2 cl_int
  end.

(** Straightforward expression translation *)
Fixpoint translate_exp (e: exp): cl_expr :=
  let ty := Common.Tint in
  match e with
  | Var x (* ty *) => Clight.Evar x (translate_type ty)  
  | State x (* ty *) => Clight.Evar x (translate_type ty) 
  | Const c (* ty *) => translate_const c
  | Unop op e (* ty *) =>
    translate_unop op (translate_exp e)
  | Binop op e1 e2 (* ty *) =>
    translate_binop op (translate_exp e1) (translate_exp e2)
  end.

Fixpoint list_type_to_typelist (tys: list cl_type): cl_typelist :=
  match tys with
  | [] => Ctypes.Tnil
  | ty :: tys => Ctypes.Tcons ty (list_type_to_typelist tys)
  end.

(** pointer expressions  *)
Definition pointer_of_cls (x cls: cl_ident): cl_expr :=
  Clight.Eaddrof (Clight.Evar x (type_of_inst cls)) (type_of_inst_p cls).

(** function call and assignment *)
(* Q: Can we really use same ident for temporary and classic variables ? *)
Definition funcall
           (bind: option cl_ident) (f: cl_ident) (sig: cl_type)
           (args: list cl_expr)
  : cl_stmt :=
  Clight.Scall bind (Clight.Evar f sig) args.

Definition assign (bind: cl_ident) (ty: cl_type) (e: cl_expr): cl_stmt :=
  Clight.Sassign (Clight.Evar bind ty) e.

Definition st_assign (name x: cl_ident) (e: cl_expr): cl_stmt :=
  let ty_self := type_of_inst_p name in
  let ty_deref_self := type_of_inst name in
  Clight.Sassign
    (Clight.Efield (Clight.Ederef (Clight.Evar self_id ty_self) ty_deref_self) x
                   (Clight.typeof e)) e.
                 
Definition binded_funcall (bind f: cl_ident) (ty: cl_type) (args: list cl_expr)
  : cl_bind * cl_stmt :=
  let temp := bind in
  let tys := List.map Clight.typeof args in
  let sig := Ctypes.Tfunction (list_type_to_typelist tys) ty AST.cc_default in
  ((temp, ty),
   Clight.Ssequence (funcall (Some temp) f sig args)
                    (assign bind ty (Clight.Etempvar temp ty))).

Definition reset_call (cls obj: cl_ident): cl_stmt :=
  let ty_reset :=
      Ctypes.Tfunction (Ctypes.Tcons (type_of_inst_p cls) Ctypes.Tnil)
                       Ctypes.Tvoid AST.cc_default
  in
  funcall None (reset_id cls) ty_reset [pointer_of_cls obj cls].

Definition step_call
           (bind cls: cl_ident) (obj: cl_ident) (args: list cl_expr)
           (out_ty: cl_type)
  : cl_bind * cl_stmt :=
  let args := pointer_of_cls obj cls :: args in
  binded_funcall bind (step_id cls) out_ty args.

(** 
Statement conversion keeps track of the produced temporaries (function calls). 
[name] represents the name of the current class.
 *)
Fixpoint translate_stmt (temps: list cl_bind) (name: cl_ident) (s: stmt)
  : (list cl_bind * cl_stmt) :=
  match s with
  | Syn.Assign x e =>
    let ty := (* Syn.typeof e *) Common.Tint in
    (temps, assign x (translate_type ty) (translate_exp e))
  | Syn.AssignSt x e =>
    (temps, st_assign name x (translate_exp e))
  | Syn.Ifte e s1 s2 =>
    let (temps1, s1') := translate_stmt temps name s1 in
    let (temps2, s2') := translate_stmt temps1 name s2 in
    (temps2, Clight.Sifthenelse (translate_exp e) s1' s2')
  | Syn.Step_ap y cls x es (* ty *) =>
    let ty := Common.Tint in
    let args := nelist2list (Nelist.map translate_exp es) in
    let out_ty := translate_type ty in
    let (temp, s_step) := step_call y cls x args out_ty in 
    (temp :: temps, s_step)
  | Syn.Reset_ap cls x =>
    (temps, reset_call cls x)
  | Syn.Comp s1 s2 =>
    let (temps1, s1') := translate_stmt temps name s1 in
    let (temps2, s2') := translate_stmt temps1 name s2 in
    (temps2, Clight.Ssequence s1' s2')
  | Syn.Skip =>
    (temps, Clight.Sskip)
  end.

(** return statements  *)
Definition return_some (s: cl_stmt) (out: cl_bind): cl_stmt :=
  let (id, ty) := out in
  Clight.Ssequence s (Clight.Sreturn (Some (Clight.Evar id ty))).
Definition return_none (s: cl_stmt): cl_stmt :=
  Clight.Ssequence s (Clight.Sreturn None).
Definition return_zero (s: cl_stmt): cl_stmt :=
  Clight.Ssequence s (Clight.Sreturn (Some cl_zero)).

Definition fundef
           (ins: list cl_bind) (out: option cl_bind) (ty: cl_type)
           (temps: list cl_bind) (body: cl_stmt)
  : cl_globdef :=
  let out := match out with Some o => [o] | None => [] end in 
  let f := Clight.mkfunction ty AST.cc_default ins out temps body in
  @AST.Gfun Clight.fundef cl_type (Clight.Internal f).

(** build the step function *)
Definition make_step
           (self: cl_bind) (ins: list cl_bind) (out: cl_bind)
           (temps: list cl_bind) (body: cl_stmt)
  : cl_globdef :=
  let body := return_some body out in
  fundef (self :: ins) (Some out) (snd out) temps body.

Fixpoint seq_of_statements (sl: list cl_stmt): cl_stmt :=
  match sl with
  | [] => Clight.Sskip
  | s :: sl' => Clight.Ssequence s (seq_of_statements sl')
  end.

Definition reset_obj (obj: obj_dec): cl_stmt :=
  reset_call (obj_class obj) (obj_inst obj).

(** build the reset function *)
Definition make_reset
           (self: cl_bind) (objs: list obj_dec) (temps: list cl_bind)
           (body: cl_stmt)
  : cl_globdef :=
  let seq_res := seq_of_statements (body :: (List.map reset_obj objs)) in
  let body := return_none seq_res in
  fundef [self] None Ctypes.Tvoid temps body.

Definition translate_ident (id: ident): cl_ident := id.

Definition translate_obj_dec (obj: obj_dec): cl_bind :=
  match obj with
    mk_obj_dec inst cls =>
    let inst := translate_ident inst in
    let cls := translate_ident cls in
    (inst, type_of_inst cls)
  end.

Definition translate_param (p: ident): cl_bind :=
  let (id, ty) := (p, Common.Tint) in
  (translate_ident id, translate_type ty).

(** build the structure *)
Definition make_struct (name: cl_ident) (members: list cl_bind)
 : cl_structdef :=
  Ctypes.Composite name Ctypes.Struct members Ctypes.noattr.

(** translate a class into a triple: structure, step function, reset function  *)
Definition translate_class (c: class)
 : cl_structdef * (cl_ident * cl_globdef) * (cl_ident * cl_globdef) :=
  match c with
    mk_class c_name c_input c_output c_mems c_objs c_step c_reset =>
    let mems := List.map translate_param c_mems in
    let objs := List.map translate_obj_dec c_objs in
    let ins := nelist2list (Nelist.map translate_param c_input) in
    let out := translate_param c_output in
    let members := mems ++ objs in
    let name := translate_ident c_name in
    let (temps_step, step) := translate_stmt [] name c_step in
    let (temps_reset, reset) := translate_stmt [] name c_reset in
    let self := (self_id, type_of_inst_p name) in
    let cl_struct := make_struct name members in
    let cl_step := (step_id name, make_step self ins out temps_step step) in
    let cl_reset := (reset_id name, make_reset self c_objs temps_reset reset) in
    (cl_struct, cl_step, cl_reset) 
  end.

(** build the main function (entry point) *)
Definition make_main
           (node: cl_ident) (f: cl_ident) (ins: nelist cl_ident) (out: cl_ident)
 : cl_globdef :=
  let ty := Common.Tint in
  let args := nelist2list (Nelist.alls cl_zero ins) in
  let out_ty := translate_type ty in
  let (temp, step) := step_call out node f args out_ty in
  let loop := Clight.Swhile cl_true step in
  let body := return_zero (Clight.Ssequence (reset_call node f) loop) in
  fundef [] None cl_int [temp] body.

Definition split_3 {A B C: Type} (l: list (A * B * C))
 : list A * list B * list C :=
  List.fold_right (fun (xyz: A * B * C) (abc: list A * list B * list C) =>
                     match xyz with
                       (x, y, z) => match abc with
                                     (a, b, c) => (x :: a, y :: b, z :: c)
                                   end
                     end
                  ) ([], [], []) l.

Definition vardef (ty: cl_type) (volatile: bool): cl_globdef :=
  @AST.Gvar Clight.fundef cl_type (AST.mkglobvar ty [] false volatile).

(** translation function: the main instance is declared as 'extern' and it's 
step function's return variable as 'volatile' *)
Definition translate (p: program) (main_node: ident)
  : Errors.res Clight.program :=
  let main_node := translate_ident main_node in
  match find_class main_node p with
  | Some (cls, _) =>
    let f := pos_of_str "f_" in
    let o := pos_of_str "o_" in
    let f_gvar := vardef (type_of_inst main_node) false in
    let o_gvar := vardef cl_int true in
    let main := make_main main_node f (c_input cls) o in
    let cs := List.map translate_class p in
    match split_3 cs with
      (structs, steps, resets) =>
      let gdefs := (o, o_gvar) :: (f, f_gvar) ::
                               resets ++ steps ++ [(main_id, main)]
      in
      Clight.make_program structs gdefs [] main_id                    
    end
  | None => Errors.Error (Errors.msg "undefined node")
  end. 

Definition compile (p: Syn.program) (main_node: cl_ident)
  : Errors.res Asm.program :=
  match translate p main_node with
  | Errors.OK p => Compiler.transf_clight_program p
  | Errors.Error res => Errors.Error res
  end.