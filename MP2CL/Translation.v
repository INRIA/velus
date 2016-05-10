Require Import Rustre.Minimp.Syntax.
Require Import Rustre.Common.
Require Import Rustre.Nelist.
Require Import Rustre.Interface.
Require Import Coq.FSets.FMapPositive.

Module Import Syn := SyntaxFun Op.

(* Require Import Rustre.Minimp.Semantics. *)
(* Module Import Sem := SemanticsFun Op Syn. *)

Require common.AST.
Require common.Errors.
Require cfrontend.Ctypes.
Require cfrontend.Clight.
Require cfrontend.Cop.
(* Require driver.Compiler. *)

Require Import String.

(* Open Scope string_scope. *)
Open Scope list_scope.
Import List.ListNotations.

Axiom pos_of_str: string -> ident.
Axiom pos_to_str: ident -> string.
Axiom first_unused_ident: unit -> ident.

Definition cl_type := Ctypes.type.
Definition cl_typelist := Ctypes.typelist.
Definition cl_expr := Clight.expr.
Definition cl_stmt := Clight.statement.
Definition cl_bool := Ctypes.type_bool.
Definition cl_int := Ctypes.type_int32s.
Definition cl_void := Ctypes.Tvoid.
Definition cl_float := Ctypes.Tfloat Ctypes.F32 Ctypes.noattr.
Definition cl_ident := AST.ident.
Definition cl_bind := prod cl_ident cl_type.
Definition cl_globdef := AST.globdef Clight.fundef Ctypes.type.
Definition cl_structdef := Ctypes.composite_definition.

(** Common identifiers  *)
Definition main_id: ident := pos_of_str "main".
Definition step_id (id: cl_ident): ident :=
  pos_of_str ("step_" ++ (pos_to_str id)).
Definition reset_id (id: cl_ident): ident :=
  pos_of_str ("reset_" ++ (pos_to_str id)).
Definition self_id: ident := pos_of_str "self".
Definition wait_id: ident := pos_of_str "wait".
Definition delay_id: ident := pos_of_str "delay".

(** struct types  *)
Definition type_of_inst (o: cl_ident): cl_type :=
  Ctypes.Tstruct o Ctypes.noattr.
Definition pointer_of (ty: cl_type): cl_type :=
  Ctypes.Tpointer ty Ctypes.noattr.
Definition type_of_inst_p (o: cl_ident): cl_type :=
  pointer_of (type_of_inst o).

(** Constants  *)
Definition cl_true: cl_expr := Clight.Econst_int one cl_bool.
Definition cl_false: cl_expr := Clight.Econst_int zero cl_bool.
Definition cl_zero: cl_expr := Clight.Econst_int zero cl_int.

Definition translate_ident (id: ident): cl_ident := id.

Definition translate_const (c: val): cl_type -> cl_expr :=
  match c with
  | Vbool b => Clight.Econst_int (if b then one else zero)
  | Val v =>
    match v with
    (* | Vundef => *)
    | Vint n => Clight.Econst_int n
    | Vfloat f => Clight.Econst_single f
    end
  end.

Definition translate_type (ty: typ): cl_type :=
  match ty with
  | Tbool => cl_bool
  | Tvoid => cl_void
  | Tint => cl_int
  | Tfloat => cl_float
  end.

Definition translate_unop (op: unary_op): cl_expr -> cl_type -> cl_expr :=
  match op with
  | Opposite => Clight.Eunop Cop.Oneg
  | Negation => Clight.Eunop Cop.Onotbool
  end.

Definition translate_binop (op: binary_op): cl_expr -> cl_expr -> cl_type -> cl_expr :=
  match op with
  | Add => Clight.Ebinop Cop.Oadd
  | Sub => Clight.Ebinop Cop.Osub
  | Mul => Clight.Ebinop Cop.Omul
  | Div => Clight.Ebinop Cop.Odiv
  end.

Definition deref_self_field (cls x: cl_ident) (ty: cl_type): cl_expr :=
  let ty_deref_self := type_of_inst cls in
  let ty_self := pointer_of ty_deref_self in
  Clight.Efield (Clight.Ederef (Clight.Evar self_id ty_self) ty_deref_self) x ty.
                
(** Straightforward expression translation *)
Fixpoint translate_exp (cls: cl_ident) (e: exp): cl_expr :=
  match e with
  | Var x ty => Clight.Evar (translate_ident x) (translate_type ty)  
  | State x ty =>
    deref_self_field cls (translate_ident x) (translate_type ty)
  | Const c ty => translate_const c (translate_type ty)
  | Unop op e ty =>
    translate_unop op (translate_exp cls e) (translate_type ty)
  | Binop op e1 e2 ty =>
    translate_binop op (translate_exp cls e1) (translate_exp cls e2) (translate_type ty)
  end.

Fixpoint list_type_to_typelist (tys: list cl_type): cl_typelist :=
  match tys with
  | [] => Ctypes.Tnil
  | ty :: tys => Ctypes.Tcons ty (list_type_to_typelist tys)
  end.

(** function call and assignment *)
(* Q: Can we really use same ident for temporary and classic variables ? *)
Definition funcall
           (bind: option cl_ident) (f: cl_ident) (ty: cl_type) (args: list cl_expr)
  : cl_stmt :=
  let tys := List.map Clight.typeof args in
  let sig := Ctypes.Tfunction (list_type_to_typelist tys) ty AST.cc_default in
  Clight.Scall bind (Clight.Evar f sig) args.

Definition assign (bind: cl_ident) (ty: cl_type) (e: cl_expr): cl_stmt :=
  Clight.Sassign (Clight.Evar bind ty) e.

Definition st_assign (cls x: cl_ident) (ty: cl_type) (e: cl_expr): cl_stmt :=
  Clight.Sassign (deref_self_field cls x ty) e.
                 
Definition binded_funcall (bind temp f: cl_ident) (ty: cl_type) (args: list cl_expr)
  : cl_stmt :=
   Clight.Ssequence (funcall (Some temp) f ty args)
                   (assign bind ty (Clight.Etempvar temp ty)).

Definition ptr_obj (owner: option cl_ident) (cls obj: cl_ident):=
  Clight.Eaddrof
    ((match owner with
      | Some owner => deref_self_field owner
      | None => Clight.Evar
      end) obj (type_of_inst cls))
    (type_of_inst_p cls).

Definition reset_call (owner: option cl_ident) (cls obj: cl_ident): cl_stmt :=
  funcall None (reset_id cls) cl_void [ptr_obj owner cls obj].

Definition step_call
           (owner: option cl_ident) (bind temp cls: cl_ident) (obj: cl_ident) (args: list cl_expr)
           (out_ty: cl_type)
  : cl_stmt :=
  let args := ptr_obj owner cls obj :: args in
  binded_funcall bind temp (step_id cls) out_ty args.

(** 
Statement conversion keeps track of the produced temporaries (function calls).
NEW: use a unique temporary 
[owner] represents the name of the current class.
 *)
Fixpoint translate_stmt (vars: PM.t cl_type) (temp: option cl_bind) (owner: cl_ident) (s: stmt)
  : (PM.t cl_type * option cl_bind * cl_stmt) :=
  match s with
  | Assign x e =>
    let ty := translate_type (typeof e) in
    let vars := PM.add x ty vars in 
    (vars, temp, assign (translate_ident x) ty (translate_exp owner e))
  | AssignSt x e =>
    let ty := typeof e in
    (vars, temp, st_assign owner (translate_ident x) (translate_type ty) (translate_exp owner e))
  | Ifte e s1 s2 =>
    let '(vars1, temp1, s1') := translate_stmt vars temp owner s1 in
    let '(vars2, temp2, s2') := translate_stmt vars1 temp1 owner s2 in
    (vars2, temp2, Clight.Sifthenelse (translate_exp owner e) s1' s2')
  | Step_ap y cls x es (* ty *) =>
    let ty := Tint in
    let y := translate_ident y in
    let cls := translate_ident cls in
    let x := translate_ident x in
    let args := nelist2list (Nelist.map (translate_exp cls) es) in
    let out_ty := translate_type ty in
    let temp' := match temp with Some t => t | None => (first_unused_ident tt, out_ty) end in
    let s_step := step_call (Some owner) y (fst temp') cls x args out_ty in 
    let vars := PM.add y out_ty vars in 
    (vars, Some temp', s_step)
  | Reset_ap cls x =>
    (vars, temp, reset_call (Some owner) cls x)
  | Comp s1 s2 =>
    let '(vars1, temp1, s1') := translate_stmt vars temp owner s1 in
    let '(vars2, temp2, s2') := translate_stmt vars1 temp1 owner s2 in
    (vars2, temp2, Clight.Ssequence s1' s2')
  | Skip =>
    (vars, temp, Clight.Sskip)
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
           (ins: list cl_bind) (vars: list cl_bind) (ty: cl_type)
           (temps: list cl_bind) (body: cl_stmt)
  : cl_globdef :=
  let f := Clight.mkfunction ty AST.cc_default ins vars temps body in
  @AST.Gfun Clight.fundef cl_type (Clight.Internal f).

(** build the step function *)
Definition make_step
           (self: cl_bind) (ins: list cl_bind) (out: cl_bind)
           (vars: list cl_bind) (temps: list cl_bind) (body: cl_stmt)
  : cl_globdef :=
  let body := return_some body out in
  fundef (self :: ins) vars (snd out) temps body.

Fixpoint seq_of_statements (sl: list cl_stmt): cl_stmt :=
  match sl with
  | [] => Clight.Sskip
  | s :: sl' => Clight.Ssequence s (seq_of_statements sl')
  end.

(** build the reset function *)
Definition make_reset
           (self: cl_bind) (vars: list cl_bind) (temps: list cl_bind) (body: cl_stmt)
  : cl_globdef :=
  let body := return_none body in
  fundef [self] vars cl_void temps body.

Definition translate_obj_dec (obj: obj_dec): cl_bind :=
  match obj with
    mk_obj_dec inst cls =>
    let inst := translate_ident inst in
    let cls := translate_ident cls in
    (inst, type_of_inst cls)
  end.

Definition translate_param (p: ident * typ): cl_bind :=
  let (id, ty) := p in
  (translate_ident id, translate_type ty).

(** build the structure *)
Definition make_struct (cls: cl_ident) (members: list cl_bind)
 : cl_structdef :=
  Ctypes.Composite cls Ctypes.Struct members Ctypes.noattr.

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
    let '(vars_step, temp_step, step) := translate_stmt (PM.empty cl_type) None name c_step in
    let '(vars_reset, temp_reset, reset) := translate_stmt (PM.empty cl_type) None name c_reset in
    let self := (self_id, type_of_inst_p name) in
    let temp_step' := match temp_step with Some t => [t] | None => [] end in
    let temp_reset' := match temp_reset with Some t => [t] | None => [] end in
    let cl_struct := make_struct name members in
    let cl_step := (step_id name, make_step self ins out (PM.elements vars_step) temp_step' step) in
    let cl_reset := (reset_id name, make_reset self (PM.elements vars_reset) temp_reset' reset) in
    (cl_struct, cl_step, cl_reset) 
  end.

Definition glob_id (id: cl_ident): cl_ident :=
  pos_of_str ("_" ++ (pos_to_str id)).
Definition glob_bind (bind: cl_bind): cl_bind :=
  let (x, ty) := bind in
  (glob_id x, ty).
Definition make_arg (arg: cl_bind): cl_expr :=
  let (x, ty) := arg in
  Clight.Evar (glob_id x) ty.
  
(** build the main function (entry point) *)
Definition make_main
           (node: cl_ident) (f: cl_ident) (ins: list cl_bind) (out: cl_bind)
  : cl_globdef :=
  let (out, out_ty) := out in
  let args := List.map make_arg ins in
  let wait := (* funcall None wait_id cl_void [make_arg (delay_id, cl_int)] *) Clight.Sskip in
  let step := step_call None out out node f args out_ty in
  let loop := Clight.Sloop (Clight.Ssequence wait step) Clight.Sskip in
  let body := return_zero (Clight.Ssequence (reset_call None node f) loop) in
  fundef [] [] cl_int [(out, out_ty)] body.

Definition split_3 {A B C: Type} (l: list (A * B * C))
 : list A * list B * list C :=
  List.fold_right (fun (xyz: A * B * C) (abc: list A * list B * list C) =>
                     match xyz with
                       (x, y, z) => match abc with
                                     (a, b, c) => (x :: a, y :: b, z :: c)
                                   end
                     end
                  ) ([], [], []) l.

Definition vardef (init volatile: bool) (x: cl_bind): cl_ident * cl_globdef :=
  let (x, ty) := x in
  let ty' := Ctypes.merge_attributes ty (Ctypes.mk_attr volatile None) in
  (x, @AST.Gvar Clight.fundef _
                (AST.mkglobvar ty' (if init then [AST.Init_space Z0] else []) false volatile)).

Definition make_wait: cl_ident * cl_globdef :=
  let sig := AST.mksignature [AST.Tint] None AST.cc_default in
  (wait_id,
   @AST.Gfun _ cl_type
             (Clight.External (AST.EF_external (pos_to_str wait_id) sig)
                              (Ctypes.Tcons cl_int Ctypes.Tnil)
                              cl_void AST.cc_default)).

(** translation function: the main instance is declared as 'extern' and it's 
step function's return variable as 'volatile' *)
Definition translate (p: program) (main_node: ident)
  : Errors.res Clight.program :=
  match find_class main_node p with
  | Some (cls, _) =>
    let main_node := translate_ident main_node in
    let f := glob_id main_node in
    let ins := nelist2list (Nelist.map translate_param cls.(c_input)) in
    let out := translate_param cls.(c_output) in
    let out' := glob_bind out in
    let main := make_main main_node f ins out' in
    let cs := List.map translate_class p in
    let f_gvar := vardef true false (f, type_of_inst main_node) in
    let o_gvar := vardef true true out' in
    let ins' := List.map glob_bind ins in
    let ins_gvar := List.map (vardef true true) ins' in
    let '(structs, steps, resets) := split_3 cs in
    let gdefs := make_wait :: vardef false false (glob_id delay_id, cl_int)
                           :: f_gvar :: o_gvar :: ins_gvar ++
                           resets ++ steps ++ [(main_id, main)]
    in
    Clight.make_program structs gdefs [] main_id                    
  | None => Errors.Error (Errors.msg "undefined node")
  end. 

(* Definition compile (p: program) (main_node: cl_ident) *)
(*   : Errors.res Asm.program := *)
(*   match translate p main_node with *)
(*   | Errors.OK p => Compiler.transf_clight_program p *)
(*   | Errors.Error res => Errors.Error res *)
(*   end. *)




(* Require Import common.Events. *)
(* Require Import common.Globalenvs. *)
(* Require Import common.Memory. *)
(* Require Import lib.Integers. *)
(* Require Import common.Smallstep. *)

(* Record fundeft := Fundeft {name: ident; body: stmt}. *)
(* Definition vart := cl_ident. *)

(* Definition genv := Genv.t fundeft vart. *)
(* Inductive state := State (H: heap) (S: stack) (s: stmt). *)

(* Definition make_gvar (init volatile: bool) (name: cl_ident) := *)
(*   (name, *)
(*    @AST.Gvar fundeft _ (AST.mkglobvar name (if init then [AST.Init_space Z0] else []) false volatile)). *)

(* Definition make_gfun (name: cl_ident) (body: stmt) := *)
(*   (name, *)
(*    @AST.Gfun _ vart (Fundeft name body)). *)

(* Definition convert_class (defs: list (cl_ident * AST.globdef fundeft vart)) (c: class) *)
(*   : list (cl_ident * AST.globdef fundeft vart) := *)
(*   match c with *)
(*     mk_class c_name c_input c_output c_mems c_objs c_step c_reset => *)
(*     let name := translate_ident c_name in *)
(*     let cls := make_gvar false false name in *)
(*     let step := make_gfun (step_id name) c_step in *)
(*     let reset := make_gfun (reset_id name) c_reset in *)
(*     cls :: step :: reset :: defs *)
(*   end. *)

(* Definition convert_prog (p: program): AST.program fundeft vart := *)
(*   let defs := List.fold_left convert_class p nil in *)
(*   AST.mkprogram defs [] main_id.  *)
  
(* Inductive step: genv -> state -> trace -> state -> Prop := *)
(*   DoStep: forall prog ge H S s H' S' t, *)
(*     stmt_eval prog H S s (H', S') -> *)
(*     step ge (State H S s) t (State H' S' Skip). *)

(* Parameter convert_mem: mem -> heap * stack. *)
(* Inductive initial_state (ge: genv) (p: program): state -> Prop := *)
(*   IniState: forall b f m0 H0 S0, *)
(*     let p' := convert_prog p in *)
(*     Genv.init_mem p' = Some m0 -> *)
(*     Genv.find_symbol ge p'.(AST.prog_main) = Some b -> *)
(*     Genv.find_funct_ptr ge b = Some f -> *)
(*     convert_mem m0 = (H0, S0) -> *)
(*     initial_state ge p (State H0 S0 f.(body)). *)

(* Inductive final_state (s: state) (n: int): Prop := False. *)

(* Definition globalenv (p: program) := *)
(*   Genv.globalenv (convert_prog p). *)

(* Definition semantics (p: program) := *)
(*   let ge := globalenv p in *)
(*   Semantics_gen step (initial_state ge p) final_state ge ge. *)