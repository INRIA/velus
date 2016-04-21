Require Import Rustre.Minimp.Syntax.
Require Import Rustre.Common.
Require Import Rustre.Nelist.
Require Import common.AST.
Require Import common.Errors.
Require Import cfrontend.Ctypes.
Require Import cfrontend.Clight.
Require Import cfrontend.Cop.
Require Import lib.Integers.
Require Import driver.Compiler.

Require Import ZArith.
Open Scope string_scope.
Open Scope list_scope.
Import List.ListNotations.

Axiom pos_of_str : String.string -> ident.
Axiom pos_to_str : ident -> String.string.

Inductive unary_op' : Type :=
| Opposite : unary_op'
| Negation : unary_op'.
Inductive binary_op' : Type :=
| Plus : binary_op'
| Minus : binary_op'
| Mult : binary_op'.
    
Module Op <:
  OPERATORS with Definition unary_op := unary_op'
with Definition binary_op := binary_op'.
    Definition val := Z.
    Definition typ := Z.
    Open Scope Z_scope.
    Definition unary_op := unary_op'.
    Definition binary_op := binary_op'.
    Definition sem_unary (op : unary_op) (v : val) :=
      match op with
      | Opposite => Some (- v)
      | Negation => Some (if Z.eqb v 0 then 1 else 0)
      end.
    Definition sem_binary (op : binary_op) (v1 v2 : val) :=
      match op with
      | Plus => Some (v1 + v2)
      | Minus => Some (v1 - v2)
      | Mult => Some (v1 * v2)
      end.
    Definition of_bool (b : bool) := if b then 1 else 0.
    Definition to_bool n := match n with 0 => false | _ => true end.
    Theorem bool_inv : forall b, to_bool (of_bool b) = b. Admitted.
    Definition val_eqb := Z.eqb.
    Definition unop_eqb (op1 op2 : unary_op) := true.
    Definition binop_eqb (op1 op2 : binary_op) := true.
    Theorem val_eqb_true_iff : forall v1 v2, val_eqb v1 v2 = true <-> v1 = v2. Admitted.
    Theorem val_eqb_false_iff : forall v1 v2, val_eqb v1 v2 = false <-> v1 <> v2. Admitted.
    Theorem unop_eqb_true_iff : forall op1 op2, unop_eqb op1 op2 = true <-> op1 = op2. Admitted.
    Theorem unop_eqb_false_iff : forall op1 op2, unop_eqb op1 op2 = false <-> op1 <> op2. Admitted.
    Theorem binop_eqb_true_iff : forall op1 op2, binop_eqb op1 op2 = true <-> op1 = op2. Admitted.
    Theorem binop_eqb_false_iff : forall op1 op2, binop_eqb op1 op2 = false <-> op1 <> op2. Admitted.
End Op.

Module Import Syn := SyntaxFun Op.

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
    c_reset := AssignSt (pos_of_str "t") (Const Z0)
  |}.

(** Common identifiers  *)
Definition main_id : ident := pos_of_str "main".
Definition step_id (id : ident) : ident := pos_of_str (String.append "step_" (pos_to_str id)).
Definition reset_id (id : ident) : ident := pos_of_str (String.append "reset_" (pos_to_str id)).
Definition self_id : ident := pos_of_str "self".

(** struct types  *)
Definition type_of_inst (o : ident) : type := Tstruct o noattr.
Definition type_of_inst_p (o : ident) : type := Tpointer (type_of_inst o) noattr.

(** Constants  *)
Definition cl_true : expr := Econst_int Int.one type_bool.
Definition cl_false : expr := Econst_int Int.zero type_bool.
Definition cl_zero : expr := Econst_int Int.zero type_int32s.

Definition translate_const (c : Op.val) : expr :=
  Econst_int (Integers.Int.repr Z0) type_int32s.

Definition translate_type (ty : base_type) : type :=
  match ty with
  | Common.Tint => type_int32s
  | Common.Tbool => type_bool
  end.

Definition translate_unop (op : Op.unary_op) (e : expr) : expr :=
  match op with
  | Opposite => Eunop Oneg e type_int32s
  | Negation => Eunop Onotbool e type_int32s
  end.

Definition translate_binop (op : Op.binary_op) (e1 e2 : expr) : expr :=
  match op with
  | Plus => Ebinop Oadd e1 e2 type_int32s
  | Minus => Ebinop Osub e1 e2 type_int32s
  | Mult => Ebinop Omul e1 e2 type_int32s
  end.

(** Straightforward expression translation *)
Fixpoint translate_exp (e : exp) : expr :=
  let ty := Common.Tint in
  match e with
  | Syn.Var x (* ty *) => Evar x (translate_type ty)  
  | Syn.State x (* ty *) => Evar x (translate_type ty) 
  | Syn.Const c (* ty *) => translate_const c
  | Syn.Unop op e (* ty *) =>
    translate_unop op (translate_exp e)
  | Syn.Binop op e1 e2 (* ty *) =>
    translate_binop op (translate_exp e1) (translate_exp e2)
  end.

Fixpoint list_type_to_typelist (tys : list type) : typelist :=
  match tys with
  | [] => Tnil
  | ty :: tys => Tcons ty (list_type_to_typelist tys)
  end.

(** pointer expressions  *)
Definition pointer_of_cls (x cls : ident) : expr :=
  Eaddrof (Evar x (type_of_inst cls)) (type_of_inst_p cls).
(* Definition pointer_of_ty (x : ident) (ty : type) : expr := *)
(*   Eaddrof (Evar x ty) (Tpointer ty noattr). *)

(** function call and assignment *)
(* Q : Can we really use same ident for temporary and classic variables ? *)
Definition funcall (bind : option ident) (f : ident) (sig : type) (args : list expr) : statement :=
  Scall bind (Evar f sig) args.
Definition assign (bind : ident) (ty : type) (e : expr) : statement :=
  Sassign (Evar bind ty) e.
Definition binded_funcall (bind : ident) (f : ident) (ty : type) (args : list expr)
  : (ident * type) * statement :=
  let temp := bind in
  let tys := List.map typeof args in
  let sig := Tfunction (list_type_to_typelist tys) ty cc_default in
  ((temp, ty), Ssequence (funcall (Some temp) f sig args) (assign bind ty (Etempvar temp ty))).
Definition reset_call (cls : ident) (obj : ident) : statement :=
  let ty_reset := Tfunction (Tcons (type_of_inst_p cls) Tnil) Tvoid cc_default in
  funcall None (reset_id cls) ty_reset [pointer_of_cls obj cls].
Definition step_call (bind : ident) (cls : ident) (obj : ident) (args : list expr) (out_ty : type)
  : (ident * type) * statement :=
  let args := pointer_of_cls obj cls :: args in
  binded_funcall bind (step_id cls) out_ty args.

(** 
Statement conversion keeps track of the produced temporaries (function calls). 
[name] represents the name of the current class.
 *)
Fixpoint translate_stmt (temps : list (ident * type)) (name : ident) (s : stmt)
  : (list (ident * type) * statement) :=
  match s with
  | Syn.Assign x e =>
    let ty := (* Syn.typeof e *) Common.Tint in
    (temps, assign x (translate_type ty) (translate_exp e))
  | Syn.AssignSt x e =>
    let e' := translate_exp e in
    let ty_self := type_of_inst_p name in
    let ty_deref_self := type_of_inst name in
    (temps, Sassign (Efield (Ederef (Evar self_id ty_self) ty_deref_self) x (typeof e')) e')
  | Syn.Ifte e s1 s2 =>
    let (temps1, s1') := translate_stmt temps name s1 in
    let (temps2, s2') := translate_stmt temps1 name s2 in
    (temps2, Sifthenelse (translate_exp e) s1' s2')
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
    (temps2, Ssequence s1' s2')
  | Syn.Skip =>
    (temps, Sskip)
  end.

(** return statements  *)
Definition return_some (s : statement) (out : ident * type) : statement :=
  let (id, ty) := out in
  Ssequence s (Sreturn (Some (Evar id ty))).
Definition return_none (s : statement) : statement :=
  Ssequence s (Sreturn None).
Definition return_zero (s : statement) : statement :=
  Ssequence s (Sreturn (Some cl_zero)).

(** build the step function *)
Definition make_step (self : ident * type) (ins : list (ident * type))
           (out : ident * type) (temps : list (ident * type)) (body : statement)
  : globdef fundef type :=
  let body := return_some body out in
  let f := mkfunction (snd out) cc_default (self :: ins) [out] temps body in
  @Gfun fundef type (Internal f).

Fixpoint seq_of_statements (sl: list statement) : statement :=
  match sl with
  | [] => Sskip
  | s :: sl' => Ssequence s (seq_of_statements sl')
  end.

Definition reset_obj (obj : obj_dec) : statement :=
  reset_call (obj_class obj) (obj_inst obj).

(** build the reset function *)
Definition make_reset (self : ident * type) (objs : list obj_dec)
           (temps : list (ident * type)) (body : statement) : globdef fundef type :=
  let seq_res := seq_of_statements (body :: (List.map reset_obj objs)) in
  let body := return_none seq_res in
  let f := mkfunction Tvoid cc_default [self] [] temps body in
  @Gfun fundef type (Internal f).

Definition translate_obj_dec (obj : obj_dec) : (ident * type) :=
  match obj with mk_obj_dec inst cls => (inst, type_of_inst cls) end.

Definition translate_param (p : ident (* * base_type *)) : (ident * type) :=
  let (id, ty) := (p, Common.Tint) in
  (id, translate_type ty).

(** build the structure *)
Definition make_struct (name : ident) (members : list (ident * type))
  : composite_definition :=
  Composite name Struct members noattr.

(** translate a class into a triple : structure, step function, reset function  *)
Definition translate_class (c : Syn.class)
  : composite_definition * (ident * globdef fundef type) * (ident * globdef fundef type) :=
  match c with
    mk_class c_name c_input c_output c_mems c_objs c_step c_reset =>
    let mems := List.map translate_param c_mems in
    let objs := List.map translate_obj_dec c_objs in
    let ins := nelist2list (Nelist.map translate_param c_input) in
    let out := translate_param c_output in
    let members := mems ++ objs in
    let (temps_step, step) := translate_stmt [] c_name c_step in
    let (temps_reset, reset) := translate_stmt [] c_name c_reset in
    let self := (self_id, type_of_inst_p c_name) in
    let cl_struct := make_struct c_name members in
    let cl_step := (step_id c_name, make_step self ins out temps_step step) in
    let cl_reset := (reset_id c_name, make_reset self c_objs temps_reset reset) in
    (cl_struct, cl_step, cl_reset) 
  end.

(** build the main function (entry point) *)
Definition make_main (node : ident) (f : ident) (ins : nelist ident) (out : ident)
  : globdef fundef type :=
  let ty := Common.Tint in
  let args := nelist2list (Nelist.alls cl_zero ins) in
  let out_ty := translate_type ty in
  let (temp, step) := step_call out node f args out_ty in
  let loop := Swhile cl_true step in
  let body := return_zero (Ssequence (reset_call node f) loop) in
  let f := mkfunction type_int32s cc_default [] [] [temp] body in 
  @Gfun fundef type (Internal f).

Definition split_3 {A B C : Type} (l : list (A * B * C))
  : list A * list B * list C :=
  List.fold_right (fun (xyz : A * B * C) (abc : list A * list B * list C) =>
                     match xyz with
                       (x, y, z) => match abc with
                                     (a, b, c) => (x :: a, y :: b, z :: c)
                                   end
                     end
                  ) ([], [], []) l.

(** translation function : the main instance is declared as 'extern' and it's step function's return 
variable as 'volatile' *)
Definition translate (p : Syn.program) (main_node : ident) : res Clight.program :=
  match find_class main_node p with
  | Some (cls, _) =>
    let f := pos_of_str "f_" in
    let o := pos_of_str "o_" in
    let f_gvar := @Gvar fundef type (mkglobvar (type_of_inst main_node) nil false false) in
    let o_gvar := @Gvar fundef type (mkglobvar type_int32s nil false true) in
    let main := make_main main_node f (c_input cls) o in
    let cs := List.map translate_class p in
    match split_3 cs with
      (structs, steps, resets) =>
      let gdefs := (o, o_gvar) :: (f, f_gvar) :: resets ++ steps ++ [(main_id, main)] in
      make_program structs gdefs [] main_id                    
    end
  | None => Error (msg "undefined node")
  end. 

Definition compile (p : Syn.program) (main_node : ident) : res Asm.program :=
  match translate p main_node with
  | OK p => transf_clight_program p
  | Error res => Error res
  end.