Require cfrontend.Clight.
Require Import lib.Integers.

Require Import Rustre.Common.
Require Import Rustre.Obc.Syntax.
Require Import Rustre.ObcToClight.Interface.
Require Import Rustre.Ident.
Require Import Rustre.Operators.

Module Export OpAux := OperatorsAux Op.
Module Export Syn := SyntaxFun Ids Op OpAux.

Require Import String.
Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Definition main_id: ident := pos_of_str "main".
Axiom prefix: ident -> ident -> ident.
Definition fun_id: ident  := pos_of_str "fun".
Axiom fun_not_out: fun_id <> out.

Definition prefix_fun (c f: ident): ident :=
  prefix fun_id (prefix c f).
Definition prefix_out (o f: ident): ident :=
  prefix out (prefix o f).

Axiom prefix_injective:
  forall pref id pref' id',
    prefix pref id = prefix pref' id' -> pref = pref' /\ id = id'.
Lemma prefix_fun_injective: 
 forall c c' f f',
   prefix_fun c f = prefix_fun c' f' -> c = c' /\ f = f'.
Proof.
  unfold prefix_fun.
  intros ** Eq.
  apply prefix_injective in Eq; destruct Eq as [E Eq]; clear E.
  now apply prefix_injective.
Qed.
Lemma prefix_out_injective: 
 forall c c' f f',
   prefix_out c f = prefix_out c' f' -> c = c' /\ f = f'.
Proof.
  unfold prefix_out.
  intros ** Eq.
  apply prefix_injective in Eq; destruct Eq as [E Eq]; clear E.
  now apply prefix_injective.
Qed.

Definition step_id (id: ident): ident := 
  pos_of_str ("step_" ++ (pos_to_str id)).
(* Definition reset_id (id: ident): ident := *)
(*   pos_of_str ("reset_" ++ (pos_to_str id)). *)

(* TRANSLATION *)
Definition type_of_inst (o: ident): Ctypes.type :=
  Ctypes.Tstruct o Ctypes.noattr.
Definition pointer_of (ty: Ctypes.type): Ctypes.type :=
  Ctypes.Tpointer ty Ctypes.noattr.
Definition type_of_inst_p (o: ident): Ctypes.type :=
  pointer_of (type_of_inst o).

Definition deref_field (id cls x: ident) (xty: Ctypes.type): Clight.expr :=
  let ty_deref := type_of_inst cls in
  let ty_ptr := pointer_of ty_deref in
  Clight.Efield (Clight.Ederef (Clight.Etempvar id ty_ptr) ty_deref) x xty.

Definition translate_const (c: const): Clight.expr :=
  (match c with
  | Cint i _ _ => Clight.Econst_int i
  | Clong l _ => Clight.Econst_long l
  | Cfloat f => Clight.Econst_float f
  | Csingle s => Clight.Econst_single s
  end) (cltype (type_const c)).

Definition translate_unop (op: unop) (e: Clight.expr) (ty: Ctypes.type): Clight.expr :=
  match op with
  | UnaryOp cop => Clight.Eunop cop e ty
  | CastOp ty => Clight.Ecast e (cltype ty)
  end.

Definition translate_binop (op: binop): Clight.expr -> Clight.expr -> Ctypes.type -> Clight.expr :=
  Clight.Ebinop op.

(** Straightforward expression translation *)
Fixpoint translate_exp (c: class) (m: method) (e: exp): Clight.expr :=
  match e with
  | Var x ty =>
    let ty := cltype ty in
    if existsb (fun out => ident_eqb (fst out) x) m.(m_out) then
      deref_field out (prefix_fun c.(c_name) m.(m_name)) x ty
    else
      Clight.Etempvar x ty  
  | State x ty =>
    deref_field self c.(c_name) x (cltype ty)
  | Const c =>
    translate_const c
  | Unop op e ty =>
    translate_unop op (translate_exp c m e) (cltype ty)
  | Binop op e1 e2 ty =>
    translate_binop op (translate_exp c m e1) (translate_exp c m e2) (cltype ty)
  end.

Fixpoint list_type_to_typelist (tys: list Ctypes.type): Ctypes.typelist :=
  match tys with
  | [] => Ctypes.Tnil
  | ty :: tys => Ctypes.Tcons ty (list_type_to_typelist tys)
  end.

Definition funcall (f: ident) (args: list Clight.expr) : Clight.statement :=
  let tys := map Clight.typeof args in
  let sig := Ctypes.Tfunction (list_type_to_typelist tys) Ctypes.Tvoid AST.cc_default in
  Clight.Scall None (Clight.Evar f sig) args.

Definition assign (x: ident) (ty: Ctypes.type) (clsid: ident) (m: method): Clight.expr -> Clight.statement :=
  if existsb (fun out => ident_eqb (fst out) x) m.(m_out) then
    Clight.Sassign (deref_field out (prefix_fun clsid m.(m_name)) x ty)
  else
    Clight.Sset x.

Definition ptr_obj (owner: ident) (cls obj: ident): Clight.expr :=
  Clight.Eaddrof (deref_field self owner obj (type_of_inst cls)) (type_of_inst_p cls).  

Definition funcall_assign
           (ys: list (ident * Ctypes.type)) (owner: ident) (caller: method)
           (obj: ident) (tyout: Ctypes.type) (callee: method)
           : Clight.statement :=
  fold_right
    (fun y s =>
       let '((y, ty), (y', _)) := y in
       let assign_out := assign y ty owner caller (Clight.Efield (Clight.Evar obj tyout) y' ty) in
       Clight.Ssequence assign_out s
    ) Clight.Sskip (combine ys callee.(m_out)).

Definition binded_funcall
           (prog: program) (ys: list (ident * Ctypes.type)) (owner: ident)
           (caller: method) (cls obj f: ident) (args: list Clight.expr)
  : Clight.statement :=
  match find_class cls prog with
  | Some (c, _) =>
    match find_method f c.(c_methods) with
    | Some m =>
      let tyout := type_of_inst (prefix_fun cls f) in
      let out := Clight.Eaddrof (Clight.Evar (prefix_out obj f) tyout) (pointer_of tyout) in 
      let args := ptr_obj owner cls obj :: out :: args in
      Clight.Ssequence
        (funcall (prefix_fun cls f) args)
        (funcall_assign ys owner caller (prefix_out obj f) tyout m)
    | None => Clight.Sskip
    end
  | None => Clight.Sskip
  end.

Definition translate_param (yt: ident * type): ident * Ctypes.type :=
  let (y, t) := yt in
  (y, cltype t).

(** 
Statement conversion keeps track of the produced temporaries (function calls).
[c] represents the current class.
 *)
Fixpoint translate_stmt (prog: program) (c: class) (m: method) (s: stmt)
  : Clight.statement :=
  match s with
  | Assign x e =>
    assign x (cltype (typeof e)) c.(c_name) m (translate_exp c m e)
  | AssignSt x e =>
    Clight.Sassign (deref_field self c.(c_name) x (cltype (typeof e))) (translate_exp c m e)
  | Ifte e s1 s2 =>
    Clight.Sifthenelse (translate_exp c m e) (translate_stmt prog c m s1) (translate_stmt prog c m s2) 
  | Comp s1 s2 =>
    Clight.Ssequence (translate_stmt prog c m s1) (translate_stmt prog c m s2)
  | Call ys cls o f es =>
    let ys := map translate_param ys in
    binded_funcall prog ys c.(c_name) m cls o f (map (translate_exp c m) es)  
  | Skip => Clight.Sskip
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
           (ins: list (ident * Ctypes.type)) (vars temps: list (ident * Ctypes.type))
           (ty: Ctypes.type) (body: Clight.statement)
  : AST.globdef Clight.fundef Ctypes.type :=
  let f := Clight.mkfunction ty AST.cc_default ins vars temps body in
  @AST.Gfun Clight.fundef Ctypes.type (Ctypes.Internal f).

Definition make_fundef
           (self: ident * Ctypes.type) (ins: list (ident * Ctypes.type))
           (out: ident * Ctypes.type) (vars temps: list (ident * Ctypes.type))
           (body: Clight.statement)
  : AST.globdef Clight.fundef Ctypes.type :=
  let body := return_none body in
  fundef (self :: out :: ins) vars temps Ctypes.Tvoid body.

Definition make_out_vars (out_vars: list (ident * ident * ident)): list (ident * Ctypes.type) :=
  map (fun ofc =>
         let '(o, f, cid) := ofc in
         (prefix_out o f, type_of_inst (prefix_fun cid f))
      ) out_vars.

Lemma dec_pair: forall x y : (ident * ident), {x = y} + {x <> y}.
Proof. repeat decide equality. Qed.

Fixpoint rec_instance_methods (s: stmt) (l: list (ident * ident * ident))
  : list (ident * ident * ident) :=
  match s with
  | Ifte _ s1 s2  
  | Comp s1 s2 => rec_instance_methods s2 (rec_instance_methods s1 l)
  | Call _ cls o f _ => if in_dec dec_pair (o, f) (map fst l) then l else (o, f, cls) :: l 
  | _ => l
  end.
  
Definition instance_methods (m: method): list (ident * ident * ident) :=
  rec_instance_methods m.(m_body) [].

Definition translate_method (prog: program) (c: class) (m: method)
  : ident * AST.globdef Clight.fundef Ctypes.type :=
  let body := translate_stmt prog c m m.(m_body) in
  let out_vars := instance_methods m in
  let self := (self, type_of_inst_p c.(c_name)) in
  let ins := map translate_param m.(m_in) in
  let out := (out, type_of_inst_p (prefix_fun c.(c_name) m.(m_name))) in
  let vars := map translate_param m.(m_vars) in
  (prefix_fun c.(c_name) m.(m_name),
   make_fundef self ins out (make_out_vars out_vars) vars body).

Definition make_methods (prog: program) (c: class)
  : list (ident * AST.globdef Clight.fundef Ctypes.type) :=
  map (translate_method prog c) c.(c_methods).

Definition translate_obj (obj: ident * ident): (ident * Ctypes.type) :=
  let (o, c) := obj in
  (o, type_of_inst c).

Definition make_members (c: class): Ctypes.members :=
  map translate_param c.(c_mems) ++ map translate_obj c.(c_objs).

Definition make_struct (c: class): Ctypes.composite_definition :=
  Ctypes.Composite c.(c_name) Ctypes.Struct (make_members c) Ctypes.noattr.

Definition translate_out (c: class) (m: method): Ctypes.composite_definition :=
  Ctypes.Composite
    (prefix_fun c.(c_name) m.(m_name))
    Ctypes.Struct
    (map translate_param m.(m_out))
    Ctypes.noattr.

Definition make_out (c: class): list Ctypes.composite_definition :=
  map (translate_out c) c.(c_methods).

Definition translate_class (prog: program) (c: class)
  : list Ctypes.composite_definition * list (ident * AST.globdef Clight.fundef Ctypes.type) :=
  let methods := make_methods prog c in
  let class_struct := make_struct c in
  let out_structs := make_out c in   
  (class_struct :: out_structs, methods).

Definition glob_id (id: ident): ident :=
  pos_of_str ("_" ++ (pos_to_str id)).
Definition glob_bind (bind: ident * type): ident * Ctypes.type :=
  let (x, ty) := bind in
  (glob_id x, cltype ty).

Definition make_in_arg (arg: ident * Ctypes.type): Clight.expr :=
  let (x, ty) := arg in
  Clight.Evar x ty.
(* Definition make_out_arg (arg: ident * typ): Clight.expr := *)
(*   let (x, ty) := arg in *)
(*   Clight.Eaddrof (Clight.Evar x ty) (pointer_of ty). *)

Definition make_main
           (prog: program) (node: ident) (ins: list (ident * Ctypes.type))
           (outs: list (ident * Ctypes.type)) (m: method)
  : AST.globdef Clight.fundef Ctypes.type :=
  let out_struct := step_id node in
  let args_in := map make_in_arg ins in
  let tyout := type_of_inst (step_id node) in
  let out := Clight.Eaddrof (Clight.Evar out_struct tyout) (pointer_of tyout) in 
  let args := (Clight.Eaddrof (Clight.Evar (glob_id node) (type_of_inst node)) (type_of_inst_p node))
                :: args_in ++ [out] in
  let step := Clight.Ssequence
                (funcall (step_id node) args)
                (fold_right
                   (fun y s =>
                      let '((y, ty), (y', _)) := y in
                      let assign_out := Clight.Sassign (Clight.Evar y ty)
                                                       (Clight.Efield (Clight.Evar out_struct tyout) y' ty) in
                      Clight.Ssequence assign_out s
                   ) Clight.Sskip (combine outs m.(m_out))) in
  let loop := Clight.Sloop ((* Clight.Ssequence wait *) step) Clight.Sskip in
  let body := return_zero ((* Clight.Ssequence (reset_call None node f) *) loop) in
  fundef [] [(out_struct, type_of_inst (step_id node))] [] Ctypes.type_int32s body.

Definition vardef (init volatile: bool) (x: ident * Ctypes.type)
  : ident * AST.globdef Clight.fundef Ctypes.type :=
  let (x, ty) := x in
  let ty' := Ctypes.merge_attributes ty (Ctypes.mk_attr volatile None) in
  (x, @AST.Gvar Clight.fundef _
                (AST.mkglobvar ty' (if init then [AST.Init_space Z0] else []) false volatile)).

Definition build_composite_env' (types: list Ctypes.composite_definition) :
  { ce | Ctypes.build_composite_env types = Errors.OK ce } + Errors.errmsg.
Proof.
  destruct (Ctypes.build_composite_env types) as [ce|msg].
  - left. exists ce; auto.
  - right. exact msg.
Defined.

Definition make_program'
           (types: list Ctypes.composite_definition)
           (defs: list (ident * AST.globdef Clight.fundef Ctypes.type))
           (public: list ident)
           (main: ident) : Errors.res (Ctypes.program Clight.function) :=
  match build_composite_env' types with
  | inl (exist ce P) =>
    Errors.OK {| Ctypes.prog_defs := defs;
                 Ctypes.prog_public := public;
                 Ctypes.prog_main := main;
                 Ctypes.prog_types := types;
                 Ctypes.prog_comp_env := ce;
                 Ctypes.prog_comp_env_eq := P |}
  | inr msg => Errors.Error msg
  end.

Definition translate (prog: program) (main_node: ident): Errors.res Clight.program :=
  match find_class main_node prog with
  | Some (c, _) =>
    match find_method (step_id main_node) c.(c_methods) with
    | Some m =>
      let f := glob_id main_node in
      let ins := map glob_bind m.(m_in) in
      let outs := map glob_bind m.(m_out) in
      let main := make_main prog main_node ins outs m in
      let cs := map (translate_class prog) prog in
      let f_gvar := vardef true false (f, type_of_inst main_node) in
      let o_gvars := map (vardef true true) outs in
      let i_gvars := map (vardef true true) ins in
      let (structs, funs) := split cs in
      let gdefs := f_gvar :: o_gvars ++ i_gvars ++ (concat funs) ++ [(main_id, main)] in
      make_program' (concat structs) gdefs [] main_id
    | None => Errors.Error (Errors.msg "unfound step function")
    end
  | None => Errors.Error (Errors.msg "undefined node")
  end.