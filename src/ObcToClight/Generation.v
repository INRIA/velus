From Coq Require Import ZArith.BinInt.
From Coq Require Import String.
From Coq Require Import List.

From compcert Require cfrontend.Clight.
From compcert Require Import lib.Integers.
From compcert Require Import common.Errors.
From compcert Require Import lib.Maps.

From Velus Require Import Common.
From Velus Require Import Common.CompCertLib.
From Velus Require Import Environment.
From Velus Require Import ObcToClight.Interface.
From Velus Require Import Ident.

Import Obc.Syn.
Import Obc.Typ.

Open Scope error_monad_scope.
Open Scope Z.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import FMapAVL.
From Coq Require Export Structures.OrderedTypeEx.

Module IdentPair := PairOrderedType Positive_as_OT Positive_as_OT.
Module M := FMapAVL.Make(IdentPair).

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
  | Cint i sz sg => Clight.Econst_int (Cop.cast_int_int sz sg i)
  | Clong l _ => Clight.Econst_long l
  | Cfloat f => Clight.Econst_float f
  | Csingle s => Clight.Econst_single s
  end) (cltype (type_const c)).

Definition translate_unop (op: unop): Clight.expr -> Ctypes.type -> Clight.expr :=
  match op with
  | UnaryOp cop => Clight.Eunop cop
  | CastOp _ => Clight.Ecast
  end.

Definition translate_binop (op: binop): Clight.expr -> Clight.expr -> Ctypes.type -> Clight.expr :=
  Clight.Ebinop op.

Section Translate.
  Variable (prog: program) (owner: class) (caller: method).

  Definition translate_var (x: ident) (ty: type): Clight.expr :=
    let ty := cltype ty in
    match caller.(m_out) with
    | [] | [_] => Clight.Etempvar x ty
    | xs =>
      if mem_assoc_ident x xs then
        deref_field (prefix obc2c out) (prefix_fun caller.(m_name) owner.(c_name)) x ty
      else
        Clight.Etempvar x ty
    end.

  (** Straightforward expression translation *)
  Fixpoint translate_exp (e: exp): Clight.expr :=
    match e with
    | Var x ty =>
      translate_var x ty
    | Valid x ty =>
      translate_var x ty
    | State x ty =>
      deref_field (prefix obc2c self) owner.(c_name) x (cltype ty)
    | Const c =>
      translate_const c
    | Unop op e ty =>
      translate_unop op (translate_exp e) (cltype ty)
    | Binop op e1 e2 ty =>
      translate_binop op (translate_exp e1) (translate_exp e2) (cltype ty)
    end.

  Fixpoint list_type_to_typelist (tys: list Ctypes.type): Ctypes.typelist :=
    match tys with
    | [] => Ctypes.Tnil
    | ty :: tys => Ctypes.Tcons ty (list_type_to_typelist tys)
    end.

  Definition funcall (y: option ident) (f: ident) (tret: option Ctypes.type) (args: list Clight.expr) : Clight.statement :=
    let tys := map Clight.typeof args in
    let tret := match tret with Some t => t | None => Ctypes.Tvoid end in
    let sig := Ctypes.Tfunction (list_type_to_typelist tys) tret AST.cc_default in
    Clight.Scall y (Clight.Evar f sig) args.

  Definition assign (x: ident) (ty: Ctypes.type): Clight.expr -> Clight.statement :=
    match caller.(m_out) with
    | [] | [_] => Clight.Sset x
    | xs =>
      if mem_assoc_ident x xs then
        Clight.Sassign (deref_field (prefix obc2c out) (prefix_fun caller.(m_name) owner.(c_name)) x ty)
      else
        Clight.Sset x
    end.

  Definition ptr_obj (cls obj: ident): Clight.expr :=
    Clight.Eaddrof (deref_field (prefix obc2c self) owner.(c_name) obj (type_of_inst cls)) (type_of_inst_p cls).

  Definition funcall_assign (ys: list ident) (obj: ident) (tyout: Ctypes.type) (outs: list (ident * type)) : Clight.statement :=
    fold_right
      (fun '(y, (y', ty)) s =>
         let ty := cltype ty in
         let assign_out := assign y ty (Clight.Efield (Clight.Evar obj tyout) y' ty) in
         Clight.Ssequence assign_out s
      ) Clight.Sskip (combine ys outs).

  Definition binded_funcall (ys: list ident) (cls obj f: ident) (args: list Clight.expr) : Clight.statement :=
    match find_class cls prog with
    | Some (c, _) =>
      match find_method f c.(c_methods) with
      | Some m =>
        match ys, m.(m_out) with
        | [], [] =>
          let args := ptr_obj cls obj :: args in
          funcall None (prefix_fun f cls) None args
        | [y], [(y', t)] =>
          let args := ptr_obj cls obj :: args in
          let c_t := cltype t in
          let temp := prefix_temp c.(c_name) (prefix f y') in
          Clight.Ssequence
            (funcall (Some temp) (prefix_fun f cls) (Some c_t) args)
            (assign y c_t (Clight.Etempvar temp c_t))
        | _, outs =>
          let tyout := type_of_inst (prefix_fun f cls) in
          let out := Clight.Eaddrof (Clight.Evar (prefix_out f obj) tyout) (pointer_of tyout) in
          let args := ptr_obj cls obj :: out :: args in
          Clight.Ssequence
            (funcall None (prefix_fun f cls) None args)
            (funcall_assign ys (prefix_out f obj) tyout outs)
        end
      | None => Clight.Sskip
      end
    | None => Clight.Sskip
    end.

  Definition translate_param '((y, t): ident * type): ident * Ctypes.type := (y, cltype t).

  Fixpoint translate_stmt (s: stmt) : Clight.statement :=
    match s with
    | Assign x e =>
      assign x (cltype (typeof e)) (translate_exp e)
    | AssignSt x e =>
      Clight.Sassign (deref_field (prefix obc2c self) owner.(c_name) x (cltype (typeof e))) (translate_exp e)
    | Ifte e s1 s2 =>
      Clight.Sifthenelse (translate_exp e) (translate_stmt s1) (translate_stmt s2)
    | Comp s1 s2 =>
      Clight.Ssequence (translate_stmt s1) (translate_stmt s2)
    | Call ys cls o f es =>
      binded_funcall ys cls o f (map translate_exp es)
    | Skip => Clight.Sskip
    end.

End Translate.

Definition return_with (s: Clight.statement) (e: option Clight.expr): Clight.statement :=
  Clight.Ssequence s (Clight.Sreturn e).
Definition cl_zero: Clight.expr :=
  Clight.Econst_int Int.zero Ctypes.type_int32s.

Definition fundef
           (ins vars temps: list (ident * Ctypes.type))
           (ty: Ctypes.type) (body: Clight.statement)
  : AST.globdef Clight.fundef Ctypes.type :=
  let f := Clight.mkfunction ty AST.cc_default ins vars temps body in
  @AST.Gfun Clight.fundef Ctypes.type (Ctypes.Internal f).


Fixpoint rec_instance_methods (s: stmt) (m: M.t ident): M.t ident :=
  match s with
  | Ifte _ s1 s2
  | Comp s1 s2 => rec_instance_methods s2 (rec_instance_methods s1 m)
  | Call ys cls o f _ =>
    match ys with
    | [] | [_] => m
    | _ => M.add (o, f) cls m
    end
  | _ => m
  end.

Definition instance_methods (m: method): M.t ident :=
  rec_instance_methods m.(m_body) (@M.empty ident).

Definition make_out_vars (out_vars: M.t ident): list (ident * Ctypes.type) :=
  map (fun ofc =>
         let '(o, f, cid) := ofc in
         (prefix_out f o, type_of_inst (prefix_fun f cid))
      ) (M.elements out_vars).

Fixpoint rec_instance_methods_temp (prog: program) (s: stmt) (m: Env.t type): Env.t type :=
  match s with
  | Ifte _ s1 s2
  | Comp s1 s2 => rec_instance_methods_temp prog s2 (rec_instance_methods_temp prog s1 m)
  | Call ys cls o f _ =>
    match find_class cls prog with
    | Some (c, _) =>
      match find_method f c.(c_methods) with
      | Some m' =>
        match ys, m'.(m_out) with
        | [_], [(y', t)] => Env.add (prefix_temp c.(c_name) (prefix f y')) t m
        | _, _ => m
        end
      | None => m
      end
    | None => m
    end
  | _ => m
  end.

Definition instance_methods_temp (prog: program) (m: method): Env.t type :=
  rec_instance_methods_temp prog m.(m_body) (Env.empty _).

Definition make_out_temps (out_temps: Env.t type): list (ident * Ctypes.type) :=
  map translate_param (Env.elements out_temps).

Definition make_in_arg (arg: ident * type): Clight.expr :=
  let (x, ty) := arg in
  Clight.Etempvar x (cltype ty).

Definition translate_method (prog: program) (c: class) (m: method)
  : ident * AST.globdef Clight.fundef Ctypes.type :=
  let body := translate_stmt prog c m m.(m_body) in
  let out_vars := make_out_vars (instance_methods m) in
  let out_temps := make_out_temps (instance_methods_temp prog m) in
  let self := (prefix obc2c self, type_of_inst_p c.(c_name)) in
  let ins := map translate_param m.(m_in) in
  let out := (prefix obc2c out, type_of_inst_p (prefix_fun m.(m_name) c.(c_name))) in
  let vars := map translate_param m.(m_vars) in
  (prefix_fun m.(m_name) c.(c_name),
  match m.(m_out) with
  | [] =>
    let args := self :: ins in
    fundef args out_vars (out_temps ++ vars) Ctypes.Tvoid (return_with body None)
  | [(y, t) as yt] =>
    let args := self :: ins in
    let c_t := cltype t in
    fundef args out_vars (translate_param yt :: out_temps ++ vars) c_t (return_with body (Some (make_in_arg yt)))
  | _ :: _ =>
    let args := self :: out :: ins in
    fundef args out_vars (out_temps ++ vars) Ctypes.Tvoid (return_with body None)
  end).

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
    (prefix_fun m.(m_name) c.(c_name))
    Ctypes.Struct
    (map translate_param m.(m_out))
    Ctypes.noattr.

Definition filter_out: list Ctypes.composite_definition -> list Ctypes.composite_definition :=
  filter (fun co => match co with
                 | Ctypes.Composite _ _ [] _
                 | Ctypes.Composite _ _ [_] _ => false
                 | _ => true
                 end).

Definition make_out (c: class): list Ctypes.composite_definition :=
  filter_out (map (translate_out c) c.(c_methods)).

Definition translate_class (prog: program) (c: class)
  : list Ctypes.composite_definition * list (ident * AST.globdef Clight.fundef Ctypes.type) :=
  let methods := make_methods prog c in
  let class_struct := make_struct c in
  let out_structs := make_out c in
  (class_struct :: out_structs, methods).

Definition glob_bind (bind: ident * type): ident * Ctypes.type :=
  let (x, ty) := bind in
  (prefix_glob x, cltype ty).

Definition load_in (ins: list (ident * type)): Clight.statement :=
  fold_right
    (fun (xt: ident * type) s =>
       let (x, t) := xt in
       let typtr := Ctypes.Tpointer (cltype t) Ctypes.noattr in
       let load :=
           Clight.Sbuiltin (Some x) (AST.EF_vload (type_chunk t))
                           (Ctypes.Tcons typtr Ctypes.Tnil)
                           [Clight.Eaddrof (Clight.Evar (prefix_glob x) (cltype t)) typtr] in
       Clight.Ssequence load s) Clight.Sskip ins.

Definition write_multiple_outs (node: ident) (outs: list (ident * type))
  : Clight.statement :=
  let out_struct := prefix out step in
  let t_struct := type_of_inst (prefix_fun step node) in
  fold_right
    (fun (xt: ident * type) s =>
       let (x, t) := xt in
       let typtr := Ctypes.Tpointer (cltype t) Ctypes.noattr in
       let write :=
           Clight.Sbuiltin None (AST.EF_vstore (type_chunk t))
                           (Ctypes.Tcons typtr (Ctypes.Tcons (cltype t) Ctypes.Tnil))
                           [Clight.Eaddrof (Clight.Evar (prefix_glob x) (cltype t)) typtr;
                              Clight.Efield (Clight.Evar out_struct t_struct) x (cltype t)] in
       Clight.Ssequence write s
    ) Clight.Sskip outs.

Definition write_out (node: ident) (outs: list (ident * type))
  : Clight.statement :=
  match outs with
  | [] => Clight.Sskip
  | [(x, t)] =>
    let typtr := Ctypes.Tpointer (cltype t) Ctypes.noattr in
    Clight.Sbuiltin None (AST.EF_vstore (type_chunk t))
                    (Ctypes.Tcons typtr (Ctypes.Tcons (cltype t) Ctypes.Tnil))
                    [Clight.Eaddrof (Clight.Evar (prefix_glob x) (cltype t)) typtr;
                       (Clight.Etempvar x (cltype t))]
  | outs => write_multiple_outs node outs
  end.

Definition reset_call (node: ident): Clight.statement :=
  let p_self := Clight.Eaddrof (Clight.Evar (prefix_glob (prefix self main_id)) (type_of_inst node)) (type_of_inst_p node) in
  funcall None (prefix_fun reset node) None [p_self].

Definition step_call (node: ident) (args: list Clight.expr) (m_out: list (ident * type)): Clight.statement :=
  let p_self := Clight.Eaddrof (Clight.Evar (prefix_glob (prefix self main_id)) (type_of_inst node)) (type_of_inst_p node) in
  match m_out with
  | [] =>
    let args := p_self :: args in
    funcall None (prefix_fun step node) None args
  | [(y, t)] =>
    let args := p_self :: args in
    funcall (Some y) (prefix_fun step node) (Some (cltype t)) args
  | _ =>
    let out_struct := prefix out step in
    let t_struct := type_of_inst (prefix_fun step node) in
    let p_out := Clight.Eaddrof (Clight.Evar out_struct t_struct) (pointer_of t_struct) in
    let args := p_self :: p_out :: args in
    funcall None (prefix_fun step node) None args
  end.

Definition main_loop_body (do_sync: bool) (node: ident) (m: method): Clight.statement :=
  let args := map make_in_arg m.(m_in) in
  let body := Clight.Ssequence
                (load_in m.(m_in))
                (Clight.Ssequence
                   (step_call node args m.(m_out))
                   (write_out node m.(m_out)))
  in
  if do_sync
  then Clight.Ssequence (funcall None sync_id None []) body
  else body.

Definition main_loop (do_sync: bool) (node: ident) (m: method): Clight.statement :=
  Clight.Sloop (main_loop_body do_sync node m) Clight.Sskip.

Definition main_body (do_sync: bool) (node: ident) (m: method): Clight.statement :=
  Clight.Ssequence (reset_call node) (main_loop do_sync node m).

Definition make_main (do_sync: bool) (node: ident) (m: method): AST.globdef Clight.fundef Ctypes.type :=
  let vars :=  match m.(m_out) with
               | [] | [_] => []
               | _ => [(prefix out step, type_of_inst (prefix_fun step node))]
               end
  in
  let temp := match m.(m_out) with
               | [yt] => [yt]
               | _ => []
              end
  in
  fundef [] vars (map translate_param (temp ++ m.(m_in))) Ctypes.type_int32s (main_body do_sync node m).

Definition make_entry_point (do_sync: bool): AST.globdef Clight.fundef Ctypes.type :=
  let sig := Ctypes.Tfunction Ctypes.Tnil Ctypes.Tvoid AST.cc_default in
  let main := Clight.Evar (if do_sync then main_sync_id else main_proved_id) sig in
  let body := Clight.Scall None main [] in
  fundef [] [] [] Ctypes.type_int32s body.

Definition ef_sync: Clight.fundef :=
  let sg := AST.mksignature [] AST.Tvoid AST.cc_default in
  let ef := AST.EF_external "sync" sg in
  Ctypes.External ef Ctypes.Tnil Ctypes.Tvoid AST.cc_default.

Definition make_sync: AST.globdef Clight.fundef Ctypes.type :=
  @AST.Gfun Clight.fundef Ctypes.type ef_sync.

Definition vardef (env: Ctypes.composite_env) (volatile: bool) (x: ident * Ctypes.type)
  : ident * AST.globdef Clight.fundef Ctypes.type :=
  let (x, ty) := x in
  let ty' := Ctypes.merge_attributes ty (Ctypes.mk_attr volatile None) in
  (x, @AST.Gvar Clight.fundef _
                (AST.mkglobvar ty' [AST.Init_space (Ctypes.sizeof env ty')] false volatile)).

Definition build_composite_env' (types: list Ctypes.composite_definition) :
  res { ce | Ctypes.build_composite_env types = OK ce }.
Proof.
  destruct (Ctypes.build_composite_env types) as [ce|msg].
  - left. exists ce; auto.
  - right. exact msg.
Defined.

Definition check_size (env: Ctypes.composite_env) (id: AST.ident) :=
  match env ! id with
  | Some co =>
      if (Ctypes.co_sizeof co) <=? Ptrofs.max_unsigned
      then OK tt
      else Error [MSG "ObcToClight: structure is too big: '"; CTX id; MSG "'." ]
  | None =>
      Error [MSG "ObcToClight: structure is undefined: '"; CTX id; MSG "'." ]
  end.

Fixpoint check_size_env (env: Ctypes.composite_env) (types: list Ctypes.composite_definition)
  : res unit :=
  match types with
  | nil => OK tt
  | Ctypes.Composite id _ _ _ :: types =>
      do _ <- check_size env id;
      check_size_env env types
  end.

Definition make_program'
           (types: list Ctypes.composite_definition)
           (gvars gvars_vol: list (ident * Ctypes.type))
           (defs: list (ident * AST.globdef Clight.fundef Ctypes.type))
           (public: list ident)
           (main: ident) : res (Ctypes.program Clight.function) :=
  match build_composite_env' types with
  | OK (exist ce P) =>
    do _ <- check_size_env ce types;
      OK {| Ctypes.prog_defs := map (vardef ce false) gvars ++
                                map (vardef ce true) gvars_vol ++
                                defs;
            Ctypes.prog_public := public;
            Ctypes.prog_main := main;
            Ctypes.prog_types := types;
            Ctypes.prog_comp_env := ce;
            Ctypes.prog_comp_env_eq := P |}
  | Error msg => Error msg
  end.

Definition translate (do_sync: bool) (all_public: bool)
                     (main_node: ident) (prog: program): res Clight.program :=
  match find_class main_node prog with
  | Some (c, _) =>
    match find_method step c.(c_methods) with
    | Some m =>
      match find_method reset c.(c_methods) with
      | Some _ =>
        let f := prefix_glob (prefix self main_id) in
        let f_gvar := (f, type_of_inst main_node) in
        let ins := map glob_bind m.(m_in) in
        let outs := map glob_bind m.(m_out) in
        (* revert the declarations ! *)
        let prog := rev prog in
        let cs := map (translate_class prog) prog in
        let (structs, funs) := split cs in
        let main_proved := (main_proved_id, make_main false main_node m) in
        let entry_point := (main_id, make_entry_point do_sync) in
        let gdefs := concat funs
                            ++ (if do_sync
                                then [(sync_id, make_sync);
                                      (main_sync_id, make_main true main_node m)]
                                else [])
                            ++ [main_proved; entry_point]
        in
        make_program' (concat structs)
                      [f_gvar]
                      (outs ++ ins)
                      gdefs
                      (main_id ::
                               (if do_sync then [main_sync_id] else [])
                               ++ (if all_public then map fst (concat funs) else []))
                      main_proved_id
      | None => Error (msg "ObcToClight: reset function not found")
      end
    | None => Error (msg "ObcToClight: step function not found")
    end
  | None => Error [MSG "ObcToClight: undefined node: '"; CTX main_node; MSG "'." ]
  end.
