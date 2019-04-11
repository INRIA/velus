(* *********************************************************************)
(*                                                                     *)
(*                    The Velus Lustre compiler                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

open Frustre

module PP = Frustre_pp

let cltype = function
  | Tint (sz, sg) -> Ctypes.(Tint (sz, sg, noattr))
  | Tlong sg      -> Ctypes.(Tlong (sg,
                        { attr_volatile = false;
                          attr_alignas = Some (Camlcoq.N.of_int 3) }))
  | Tfloat sz     -> Ctypes.(Tfloat (sz, noattr))

let typecl = function
  | Ctypes.Tint (sz, sg, attr) -> Some (Tint (sz, sg))
  | Ctypes.Tlong (sg, attr)    -> Some (Tlong sg)
  | Ctypes.Tfloat (sz, attr)   -> Some (Tfloat sz)
  | _ -> None

let cluop = function
  | Eneg     -> Cop.Oneg
  | Enotint  -> Cop.Onotint
  | Enotbool -> Cop.Onotbool
  | Ecast _  -> assert false

let clbop = function
  | Eadd -> Cop.Oadd
  | Esub -> Cop.Osub
  | Emul -> Cop.Omul
  | Ediv -> Cop.Odiv
  | Emod -> Cop.Omod
  | Eand -> Cop.Oand
  | Eor  -> Cop.Oor
  | Exor -> Cop.Oxor
  | Eshl -> Cop.Oshl
  | Eshr -> Cop.Oshr
  | Eeq  -> Cop.Oeq
  | Ene  -> Cop.One
  | Elt  -> Cop.Olt
  | Egt  -> Cop.Ogt
  | Ele  -> Cop.Ole
  | Ege  -> Cop.Oge

let is_bool_type = function
  | Tint (Ctypes.IBool, sg) -> true
  | _ -> false

let is_bool_types = function
  | [ty] -> is_bool_type ty
  | _ -> false

let type_unop uop ty =
  match uop with
  | Ecast ty' -> begin
      match Ctyping.check_cast (cltype ty) (cltype ty') with
      | Errors.OK _ -> Some ty'
      | Errors.Error _ -> None
      end
  | Enotbool -> Some typ_bool
  | op -> begin
      match Ctyping.type_unop (cluop op) (cltype ty) with
      | Errors.OK ty' -> typecl ty'
      | Errors.Error _ -> None
      end

let binop_always_returns_bool = function
  | Eeq | Ene | Elt | Egt | Ele | Ege -> true
  | _ -> false

let is_bool_binop = function Eand | Eor | Exor -> true | _ -> false

let type_binop op ty1 ty2 =
  if binop_always_returns_bool op
       || (is_bool_binop op && (is_bool_type ty1 && is_bool_type ty2))
    then Some typ_bool
    else match Ctyping.type_binop (clbop op) (cltype ty1) (cltype ty2) with
         | Errors.OK ty'  -> typecl ty'
         | Errors.Error _ -> None

let init_type = function
  | Tint (sz, sg)     -> Cint (Integers.Int.zero, sz, sg)
  | Tlong sg          -> Clong (Integers.Int64.zero, sg)
  | Tfloat Ctypes.F64 -> Cfloat Floats.Float.zero
  | Tfloat Ctypes.F32 -> Csingle Floats.Float32.zero

let const = function
  | Cint (v, sz, sg) -> Tint (sz, sg)
  | Clong (v, sg)    -> Tlong sg
  | Cfloat v         -> Tfloat Ctypes.F64
  | Csingle v        -> Tfloat Ctypes.F32

let sprintf = Format.asprintf
let pp_loc = Frustre_of_ast.formatloc

exception TypingError

let error loc s =
  Format.eprintf "@[%a:%s@.@]" pp_loc loc s;
  raise TypingError

let expected_got loc tye tyg =
  error loc (sprintf "mismatched types:@[<hov>expected [@[%a@]]@ got [@[%a@]]@]"
                 PP.typs tye PP.typs tyg)

let tyvar env loc x = try (Env.find x env).v_typ with Not_found ->
  error loc (sprintf "undeclared variable '%a'" PP.ident x)

let exp genv env =
  let rec f e =
    let tyvar = tyvar env e.e_loc in
    let tys =
      match e.e_desc with
      | Econst c -> [const c]
      | Evar x   -> [tyvar x]

      | Eunop (op, e') ->
          (match f e' with
           | [ty] ->
             (match type_unop op ty with
              | None -> error e.e_loc
                 (sprintf "cannot apply operator to value of type %a"
                    PP.typ ty)
              | Some ty -> [ty])
           | _ -> error e.e_loc
                    (sprintf "cannot apply unary operator to more than one flow"))

      | Ebinop (op, e1, e2) ->
          (match f e1, f e2 with
           | [ty1], [ty2] ->
               (match type_binop op ty1 ty2 with
                | None -> error e.e_loc
                   (sprintf "cannot apply operator to values of type %a and %a"
                      PP.typ ty1 PP.typ ty2)
                | Some ty -> [ty])
           | _, _ -> error e.e_loc
               (sprintf "cannot apply binary operator to more than two flows"))

      | Efby (e0s, es) ->
          let ty0s = List.(concat (map f e0s)) in
          let tys  = List.(concat (map f es)) in
          if ty0s = tys then tys
          else error e.e_loc (sprintf "mismatched types: %a versus %a"
               PP.typs ty0s PP.typs tys)

      | Ewhen (es, x, b) ->
          if not (is_bool_type (tyvar x))
          then error e.e_loc (sprintf "%a is not of type bool" PP.ident x)
          else List.(concat (map f es))

      | Emerge (x, ets, efs) ->
          if not (is_bool_type (tyvar x))
          then error e.e_loc (sprintf "%a is not of type bool" PP.ident x)
          else
            let ttys  = List.(concat (map f ets)) in
            let ftys  = List.(concat (map f efs)) in
            if ttys = ftys then ttys
            else error e.e_loc (sprintf "mismatched types: %a versus %a"
                 PP.typs ttys PP.typs ftys)

      | Eite (eb, ets, efs) ->
          let bty = f eb in
          let ttys  = List.(concat (map f ets)) in
          let ftys  = List.(concat (map f efs)) in
          if not (is_bool_types bty)
          then error eb.e_loc (sprintf "expected bool got [%a]" PP.typs bty)
          else if ttys = ftys then ttys
               else error e.e_loc (sprintf "mismatched types: %a versus %a"
                                     PP.typs ttys PP.typs ftys)

      | Eapp (n, es) ->
          let tys = List.(concat (map f es)) in
          let (itys, otys) = try Env.find n genv
            with Not_found -> error e.e_loc
              (sprintf "use of undeclared node '%a'" PP.ident n)
          in
          if tys = itys then otys
          else expected_got e.e_loc itys tys
    in
    e.e_typ <- tys;
    tys
  in
  f

let check_defined loc defined x =
  if ISet.mem x defined
  then error loc (sprintf "duplicate definition of '%a'" PP.ident x)
  else ISet.add x defined

let equation genv env defined { eq_desc = (xs, es); eq_loc } =
  let tyvar = tyvar env eq_loc in
  let xtys = List.map tyvar xs in
  let etys = List.(concat (map (exp genv env) es)) in
  if xtys <> etys then expected_got eq_loc etys xtys
  else List.fold_left (check_defined eq_loc) defined xs

let node loc genv { n_name; n_hasstate; n_in; n_out; n_vars; n_eqs; n_env } =
  try
    if Env.mem n_name genv
      then error loc (sprintf "node already defined '%a'" PP.ident n_name);
    let defined = List.fold_left (equation genv n_env) ISet.empty n_eqs in
    let check_def x = if not (ISet.mem x defined)
      then error loc (sprintf "undefined variable '%a'" PP.ident x)
    in
    let tyvar = tyvar n_env loc in
    let check_and_type x = check_def x; tyvar x in
    let itys = List.map tyvar n_in in
    let () = List.iter check_def n_vars in
    let otys = List.map check_and_type n_out in
    Env.add n_name (itys, otys) genv
  with TypingError ->
    (Format.eprintf "typing error in node '%a'@." PP.ident n_name; exit 1)

let implementation genv { desc; loc } =
  match desc with
  | Enodedecl n -> node loc genv n

let global = List.fold_left implementation Env.empty

(*
module Operators : OPERATORS =
  struct
    type coq_val = unit
    type coq_type = typ

    type _const = const
    type const = _const

    let bool_type = typ_bool

    type _unop = unop
    type unop = _unop

    type _binop = binop
    type binop = _binop

    let type_const = function
      | Cint (_, sz, sg) -> Tint (sz, sg)
      | Clong (_, sg)    -> Tlong sg
      | Cfloat           -> Tfloat Ctypes.F64
      | Csingle          -> Tfloat Ctypes.F32

    let type_unop  = type_unop
    let type_binop = type_binop

    let init_type = init_type

    let true_val = ()
    let false_val = ()
    let sem_const _ = ()
    let sem_unop _ _ _ = None
    let sem_binop _ _ _ _ _ = None

    let val_dec    v1  v2 = (v1 = v2)
    let type_dec  ty1 ty2 = (ty1 = ty2)
    let const_dec  c1  c2 = (c1 = c2)
    let unop_dec  op1 op2 = (op1 = op2)
    let binop_dec op1 op2 = (op1 = op2)
  end
*)

