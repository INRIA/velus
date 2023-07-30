(***********************************************************************)
(*                                                                     *)
(*                Heptagon Parsetree -> Velus AST                      *)
(*                                                                     *)
(***********************************************************************)

open Hept_parsetree
open LustreAst

exception Unsupported of string

(** Compilation environment *)

module Env = Map.Make(String)

type cenv = {
  consts : (LustreAst.expression list) Env.t;
  types  : type_desc Env.t;
  venv   : ty Env.t;
  decls  : LustreAst.declaration list
}

(* exception TypeNotFound of string *)

(* let find_type tn env = *)
(*   match Env.find_opt tn env with *)
(*   | Some td -> td *)
(*   | None -> raise (TypeNotFound tn) *)

exception VarNotFound of string

let find_var tn env =
  match Env.find_opt tn env with
  | Some ty -> ty
  | None -> raise (VarNotFound tn)

let unsupported s = raise (Unsupported s)

let name (n : Names.name) : Common.ident =
  Camlcoq.intern_string n

let postfix x1 x2 = x1^"_"^x2

(* let string_of_qualname = function *)
(*   | ToQ n -> n *)
(*   | Q qual -> Names.shortname qual *)

let shortname = function
  | ToQ n -> n
  | Q qn -> Names.shortname qn

let qualname = function
  | ToQ n -> name n
  | Q _ -> unsupported "qualified name"

let constructor n =
  match shortname n with
  | "true" -> Ident.Ids.true_id
  | "false" -> Ident.Ids.false_id
  | n -> name n

let location =
  let nextident = ref 0 in
  let getident () =
    nextident := !nextident + 1;
    !nextident
  in
  fun (loc: Location.location) ->
    let Loc (startp, endp) = loc in
    { ast_lnum = startp.pos_lnum;
      ast_cnum = startp.pos_cnum;
      ast_fname = startp.pos_fname;
      ast_bol = startp.pos_bol;
      ast_ident = getident ()
    }

let type_name tn =
  match tn with
  | "int8" -> Tint8
  | "int16" -> Tint16
  | "int" | "int32" -> Tint32
  | "int64" -> Tint64
  | "uint8" -> Tuint8
  | "uint16" -> Tuint16
  | "uint32" -> Tuint32
  | "uint64" -> Tuint64
  | "float" | "float32" -> Tfloat32
  | "real" | "float64" -> Tfloat64
  | s -> Tenum_name (name s)

let rec ty env ((n, (clock, loc)) as decl) = function
  | Tprod _ -> unsupported "product types"
  | Tid (ToQ tn) ->
    (match Env.find_opt tn env.types with
     | Some (Type_alias t) -> ty env decl t
     | Some (Type_struct fs) ->
       List.concat_map (fun (f, t) -> ty env (postfix n f, (clock, loc)) t) fs
     | _ -> [(name n, ((type_name tn, clock), loc))])
  | Tid _ -> unsupported "qualified names"
  | Tarray _ -> failwith "TODO: array"
  | Tinvalid -> failwith "Invalid type ?"

let rec full_ck = function
  | Cbase -> BASE
  | Con (ck, c, x) -> ON (full_ck ck, name x, constructor c)
  | Cwhen _ -> invalid_arg "full_ck"

let pre_ck = function
  | Cwhen (c, x) -> WHENCK (name x, constructor c)
  | ck -> FULLCK (full_ck ck)

let opt_ck = function
  | None -> FULLCK BASE
  | Some ck -> pre_ck ck

let var_dec env vd =
  let decl = (vd.v_name, (opt_ck vd.v_clock, location vd.v_loc)) in
  ty env decl vd.v_type

(** Number of scalar values represented by [ty] *)
let rec size_type env ty =
  match ty with
  | Tprod tys ->
    List.fold_left (fun acc ty -> acc + size_type env ty) 0 tys
  | Tarray (ty, _) -> failwith "TODO: tarray"
  | Tinvalid -> failwith "Invalid type ?"
  | Tid tn ->
    match Env.find_opt (shortname tn) env.types with
    | Some (Type_alias ty) -> size_type env ty
    | Some (Type_struct fs) ->
      List.fold_left (fun acc (f, ty) -> acc + size_type env ty) 0 fs
    | _ -> 1

(** Decompose a variable [n] with type [ty] *)
let rec decomp_type env n ty =
  match ty with
  | Tprod tys ->
    List.flatten
      (List.mapi (fun i -> decomp_type env (postfix n (string_of_int i))) tys)
  | Tarray (ty, _) -> failwith "TODO: tarray"
  | Tinvalid -> failwith "Invalid type ?"
  | Tid tn ->
    match Env.find_opt (shortname tn) env.types with
    | Some (Type_alias ty) -> decomp_type env n ty
    | Some (Type_struct fs) ->
      List.concat_map (fun (f, ty) -> decomp_type env (postfix n f) ty) fs
    | _ -> [name n]

(** Find the record definition with field [f] *)
let find_record env f =
  match
    Env.fold
      (fun _ td acc ->
         if Option.is_some acc then acc else
           match td with
           | Type_struct fs ->
             if List.mem_assoc f fs then Some fs else None
           | _ -> None)
      env.types None
  with Some fs -> fs | None -> invalid_arg "find_record"

(** Find the record definition with field [f] and its index *)
let find_record_index env f =
  let rec aux fs n =
    match fs with
    | [] -> invalid_arg "find_record_index"
    | (f', ty)::_ when f' = f -> n
    | (_, ty)::fs -> aux fs (n + size_type env ty)
  in aux (find_record env f) 0

let rec pat env = function
  | Etuplepat pats -> List.concat_map (pat env) pats
  | Evarpat n ->
    decomp_type env n (find_var n env.venv)

(** Application of node or operator *)
let app f es loc =
  match f, es with
  | ToQ ("~-" | "~-."), [e1] -> UNARY (MINUS, [e1], loc)
  (* TODO NOT? *)
  | ToQ "not", [e1] -> UNARY (BNOT, [e1], loc)

  | ToQ ("+" | "+."), [e1;e2] -> BINARY (ADD, [e1], [e2], loc)
  | ToQ ("-" | "-."), [e1;e2] -> BINARY (SUB, [e1], [e2], loc)
  | ToQ ("*" | "*."), [e1;e2] -> BINARY (MUL, [e1], [e2], loc)
  | ToQ ("/" | "/."), [e1;e2] -> BINARY (DIV, [e1], [e2], loc)
  | ToQ "%", [e1;e2] -> BINARY (MOD, [e1], [e2], loc)

  | ToQ "and", [e1;e2] -> BINARY (BAND, [e1], [e2], loc)
  | ToQ "or", [e1;e2] -> BINARY (BOR, [e1], [e2], loc)

  | ToQ "&", [e1;e2] -> BINARY (LAND, [e1], [e2], loc)
  | ToQ "|", [e1;e2] -> BINARY (LOR, [e1], [e2], loc)
  | ToQ "^", [e1;e2] -> BINARY (XOR, [e1], [e2], loc)
  | ToQ "<<", [e1;e2] -> BINARY (LSL, [e1], [e2], loc)
  | ToQ ">>", [e1;e2] -> BINARY (LSR, [e1], [e2], loc)

  | ToQ "=", [e1;e2] -> BINARY (EQ, [e1], [e2], loc)
  | ToQ "<>", [e1;e2] -> BINARY (NE, [e1], [e2], loc)
  | ToQ ("<" | "<."), [e1;e2] -> BINARY (LT, [e1], [e2], loc)
  | ToQ (">" | ">."), [e1;e2] -> BINARY (GT, [e1], [e2], loc)
  | ToQ ("<=" | "<=."), [e1;e2] -> BINARY (LE, [e1], [e2], loc)
  | ToQ (">=" | ">=."), [e1;e2] -> BINARY (GE, [e1], [e2], loc)

  | _, _ -> APP (qualname f, es, [], loc)

(** Add local declarations to the env *)
let add_decls env vds =
  { env with
    consts = Env.filter (fun x _ -> not (List.mem x (List.map (fun vd -> vd.v_name) vds))) env.consts;
    venv = Env.add_seq (List.to_seq (List.map (fun vd -> (vd.v_name, vd.v_type)) vds)) env.venv }

(** Compilation of exprs, equations, blocks *)

let rec static_exp (env: cenv) se =
  match se.se_desc with
  | Svar cname -> failwith "TODO: const"
  | Sint i -> [CONSTANT (CONST_INT (string_of_int i), location se.se_loc)]
  | Sfloat f ->
    let (f, i) = Float.modf f in
    let i =
      match String.split_on_char '.' (string_of_float i) with
      | i::_ -> i
      | _ -> "0"
    and f =
      match String.split_on_char '.' (string_of_float f) with
      | _::f::_ -> f
      | _ -> "0" in
    [CONSTANT (CONST_FLOAT {
      isHex_FI = false;
      integer_FI = Some i;
      fraction_FI = Some f;
      exponent_FI = None;
      suffix_FI = None;
    }, location se.se_loc)]
  | Sbool true -> [CONSTANT (CONST_ENUM Ident.Ids.true_id, location se.se_loc)]
  | Sbool false -> [CONSTANT (CONST_ENUM Ident.Ids.false_id, location se.se_loc)]
  | Sstring _ -> unsupported "string"
  | Sconstructor n -> [CONSTANT (CONST_ENUM (constructor n), location se.se_loc)]
  | Sfield f -> invalid_arg "static_exp: field"
  | Stuple es -> List.concat_map (static_exp env) es
  | Sarray_power _ -> failwith "TODO: array_power"
  | Sarray _ -> failwith "TODO: array"
  | Srecord _ -> failwith "TODO: record"
  | Sop (f, es) -> [app f (List.concat_map (static_exp env) es) (location se.se_loc)]

let rec exp (env: cenv) e =
  match e.e_desc with
  | Econst se -> static_exp env se
  | Evar x ->
    (match Env.find_opt x env.consts with
     | Some e -> e
     | None ->
       let vs = decomp_type env x (find_var x env.venv) in
       List.map (fun x -> VARIABLE (x, location e.e_loc)) vs)
  | Elast x ->
    let vs = decomp_type env x (find_var x env.venv) in
    List.map (fun x -> LAST (x, location e.e_loc)) vs
  | Epre _ -> unsupported "pre"
  | Efby (e1, e2) -> [FBY (exp env e1, exp env e2, location e.e_loc)]
  | Estruct fs ->
    let fs = List.map (fun (s, e) -> (shortname s, exp env e)) fs in
    let fs = List.sort (fun (s1, _) (s2, _) -> String.compare s1 s2) fs in
    List.concat_map snd fs
  | Eapp ({ a_op = Etuple }, es) -> List.concat_map (exp env) es
  | Eapp ({ a_op = Enode f | Efun f; a_params }, es) ->
    [app f (List.concat_map (exp env) (a_params@es)) (location e.e_loc)]
  | Eapp ({ a_op = Eifthenelse }, [ec; et; ef]) ->
    [CASE (exp env ec, [(Ident.Ids.true_id, exp env et); (Ident.Ids.false_id, exp env ef)], [], location e.e_loc)]
  | Eapp ({ a_op = Earrow }, [e0; e1]) -> [ARROW (exp env e0, exp env e1, location e.e_loc)]
  | Eapp ({ a_op = Efield;
            a_params = [{ e_desc = Econst { se_desc = Sfield f } }] },
          [e]) ->
    let es = exp env e in
    [List.nth es (find_record_index env (shortname f))]
  | Eapp ({ a_op = Efield_update;
            a_params = [{ e_desc = Econst { se_desc = Sfield f } }] },
          [e1;e2]) ->
    let rec replace e1s e2s n =
      (match e1s, e2s, n with
      | [], _, _ -> []
      | e1s, [], _ -> e1s
      | _::e1s, e2::e2s, 0 -> e2::replace e1s e2s 0
      | e1::e1s, e2s, n -> e1::replace e1s e2s (n - 1))
    in replace (exp env e1) (exp env e2) (find_record_index env (shortname f))
  | Eapp ({ a_op = Earray }, _) -> failwith "TODO: array"
  | Eapp ({ a_op = Earray_fill }, _) -> failwith "TODO: array_fill"
  | Eapp ({ a_op = _ }, _) -> unsupported "app"
  | Eiterator _ -> unsupported "iterators"
  | Ewhen (e, c, x) -> [WHEN (exp env e, name x, constructor c, location e.e_loc)]
  | Emerge (x, brs) -> [MERGE (name x, List.map (fun (c, e) -> (constructor c, exp env e)) brs, location e.e_loc)]
  | Esplit _ -> unsupported "split"

let escape env esc =
  ((exp env esc.e_cond, (name esc.e_next_state, esc.e_reset)), location esc.e_cond.e_loc)

let last_decl env vd =
  match vd.v_last with
  | Last (Some e) -> Some (name vd.v_name, exp env e, location vd.v_loc)
  | _ -> None

let rec eq env eq =
  match eq.eq_desc with
  | Eautomaton sts -> BAUTO (([], name (List.hd sts).s_state),
                             List.map (state_handler env) sts,
                             location eq.eq_loc)
  | Eswitch (e, brs) -> BSWITCH (exp env e, List.map (switch_handler env) brs, location eq.eq_loc)
  | Epresent _ -> unsupported "present"
  | Ereset (blk, e) -> BRESET ([block env [] blk], exp env e, location eq.eq_loc)
  | Eblock blk -> block env [] blk
  | Eeq (p, _, e) -> BEQ ((pat env p, exp env e), location eq.eq_loc)

and block env lasts1 blk =
  let env' = add_decls env blk.b_local in
  let lasts2 = List.filter_map (last_decl env') blk.b_local in
  BLOCAL (List.concat_map (var_dec env) blk.b_local,
          List.map (eq env') blk.b_equs@
          List.map (fun (x, e, loc) -> BLAST (x, e, loc)) (lasts1@lasts2),
          location blk.b_loc)

and switch_handler env br =
  (constructor br.w_name, [block env [] br.w_block])

and state_handler env st =
  let env' = add_decls env st.s_block.b_local in
  let lasts = List.filter_map (last_decl env') st.s_block.b_local in
  (name st.s_state,
   (((List.concat_map (var_dec env) st.s_block.b_local,
      List.map (eq env') st.s_block.b_equs@
      List.map (fun (x, e, loc) -> BLAST (x, e, loc)) lasts),
     List.map (escape env') st.s_until),
    List.map (escape env') st.s_unless))

let node_dec env nd =
  let lasts = List.filter_map (last_decl env) nd.n_output in
  let env = add_decls env (nd.n_params@nd.n_input@nd.n_output) in
  NODE (name nd.n_name, nd.n_stateful,
        List.concat_map (var_dec env) (nd.n_params@nd.n_input),
        List.concat_map (var_dec env) nd.n_output,
        block env lasts nd.n_block,
        location nd.n_loc)

let type_dec env ty =
  match ty.t_desc with
  | Type_abs -> unsupported "abstract types"
  | Type_enum decs ->
    { env with decls =
                 (TYPE (name ty.t_name,
                        List.map name decs,
                        location ty.t_loc))::env.decls }
  | Type_alias _ ->
    { env with types = Env.add ty.t_name ty.t_desc env.types }
  | Type_struct fs ->
    (* We order fields by lexicographic order *)
    let fs = List.sort (fun (s1, _) (s2, _) -> String.compare s1 s2) fs in
    { env with types = Env.add ty.t_name (Type_struct fs) env.types }

let program_desc env = function
  | Ppragma _ -> unsupported "pragmas"
  | Ptype ty -> type_dec env ty
  | Pconst cd -> { env with consts = Env.add cd.c_name (exp env cd.c_value) env.consts }
  | Pnode n -> { env with decls = (node_dec env n)::env.decls }

let program (p : program) : declaration list =
  let init_env = { consts = Env.empty; types = Env.empty; decls = []; venv = Env.empty } in
  let env =  List.fold_left program_desc init_env p.p_desc in
  List.rev env.decls
