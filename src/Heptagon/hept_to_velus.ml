(***********************************************************************)
(*                                                                     *)
(*                Heptagon Parsetree -> Velus AST                      *)
(*                                                                     *)
(***********************************************************************)

open Hept_parsetree
open LustreAst

exception Unsupported of string
let unsupported s = raise (Unsupported s)

exception CompileError of string
let compile_error msg loc =
  Location.print_location Format.str_formatter loc;
  raise (CompileError (msg^" at "^(Format.flush_str_formatter ())))

(** Utilities *)

let rec replace_assoc f v = function
  | [] -> []
  | (f', _)::tl when f' = f -> (f', v)::tl
  | hd::tl -> hd::(replace_assoc f v tl)

(** Structured expressions, used to "normalize" structs and arrays *)

type 'a struct_exp =
  | Simple of 'a list
  | Struct of (string * 'a struct_exp) list
  | Array of 'a struct_exp list

let rec struct_flatten = function
  | Simple es -> es
  | Struct fs -> List.concat_map (fun (_, e) -> struct_flatten e) fs
  | Array es -> List.concat_map struct_flatten es

let rec struct_map f = function
  | Simple es -> Simple (f es)
  | Struct fs -> Struct (List.map (fun (s, e) -> (s, struct_map f e)) fs)
  | Array es -> Array (List.map (struct_map f) es)

(** Distribute binary operator *)
let rec struct_map2 f e1 e2 =
  match e1, e2 with
  | Simple es1, Simple es2 -> Simple (f es1 es2)
  | Struct fs1, Struct fs2 ->
    Struct (List.map2 (fun (s, e1) (_, e2) -> (s, struct_map2 f e1 e2)) fs1 fs2)
  | Array es1, Array es2 ->
    Array (List.map2 (struct_map2 f) es1 es2)
  | _, _ -> invalid_arg "struct_map2: incompatible structures"

let struct_distrn es =
  let rec go : 'a struct_exp list -> ('a list) struct_exp = function
    | [] -> invalid_arg "struct_distrn: empty"
    | [e] -> go1 e
    | e1::tl -> go2 e1 (go tl)
  and go1 = function
    | Simple es -> Simple [es]
    | Struct fs -> Struct (List.map (fun (f, e) -> (f, go1 e)) fs)
    | Array es -> Array (List.map go1 es)
  and go2 e1 e2 =
    match e1, e2 with
    | Simple es1, Simple es2 -> Simple (es1::es2)
    | Struct fs1, Struct fs2 ->
      Struct (List.map2 (fun (f, e1) (_, e2) -> (f, go2 e1 e2)) fs1 fs2)
    | Array es1, Array es2 ->
      Array (List.map2 go2 es1 es2)
    | _, _ -> invalid_arg "struct_distrn: incompatible structures"
  in go es

let rec struct_mapn f e =
  struct_map f (struct_distrn e)

(** Compilation environment *)

module Env = Map.Make(String)

type cenv = {
  consts : LustreAst.expression struct_exp Env.t;
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
  | Sarray_power _ -> failwith "TODO: static array_power"
  | Sarray _ -> failwith "TODO: static array"
  | Srecord _ -> failwith "TODO: static record"
  | Sop (f, es) -> [app f (List.concat_map (static_exp env) es) (location se.se_loc)]

let rec exp (env: cenv) e : LustreAst.expression struct_exp =
  match e.e_desc with
  | Econst se -> Simple (static_exp env se)
  | Evar x ->
    (match Env.find_opt x env.consts with
     | Some e -> e
     | None ->
       let ste = decomp_type env x (find_var x env.venv) in
       struct_map (List.map (fun x -> VARIABLE (x, location e.e_loc))) ste)
  | Elast x ->
    let ste = decomp_type env x (find_var x env.venv) in
    struct_map (List.map (fun x -> LAST (x, location e.e_loc))) ste
  | Epre _ -> unsupported "pre"
  | Efby (e1, e2) ->
    let e1 = exp env e1 and e2 = exp env e2 in
    struct_map2 (fun e1 e2 -> [FBY (e1, e2, location e.e_loc)]) e1 e2
  | Estruct fs ->
    let fs = List.map (fun (s, e) -> (shortname s, exp env e)) fs in
    let fs = List.sort (fun (s1, _) (s2, _) -> String.compare s1 s2) fs in
    Struct fs
  | Eapp ({ a_op = Etuple }, es) -> (* List.concat_map (exp env) es *)
    failwith "TODO: tuple"
  | Eapp ({ a_op = Enode f | Efun f; a_params }, es) ->
    (* TODO This is not ideal, as it means we cannot write f(x).[0] *)
    Simple [app f (List.concat_map (flat_exp env) (a_params@es)) (location e.e_loc)]
  | Eapp ({ a_op = Eifthenelse }, [ec; et; ef]) ->
    let ec = flat_exp env ec and et = exp env et and ef = exp env ef in
    struct_map2
      (fun et ef -> [CASE (ec, [(Ident.Ids.true_id, et); (Ident.Ids.false_id, ef)], [], location e.e_loc)])
      et ef
  | Eapp ({ a_op = Earrow }, [e1; e2]) ->
    let e1 = exp env e1 and e2 = exp env e2 in
    struct_map2 (fun e1 e2 -> [ARROW (e1, e2, location e.e_loc)]) e1 e2
  | Eapp ({ a_op = Efield;
            a_params = [{ e_desc = Econst { se_desc = Sfield f } }] },
          [e1]) ->
    (match exp env e1 with
     | Struct fs ->
       (try List.assoc (shortname f) fs
        with Not_found -> compile_error (Printf.sprintf "no field %s" (shortname f)) e.e_loc)
     | _ -> compile_error "not a struct" e.e_loc)
  | Eapp ({ a_op = Efield_update;
            a_params = [{ e_desc = Econst { se_desc = Sfield f } }] },
          [e1;e2]) ->
    (match exp env e1 with
     | Struct fs ->
       Struct (replace_assoc (shortname f) (exp env e2) fs)
     | _ -> compile_error "not a struct" e.e_loc)
  | Eapp ({ a_op = Earray }, es) ->
    Array (List.map (exp env) es)
  | Eapp ({ a_op = Earray_fill;
            a_params = [esize] },
          [e]) ->
    let size = const_int_exp env esize in
    let es = exp env e in
    Array (List.init size (fun _ -> es))
  | Eapp ({ a_op = Eselect;
            a_params = [eidx] },
         [e1]) ->
    let idx = const_int_exp env eidx in
    (match exp env e1 with
     | Array es ->
       (try List.nth es idx
        with Not_found -> compile_error (Printf.sprintf "array index %d out of bound" idx) e.e_loc)
     | _ -> compile_error "not an array" e.e_loc)
  | Eapp ({ a_op = _ }, _) -> unsupported "app"
  | Eiterator _ -> unsupported "iterators"
  | Ewhen (e, c, x) ->
    let e = exp env e and c = constructor c and x = name x and loc = location e.e_loc in
    struct_map (fun es -> [WHEN (es, x, c, loc)]) e
  | Emerge (x, brs) ->
    let x = name x
    and cstrs = List.map (fun (c, _) -> constructor c) brs
    and es = List.map (fun (_, e) -> exp env e) brs
    and loc = location e.e_loc in
    struct_mapn (fun es -> [MERGE (x, List.map2 (fun c e -> (c, e)) cstrs es, loc)]) es
  | Esplit _ -> unsupported "split"

and flat_exp env e = struct_flatten (exp env e)

and const_int_exp env e =
  match exp env e with
  | Simple [CONSTANT (CONST_INT s, _)] -> int_of_string s
  | _ -> unsupported "Array with non-constant size"

(** Decompose a variable [n] with type [ty] *)
and decomp_type env n ty =
  match ty with
  | Tprod tys ->
    (* List.flatten *)
    (*   (List.mapi (fun i -> decomp_type env (postfix n (string_of_int i))) tys) *)
    failwith "TODO: decomp prod"
  | Tarray (ty, e) ->
    let size = const_int_exp env e in
    Array (List.init size (fun i -> decomp_type env (postfix n (string_of_int i)) ty))
  | Tinvalid -> failwith "Invalid type ?"
  | Tid tn ->
    match Env.find_opt (shortname tn) env.types with
    | Some (Type_alias ty) -> decomp_type env n ty
    | Some (Type_struct fs) ->
      Struct (List.map (fun (f, ty) -> (f, decomp_type env (postfix n f) ty)) fs)
    | _ -> Simple [name n]

(** Number of scalar values represented by [ty] *)
and size_type env ty =
  match ty with
  | Tprod tys ->
    List.fold_left (fun acc ty -> acc + size_type env ty) 0 tys
  | Tarray (ty, e) ->
    let size = const_int_exp env e in
    size * (size_type env ty)
  | Tinvalid -> failwith "Invalid type ?"
  | Tid tn ->
    match Env.find_opt (shortname tn) env.types with
    | Some (Type_alias ty) -> size_type env ty
    | Some (Type_struct fs) ->
      List.fold_left (fun acc (f, ty) -> acc + size_type env ty) 0 fs
    | _ -> 1

(** Find the record definition with field [f] and its index *)
and find_record_index env f =
  let rec aux fs n =
    match fs with
    | [] -> invalid_arg "find_record_index"
    | (f', ty)::_ when f' = f -> n, size_type env ty
    | (_, ty)::fs -> aux fs (n + size_type env ty)
  in aux (find_record env f) 0

let escape env esc =
  ((flat_exp env esc.e_cond,
    (name esc.e_next_state, esc.e_reset)),
   location esc.e_cond.e_loc)

let last_decl env vd =
  match vd.v_last with
  | Last (Some e) -> Some (name vd.v_name, flat_exp env e, location vd.v_loc)
  | _ -> None

let rec ty env ((n, (clock, loc)) as decl) = function
  | Tprod _ -> unsupported "product types"
  | Tid (ToQ tn) ->
    (match Env.find_opt tn env.types with
     | Some (Type_alias t) -> ty env decl t
     | Some (Type_struct fs) ->
       List.concat_map (fun (f, t) -> ty env (postfix n f, (clock, loc)) t) fs
     | _ -> [(name n, ((type_name tn, clock), loc))])
  | Tid _ -> unsupported "qualified names"
  | Tarray (t, e) ->
    let size = const_int_exp env e in
    List.flatten (List.init size (fun i -> ty env (postfix n (string_of_int i), (clock, loc)) t))
  | Tinvalid -> failwith "Invalid type ?"

let var_dec env vd =
  let decl = (vd.v_name, (opt_ck vd.v_clock, location vd.v_loc)) in
  ty env decl vd.v_type

let rec pat env = function
  | Etuplepat pats -> List.concat_map (pat env) pats
  | Evarpat n ->
    struct_flatten (decomp_type env n (find_var n env.venv))

let rec eq env eq =
  match eq.eq_desc with
  | Eautomaton sts -> BAUTO (([], name (List.hd sts).s_state),
                             List.map (state_handler env) sts,
                             location eq.eq_loc)
  | Eswitch (e, brs) -> BSWITCH (flat_exp env e,
                                 List.map (switch_handler env) brs, location eq.eq_loc)
  | Epresent _ -> unsupported "present"
  | Ereset (blk, e) -> BRESET ([block env [] blk], flat_exp env e, location eq.eq_loc)
  | Eblock blk -> block env [] blk
  | Eeq (p, _, e) -> BEQ ((pat env p, flat_exp env e), location eq.eq_loc)

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
