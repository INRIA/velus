(***********************************************************************)
(*                                                                     *)
(*                Heptagon Parsetree -> Velus AST                      *)
(*                                                                     *)
(***********************************************************************)

open Hept_parsetree
open LustreAst

exception Unsupported of string

let unsupported s = raise (Unsupported s)

let name (n : Names.name) : Common.ident =
  Camlcoq.intern_string n

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

let type_dec ty =
  match ty.t_desc with
  | Type_abs -> unsupported "abstract types"
  | Type_alias ty -> unsupported "type aliases"
  | Type_enum decs -> Some (TYPE (name ty.t_name,
                                  List.map name decs,
                                  location ty.t_loc))
  | Type_struct _ -> None (* TODO use to compile structures *)

let ty = function
  | Tprod _ -> unsupported "product types"
  | Tid (ToQ n) -> type_name n
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

let var_dec vd =
  (* TODO last *)
  (name vd.v_name,
   ((ty vd.v_type,
     opt_ck vd.v_clock),
    location vd.v_loc))

let rec pat = function
  | Etuplepat pats -> List.concat_map pat pats
  | Evarpat v -> [name v]

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

let rec static_exp se =
  match se.se_desc with
  | Svar cname -> failwith "TODO: const"
  | Sint i -> [CONSTANT (CONST_INT (string_of_int i), location se.se_loc)]
  | Sfloat f ->
    let (f, i) = Float.modf f in
    let i = List.nth (String.split_on_char '.' (string_of_float i)) 0
    and f = List.nth (String.split_on_char '.' (string_of_float f)) 1 in
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
  | Sfield f -> failwith "TODO: field"
  | Stuple es -> List.concat_map static_exp es
  | Sarray_power _ -> failwith "TODO: array_power"
  | Sarray _ -> failwith "TODO: array"
  | Srecord _ -> failwith "TODO: record"
  | Sop (f, es) -> [app f (List.concat_map static_exp es) (location se.se_loc)]

let rec exp e =
  match e.e_desc with
  | Econst se -> static_exp se
  | Evar x -> [VARIABLE (name x, location e.e_loc)] (* TODO constants *)
  | Elast x -> [LAST (name x, location e.e_loc)]
  | Epre _ -> unsupported "pre"
  | Efby (e1, e2) -> [FBY (exp e1, exp e2, location e.e_loc)]
  | Estruct _ -> failwith "TODO: struct"
  | Eapp ({ a_op = Etuple }, es) -> List.concat_map exp es
  | Eapp ({ a_op = Enode f | Efun f }, es) ->
    [app f (List.concat_map exp es) (location e.e_loc)]
  | Eapp ({ a_op = Eifthenelse }, [ec; et; ef]) ->
    [CASE (exp ec, [(Ident.Ids.true_id, exp et); (Ident.Ids.false_id, exp ef)], [], location e.e_loc)]
  | Eapp ({ a_op = Earrow }, [e0; e1]) -> [ARROW (exp e0, exp e1, location e.e_loc)]
  | Eapp ({ a_op = Efield }, _) -> failwith "TODO: field"
  | Eapp ({ a_op = Efield_update}, _) -> failwith "TODO: field update"
  | Eapp ({ a_op = Earray}, _) -> failwith "TODO: array"
  | Eapp ({ a_op = Earray_fill}, _) -> failwith "TODO: array_fill"
  | Eapp ({ a_op = _ }, _) -> unsupported "app"
  | Eiterator _ -> unsupported "iterators"
  | Ewhen (e, c, x) -> [WHEN (exp e, name x, constructor c, location e.e_loc)]
  | Emerge (x, brs) -> [MERGE (name x, List.map (fun (c, e) -> (constructor c, exp e)) brs, location e.e_loc)]
  | Esplit _ -> unsupported "split"

let escape esc =
  ((exp esc.e_cond, (name esc.e_next_state, esc.e_reset)), location esc.e_cond.e_loc)

let last_decl vd =
  match vd.v_last with
  | Last (Some e) -> Some (name vd.v_name, exp e, location vd.v_loc)
  | _ -> None

let rec eq eq =
  match eq.eq_desc with
  | Eautomaton sts -> BAUTO (([], name (List.hd sts).s_state),
                             List.map state_handler sts,
                             location eq.eq_loc)
  | Eswitch (e, brs) -> BSWITCH (exp e, List.map switch_handler brs, location eq.eq_loc)
  | Epresent _ -> unsupported "present"
  | Ereset (blk, e) -> BRESET ([block [] blk], exp e, location eq.eq_loc)
  | Eblock blk -> block [] blk
  | Eeq (p, _, e) -> BEQ ((pat p, exp e), location eq.eq_loc)

and block lasts1 blk =
  let lasts2 = List.filter_map last_decl blk.b_local in
  BLOCAL (List.map var_dec blk.b_local,
          List.map eq blk.b_equs@
          List.map (fun (x, e, loc) -> BLAST (x, e, loc)) (lasts1@lasts2),
          location blk.b_loc)

and switch_handler br =
  (constructor br.w_name, [block [] br.w_block])

and state_handler st =
  let lasts = List.filter_map last_decl st.s_block.b_local in
  (name st.s_state,
   (((List.map var_dec st.s_block.b_local,
      List.map eq st.s_block.b_equs@
      List.map (fun (x, e, loc) -> BLAST (x, e, loc)) lasts),
     List.map escape st.s_until),
    List.map escape st.s_unless))

let node_dec nd =
  let lasts = List.filter_map last_decl nd.n_output in
  NODE (name nd.n_name, nd.n_stateful,
       List.map var_dec nd.n_input,
       List.map var_dec nd.n_output,
       block lasts nd.n_block,
       location nd.n_loc)

let program_desc = function
  | Ppragma _ -> unsupported "pragmas"
  | Ptype ty -> type_dec ty
  | Pconst _ -> None (* TODO use to rewrite constant use *)
  | Pnode n -> Some (node_dec n)

let program (p : program) : declaration list =
  List.filter_map program_desc p.p_desc
