open Errors
open Camlcoq
open Printf
open Clight
open C2C
open Builtins
    
let print_error oc msg =
  let print_one_error = function
  | Errors.MSG s -> output_string oc (camlstring_of_coqstring s)
  | Errors.CTX i -> output_string oc (extern_atom i)
  | Errors.POS i -> fprintf oc "%ld" (P.to_int32 i)
  in
    List.iter print_one_error msg;
    output_char oc '\n'
  
let add_builtin p (name, (out, ins, b)) =
  let env = Env.empty in
  let id = intern_string name in
  let id' = coqstring_of_camlstring name in
  let targs = List.map (convertTyp env) ins |> MinimpToClight.list_type_to_typelist in
  let tres = convertTyp env out in
  let sg = Ctypes.signature_of_type targs tres AST.cc_default in
  let ef =
    if name = "malloc" then AST.EF_malloc else
    if name = "free" then AST.EF_free else
    if Str.string_match re_builtin name 0
    && List.mem_assoc name builtins_generic.functions
    then AST.EF_builtin (id', sg)
    else AST.EF_external (id', sg) in
  let decl = (id, AST.Gfun (External (ef, targs, tres, AST.cc_default))) in
  { p with prog_defs = decl :: p.prog_defs }
  
let add_builtins p =
  List.fold_left add_builtin p builtins_generic.functions
  
let _ =
  Sections.initialize();
  match MinimpToClight.(translate [example] (intern_string "count")) with
  | Error errmsg -> print_error stderr errmsg
  | OK p ->
    PrintClight.print_program Format.std_formatter p;
    let p = add_builtins p in
    match Compiler.transf_clight_program p with
    | Error errmsg -> print_error stderr errmsg
    | OK p -> print_endline "Compilation OK"
