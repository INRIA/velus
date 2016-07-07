open Errors
open Camlcoq
open Printf
open Clight
open C2C
open Builtins
open Ctypes
    
open Location

let print_c = ref false
let write_c = ref false

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
  let targs = List.map (convertTyp env) ins |> Translation0.list_type_to_typelist in
  let tres = convertTyp env out in
  let sg = signature_of_type targs tres AST.cc_default in
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

exception Erroneous_program

let syntax_error loc =
  Printf.eprintf "%aSyntax error.\n" output_location loc;
  raise Erroneous_program

let compilation_error loc =
  Printf.eprintf "%aCompilation error.\n" output_location loc;
  raise Erroneous_program

let parse parsing_fun lexing_fun lexbuf =
  try
    parsing_fun lexing_fun lexbuf
  with
    Parsing.Parse_error ->
    begin
	  let pos1 = Lexing.lexeme_start lexbuf
	  and pos2 = Lexing.lexeme_end lexbuf in
	  let l = { loc_fst = pos1;
		        loc_end = pos2 } in
	  syntax_error l
    end

let parse_implementation lexbuf =
  parse Parser.program Lexer.token lexbuf

let compile filename =
  let source_name = filename ^ ".cdf" in
  let ic = open_in source_name in
  try
    initialise_location source_name ic;
    let lexbuf = Lexing.from_channel ic in
    let p = parse_implementation lexbuf in
    let p = Elab.elab_global p in
    match DataflowToClight.compile p (intern_string (Filename.basename filename)) with
    | Error errmsg -> print_error stderr errmsg
    | OK p ->
      if !print_c then
        PrintClight.print_program Format.std_formatter p;
      if !write_c then
        begin
          let target_name = filename ^ ".light.c" in
          let oc = open_out target_name in
          PrintClight.print_program (Format.formatter_of_out_channel oc) p;
          close_out oc
        end;
      let p = add_builtins p in
      match Compiler.transf_clight_program p with
      | Error errmsg -> print_error stderr errmsg
      | OK p -> print_endline "Compilation OK"
  with x -> close_in ic; raise x

let process file =
  if Filename.check_suffix file ".cdf"
  then
    let filename = Filename.chop_suffix file ".cdf" in
    compile filename
  else
    raise (Arg.Bad ("don't know what to do with " ^ file))

let speclist = [
  "-p", Arg.Set print_c, " Print generated Clight on standard output";
  "-dclight", Arg.Set write_c, " Save generated Clight in <source>.light.c"
]

let usage_msg = "Usage: rustre [options] <source>"

let _ =
  Arg.parse (Arg.align speclist) process usage_msg
