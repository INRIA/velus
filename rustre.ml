open Errors
open Camlcoq
open Printf
open Clight
open C2C
open Builtins
open Ctypes
    
let print_c = ref false
let write_cl = ref false
let write_cm = ref false
    
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
    if Str.string_match re_runtime name 0 then AST.EF_runtime(id', sg) else
    if Str.string_match re_builtin name 0
    && List.mem_assoc name builtins.functions
    then AST.EF_builtin(id', sg)
    else AST.EF_external(id', sg) in
  let decl = (id, AST.Gfun (External (ef, targs, tres, AST.cc_default))) in
  { p with prog_defs = decl :: p.prog_defs }


let add_builtins p =
  List.fold_left add_builtin p builtins_generic.functions

(** Incremental parser to reparse the token stream and generate an
    error message (the verified and extracted parser does not
    generate error messages). Adapted directly from menhir's
    calc-incremental example. *)

module I = Parser2.MenhirInterpreter

let rec parsing_loop toks (checkpoint : unit I.checkpoint) =
  match checkpoint with
  | I.InputNeeded env ->
      (* The parser needs a token. Request one from the lexer,
         and offer it to the parser, which will produce a new
         checkpoint. Then, repeat. *)
      let (token, loc) = Relexer.map_token (Streams.hd toks) in
      let loc = Lexer.lexing_loc loc in
      let checkpoint = I.offer checkpoint (token, loc, loc) in
      parsing_loop (Streams.tl toks) checkpoint
  | I.Shifting _
  | I.AboutToReduce _ ->
      let checkpoint = I.resume checkpoint in
      parsing_loop toks checkpoint
  | I.HandlingError env ->
      (* The parser has suspended itself because of a syntax error. Stop. *)
      let (token, {Ast.ast_fname = fname;
                   Ast.ast_lnum  = lnum;
                   Ast.ast_cnum  = cnum;
                   Ast.ast_bol   = bol }) = Relexer.map_token (Streams.hd toks)
      in
      (* TODO: improve the error messages *)
      Printf.fprintf stderr "%s:%d:%d: syntax error.\n%!"
        fname lnum (cnum - bol + 1)
  | I.Accepted v ->
      assert false (* Parser2 should not succeed where Parser failed. *)
  | I.Rejected ->
      (* The parser rejects this input. This cannot happen, here, because
         we stop as soon as the parser reports [HandlingError]. *)
      assert false

let reparse toks =
  let (_, l) = Relexer.map_token (Streams.hd toks) in
  parsing_loop toks
    (Parser2.Incremental.translation_unit_file (Lexer.lexing_loc l))

(** Parser *)

let parse toks =
  Cerrors.reset();
  let rec inf = Datatypes.S inf in
  match Parser.translation_unit_file inf toks with
  | Parser.Parser.Inter.Fail_pr -> (reparse toks; exit 1)
  | Parser.Parser.Inter.Timeout_pr -> assert false
  | Parser.Parser.Inter.Parsed_pr (ast, _) ->
      (Obj.magic ast : Ast.declaration list)

let compile filename =
  let source_name = filename ^ ".ept" in
  let toks = Lexer.tokens_stream source_name in
  let ast = parse toks in
  let p =
    match DataflowElab.elab_declarations ast with
    | Errors.OK p -> p
    | Errors.Error msg -> (Driveraux.print_error stderr msg; exit 1) in
  if Cerrors.check_errors() then exit 2;
  match DataflowToClight.compile p (intern_string (Filename.basename filename)) with
  | Error errmsg -> print_error stderr errmsg
  | OK p ->
    if !print_c then
      PrintClight.print_program Format.std_formatter p;
    (* if !write_cl then *)
    (*   begin *)
    (*     let target_name = filename ^ ".light.c" in *)
    (*     let oc = open_out target_name in *)
    (*     PrintClight.print_program (Format.formatter_of_out_channel oc) p; *)
    (*     close_out oc *)
    (*   end; *)
    if !write_cl then PrintClight.destination := Some (filename ^ ".light.c");
    if !write_cm then PrintCminor.destination := Some (filename ^ ".minor.c");
    let p = add_builtins p in
    match Compiler.transf_clight_program p with
    | Error errmsg -> print_error stderr errmsg
    | OK p -> print_endline "Compilation OK"

let process file =
  if Filename.check_suffix file ".ept"
  then
    let filename = Filename.chop_suffix file ".ept" in
    compile filename
  else
    raise (Arg.Bad ("don't know what to do with " ^ file))

let speclist = [
  "-p", Arg.Set print_c, " Print generated Clight on standard output";
  "-dclight", Arg.Set write_cl, " Save generated Clight in <source>.light.c";
  "-dcminor", Arg.Set write_cm, " Save generated Clight in <source>.minor.c"
]

let usage_msg = "Usage: rustre [options] <source>"

let _ =
  Arg.parse (Arg.align speclist) process usage_msg
