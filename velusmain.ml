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
let main_node = ref (None : string option)

let set_main_node s =
  main_node := Some s

let get_main_node decls =
  match !main_node with
  | Some s -> intern_string s
  | None   -> match decls with
              | [] -> (Printf.fprintf stderr "no nodes found"; exit 1)
              | d::_ -> Instantiator.NL.Syn.n_name d

(** Incremental parser to reparse the token stream and generate an
    error message (the verified and extracted parser does not
    generate error messages). Adapted directly from menhir's
    calc-incremental example. *)

module I = LustreParser2.MenhirInterpreter

let rec parsing_loop toks (checkpoint : unit I.checkpoint) =
  match checkpoint with
  | I.InputNeeded env ->
    (* The parser needs a token. Request one from the lexer,
       and offer it to the parser, which will produce a new
       checkpoint. Then, repeat. *)
    let (token, loc) = Relexer.map_token (Streams.hd toks) in
    let loc = LustreLexer.lexing_loc loc in
    let checkpoint = I.offer checkpoint (token, loc, loc) in
    parsing_loop (Streams.tl toks) checkpoint
  | I.Shifting _
  | I.AboutToReduce _ ->
    let checkpoint = I.resume checkpoint in
    parsing_loop toks checkpoint
  | I.HandlingError env ->
    (* The parser has suspended itself because of a syntax error. Stop. *)
    let (token, {LustreAst.ast_fname = fname;
                 LustreAst.ast_lnum  = lnum;
                 LustreAst.ast_cnum  = cnum;
                 LustreAst.ast_bol   = bol }) =
                  Relexer.map_token (Streams.hd toks)
    in
    (* TODO: improve error messages *)
    Printf.fprintf stderr "%s:%d:%d: syntax error.\n%!"
      fname lnum (cnum - bol + 1)
  | I.Accepted v ->
    assert false (* LustreParser2 should not succeed where Parser failed. *)
  | I.Rejected ->
    (* The parser rejects this input. This cannot happen, here, because
       we stop as soon as the parser reports [HandlingError]. *)
    assert false

let reparse toks =
  let (_, l) = Relexer.map_token (Streams.hd toks) in
  parsing_loop toks
    (LustreParser2.Incremental.translation_unit_file (LustreLexer.lexing_loc l))

(** Parser *)

let parse toks =
  Cerrors.reset();
  let rec inf = Datatypes.S inf in
  match LustreParser.translation_unit_file inf toks with
  | LustreParser.Parser.Inter.Fail_pr -> (reparse toks; exit 1)
  | LustreParser.Parser.Inter.Timeout_pr -> assert false
  | LustreParser.Parser.Inter.Parsed_pr (ast, _) ->
    (Obj.magic ast : LustreAst.declaration list)

let compile source_name filename =
  if !write_cl then PrintClight.destination := Some (filename ^ ".light.c");
  if !write_cm then PrintCminor.destination := Some (filename ^ ".minor.c");
  let toks = LustreLexer.tokens_stream source_name in
  let ast = parse toks in
  let p =
    match NLustreElab.elab_declarations ast with
    | Errors.OK p -> p
    | Errors.Error msg -> (Driveraux.print_error stderr msg; exit 1) in
  if Cerrors.check_errors() then exit 2;
  let main_node = get_main_node p in
  match Compiler.apply_partial
          (VelusCorrectness.compile (List.rev p) main_node)
          Asmexpand.expand_program with
  | Error errmsg -> Driveraux.print_error stderr errmsg
  | OK asm ->
    let oc = open_out (filename ^ ".s") in
    PrintAsm.print_program oc asm;
    close_out oc
    
let process file =
  if Filename.check_suffix file ".ept"
  then compile file (Filename.chop_suffix file ".ept")
  else if Filename.check_suffix file ".lus"
  then compile file (Filename.chop_suffix file ".lus")
  else
    raise (Arg.Bad ("don't know what to do with " ^ file))

let speclist = [
  "-main", Arg.String set_main_node, " Specify the main node";
  (* "-p", Arg.Set print_c, " Print generated Clight on standard output"; *)
  "-dclight", Arg.Set write_cl, " Save generated Clight in <source>.light.c";
  "-dcminor", Arg.Set write_cm, " Save generated Clight in <source>.minor.c"
]

let usage_msg = "Usage: velus [options] <source>"

let _ =
  Machine.config :=
    begin match Configuration.arch with
      | "powerpc" -> if Configuration.system = "linux"
        then Machine.ppc_32_bigendian
        else Machine.ppc_32_diab_bigendian
      | "arm"     -> Machine.arm_littleendian
      | "ia32"    -> if Configuration.abi = "macosx"
        then Machine.x86_32_macosx
        else Machine.x86_32
      | _         -> assert false
    end;
  Builtins.set C2C.builtins;
  CPragmas.initialize()

let _ =
  Arg.parse (Arg.align speclist) process usage_msg

