open Errors
open Camlcoq
open Printf
open Clight
open C2C
open Builtins
open Ctypes

let print_c = ref false
let write_snlustre = ref false
let write_sybloc = ref false
let write_obc = ref false
let write_cl = ref false
let write_cm = ref false
let write_sync = ref false

let set_main_node s =
  Veluslib.main_node := Some s

let get_main_node decls =
  let rec last_decl ds =
    match ds with
    | [] -> (Printf.fprintf stderr "no nodes found"; exit 1)
    | [LustreAst.NODE (n, _, _, _, _, _)] -> n
    | _::ds -> last_decl ds
  in
  match !Veluslib.main_node with
  | Some s -> intern_string s
  | None   -> last_decl decls

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
  if !write_snlustre
    then Veluslib.snlustre_destination := Some (filename ^ ".sn.lus");
    if !write_sybloc
    then Veluslib.sybloc_destination := Some (filename ^ ".syb");
  if !write_obc
    then Veluslib.obc_destination := Some (filename ^ ".obc");
  if !write_sync
    then Veluslib.sync_destination := Some (filename ^ ".sync.c");
  if !write_cl
    then PrintClight.destination := Some (filename ^ ".light.c");
  if !write_cm
    then PrintCminor.destination := Some (filename ^ ".cm");
  let toks = LustreLexer.tokens_stream source_name in
  let ast = parse toks in
  let main_node = get_main_node ast in
  match Compiler.apply_partial
          (VelusCorrectness.compile ast main_node)
          Asmexpand.expand_program with
  | Error errmsg -> Driveraux.print_error stderr errmsg; exit 1
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
  "-sync", Arg.Set write_sync,   " Generate sync() in <source>.sync.c";
  (* "-p", Arg.Set print_c, " Print generated Clight on standard output"; *)
  "-dsnlustre",Arg.Set write_snlustre,
                            " Save the parsed SN-Lustre in <source>.sn.lus";
  "-dsybloc", Arg.Set write_sybloc, " Save generated SyBloc in <source>.syb";
  "-dobc",    Arg.Set write_obc, " Save generated Obc in <source>.obc";
  "-dclight", Arg.Set write_cl,  " Save generated Clight in <source>.light.c";
  "-dcminor", Arg.Set write_cm,  " Save generated Cminor in <source>.minor.c";
  "-fullclocks", Arg.Set Interfacelib.PrintNLustre.print_fullclocks,
                                 " Print 'full' clocks in declarations";
  "-nofusion", Arg.Clear Veluslib.fuse_obc, " Skip Obc fusion optimization";
  "-lib", Arg.Set Veluslib.expose, " Expose all nodes in generated code";
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
