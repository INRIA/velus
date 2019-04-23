open Errors
open Camlcoq
open Printf
open Clight
open C2C
open Builtins
open Ctypes

let print_c = ref false
let write_lustre = ref false
let write_nlustre = ref false
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
    | [LustreAst.NODE (n, _, _, _, _, _, _)] -> n
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
  Diagnostics.reset();
  let rec inf = Datatypes.S inf in
  match LustreParser.translation_unit_file inf toks with
  | LustreParser.Parser.Inter.Fail_pr -> (reparse toks; exit 1)
  | LustreParser.Parser.Inter.Timeout_pr -> assert false
  | LustreParser.Parser.Inter.Parsed_pr (ast, _) ->
    (Obj.magic ast : LustreAst.declaration list)

let compile source_name filename =
  Format.printf "compile@."; (* XXX *)
  if !write_lustre
    then Veluslib.lustre_destination := Some (filename ^ ".parsed.lus");
  if !write_nlustre
    then Veluslib.nlustre_destination := Some (filename ^ ".n.lus");
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
  (* XXX Elaboration testing. Compilation disconnected. XXX *)
  let p =
    match LustreElab.elab_declarations ast with
    | Errors.OK p -> p
    | Errors.Error msg -> (Driveraux.print_error Format.err_formatter msg; exit 1) in
  Format.printf "%a@." Interfacelib.PrintLustre.print_global p;
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

let set_fullclocks () =
  Interfacelib.PrintLustre.print_fullclocks := true;
  Interfacelib.PrintNLustre.print_fullclocks := true;
  Interfacelib.PrintSyBloc.print_fullclocks := true

let speclist = [
  "-main", Arg.String set_main_node, " Specify the main node";
  "-sync", Arg.Set write_sync,   " Generate sync() in <source>.sync.c";
  (* "-p", Arg.Set print_c, " Print generated Clight on standard output"; *)
  "-dlustre",Arg.Set write_lustre,
                            " Save the parsed Lustre in <source>.parsed.lus";
  "-dnlustre",Arg.Set write_nlustre,
                            " Save generated N-Lustre in <source>.n.lus";
  "-dsybloc", Arg.Set write_sybloc, " Save generated SyBloc in <source>.syb";
  "-dobc",    Arg.Set write_obc, " Save generated Obc in <source>.obc";
  "-dclight", Arg.Set write_cl,  " Save generated Clight in <source>.light.c";
  "-dcminor", Arg.Set write_cm,  " Save generated Cminor in <source>.minor.c";
  "-fullclocks", Arg.Unit set_fullclocks,
                                 " Print 'full' clocks in declarations";
  "-appclocks", Arg.Set Interfacelib.PrintLustre.print_appclocks,
                                 " Show result clocks of nested applications";
  "-nofusion", Arg.Clear Veluslib.fuse_obc, " Skip Obc fusion optimization";
  "-noaddwhens", Arg.Clear Veluslib.add_when_to_constants,
                               " Do not automatically add 'when' to constants";
  "-lib", Arg.Set Veluslib.expose, " Expose all nodes in generated code";
]

let usage_msg =
  Format.sprintf "Usage: velus [options] <source>\n(arch=%s system=%s abi=%s)\n"
    Configuration.arch Configuration.system Configuration.abi

let _ =
  Machine.config:=
    begin match Configuration.arch with
    | "powerpc" -> if Configuration.model = "e5500" || Configuration.model = "ppc64"
                   then if Configuration.abi = "linux" then Machine.ppc_32_r64_linux_bigendian
                   else if Configuration.gnu_toolchain then Machine.ppc_32_r64_bigendian
                   else Machine.ppc_32_r64_diab_bigendian
                   else if Configuration.abi = "linux" then Machine.ppc_32_linux_bigendian
                   else if Configuration.gnu_toolchain then Machine.ppc_32_bigendian
                   else Machine.ppc_32_diab_bigendian
    | "arm"     -> if Configuration.is_big_endian
                   then Machine.arm_bigendian
                   else Machine.arm_littleendian
    | "x86"     -> if Configuration.model = "64" then
                     Machine.x86_64
                   else
                     if Configuration.abi = "macosx"
                     then Machine.x86_32_macosx
                     else if Configuration.system = "bsd"
                     then Machine.x86_32_bsd
                     else Machine.x86_32
    | "riscV"   -> if Configuration.model = "64"
                   then Machine.rv64
                   else Machine.rv32
    | _         -> assert false
  end;
  Builtins.set C2C.builtins;
  (* Cutil.declare_attributes C2C.attributes; *)
  CPragmas.initialize()

let _ =
  Arg.parse (Arg.align speclist) process usage_msg
