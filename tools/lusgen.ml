open Errors

(** [lusgen] takes a .lus file and outputs the corresponding Lustre
    AST in a .v file. *)

(* TODO on ajoutait ça au Makefile principal :
ocamlbuild $(FLAGS) src/verif/lusgen.native
*)

(* output filename *)
let ofile = ref (None : string option)

(* Parser code from src/velusmain.ml *)

module I = LustreParser2.MenhirInterpreter

let rec parsing_loop toks (checkpoint : unit I.checkpoint) =
  match checkpoint with
  | I.InputNeeded env ->
    (* The parser needs a token. Request one from the lexer,
       and offer it to the parser, which will produce a new
       checkpoint. Then, repeat. *)
    let (token, loc) = Relexer.map_token (LustreParser.MenhirLibParser.Inter.buf_head toks) in
    let loc = LustreLexer.lexing_loc loc in
    let checkpoint = I.offer checkpoint (token, loc, loc) in
    parsing_loop (LustreParser.MenhirLibParser.Inter.buf_tail toks) checkpoint
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
                  Relexer.map_token (LustreParser.MenhirLibParser.Inter.buf_head toks)
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
  let (_, l) = Relexer.map_token (LustreParser.MenhirLibParser.Inter.buf_head toks) in
  parsing_loop toks
    (LustreParser2.Incremental.translation_unit_file (LustreLexer.lexing_loc l))

let parse toks =
  Diagnostics.reset();
  match LustreParser.translation_unit_file (Camlcoq.Nat.of_int 10000) toks with
  | LustreParser.MenhirLibParser.Inter.Fail_pr_full _ -> (reparse toks; exit 1)
  | LustreParser.MenhirLibParser.Inter.Timeout_pr -> assert false
  | LustreParser.MenhirLibParser.Inter.Parsed_pr (ast, _) -> ast

(* Print Lustre in Coq syntax *)

let compile source_name filename =
  let toks = LustreLexer.tokens_stream source_name in
  (* remove from the tables all identifiers which are unused in
     verification, e.g. "step", "main_sync", etc. *)
  (* FIXME: ça fait tout foirer *)
  (* Hashtbl.clear Camlcoq.string_of_atom;
   * Hashtbl.clear Camlcoq.atom_of_string; *)
  let ast = parse toks in
  match LustreElab.elab_declarations ast with
  | OK g ->
     let oc = open_out filename in
     ExportLustre.print_program (Format.formatter_of_out_channel oc) g;
     close_out oc
  | Error msg ->
     Format.eprintf "%a@." Driveraux.print_error msg; exit 1

let process file =
  if Filename.check_suffix file ".lus"
  then
    let filename = match !ofile with
      | Some f -> f
      | None -> (Filename.chop_suffix file ".lus") ^ ".v"
    in compile file filename
  else raise (Arg.Bad ("don't know what to do with " ^ file))

let set_ofile s =
  ofile := Some s

let speclist = [
    "-o", Arg.String set_ofile, "<file> Generate output in <file>";
  ]

let usage_msg =
  Format.sprintf "Usage: lusgen [options] <source>\n"

let init () =
  Machine.config :=
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
                     then Machine.x86_32_macos
                     else if Configuration.system = "bsd"
                     then Machine.x86_32_bsd
                     else Machine.x86_32
    | "riscV"   -> if Configuration.model = "64"
                   then Machine.rv64
                   else Machine.rv32
    | _         -> assert false
  end;
  (* Builtins.set C2C.builtins; (* ?? *) *)
  (* Cutil.declare_attributes C2C.attributes; *)
  (* CPragmas.initialize() *)
  ()

let _ =
  init();
  Arg.parse (Arg.align speclist) process usage_msg
