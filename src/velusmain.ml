open Errors
open Camlcoq
open Printf
open Clight
open C2C
open Builtins
open Ctypes

let print_c = ref false
let write_lustre = ref false
let write_complete = ref false
let write_noauto = ref false
let write_noswitch = ref false
let write_nolocal = ref false
let write_unnested = ref false
let write_normlast = ref false
let write_normfby = ref false
let write_nlustre = ref false
let write_stc = ref false
let write_cut = ref false
let write_sch = ref false
let write_obc = ref false
let write_cl = ref false
let write_cm = ref false
let write_sync = ref false
let write_header = ref false
let no_main = ref false

let output_file = ref None

let set_output_file s =
  output_file := Some s

let set_main_node s =
  Veluslib.main_node := Some s

let get_main_node decls =
  let rec last_decl last ds =
    match ds with
    | [] -> last
    | LustreAst.NODE (n, _, _, _, _, _) :: ds -> last_decl (Some n) ds
    | _ :: ds -> last_decl last ds
  in

  if !no_main then (
    if Option.is_some !Veluslib.main_node
    then (Printf.fprintf stderr "-nomain is not compatible with -main"; exit 1);
    if !write_sync
    then (Printf.fprintf stderr "-nomain is not compatible with -sync"; exit 1);
    None
  ) else
    match !Veluslib.main_node with
    | Some s -> Some (intern_string s)
    | None   -> begin match last_decl None decls with
        | Some s -> Some s
        | None   -> Printf.fprintf stderr "no nodes found\n"; exit 1
      end

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

(** Parser *)

let parse toks =
  Diagnostics.reset();
  match LustreParser.translation_unit_file (Camlcoq.Nat.of_int 10000) toks with
  | LustreParser.MenhirLibParser.Inter.Fail_pr_full _ -> (reparse toks; exit 1)
  | LustreParser.MenhirLibParser.Inter.Timeout_pr -> assert false
  | LustreParser.MenhirLibParser.Inter.Parsed_pr (ast, _) -> ast

let compile source_name out_name =
  if !write_lustre
  then Veluslib.lustre_destination := Some (out_name ^ ".parsed.lus");
  if !write_complete
  then Veluslib.complete_destination := Some (out_name ^ ".complete.lus");
  if !write_noauto
  then Veluslib.noauto_destination := Some (out_name ^ ".noauto.lus");
  if !write_noswitch
  then Veluslib.noswitch_destination := Some (out_name ^ ".noswitch.lus");
  if !write_nolocal
  then Veluslib.nolocal_destination := Some (out_name ^ ".nolocal.lus");
  if !write_unnested
  then Veluslib.unnested_destination := Some (out_name ^ ".unn.lus");
  if !write_normlast
  then Veluslib.normlast_destination := Some (out_name ^ ".nlast.lus");
  if !write_normfby
  then Veluslib.normfby_destination := Some (out_name ^ ".nfby.lus");
  if !write_nlustre
  then Veluslib.nlustre_destination := Some (out_name ^ ".n.lus");
  if !write_stc
  then Veluslib.stc_destination := Some (out_name ^ ".stc");
  if !write_cut
  then Veluslib.cut_destination := Some (out_name ^ ".cut.stc");
  if !write_sch
  then Veluslib.sch_destination := Some (out_name ^ ".sch.stc");
  if !write_obc
  then Veluslib.obc_destination := Some (out_name ^ ".obc");
  if !write_sync
  then Veluslib.sync_destination := Some (out_name ^ ".sync.c");
  if !write_cl
  then PrintClight.destination := Some (out_name ^ ".light.c");
  if !write_cm
  then PrintCminor.destination := Some (out_name ^ ".cm");
  if !write_header
  then Veluslib.header_destination := Some (out_name ^ ".h");
  let toks = LustreLexer.tokens_stream source_name in
  let ast = parse toks in
  let main_node = get_main_node ast in
  (* TODO: move these two checks to a new pass *)
  (match Compiler.apply_partial (LustreElab.elab_declarations ast) (fun x -> Errors.OK (Instantiator.Restr.check_global (Ident.Ids.elab_prefs) x)) with
   | Errors.OK true -> ()
   | _ -> Format.eprintf "warning: could not check semantic existence@."
  );
  (match Compiler.apply_partial (LustreElab.elab_declarations ast) (fun x -> Errors.OK (Instantiator.op_check_global (Ident.Ids.elab_prefs) x)) with
   | Errors.OK true -> ()
   | _ -> Format.eprintf "warning: cannot guarantee absence of arithmetic errors@."
  );
  match Compiler.apply_partial
          (Velus.compile ast main_node)
          Asmexpand.expand_program with
  | Error errmsg ->
    Format.eprintf "%a@." Driveraux.print_error errmsg; exit 1
  | OK asm ->
    let oc = open_out (out_name ^ ".s") in
    PrintAsm.print_program oc asm;
    close_out oc

let process file =
  let filename =
    if Filename.check_suffix file ".ept"
      then Filename.chop_suffix file ".ept"
      else if Filename.check_suffix file ".lus"
      then Filename.chop_suffix file ".lus"
      else raise (Arg.Bad ("don't know what to do with " ^ file))
  in let out_name =
    match !output_file with
    | Some f -> f
    | None -> filename
  in compile file (Filename.remove_extension out_name)

let set_fullclocks () =
  Interfacelib.PrintLustre.print_fullclocks := true;
  Interfacelib.PrintNLustre.print_fullclocks := true;
  Interfacelib.PrintStc.print_fullclocks := true

let speclist = [
  "-o", Arg.String set_output_file, " Set <output> file name";
  "-main", Arg.String set_main_node, " Specify the main node";
  "-nomain", Arg.Set no_main, " Compile as a library, without a main() function";
  "-sync", Arg.Set write_sync, " Generate sync() in <output>.sync.c";
  "-lib", Arg.Set Veluslib.expose, " Expose all nodes in generated code";
  "-header", Arg.Set write_header, " Generate a header file in <output>.h";

  "-dlustre", Arg.Set write_lustre, " Save the parsed Lustre in <output>.parsed.lus";
  "-dcomplete", Arg.Set write_complete, " Save Lustre after completion in <output>.complete.lus";
  "-dnoauto", Arg.Set write_noauto, " Save Lustre without automaton in <output>.noauto.lus";
  "-dnoswitch", Arg.Set write_noswitch, " Save Lustre without switch blocks in <output>.noswitch.lus";
  "-dnolocal", Arg.Set write_nolocal, " Save Lustre without local blocks in <output>.nolocal.lus";
  "-dunnested", Arg.Set write_normlast, " Save unnested Lustre in <output>.unn.lus";
  "-dnormlast", Arg.Set write_normlast, " Save Lustre with normalized last in <output>.nolast.lus";
  "-dnormfby", Arg.Set write_normlast, " Save Lustre with normalized fby in <output>.nfby.lus";
  "-dnlustre", Arg.Set write_nlustre,
                                   " Save generated N-Lustre in <output>.n.lus";
  "-dstc", Arg.Set write_stc, " Save generated Stc in <output>.stc";
  "-dcut", Arg.Set write_cut, " Save Stc with cut cycles in <output>.cut.stc";
  "-dsch", Arg.Set write_sch, " Save re-scheduled Stc in <output>.sch.stc";
  "-dobc", Arg.Set write_obc, " Save generated Obc in <output>.obc";
  "-dclight", Arg.Set write_cl, " Save generated Clight in <output>.light.c";
  "-dcminor", Arg.Set write_cm, " Save generated Cminor in <output>.minor.c";
  "-fullclocks", Arg.Unit set_fullclocks,
                                         " Print 'full' clocks in declarations";
  "-appclocks", Arg.Set Interfacelib.PrintLustre.print_appclocks,
                                   " Show result clocks of nested applications";
  "-noexpinlining", Arg.Clear Veluslib.exp_inlining, " skip expression inlining";
  "-nodce", Arg.Clear Veluslib.dce, " Skip dead code elimination";
  "-noremovedupregs", Arg.Clear Veluslib.dupregrem, " Skip duplicate register removal";
  "-nofusion", Arg.Clear Veluslib.fuse_obc, " Skip Obc fusion optimization";
  "-nonormswitches", Arg.Clear Veluslib.normalize_switches, " Skip Obc switches normalization";
  "-noobcdce", Arg.Clear Veluslib.obc_dce, " Skip Obc dead code elimination";
]

let usage_msg =
  Format.sprintf "Usage: velus [options] <source>\n(arch=%s system=%s abi=%s)\n"
    Configuration.arch Configuration.system Configuration.abi

let _ =
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
  CPragmas.initialize()

let _ =
  Arg.parse (Arg.align speclist) process usage_msg
