(* *********************************************************************)
(*                                                                     *)
(*                    The Velus Lustre compiler                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

let rec infinity = Datatypes.S (infinity)

let compile source_name filename =
  let toks = FrustreLexer.tokens_stream source_name in
  let ast =
    match FrustreParser.translation_unit_file infinity toks with
    | FrustreParser.Parser.Inter.Parsed_pr (r, s) ->
        (Obj.magic r : FrustreAst.declaration list)
    | _ ->
        Printf.eprintf "!error parsing '%s'.\n" source_name; exit 0
  in
  let p = Frustre_of_ast.tr_decls ast in
  let _ = Frustre_typing.global p in
  let _ = Frustre_clocking.global p in
  (* Frustre_pp.global Format.std_formatter p; *)
  let p = FSyntax_of_frustre.tr_program p in
  let p = FTransform.transform p in
  FSyntax_pp.global Format.std_formatter p

let process file =
  if Filename.check_suffix file ".ept"
  then compile file (Filename.chop_suffix file ".ept")
  else if Filename.check_suffix file ".lus"
  then compile file (Filename.chop_suffix file ".lus")
  else
    raise (Arg.Bad ("don't know what to do with " ^ file))

let usage_msg = "Usage: frustre_test [options] <source>"

let speclist = [
  "-infer", Arg.Set Frustre_of_ast.infer_clocks,
  " automatically infer clocks";

  "-fullclocks", Arg.Unit (fun () ->
      Frustre_pp.print_fullclocks := true;
      FSyntax_pp.print_fullclocks := true),
  " Print full clocks in declarations";

  "-show-clocks", Arg.Unit (fun () ->
      Frustre_pp.show_annot_clocks := true;
      FSyntax_pp.show_annot_clocks := true),
  " Annotate subexpressions with their clocks";

  "-show-types", Arg.Unit (fun () ->
      Frustre_pp.show_annot_types := true;
      FSyntax_pp.show_annot_types := true),
  " Annotate subexpressions with their types";
]

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
    end

let _ =
  Arg.parse (Arg.align speclist) process usage_msg

