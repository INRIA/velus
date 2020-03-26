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

let do_normalize = ref false

let rec nat_of_int i = match i with
  | 0 -> Datatypes.O
  | n -> Datatypes.S (nat_of_int (n-1))

module LSyn = FtoLustre.Lus.Syn
module Norm = FtoLustre.Lus.Norm

let compile source_name filename =
  let toks = FrustreLexer.tokens_stream source_name in
  let ast =
    match FrustreParser.translation_unit_file (nat_of_int 10000) toks with
    | FrustreParser.MenhirLibParser.Inter.Parsed_pr (r, s) ->
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
  if not !do_normalize then
    FSyntax_pp.global Format.std_formatter p
  else (
    let p = FtoLustre.tr_global p in
    let p = Norm.Norm.normalize_global p in
    Lustre_pp.print_global (Format.std_formatter) p
  )

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

  "-normalize", Arg.Unit (fun () ->
     do_normalize := true),
  " Normalize the program"
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
      | "x86" -> Machine.x86_64
      | _         -> assert false
    end

let _ =
  Arg.parse (Arg.align speclist) process usage_msg

