(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* coqwc - counts the lines of spec, proof and comments in Coq sources
 * Copyright (C) 2003 Jean-Christophe Filliâtre *)

(*s {\bf coqwc.} Counts the lines of spec, proof and comments in a Coq source.
    It assumes the files to be lexically well-formed. *)

(*i*){
open Printf
open Lexing
(*i*)

(*s Command-line options. *)

let spec_only = ref false
let proof_only = ref false
let code_only = ref false
let percentage = ref false
let skip_header = ref true

(*s Counters. [clines] counts the number of code lines of the current
    file, and [dlines] the number of comment lines. [tclines] and [tdlines]
    are the corresponding totals. *)

let slines = ref 0 (* spec *)
let clines = ref 0 (* code, extracted *)
let plines = ref 0 (* proof *)
let dlines = ref 0 (* comments *)
let olines = ref 0 (* other *)

let tslines = ref 0
let tclines = ref 0
let tplines = ref 0
let tdlines = ref 0
let tolines = ref 0

let update_totals () =
  tslines := !tslines + !slines;
  tclines := !tclines + !clines;
  tplines := !tplines + !plines;
  tdlines := !tdlines + !dlines;
  tolines := !tolines + !olines

(*s The following booleans indicate whether we have seen spec, proof or
    comment so far on the current line; when a newline is reached, [newline]
    is called and updates the counters accordingly. *)

let seen_spec = ref false
let seen_code = ref false
let seen_proof = ref false
let seen_comment = ref false
let seen_other = ref false

let newline () =
  if !seen_spec then incr slines;
  if !seen_code then incr clines;
  if !seen_proof then incr plines;
  if !seen_comment then incr dlines;
  if !seen_other then incr olines;
  seen_spec := false; seen_proof := false; seen_comment := false;
  seen_code := false; seen_other := false

let reset_counters () =
  seen_spec := false; seen_proof := false; seen_comment := false;
  seen_code := false; seen_other := false;
  slines := 0; plines := 0; dlines := 0; clines := 0; olines := 0

(*s Print results. *)

let print_line sl cl pl dl ol fo =
  if not (!proof_only || !code_only) then printf " %8d" sl;
  if not (!proof_only || !spec_only) then printf " %8d" cl;
  if not (!spec_only  || !code_only) then printf " %8d" pl;
  if not (!proof_only || !spec_only || !code_only) then printf " %8d" dl;
  if not (!proof_only || !spec_only || !code_only) then printf " %8d" ol;
  if not (!proof_only || !spec_only || !code_only) then
    printf " %8d" (sl + cl + pl + dl + ol);
  (match fo with Some f -> printf " %s" f | _ -> ());
  if !percentage then begin
    let s = sl + cl + pl in
    let p = if s > 0 then 100 * cl / s else 0 in
    printf " (%d%%)" p
  end;
  print_newline ()

let print_file fo = print_line !slines !clines !plines !dlines !olines fo

let print_totals () = print_line !tslines !tclines !tplines !tdlines
                        !tolines (Some "total")

(*s Set of identifiers collected in mli files. *)
let ids : (string,unit) Hashtbl.t = Hashtbl.create 100
let is_code = Hashtbl.mem ids
let add_id id = Hashtbl.add ids id ()

(*i*)}(*i*)

(*s Shortcuts for regular expressions. The [rcs] regular expression
    is used to skip the CVS infos possibly contained in some comments,
    in order not to consider it as documentation. *)

let space = [' ' '\t' '\r']
let character =
  "'" ([^ '\\' '\''] |
       '\\' (['\\' '\'' 'n' 't' 'b' 'r'] | ['0'-'9'] ['0'-'9'] ['0'-'9'])) "'"
let ident = ['A'-'Z' 'a'-'z' '_'] ['A'-'Z' 'a'-'z' '0'-'9' '\'' '_']*
let rcs_keyword =
  "Author" | "Date" | "Header" | "Id" | "Name" | "Locker" | "Log" |
  "RCSfile" | "Revision" | "Source" | "State"
let rcs = "\036" rcs_keyword [^ '$']* "\036"
let stars = "(*" '*'* "*)"
let dot = '.' (' ' | '\t' | '\r' | eof)
let dotnl = '.' '\n'
let proof_start =
  "Theorem" | "Lemma" | "Fact" | "Remark" | "Goal" | "Corollary"
  | ("Global" space+)? "Add" space+ ("Parametric" space+)? "Morphism"
let proof_start_anon =
  "Obligation" space+ (['0' - '9'])+ | "Next" space+ "Obligation"
let def_start =
  ("Global" space+)? "Instance" | "Inductive" | "Record"
  | "CoInductive" | "CoFixpoint" | "Function"
  | ("Program" space+)? ("Definition" | "Fixpoint")
let proof_end =
  ("Save" | "Qed" | "Defined" | "Abort" | "Admitted") [^'.']* '.'
let assumption_start =
  "Axiom" | "Conjecture" | "Parameter" | "Hypothesis" | "Variable" | "Context"
  | "Let" (* not sure *)
let tac_start =
  ("Local" space+)?
    ("Ltac" | "Unset" | "Set" | "Hint" | "Obligation" space+ "Tactic"
     | "Tactic" space+ "Notation")

(*s [spec] scans the specification. *)

rule spec = parse
  | "(*"   { comment lexbuf; spec lexbuf }
  | '"'    { let n = string lexbuf in slines := !slines + n;
	     seen_other := true; spec lexbuf }
  | '\n'   { newline (); (* printf "\n"; *) spec lexbuf }
  | space+ | stars
           { spec lexbuf }
  | proof_start
           { seen_spec := true; spec_to_dot false lexbuf; proof false lexbuf }
  | proof_start_anon space* dotnl
           { seen_proof := true; newline(); proof false lexbuf }
  | proof_start_anon space* dot
           { seen_proof := true; proof false lexbuf }
  | tac_start
           { seen_proof := true; proof_term false lexbuf }
  | def_start space+ (ident as id)
           { let ic = is_code id in
             (* (if ic then printf "%s as code\n" id); *)
             if ic then seen_code := true else seen_spec := true;
             definition ic lexbuf }
  | assumption_start
           { seen_spec := true; spec_to_dot false lexbuf ; spec lexbuf }
  | character | _
  (* | character as c | _ as c *)
	   { (* printf "%s" c; *) seen_other := true; spec lexbuf }
  | eof    { () }

(*s [spec_to_dot] scans a spec until a dot is reached and returns. *)

and spec_to_dot ic = parse
  | "(*"   { comment lexbuf; spec_to_dot ic lexbuf }
  | '"'    { let n = string lexbuf in slines := !slines + n;
             if ic then seen_code := true else seen_spec := true;
             spec_to_dot ic lexbuf }
  | '\n'   { newline (); spec_to_dot ic lexbuf }
  | dot
           { () }
  | dotnl
           { newline(); () }
  | space+ | stars
           { spec_to_dot ic lexbuf }
  | character | _
	   { if ic then seen_code := true else seen_spec := true;
             spec_to_dot ic lexbuf }
  | eof    { () }

(*s [definition] scans a definition; passes to [proof] if the body is
    absent, and to [spec] otherwise *)
(* maintenant on reste dans définition *)

and definition ic = parse
  | "(*"   { comment lexbuf; definition ic lexbuf }
  | '"'    { let n = string lexbuf in slines := !slines + n;
             if ic then seen_code := true else seen_spec := true;
             definition ic lexbuf }
  | '\n'   { newline (); definition ic lexbuf }
  | ":="   { if ic then seen_code := true else seen_spec := true;
             spec_to_dot ic lexbuf; spec lexbuf }
  | dot
           { proof ic lexbuf }
  | dotnl
           { newline(); proof ic lexbuf }
  | space+ | stars
           { definition ic lexbuf }
  | character | _
	   { if ic then seen_code := true else seen_spec := true;
             definition ic lexbuf }
  | eof    { () }

(*s Scans a proof, then returns to [spec]. *)

and proof ic = parse
  | "(*"   { comment lexbuf; proof ic lexbuf }
  | '"'    { let n = string lexbuf in plines := !plines + n;
	     if ic then seen_code := true else seen_proof := true;
             proof ic lexbuf }
  | space+ | stars
           { proof ic lexbuf }
  | '\n'   { newline (); proof ic lexbuf }
  | "Proof" space* '.'
  | "Proof" space+ "with"
  | "Proof" space+ "using"
	   { if ic then seen_code := true else seen_proof := true;
             proof ic lexbuf }
  | "Proof" space
           { proof_term ic lexbuf }
  | proof_end
	   { if ic then seen_code := true else seen_proof := true;
             spec lexbuf }
  | character | _
	   { if ic then seen_code := true else seen_proof := true;
             proof ic lexbuf }
  | eof    { () }

and proof_term ic = parse
  | "(*"   { comment lexbuf; proof_term ic lexbuf }
  | '"'    { let n = string lexbuf in plines := !plines + n;
	     if ic then seen_code := true else seen_proof := true;
             proof_term ic lexbuf }
  | space+ | stars
           { proof_term ic lexbuf }
  | '\n'   { newline (); proof_term ic lexbuf }
  | dot
           { spec lexbuf }
  | dotnl
           { newline(); spec lexbuf }
  | character | _
	   { if ic then seen_code := true else seen_proof := true;
             proof_term ic lexbuf }
  | eof    { () }

(*s Scans a comment. *)

and comment = parse
  | "(*"   { comment lexbuf; comment lexbuf }
  | "*)"   { () }
  | '"'    { let n = string lexbuf in dlines := !dlines + n;
	     seen_comment := true; comment lexbuf }
  | '\n'   { newline (); comment lexbuf }
  | space+ | stars
	   { comment lexbuf }
  | character | _
	   { seen_comment := true; comment lexbuf }
  | eof    { () }

(*s The entry [string] reads a string until its end and returns the number
    of newlines it contains. *)

and string = parse
  | '"'  { 0 }
  | '\\' ('\\' | 'n' | '"') { string lexbuf }
  | '\n' { succ (string lexbuf) }
  | _    { string lexbuf }
  | eof  { 0 }

(*s The following entry [read_header] is used to skip the possible header at
    the beginning of files (unless option \texttt{-e} is specified).
    It stops whenever it encounters an empty line or any character outside
    a comment. In this last case, it correctly resets the lexer position
    on that character (decreasing [lex_curr_pos] by 1). *)

and read_header = parse
  | "(*"   { skip_comment lexbuf; skip_until_nl lexbuf;
	     read_header lexbuf }
  | "\n"   { () }
  | space+ { read_header lexbuf }
  | _      { lexbuf.lex_curr_pos <- lexbuf.lex_curr_pos - 1 }
  | eof    { () }

and skip_comment = parse
  | "*)" { () }
  | "(*" { skip_comment lexbuf; skip_comment lexbuf }
  | _    { skip_comment lexbuf }
  | eof  { () }

and skip_until_nl = parse
  | '\n' { () }
  | _    { skip_until_nl lexbuf }
  | eof  { () }

(*i*){(*i*)

(*s Processing Coq files and channels. *)

let process_channel ch =
  let lb = Lexing.from_channel ch in
  reset_counters ();
  if !skip_header then read_header lb;
  spec lb

[@@@ocaml.warning "-52"]
let process_file f =
  try
    let ch = open_in f in
    process_channel ch;
    close_in ch;
    print_file (Some f);
    update_totals ()
  with
    | Sys_error "Is a directory" ->
	flush stdout; eprintf "rat: %s: Is a directory\n" f; flush stderr
    | Sys_error s ->
	flush stdout; eprintf "rat: %s\n" s; flush stderr
[@@@ocaml.warning "+52"]

(*s Processing Ocaml interface files and channels. *)

(*s Collect identifiers defined in signatures. *)
let process_mli_channel ch =
  let lb = Lexing.from_channel ch in
  let p = Parse.interface lb in
  let it =
    { Ast_iterator.default_iterator
    with
      value_description =
        fun it vd -> add_id vd.pval_name.txt
    }
  in
  it.signature it p

[@@@ocaml.warning "-52"]
let process_mli_file f =
  try
    let ch = open_in f in
    process_mli_channel ch;
    close_in ch
  with
    | Sys_error "Is a directory" ->
	flush stdout; eprintf "rat: %s: Is a directory\n" f; flush stderr
    | Sys_error s ->
	flush stdout; eprintf "rat: %s\n" s; flush stderr
[@@@ocaml.warning "+52"]


(*s Parsing of the command line. *)

let usage () =
  prerr_endline "usage: rat [options] [files]";
  prerr_endline "Options are:";
  prerr_endline "  -p    print the ratio of code wrt. spec/proof";
  prerr_endline "  -s    print only the spec size";
  prerr_endline "  -r    print only the proof size";
  prerr_endline "  -c    print only the code size";
  prerr_endline "  -e    (everything) do not skip headers";
  prerr_endline "Files are:";
  prerr_endline "  .v    Coq files to analyse";
  prerr_endline "  .mli  Ocaml interfaces of the extracted code";
  exit 1

let rec parse = function
  | [] -> []
  | ("-h" | "-?" | "-help" | "--help") :: _ -> usage ()
  | ("-s" | "--spec-only") :: args ->
      proof_only := false; spec_only := true; parse args
  | ("-r" | "--proof-only") :: args ->
      spec_only := false; proof_only := true; parse args
  | ("-p" | "--percentage") :: args -> percentage := true; parse args
  | ("-c" | "--code-only") :: args -> code_only := true; parse args
  | ("-e" | "--header") :: args -> skip_header := false; parse args
  | f :: args -> f :: (parse args)

(*s Main program. *)

let _ =
  let files = parse (List.tl (Array.to_list Sys.argv)) in
  if not (!spec_only || !proof_only || !code_only) then
    printf "     spec     code    proof comments    other    total\n";
  let files =
    (* process .mli files and keep only .v files *)
    List.filter_map
      (fun f ->
        match Filename.extension f with
        | ".mli" -> process_mli_file f; None
        | ".v" -> Some f
        | _ -> eprintf "Don't know what to do with file %s\n" f; exit 2
      ) files in
  match files with
    | [] -> process_channel stdin; print_file None
    | [f] -> process_file f
    | _ -> List.iter process_file files; print_totals ()

(*i*)}(*i*)
