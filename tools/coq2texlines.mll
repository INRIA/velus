(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* coqwc - counts the lines of file, proof and comments in Coq sources
 * Copyright (C) 2003 Jean-Christophe Filliâtre *)

(*s {\bf coqwc.} Counts the lines of file, proof and comments in a Coq source.
    It assumes the files to be lexically well-formed. *)

(*i*){
open Printf
open Lexing
(*i*)

(*s File to write to *)

let output_file = ref "veluslines.tex"
let outch = ref None

(*s File read from *)

let current_file = ref ""

(*s Registers *)

let deffirstline = ref 0
let defname = ref ""
let constrfirstline = ref 0
let constrname = ref ""

(** Register a definition. *)
(** The format of the commands is: *)
(** [current_file]XX[name]XXfstline *)
(** [current_file]XX[name]XXlastline *)
(** where in [current_file], all "/" have been replaced by "X" *)
let register name fl ll =
  let file_name = Filename.chop_extension !current_file in
  (* let file_name = String.map (fun x -> if x = '/' then 'X' else x) file_name in *)
  (* let name = String.map (fun x -> if x = '_' then 'X' else x) name in *)
  let outch = Option.get !outch in
  Printf.fprintf outch "\\expandafter\\providecommand\\csname %sXX%sXXfstline\\endcsname{%d}\n"
    file_name name fl;
  Printf.fprintf outch "\\expandafter\\providecommand\\csname %sXX%sXXlastline\\endcsname{%d}\n"
    file_name name ll

let register_def ll =
  register !defname !deffirstline ll

let register_constr ll =
  register !constrname !constrfirstline ll

let newline () = ()
(*   if !seen_file then incr slines; *)
(*   if !seen_code then incr clines; *)
(*   if !seen_proof then incr plines; *)
(*   if !seen_comment then incr dlines; *)
(*   if !seen_other then incr olines; *)
(*   seen_file := false; seen_proof := false; seen_comment := false; *)
(*   seen_code := false; seen_other := false *)

(* let reset_counters () = *)
(*   seen_file := false; seen_proof := false; seen_comment := false; *)
(*   seen_code := false; seen_other := false; *)
(*   slines := 0; plines := 0; dlines := 0; clines := 0; olines := 0 *)

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
let def_start =
  ("Local" space+)? ("Global" space+)? "Instance" | "Record"
  | "CoFixpoint" | "Function"
  | ("Program" space+)? ("Definition" | "Fixpoint")
  | "Theorem" | "Lemma" | "Fact" | "Remark" | "Goal" | "Corollary"
  | "Module" (space+ "Type")?
  | "Axiom" | "Conjecture" | "Parameter"
let inductive_start =
  "Inductive" | "CoInductive"
let admin_start =
  "From" | "Require" | "Import" | "Open" | "End"
  | ("Global" space+)? "Existing" space+ "Instance"
let proof_start_anon =
  "Obligation" space+ (['0' - '9'])+ | "Next" space+ "Obligation"
  ("Save" | "Qed" | "Defined" | "Abort" | "Admitted") [^'.']* '.'
let assumption_start =
  "Hypothesis" | "Variable" | "Context"
  | "Let" (* not sure *)
let tac_start =
  ("Local" space+)?
    ("Ltac" | "Unset" | "Set" |
     ("Global" space+)? "Hint" | "Obligation" space+ "Tactic"
     | "Tactic" space+ "Notation")

(*s [file] scans the fileification. *)

rule file = parse
  | "(*" { comment lexbuf; file lexbuf }
  | '\n' { Lexing.new_line lexbuf; file lexbuf }
  | def_start (* Start of a lemma *)
    { deffirstline := lexbuf.lex_curr_p.pos_lnum; start_def lexbuf }
  | inductive_start (* Start of an inductive *)
    { deffirstline := lexbuf.lex_curr_p.pos_lnum; start_ind lexbuf }
  | admin_start (* Some admin stuff *)
    { skip_to_dot lexbuf; file lexbuf }
  | assumption_start (* TODO *)
    { skip_to_dot lexbuf; file lexbuf }
  | tac_start
    { skip_to_dot lexbuf; file lexbuf }
  | character | _
	   { file lexbuf }
  | eof    { () }

and start_def = parse
  | '\n'   { Lexing.new_line lexbuf; start_def lexbuf }
  | space+ | stars { start_def lexbuf }
  | ident (* name of the start_def *)
    { defname := Lexing.lexeme lexbuf;
      skip_def lexbuf }
  | ":" { skip_to_dot lexbuf; file lexbuf }

and skip_def = parse
  | dot { register_def lexbuf.lex_curr_p.pos_lnum;
          file lexbuf }
  | dotnl { register_def lexbuf.lex_curr_p.pos_lnum;
            Lexing.new_line lexbuf;
            file lexbuf }
  | '\n'   { Lexing.new_line lexbuf; skip_def lexbuf }
  | "(*" { comment lexbuf; skip_def lexbuf }
  | character | _ { skip_def lexbuf }

and start_ind = parse
  | '\n'   { Lexing.new_line lexbuf; start_ind lexbuf }
  | space+ | stars { start_ind lexbuf }
  | ident (* name of the start_ind *)
    { defname := Lexing.lexeme lexbuf;
      skip_to_ind_body lexbuf}

and skip_to_ind_body = parse
  | '\n'   { Lexing.new_line lexbuf; skip_to_ind_body lexbuf }
  | ":="   { constructor lexbuf }
  | character | _ { skip_to_ind_body lexbuf }

and constructor = parse
  | '\n' { Lexing.new_line lexbuf; constructor lexbuf }
  | ident (* name of the start_def *)
    { constrfirstline := lexbuf.lex_curr_p.pos_lnum;
      constrname := Lexing.lexeme lexbuf;
      inductive lexbuf }
  | _ { constructor lexbuf }

and inductive = parse
  | '\n' space+ "with" (* Next part of the definition *)
    { register_constr (lexbuf.lex_curr_p.pos_lnum-1);
      register_def (lexbuf.lex_curr_p.pos_lnum-1);
      Lexing.new_line lexbuf;
      deffirstline := lexbuf.lex_curr_p.pos_lnum; start_ind lexbuf }
  | '|' { register_constr (lexbuf.lex_curr_p.pos_lnum-1); constructor lexbuf }
  | dot { register_constr lexbuf.lex_curr_p.pos_lnum;
          register_def lexbuf.lex_curr_p.pos_lnum;
          file lexbuf }
  | dotnl { register_constr lexbuf.lex_curr_p.pos_lnum;
            register_def lexbuf.lex_curr_p.pos_lnum;
            Lexing.new_line lexbuf;
            file lexbuf }
  | '\n'   { Lexing.new_line lexbuf; inductive lexbuf }
  | "(*" { comment lexbuf; inductive lexbuf }
  | character | _ { inductive lexbuf }

and skip_to_dot = parse
  | dot { () }
  | dotnl { Lexing.new_line lexbuf }
  | '\n' { Lexing.new_line lexbuf; skip_to_dot lexbuf }
  | "(*" { comment lexbuf; skip_to_dot lexbuf }
  | character | _ { skip_to_dot lexbuf }

(*s Scans a comment. *)

and comment = parse
  | "(*"   { comment lexbuf; comment lexbuf }
  | "*)"   { () }
  | space+ | stars { comment lexbuf }
  | '\n'   { Lexing.new_line lexbuf; comment lexbuf }
  | character | _ { comment lexbuf }

(*i*){(*i*)

(*s Processing Coq files and channels. *)

let process_channel ch =
  let lb = Lexing.from_channel ~with_positions:true ch in
  try file lb
  with e -> Printf.printf "error: %s in %s at line %d\n"
              (Printexc.to_string e)
              !current_file
              lb.lex_curr_p.pos_lnum

[@@@ocaml.warning "-52"]
let process_file f =
  current_file := f;
  try
    let ch = open_in f in
    process_channel ch;
    close_in ch;
  with
    | Sys_error "Is a directory" ->
	flush stdout; eprintf "coq2texlines: %s: Is a directory\n" f; flush stderr
    | Sys_error s ->
	flush stdout; eprintf "coq2texlines: %s\n" s; flush stderr
[@@@ocaml.warning "+52"]

(*s Parsing of the command line. *)

let usage () =
  prerr_endline "usage: rat [options] [files]";
  prerr_endline "Options are:";
  prerr_endline "  -o    choose output file";
  prerr_endline "Files are:";
  prerr_endline "  .v    Coq files to analyse";
  exit 1

let rec parse = function
  | [] -> []
  | ("-h" | "-?" | "-help" | "--help") :: _ -> usage ()
  | ("-o" | "--output") :: s :: args -> output_file := s; parse args
  | f :: args -> f :: (parse args)

(*s Main program. *)

let _ =
  let files = parse (List.tl (Array.to_list Sys.argv)) in
  let files =
    (* process .mli files and keep only .v files *)
    List.filter_map
      (fun f ->
        match Filename.extension f with
        | ".v" -> Some f
        | _ -> eprintf "Don't know what to do with file %s\n" f; exit 2
      ) files in
  outch := Some (open_out !output_file);
  (match files with
   | [] -> process_channel stdin(* ; print_file None *)
   | [f] -> process_file f
   | _ -> List.iter process_file files);
  close_out (Option.get !outch)

(*i*)}(*i*)
