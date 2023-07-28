(***********************************************************************)
(*                                                                     *)
(*                             Heptagon                                *)
(*                                                                     *)
(* Gwenael Delaval, LIG/INRIA, UJF                                     *)
(* Leonard Gerard, Parkas, ENS                                         *)
(* Adrien Guatto, Parkas, ENS                                          *)
(* Cedric Pasteur, Parkas, ENS                                         *)
(* Marc Pouzet, Parkas, ENS                                            *)
(*                                                                     *)
(* Copyright 2012 ENS, INRIA, UJF                                      *)
(*                                                                     *)
(* This file is part of the Heptagon compiler.                         *)
(*                                                                     *)
(* Heptagon is free software: you can redistribute it and/or modify it *)
(* under the terms of the GNU General Public License as published by   *)
(* the Free Software Foundation, either version 3 of the License, or   *)
(* (at your option) any later version.                                 *)
(*                                                                     *)
(* Heptagon is distributed in the hope that it will be useful,         *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of      *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the       *)
(* GNU General Public License for more details.                        *)
(*                                                                     *)
(* You should have received a copy of the GNU General Public License   *)
(* along with Heptagon.  If not, see <http://www.gnu.org/licenses/>    *)
(*                                                                     *)
(***********************************************************************)
(* Printing a location in the source program *)
(* inspired from the source of the Caml Light 0.73 compiler *)

open Lexing
open Format

type location =
    Loc of position  (* Position of the first character *)
         * position  (* Position of the next character following the last one *)

let no_location =  Loc (dummy_pos, dummy_pos)

let error_prompt = ">"


(** Prints [n] times char [c] on [oc]. *)
let prints_n_chars ff n c = for _i = 1 to n do pp_print_char ff c done

(** Prints out to [oc] a line designed to be printed under [line] from file [ic]
  underlining from char [first] to char [last] with char [ch].
  [line] is the index of the first char of line. *)
let underline_line ic ff ch line first last =
  let c = ref ' '
  and f = ref first
  and l = ref (last-first) in
  ( try
    seek_in ic line;
    pp_print_string ff error_prompt;
    while c := input_char ic; !c != '\n' do
      if !f > 0 then begin
        f := !f - 1;
        pp_print_char ff (if !c == '\t' then !c else ' ')
      end
      else if !l > 0 then begin
        l := !l - 1;
        pp_print_char ff (if !c == '\t' then !c else ch)
      end
      else ()
    done
  with End_of_file ->
    if !f = 0 && !l > 0 then prints_n_chars ff 5 ch )


let copy_lines nl ic ff prompt =
  for _i = 1 to nl do
    pp_print_string ff prompt;
    (try pp_print_string ff (input_line ic)
     with End_of_file -> pp_print_string ff "<EOF>");
    fprintf ff "@\n"
  done

let copy_chunk p1 p2 ic ff =
  try for _i = p1 to p2 - 1 do pp_print_char ff (input_char ic) done
  with End_of_file -> pp_print_string ff "<EOF>"



let skip_lines n ic =
  try for _i = 1 to n do
    let _ = input_line ic in ()
    done
  with End_of_file -> ()



let print_location ff (Loc(p1,p2)) =
  let n1 = p1.pos_cnum - p1.pos_bol in (* character number *)
  let n2 = p2.pos_cnum - p2.pos_bol in
  let np1 = p1.pos_cnum in (* character position *)
  let np2 = p2.pos_cnum in
  let l1 = p1.pos_lnum in (* line number *)
  let l2 = p2.pos_lnum in
  let lp1 = p1.pos_bol in (* line position *)
  let lp2 = p2.pos_bol in
  let f1 = p1.pos_fname in (* file name *)
  let f2 = p2.pos_fname in

  if f1 != f2 then (* Strange case *)
    fprintf ff
    "File \"%s\" line %d, character %d, to file \"%s\" line %d, character %d@."
      f1 l1 n1 f2 l2 n2

  else begin (* Same file *)
    if l2 > l1 then
      fprintf ff
        "File \"%s\", line %d-%d, characters %d-%d:@\n" f1 l1 l2 n1 n2
    else
      fprintf ff "File \"%s\", line %d, characters %d-%d:@\n" f1 l1 n1 n2;
    (* Output source code *)
    try
      let ic = open_in f1 in

      if l1 == l2 then (
        (* Only one line : copy full line and underline *)
        seek_in ic lp1;
        copy_lines 1 ic ff ">";
        underline_line ic ff '^' lp1 n1 n2 )
      else (
        underline_line ic ff '.' lp1 0 n1; (* dots until n1 *)
        seek_in ic np1;
        (* copy the end of the line l1 after the dots *)
        copy_lines 1 ic ff "";
        if l2 - l1 <= 8 then
          (* copy the 6 or less middle lines *)
          copy_lines (l2-l1-1) ic ff ">"
        else (
          (* sum up the middle lines to 6 *)
          copy_lines 3 ic ff ">";
          fprintf ff "..........@\n";
          skip_lines (l2-l1-7) ic; (* skip middle lines *)
          copy_lines 3 ic ff ">"
        );
        fprintf ff ">";
        copy_chunk lp2 np2 ic ff; (* copy interesting begining of l2 *)
      )
    with Sys_error _ -> ();
  end;
  fprintf ff "@."
