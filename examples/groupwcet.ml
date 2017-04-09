#! /usr/bin/env ocaml

(* 20170409 T.Bourke: collate wcet information for gnuplot *)

(* Unfortunately, it's not possible to reliably pass "str.cma" as an argument to
   ocaml via env. *)
#use "topfind"
#require "str"

open Printf

let re_fileext = Str.regexp "\\(.*\\)\\.\\(.*\\)\\.wcet"
let re_wcetline = Str.regexp "WCET\\[\\(.*\\)\\] *= *\\([0-9]*\\) *cycles"

(* expected number of function timings (per group) *)
let exp_num_functions = 200

module Hash = Hashtbl.Make (struct include String let hash = Hashtbl.hash end)

let wcet = (Hash.create exp_num_functions : int Hash.t Hash.t)
let exts = ref ([] : string list)

let add_ext ext =
  if List.mem ext !exts then ()
  else exts := ext::!exts

let wcet_add ext fname v =
  let fhash =
    try
      Hash.find wcet fname
    with Not_found -> begin
      let n = Hash.create 5 in
      Hash.add wcet fname n; n
    end
  in
  Hash.add fhash ext v

let wcet_list () =
  let nms = ref []in
  Hash.iter (fun nm _ -> nms := nm::!nms) wcet;
  List.sort String.compare !nms

let read_lines ext fin =
  let rec read_line () =
    let s = input_line fin in
    if Str.string_match re_wcetline s 0
    then let fname = String.lowercase_ascii (Str.matched_group 1 s) in
         wcet_add ext fname (int_of_string (Str.matched_group 2 s))
    else eprintf "ignoring: %s\n" s;
    read_line ()
  in
  try read_line () with End_of_file -> ()

let read_file path =
  if Str.string_match re_fileext path 0
  then let ext = Str.matched_group 2 path in
       (add_ext ext; read_lines ext (open_in path))

let print_function fname =
  let print_value data ext =
    printf " %s" (try string_of_int (Hash.find data ext) with Not_found -> "?")
  in
  try
    let data = Hash.find wcet fname in
    printf "%s" fname;
    List.iter (print_value data) !exts;
    printf "\n"
  with Not_found ->
    eprintf "no data for '%s'\n" fname

let print_header () =
  printf "function";
  List.iter (printf " %s") !exts;
  printf "\n"

let print_data () =
  print_header ();
  List.iter print_function (wcet_list ())

let main () =
  if Array.length Sys.argv > 1 then
    for i = 1 to Array.length Sys.argv - 1 do
      read_file Sys.argv.(i)
    done
  else Array.iter read_file (Sys.readdir ".");
  print_data ()

let () = main ();;

