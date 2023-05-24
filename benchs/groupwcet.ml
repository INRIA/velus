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

let main_ext = "velus"
let calc_percentages = true

module Hash = Hashtbl.Make (struct include String let hash = Hashtbl.hash end)

let wcet = (Hash.create exp_num_functions : int Hash.t Hash.t)
let exts = ref ([] : string list)

let name_compare s1 s2 =
  if s1 = main_ext then (if s2 = main_ext then 0 else -1)
  else if s2 = main_ext then 1
  else String.compare s1 s2

let add_ext ext =
  if List.mem ext !exts then ()
  else exts := List.sort name_compare (ext::!exts)

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
  let print_value data =
    let mv = try Some (Hash.find data main_ext) with Not_found -> None in
    fun ext ->
      try
        let v = Hash.find data ext in
        printf " %d" v;
        if calc_percentages && ext <> main_ext then
          printf " %s"
            (match mv with
             | None -> " ?"
             | Some mv -> (string_of_int (((mv - v) * 100) / v)));
      with Not_found ->
        (printf " ?"; if calc_percentages then printf " ?")
  in
  try
    let data = Hash.find wcet fname in
    printf "%s" fname;
    List.iter (print_value data) !exts;
    printf "\n"
  with Not_found ->
    eprintf "no data for '%s'\n" fname

let print_header () =
  let double_name ext =
    printf " %s" ext; if ext <> main_ext then printf " %%"
  in
  let print_name = if calc_percentages then double_name else printf " %s" in
  printf "function";
  List.iter print_name !exts;
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
