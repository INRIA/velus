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
(* useful stuff *)

let optional f = function
  | None -> None
  | Some x -> Some (f x)

let optional_wacc f acc = function
  | None -> None, acc
  | Some x -> let x, acc = f acc x in Some x, acc

let optunit f = function
  | None -> ()
  | Some x -> f x


(** Print to a string *)
let print_pp_to_string print_fun element =
  let _ = Format.flush_str_formatter () in (* Ensure that the buffer is empty *)
  print_fun Format.str_formatter element;
  Format.flush_str_formatter ()

(** Replace all non [a-z A-Z 0-9] character of a string by [_] *)
let sanitize_string s =
  Str.global_replace (Str.regexp "[^a-zA-Z0-9]") "_" s


(* creation of names. Ensure unicity for the whole compilation chain *)
let symbol = ref 0

let gen_symbol () = incr symbol; "_"^(string_of_int !symbol)
let reset_symbol () = symbol := (*!min_symbol*) 0

let unique l =
  let tbl = Hashtbl.create (List.length l) in
  List.iter (fun i -> Hashtbl.replace tbl i ()) l;
  Hashtbl.fold (fun key _ accu -> key :: accu) tbl []

let rec map_butlast f l =
  match l with
    | [] -> []
    | [a] -> [a]
    | a::l -> (f a)::(map_butlast f l)

let map_butnlast n f l =
  let rec aux l = match l with
    | [] -> [], 0
    | a::l ->
        let (res, k) = aux l in
        if k < n then
          a::res, (k + 1)
        else
          (f a)::res, (k+1)
  in
  let res, _ = aux l in
  res

let rec last_element l =
  match l with
    | [] -> assert false
    | [v] -> v
    | _::l -> last_element l

(** [split_last l] returns l without its last element and
    the last element of l. *)
let rec split_last = function
  | [] -> assert false
  | [a] -> [], a
  | v::l ->
      let l, a = split_last l in
      v::l, a

(** [split_nlasts l] returns l without its last n elements and
    the last n elements of l. *)
let split_nlast n l =
  let rec aux l = match l with
    | [] -> [], [], 0
    | a::l ->
        let (l1, l2, k) = aux l in
        if k < n then
          l1, a::l2, (k + 1)
        else
          a::l1, l2, (k+1)
  in
  let l1, l2, k = aux l in
  if (k < n) then
    assert false
  else l1, l2

exception List_too_short

(** [split_at n l] splits [l] in two after the [n]th value.
    Raises List_too_short exception if the list is too short. *)
let rec split_at n l = match n, l with
  | 0, l -> [], l
  | _, [] -> raise List_too_short
  | n, x::l ->
      let l1, l2 = split_at (n-1) l in
        x::l1, l2

let take n l =
  let (l, _) = split_at n l in
  l

let drop n l =
  let (_, l) = split_at n l in
  l

let rec nth_of_list n l = match n, l with
  | 1, h::_ -> h
  | n, _::t -> nth_of_list (n-1) t
  | _ -> raise List_too_short


let remove x l =
  List.filter (fun y -> x <> y) l

let list_compare c l1 l2 =
  let rec aux l1 l2 = match (l1, l2) with
    | (h1::t1, h2::t2) ->
        let result = c h1 h2 in
        if result = 0 then aux t1 t2 else result
    | ([],     []    ) -> 0
    | (_,      []    ) -> 1
    | ([],     _     ) -> -1
  in aux l1 l2

let option_compare f ox1 ox2 = match ox1, ox2 with
  | None, None -> 0
  | Some x1, Some x2 -> f x1 x2
  | None, _ -> -1
  | _, None -> 1

let is_empty = function
  | [] -> true
  | _ -> false

(** [repeat_list v n] returns a list with n times the value v. *)
let repeat_list v n =
  let rec aux = function
    | 0 -> []
    | n -> v::(aux (n-1))
  in
  aux n

(** Same as List.mem_assoc but using the value instead of the key. *)
let rec memd_assoc value = function
  | [] -> false
  | (_,d)::l -> (d = value) || (memd_assoc value l)

(** Same as List.assoc but searching for a data and returning the key. *)
let rec assocd value = function
  | [] -> raise Not_found
  | (k,d)::l ->
      if d = value then
        k
      else
        assocd value l

(** [list_diff l dl] returns [l] without the elements belonging to [dl].*)
let rec list_diff l dl = match l with
    | [] -> []
    | x::l ->
      let l = list_diff l dl in
      if List.mem x dl then l else x::l

(** {3 Compiler iterators} *)

(** Mapfold *) (* TODO optim : in a lot of places we don't need the List.rev *)
let mapfold f acc l =
  let l,acc = List.fold_left
                (fun (l,acc) e -> let e,acc = f acc e in e::l, acc)
                ([],acc) l in
  List.rev l, acc

let mapfold2 f acc l1 l2 =
  let l,acc = List.fold_left2
                (fun (l,acc) e1 e2 -> let e,acc = f acc e1 e2 in e::l, acc)
                ([],acc) l1 l2 in
  List.rev l, acc

let mapfold_right f l acc =
  List.fold_right (fun e (acc, l) -> let acc, e = f e acc in (acc, e :: l))
    l (acc, [])

let rec fold_right_1 f l = match l with
  | [] -> invalid_arg "fold_right_1: empty list"
  | [x] -> x
  | x :: l -> f x (fold_right_1 f l)

let rec fold_left_1 f l = match l with
  | [] -> invalid_arg "fold_left_1: empty list"
  | [x] -> x
  | x :: l -> f (fold_left_1 f l) x

let rec fold_left4 f acc l1 l2 l3 l4 = match l1, l2, l3, l4 with
  | [], [], [], [] -> acc
  | x1 :: l1, x2 :: l2, x3 :: l3, x4 :: l4 -> fold_left4 f (f acc x1 x2 x3 x4) l1 l2 l3 l4
  | _ -> invalid_arg "Misc.fold_left4"

let mapi f l =
  let rec aux i = function
    | [] -> []
    | v::l -> (f i v)::(aux (i+1) l)
  in
    aux 0 l

let mapi2 f l1 l2 =
  let rec aux i l1 l2 =
    match l1, l2 with
      | [], [] -> []
      | [], _ -> invalid_arg ""
      | _, [] -> invalid_arg ""
      | v1::l1, v2::l2 -> (f i v1 v2)::(aux (i+1) l1 l2)
  in
    aux 0 l1 l2

let mapi3 f l1 l2 l3 =
  let rec aux i l1 l2 l3 =
    match l1, l2, l3 with
      | [], [], [] -> []
      | [], _, _ -> invalid_arg ""
      | _, [], _ -> invalid_arg ""
      | _, _, [] -> invalid_arg ""
      | v1::l1, v2::l2, v3::l3 ->
          (f i v1 v2 v3)::(aux (i+1) l1 l2 l3)
  in
    aux 0 l1 l2 l3

let fold_righti f l acc =
  let rec aux i l acc = match l with
    | [] -> acc
    | h :: l -> f i h (aux (i + 1) l acc) in
  aux 0 l acc

let rec map3 f l1 l2 l3 = match l1, l2, l3 with
  | [], [], [] -> []
  | v1::l1, v2::l2, v3::l3 -> (f v1 v2 v3)::(map3 f l1 l2 l3)
  | _ -> invalid_arg "Misc.map3"

exception Assert_false
let internal_error passe =
  Format.eprintf "@.---------@\n\
                  Internal compiler error@\n\
                  Passe : %s@\n\
                  ----------@." passe;
  raise Assert_false

exception Unsupported
let unsupported passe =
  Format.eprintf "@.---------@\n\
Unsupported feature, please report it@\n\
Passe : %s@\n\
----------@." passe;
  raise Unsupported

(* Functions to decompose a list into a tuple *)
let _arity_error i l =
  Format.eprintf "@.---------@\n\
Internal compiler error: wrong list size (found %d, expected %d).@\n\
----------@." (List.length l) i;
  raise Assert_false

let _arity_min_error i l =
  Format.eprintf "@.---------@\n\
Internal compiler error: wrong list size (found %d, expected %d at least).@\n\
----------@." (List.length l) i;
  raise Assert_false

let assert_empty = function
  | [] -> ()
  | l -> _arity_error 0 l

let assert_1 = function
  | [v] -> v
  | l -> _arity_error 1 l

let assert_1min = function
  | v::l -> v, l
  | l -> _arity_min_error 1 l

let assert_2 = function
  | [v1; v2] -> v1, v2
  | l -> _arity_error 2 l

let assert_2min = function
  | v1::v2::l -> v1, v2, l
  | l -> _arity_min_error 2 l

let assert_3 = function
  | [v1; v2; v3] -> v1, v2, v3
  | l -> _arity_error 3 l

let (|>) x f = f x

let split_string s separator = Str.split (separator |> Str.quote |> Str.regexp) s

let file_extension s = split_string s "." |> last_element

(** Memoize the result of the function [f]*)
let memoize f =
  let map = Hashtbl.create 100 in
    fun x ->
      try
        Hashtbl.find map x
      with
        | Not_found -> let r = f x in Hashtbl.add map x r; r

(** Memoize the result of the function [f], taht should expect a
   tuple as input and be reflexive (f (x,y) = f (y,x)) *)
let memoize_couple f =
  let map = Hashtbl.create 100 in
    fun (x,y) ->
      try
        Hashtbl.find map (x,y)
      with
        | Not_found ->
            let r = f (x,y) in Hashtbl.add map (x,y) r; Hashtbl.add map (y,x) r; r

(** [iter_couple f l] calls f for all x and y distinct in [l].  *)
let rec iter_couple f l = match l with
  | [] -> ()
  | x::l ->
      List.iter (f x) l;
      iter_couple f l

(** [iter_couple_2 f l1 l2] calls f for all x in [l1] and y in [l2].  *)
let iter_couple_2 f l1 l2 =
  List.iter (fun v1 -> List.iter (f v1) l2) l1

(** [index p l] returns the idx of the first element in l
    that satisfies predicate p.*)
let index p l =
  let rec aux i = function
    | [] -> -1
    | v::l -> if p v then i else aux (i+1) l
  in
    aux 0 l
