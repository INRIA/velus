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

(* Misc. functions *)
val optional : ('a -> 'b) -> 'a option -> 'b option

(** Optional with accumulator *)
val optional_wacc : ('a -> 'b -> 'c*'a) -> 'a -> 'b option -> ('c option * 'a)
val optunit : ('a -> unit) -> 'a option -> unit

(** [split_string s c] splits the string [s] according to the separator
    [c] into a list of string without [c] *)
val split_string : string -> string -> string list

(* Generation of unique names. Mandatory call of reset_symbol between
   set_min_symbol and gen_symbol *)
(*val set_min_symbol : int -> unit*)
val gen_symbol : unit -> string
val reset_symbol : unit -> unit

(** [unique l] returns the [l] list without duplicates. O([length l]). *)
val unique : 'a list -> 'a list

(** [map_butlast f l] applies f to all the elements of
    l except the last element. *)
val map_butlast : ('a -> 'a) -> 'a list -> 'a list

(** [map_butnlast f l] applies f to all the elements of
    l except the n last element. *)
val map_butnlast : int -> ('a -> 'a) -> 'a list -> 'a list

(** [last_element l] returns the last element of the list l.*)
val last_element : 'a list -> 'a

(** [split_last l] returns the list l without its last element
    and the last element of the list .*)
val split_last : 'a list -> ('a list * 'a)

(** [split_nlast l] returns the list l without its n last elements
    and the last element of the list .*)
val split_nlast : int -> 'a list -> ('a list * 'a list)

exception List_too_short

(** [split_at n l] splits [l] in two after the [n]th value (starting at 0).
    Raises List_too_short exception if the list is too short. *)
val split_at : int -> 'a list -> 'a list * 'a list

(** [take n l] returns the [n] first elements of the list [l] *)
val take : int -> 'a list -> 'a list

(** [drop n l] removes the [n] first elements of the list [l] *)
val drop : int -> 'a list -> 'a list

(** [nth_of_list n l] @return the [n] element of the list [l] (1 is the first)
    @raise List_too_short exception if the list is too short.*)
val nth_of_list : int -> 'a list -> 'a

(** [remove x l] removes all occurrences of x from list l.*)
val remove : 'a -> 'a list -> 'a list

(** [is_empty l] returns whether the list l is empty.*)
val is_empty : 'a list -> bool

(** [repeat_list v n] returns a list with n times the value v. *)
val repeat_list : 'a -> int -> 'a list

(** Same as List.mem_assoc but using the value instead of the key. *)
val memd_assoc : 'b -> ('a * 'b) list -> bool

(** Same as List.assoc but searching for a data and returning the key. *)
val assocd : 'b -> ('a * 'b) list -> 'a

(** [list_compare c l1 l2] compares the lists [l1] and [l2] according to
    lexicographical order induced by [c]. *)
val list_compare : ('a -> 'a -> int) -> 'a list -> 'a list -> int

val option_compare : ('a -> 'a -> int) -> 'a option -> 'a option -> int

(** [list_diff l dl] returns [l] without the elements belonging to [dl].*)
val list_diff : 'a list -> 'a list -> 'a list

(** Mapfold *)
val mapfold: ('acc -> 'b -> 'c * 'acc) -> 'acc -> 'b list -> 'c list * 'acc
val mapfold2: ('acc -> 'b -> 'd -> 'c * 'acc) -> 'acc -> 'b list -> 'd list -> 'c list * 'acc

(** Mapfold, right version. *)
val mapfold_right
  : ('a -> 'acc -> 'acc * 'b) -> 'a list -> 'acc -> 'acc * 'b list

(** [fold_right_1 f [x1; x2; ...; xn]] = f x1 (f x2 (f ... xn)). The list should
    have at least one element! *)
val fold_right_1 :
  ('a -> 'a -> 'a) -> 'a list -> 'a

(** [fold_left_1 f [x1; x2; ...; xn]] = f (f ... (f x1 x2) ...) xn. The list should
    have at least one element! *)
val fold_left_1 :
  ('a -> 'a -> 'a) -> 'a list -> 'a

(** [fold_left4] is fold_left with four lists *)
val fold_left4 :
  ('a -> 'b -> 'c -> 'd -> 'e -> 'a) -> 'a -> 'b list -> 'c list -> 'd list -> 'e list -> 'a

(** Mapi *)
val map3: ('a -> 'b -> 'c -> 'd) ->
  'a list -> 'b list -> 'c list -> 'd list
val mapi: (int -> 'a -> 'b) -> 'a list -> 'b list
val mapi2: (int -> 'a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
val mapi3: (int -> 'a -> 'b -> 'c -> 'd) ->
  'a list -> 'b list -> 'c list -> 'd list
val fold_righti : (int -> 'a -> 'b -> 'b) -> 'a list -> 'b -> 'b

(** [iter_couple f l] calls f for all x and y distinct in [l].  *)
val iter_couple : ('a -> 'a -> unit) -> 'a list -> unit

(** [iter_couple_2 f l1 l2] calls f for all x in [l1] and y in [l2].  *)
val iter_couple_2 : ('a -> 'a -> unit) -> 'a list -> 'a list -> unit

(** [index p l] returns the idx of the first element in l
    that satisfies predicate p.*)
val index : ('a -> bool) -> 'a list -> int

(** Functions to decompose a list into a tuple *)
val assert_empty : 'a list -> unit
val assert_1 : 'a list -> 'a
val assert_1min : 'a list -> 'a * 'a list
val assert_2 : 'a list -> 'a * 'a
val assert_2min : 'a list -> 'a * 'a * 'a list
val assert_3 : 'a list -> 'a * 'a * 'a

(** Print to string *)
val print_pp_to_string : (Format.formatter -> 'a -> unit) -> 'a -> string

(** Replace all non [a-z A-Z 0-9] character of a string by [_] *)
val sanitize_string : string -> string

(** Pipe a value to a function *)
val (|>) : 'a -> ('a -> 'b) -> 'b

(** Return the extension of a filename string *)
val file_extension : string -> string

(** Internal error : Is used when an assertion wrong *)
val internal_error : string -> 'a

(** Unsupported : Is used when something should work but is not currently supported *)
val unsupported : string -> 'a

(** Memoize the result of the function [f]*)
val memoize : ('a -> 'b) -> ('a -> 'b)

(** Memoize the result of the function [f], taht should expect a
   tuple as input and be reflexive (f (x,y) = f (y,x)) *)
val memoize_couple : (('a * 'a) -> 'b) -> (('a * 'a) -> 'b)
