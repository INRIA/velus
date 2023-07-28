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
open Format
open Names
open Misc

type linearity_var = name

type init =
    | Lno_init
    | Linit_var of linearity_var
    | Linit_tuple of init list

type linearity =
  | Ltop
  | Lat of linearity_var
  | Lvar of linearity_var (*a linearity var, used in functions sig *)
  | Ltuple of linearity list

module LinearitySet = Set.Make(struct
  type t = linearity
  let compare = compare
end)

module LocationEnv =
    Map.Make(struct
      type t = linearity_var
      let compare = compare
    end)

module LocationSet =
    Set.Make(struct
      type t = linearity_var
      let compare = compare
    end)

(** Returns a linearity object from a linearity list. *)
let prod = function
  | [l] -> l
  | l -> Ltuple l

let linearity_list_of_linearity = function
  | Ltuple l -> l
  | l -> [l]

let flatten_lin_list l =
  List.fold_right
    (fun arg args -> match arg with Ltuple l -> l@args | a -> a::args ) l []

let rec lin_skeleton lin = function
  | Types.Tprod l -> Ltuple (List.map (lin_skeleton lin) l)
  | _ -> lin

(** Same as Misc.split_last but on a linearity. *)
let split_last_lin = function
  | Ltuple l ->
      let l, acc = split_last l in
        Ltuple l, acc
  | l ->
      Ltuple [], l

let rec is_not_linear = function
  | Ltop -> true
  | Ltuple l -> List.for_all is_not_linear l
  | _ -> false

let rec is_linear = function
  | Lat _ | Lvar _ -> true
  | Ltuple l -> List.exists is_linear l
  | _ -> false

let location_name = function
  | Lat r | Lvar r -> r
  | _ -> assert false

exception UnifyFailed

(** Unifies lin with expected_lin and returns the result
    of the unification. Applies subtyping and instantiate linearity vars. *)
let rec unify_lin expected_lin lin =
  match expected_lin,lin with
    | Ltop, Lat _ -> Ltop
    | Ltop, Lvar _ -> Ltop
    | Lat r1, Lat r2 when r1 = r2 -> Lat r1
    | Ltop, Ltop -> Ltop
    | Ltuple l1, Ltuple l2 -> Ltuple (List.map2 unify_lin l1 l2)
    | Lvar _, Lat r -> Lat r
    | Lat r, Lvar _ -> Lat r
    | _, _ -> raise UnifyFailed

let check_linearity lin =
  if is_linear lin && (* not !Compiler_options.do_linear_typing *) true then
    Ltop
  else
    lin

let rec lin_to_string = function
  | Ltop -> "at T"
  | Lat r -> "at "^r
  | Lvar r -> "at _"^r
  | Ltuple l_list -> String.concat ", " (List.map lin_to_string l_list)

let print_linearity ff l =
  match l with
    | Ltop -> ()
    | _ -> fprintf ff " %s" (lin_to_string l)

let rec linearity_compare l1 l2 = match l1, l2 with
  | Ltop, Ltop -> 0
  | Lvar v1, Lvar v2 -> compare v1 v2
  | Lat v1, Lat v2 -> compare v1 v2
  | Ltuple l1, Ltuple l2 -> list_compare linearity_compare l1 l2

  | Ltop, _ -> 1

  | Lvar _, Ltop -> -1
  | Lvar _, _ -> 1

  | Lat _ , (Ltop | Lvar _) -> -1
  | Lat _ , _ -> 1

  | Ltuple _, _ -> -1
