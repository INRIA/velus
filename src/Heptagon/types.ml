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

open Names
open Location


type static_exp = { se_desc: static_exp_desc; se_ty: ty; se_loc: location }

and static_exp_desc =
  | Svar of constant_name
  | Sint of int
  | Sfloat of float
  | Sbool of bool
  | Sstring of string (** without enclosing quotes *)
  | Sconstructor of constructor_name
  | Sfield of field_name
  | Stuple of static_exp list
  | Sarray_power of static_exp * (static_exp list) (** power : [0^n^m : [[0,0,..],[0,0,..],..]] *)
  | Sarray of static_exp list (** [[ e1, e2, e3 ]] *)
  | Srecord of (field_name * static_exp) list (** [{ f1 = e1; f2 = e2; ... }] *)
  | Sop of fun_name * static_exp list (** defined ops for now in pervasives *)

and ty =
  | Tprod of ty list (** Product type used for tuples *)
  | Tid of type_name (** Usable type_name are alias or pervasives {bool,int,float} (see [Initial])*)
  | Tarray of ty * static_exp (** [base_type] * [size] *) (* ty should not be prod *)
  | Tinvalid

let invalid_type = Tinvalid (** Invalid type given to untyped expression etc. *)

let prod = function
  | [ty]    -> ty
  | ty_list -> Tprod ty_list

let unprod = function
  | Tprod l -> l
  | t -> [t]

let mk_static_exp ?(loc = no_location) ty desc = (*note ~ty: replace as first arg*)
  { se_desc = desc; se_ty = ty; se_loc = loc }
