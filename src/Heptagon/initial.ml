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
(* initialization of the typing environment *)

open Names
open Types

let tglobal = []
let cglobal = []

let pbool = { qual = Pervasives; name = "bool" }
let tbool = Types.Tid pbool
let ptrue = { qual = Pervasives; name = "true" }
let pfalse = { qual = Pervasives; name = "false" }
let por = { qual = Pervasives; name = "or" }
let pand = { qual = Pervasives; name = "&" }
let pnot = { qual = Pervasives; name = "not" }
let pimp = { qual = Pervasives; name = "=>" }
let pint = { qual = Pervasives; name = "int" }
let tint = Types.Tid pint
let pfloat = { qual = Pervasives; name = "float" }
let tfloat = Types.Tid pfloat
let pstring = { qual = Pervasives; name = "string" }
let tstring = Types.Tid pstring

let pfile = { qual = Module "Iostream"; name = "file" }
let tfile = Types.Tid pfile

let mk_pervasives s = { qual = Pervasives; name = s }

let mk_static_int_op op args =
  mk_static_exp tint (Sop (op,args))

let mk_static_int i =
  mk_static_exp tint (Sint i)

let mk_static_float f =
  mk_static_exp tint (Sfloat f)

let mk_static_bool b =
  mk_static_exp tbool (Sbool b)

let mk_static_string s =
  mk_static_exp  tstring (Sstring s)


(* build the initial environment *)
(* let initialize modul = *)
(*   Modules.initialize modul; *)
(*   List.iter (fun (f, ty) -> Modules.add_type f ty) tglobal; *)
(*   List.iter (fun (f, ty) -> Modules.add_constrs f ty) cglobal *)
