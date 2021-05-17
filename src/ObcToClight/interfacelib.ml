(* *********************************************************************)
(*                    The Velus Lustre compiler                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* This pretty-printer draws on the work of Xavier Leroy for the CompCert
   project (CompCert/cfrontend/PrintCsyntax.ml/PrintClight.ml). *)

open Format
open Camlcoq
open Veluscommon

module ClightOpNames =
  struct
    let name_unop ty = PrintCsyntax.name_unop
    let name_binop ty = PrintCsyntax.name_binop
  end

module ClightTypeFormats
  : TYPE_FORMATS with type typ = Interface.Op.coq_type =
  struct
    type typ = Interface.Op.coq_type

    let rec type_decl ty =
      let open Interface.Op in
      let open Interface.OpAux in
      match ty with
      | Tprimitive ty ->
        begin match ty with
          | Tint (sz, sg) -> PrintCsyntax.name_inttype sz sg
          | Tlong sg      -> PrintCsyntax.name_longtype sg
          | Tfloat sz     -> PrintCsyntax.name_floattype sz
        end
      | Tenum (_, n) -> type_decl (Tprimitive (enumtag_ctype n))

    let rec type_printf ty =
      let open Ctypes in
      let open Interface.Op in
      let open Interface.OpAux in
      match ty with
      | Tprimitive ty ->
        begin match ty with
          | Tint (I8, Signed)    -> "%hhd"
          | Tint (I8, Unsigned)  -> "%hhu"
          | Tint (I16, Signed)   -> "%hd"
          | Tint (I16, Unsigned) -> "%hu"
          | Tint (I32, Signed)   -> "%d"
          | Tint (I32, Unsigned) -> "%u"
          | Tint (IBool, _)      -> "%d"
          | Tlong Signed         -> "%lld"
          | Tlong Unsigned       -> "%llu"
          | Tfloat F32           -> "%e"
          | Tfloat F64           -> "%e"
        end
      | Tenum (_, n) -> type_decl (Tprimitive (enumtag_ctype n))

    let rec type_scanf ty =
      let open Ctypes in
      let open Interface.Op in
      let open Interface.OpAux in
      match ty with
      | Tprimitive ty ->
        begin match ty with
          | Tint (I8, Signed)    -> "%hhd"
          | Tint (I8, Unsigned)  -> "%hhu"
          | Tint (I16, Signed)   -> "%hd"
          | Tint (I16, Unsigned) -> "%hu"
          | Tint (I32, Signed)   -> "%d"
          | Tint (I32, Unsigned) -> "%u"
          | Tint (IBool, _)      -> "%hhu"    (* nonstandard: CompCert stores
                                                              bools in 1-byte *)
          | Tlong Signed         -> "%lld"
          | Tlong Unsigned       -> "%llu"
          | Tfloat F32           -> "%f"
          | Tfloat F64           -> "%lf"
        end
      | Tenum (_, n) -> type_scanf (Tprimitive (enumtag_ctype n))

  end

module LustreOpNames =
  struct
    let is_bool = function
    | Interface.Op.Tint (Ctypes.IBool, _) -> true
    | _ -> false

    let name_unop ty = function
      | Cop.Onotbool -> "not"
      | Cop.Onotint  -> "lnot"
      | Cop.Oneg     -> "-"
      | Cop.Oabsfloat -> "__builtin_fabs"

    let name_binop ty = function
      | Cop.Oadd -> "+"
      | Cop.Osub -> "-"
      | Cop.Omul -> "*"
      | Cop.Odiv -> "/"
      | Cop.Omod -> "mod"
      | Cop.Oand -> if is_bool ty then "and" else "land"
      | Cop.Oor  -> if is_bool ty then "or"  else "lor"
      | Cop.Oxor -> if is_bool ty then "xor" else "lxor"
      | Cop.Oshl -> "lsl"
      | Cop.Oshr -> "lsr"
      | Cop.Oeq  -> "="
      | Cop.One  -> "<>"
      | Cop.Olt  -> "<"
      | Cop.Ogt  -> ">"
      | Cop.Ole  -> "<="
      | Cop.Oge  -> ">="
  end

module PrintClightOpsFun (OpNames : sig
    val name_unop  : Interface.Op.ctype -> Cop.unary_operation -> string
    val name_binop : Interface.Op.ctype -> Cop.binary_operation -> string
  end) =
  struct
    module Ops = Interface.Op
    module OpAux = Interface.OpAux

    type typ     = Ops.coq_type
    type cconst  = Ops.cconst
    type const   = Ops.const
    type unop    = Ops.unop
    type binop   = Ops.binop
    type enumtag = Ops.enumtag

    let print_typ' p ty = Ops.string_of_ctype ty |> fmt_coqstring p
    let print_typ p ty = Interface.string_of_type ty |> fmt_coqstring p

    let print_cconst p c =
      match c with
      | Ops.Cint (n, Ctypes.I32, Ctypes.Unsigned) ->
          fprintf p "%luU"   (camlint_of_coqint n)
      | Ops.Cint (n, _, _) ->
          fprintf p "%ld"    (camlint_of_coqint n)
      | Ops.Cfloat f ->
          fprintf p "%.15F"  (camlfloat_of_coqfloat f)
      | Ops.Csingle f ->
          fprintf p "%.15Ff"   (camlfloat_of_coqfloat32 f)
      | Ops.Clong (n, Ctypes.Unsigned) ->
          fprintf p "%LuLLU" (camlint64_of_coqint n)
      | Ops.Clong (n, _) ->
          fprintf p "%LdLL"  (camlint64_of_coqint n)

    let print_unop p uop ty print_exp e =
      match uop, ty with
      | Ops.UnaryOp op, Ops.Tprimitive ty ->
          fprintf p "%s %a" (OpNames.name_unop ty op) print_exp e
      | Ops.UnaryOp op, Ops.Tenum (_, n) ->
          fprintf p "%s %a" (OpNames.name_unop (Ops.enumtag_ctype n) op) print_exp e
      | Ops.CastOp ty, _ ->
          fprintf p "(%a : %a)" print_exp e print_typ' ty

    let print_binop p op ty print_exp1 e1 print_exp2 e2 =
      match ty with
      | Ops.Tprimitive ty ->
        fprintf p "%a@ %s %a"
          print_exp1 e1
          (OpNames.name_binop ty op)
          print_exp2 e2
      | Ops.Tenum (_, n) ->
        fprintf p "%a@ %s %a"
          print_exp1 e1
          (OpNames.name_binop (Ops.enumtag_ctype n) op)
          print_exp2 e2

    let prec_unop op = (15, RtoL)
    let prec_binop =
      let open Cop in function
        | Omul|Odiv|Omod  -> (13, LtoR)
        | Oadd|Osub       -> (12, LtoR)
        | Oshl|Oshr       -> (11, LtoR)
        | Olt|Ogt|Ole|Oge -> (10, LtoR)
        | Oeq|One         -> ( 9, LtoR)
        | Oand            -> ( 8, LtoR)
        | Oxor            -> ( 7, LtoR)
        | Oor             -> ( 6, LtoR)

    let print_enumtag p c =
      fprintf p "%d" (Nat.to_int c)

    let print_const p c =
      match c with
      | Ops.Const c -> print_cconst p c
      | Ops.Enum c -> print_enumtag p c

    let print_branches pp_br p (brs, default) =
      let _, has_default = List.fold_left (fun (n, has_def) o ->
          let n' = n+1 in
          match o with
          | Some b ->
            fprintf p "@;| %d => @[<hv 0>%a@]" n pp_br b;
            (n', has_def)
          | None ->
            fprintf p "@;| %d => _" n;
            (n', true)) (0, false) brs
      in
      match has_default, default with
      | true, Some d ->
              fprintf p "@;| default => @[<hv 0>%a@]" pp_br d
      | _ -> ()

  end

(* module Basics = struct
 *   type typ   = Interface.OpAux.coq_type
 *   type const = Interface.Op.const
 *   type unop  = Interface.Op.unop
 *   type binop = Interface.Op.binop
 * end *)

module Ops = PrintClightOpsFun (LustreOpNames)

module PrintLustre = Lustrelib.PrintFun
    (Ops)
    (struct
      include Ops
      include Interface.Cks
      include Instantiator.L.Syn
      include Basics
    end)

module CE = struct
  include Ops
  include Interface.Cks
  include Instantiator.CE.Syn
end

module PrintNLustre = Nlustrelib.PrintFun
    (Ops)
    (CE)
    (struct
      include CE
      include Instantiator.NL.Syn
    end)

module PrintStc = Stclib.PrintFun
    (Ops)
    (CE)
    (struct
      include CE
      include Instantiator.Stc.Syn
    end)

module PrintObc = Obclib.PrintFun
  (Ops)
  (struct
    (* include Basics *)
    include Ops
    include Interface.Obc.Syn
   end)

module SyncFun = Obclib.SyncFun
  (struct
    include Ops
    include Interface.Obc.Syn
   end)
  (ClightTypeFormats)

module Scheduler = Stclib.SchedulerFun
    (CE)
    (struct
      include CE
      include Instantiator.Stc.Syn
    end)
