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

open Format
open Veluscommon

open BinNums
open BinPos
open FMapPositive

type ident = Common.ident
type idents = ident list

module type SYNTAX =
  sig
    type clock
    type typ
    type cconst
    type const
    type exp
    type cexp
    type enumtag

    type equation =
    | EqDef of ident * clock * cexp
    | EqApp of idents * clock * ident * exp list * (ident * clock) list
    | EqFby of ident * clock * const * exp * (ident * clock) list

    type node = {
      n_name : ident;
      n_in   : (ident * (typ * clock)) list;
      n_out  : (ident * (typ * clock)) list;
      n_vars : (ident * (typ * clock)) list;
      n_eqs  : equation list }

    type global = {
      enums: (ident * Datatypes.nat) list;
      nodes: node list
    }
  end

module PrintFun
    (Ops: PRINT_OPS)
    (CE : Coreexprlib.SYNTAX with type typ     = Ops.typ
                              and type cconst  = Ops.cconst
                              and type unop    = Ops.unop
                              and type binop   = Ops.binop
                              and type enumtag = Ops.enumtag)
    (NL : SYNTAX with type clock   = CE.clock
                  and type typ     = Ops.typ
                  and type cconst  = Ops.cconst
                  and type const   = Ops.const
                  and type exp     = CE.exp
                  and type cexp    = CE.cexp
                  and type enumtag = Ops.enumtag) :
  sig
    val print_equation   : formatter -> NL.equation -> unit
    val print_node       : Format.formatter -> NL.node -> unit
    val print_global     : Format.formatter -> NL.global -> unit
    val print_fullclocks : bool ref
  end
  =
  struct

    include Coreexprlib.PrintFun (CE) (Ops)

    let rec print_equation p eq =
      match eq with
      | NL.EqDef (x, ck, e) ->
          fprintf p "@[<hov 2>%a =@ %a;@]"
            print_ident x
            print_cexp e
      | NL.EqApp (xs, ck, f, es, []) ->
          fprintf p "@[<hov 2>%a =@ %a(@[<hv 0>%a@]);@]"
            print_pattern xs
            print_ident f
            (print_comma_list print_exp) es
      | NL.EqApp (xs, ck, f, es, ckrs) ->
        fprintf p "@[<hov 2>%a =@ (restart@ %a@ every@ %a)(@[<hv 0>%a@]);@]"
          print_pattern xs
          print_ident f
          (print_comma_list print_ident) (List.map fst ckrs)
          (print_comma_list print_exp) es
      | NL.EqFby (x, ck, v0, e, []) ->
          fprintf p "@[<hov 2>%a =@ %a fby@ %a;@]"
            print_ident x
            Ops.print_const v0
            print_exp e
      | NL.EqFby (x, ck, v0, e, ckrs) ->
        fprintf p "@[<hov 2>%a =@ reset (%a fby@ %a) every %a;@]"
          print_ident x
          Ops.print_const v0
          print_exp e
          (print_comma_list print_ident) (List.map fst ckrs)

    let print_equations p =
      pp_print_list ~pp_sep:pp_force_newline print_equation p

    let print_node p { NL.n_name = name;
                       NL.n_in   = inputs;
                       NL.n_out  = outputs;
                       NL.n_vars = locals;
                       NL.n_eqs  = eqs } =
      fprintf p "@[<v>\
                 @[<hov 0>\
                 @[<h>node %a (%a)@]@;\
                 @[<h>returns (%a)@]@;\
                 @]@;\
                 %a\
                 @[<v 2>let@;%a@;<0 -2>@]\
                 tel@]"
        print_ident name
        print_decl_list inputs
        print_decl_list outputs
        (print_semicol_list_as "var" print_decl) locals
        print_equations (List.rev eqs)

    let print_global p prog =
      fprintf p "@[<v 0>%a@]@."
        (pp_print_list ~pp_sep:(fun p () -> fprintf p "@;@;") print_node)
        (List.rev prog.NL.nodes)
  end
