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

let extern_atom = Camlcoq.extern_atom

module type SYNTAX =
  sig
    type clock
    type typ
    type const
    type lexp
    type cexp
    type lexps

    type equation =
    | EqDef of ident * clock * cexp
    | EqApp of idents * clock * ident * lexps * ident option
    | EqFby of ident * clock * const * lexp

    type node = {
      n_name : ident;
      n_in   : (ident * (typ * clock)) list;
      n_out  : (ident * (typ * clock)) list;
      n_vars : (ident * (typ * clock)) list;
      n_eqs  : equation list }

    type global = node list
  end

module PrintFun
    (CE: Coreexprlib.SYNTAX)
    (NL: SYNTAX with type clock = CE.clock
                 and type typ   = CE.typ
                 and type const = CE.const
                 and type lexp  = CE.lexp
                 and type cexp  = CE.cexp
                 and type lexps = CE.lexps)
    (PrintOps: PRINT_OPS with type typ   = CE.typ
                          and type const = CE.const
                          and type unop  = CE.unop
                          and type binop = CE.binop) :
  sig
    val print_fullclocks : bool ref
    val print_equation : formatter -> NL.equation -> unit
    val print_node     : Format.formatter -> NL.node -> unit
    val print_global   : Format.formatter -> NL.global -> unit
  end
  =
  struct

    include Coreexprlib.PrintFun (CE) (PrintOps)

    let print_fullclocks = ref false

    let print_clock_decl p ck =
      match ck with
      | CE.Cbase -> ()
      | CE.Con (ck', x, b) ->
        if !print_fullclocks
        then fprintf p " :: @[<hov 3>%a@]" print_clock ck
        else fprintf p " when%s %s"
            (if b then "" else " not")
            (extern_atom x)

    let print_decl p (id, (ty, ck)) =
      fprintf p "%s@ : %a%a"
        (extern_atom id)
        PrintOps.print_typ ty
        print_clock_decl ck

    let print_ident p i = pp_print_string p (extern_atom i)

    let print_pattern p xs =
      match xs with
      | [x] -> print_ident p x
      | xs  -> fprintf p "(@[<hv 0>%a@])" (print_comma_list print_ident) xs

    let rec print_equation p eq =
      match eq with
      | NL.EqDef (x, ck, e) ->
          fprintf p "@[<hov 2>%s =@ %a;@]"
            (extern_atom x) print_cexpr e
      | NL.EqApp (xs, ck, f, es, None) ->
          fprintf p "@[<hov 2>%a =@ %s(@[<hv 0>%a@]);@]"
            print_pattern xs
            (extern_atom f)
            (print_list print_lexpr) es
      | NL.EqApp (xs, ck, f, es, Some r) ->
        fprintf p "@[<hov 2>%a =@ %s(@[<hv 0>%a@])@ every@ %s;@]"
          print_multiple_results xs
          (extern_atom f)
          (print_list print_lexpr) es
          (extern_atom r)
      | NL.EqFby (x, ck, v0, e) ->
          fprintf p "@[<hov 2>%s =@ %a fby@ %a;@]"
            (extern_atom x) PrintOps.print_const v0 print_lexp e

    let print_equations p =
      let rec print first eqs =
        match eqs with
        | [] -> ()
        | eq :: eqs ->
            (if first
             then print_equation p eq
             else fprintf p "@;%a" print_equation eq);
            print false eqs
      in
      print true

    let print_node p { NL.n_name = name;
                       NL.n_in   = inputs;
                       NL.n_out  = outputs;
                       NL.n_vars = locals;
                       NL.n_eqs  = eqs } =
      fprintf p "@[<v>";
      fprintf p "@[<hov 0>";
        fprintf p "@[<h>node %s (%a)@]@;"
          (extern_atom name)
          (print_comma_list print_decl) inputs;
        fprintf p "@[<h>returns (%a)@]@;"
          (print_comma_list print_decl) outputs;
      fprintf p "@]@;";
      if List.length locals > 0 then
        fprintf p "@[<h>var @[<hov 4>%a@];@]@;"
          (print_comma_list print_decl) locals;
      fprintf p "@[<v 2>let@;%a@;<0 -2>@]" print_equations (List.rev eqs);
      fprintf p "tel@]"

    let print_global p prog =
      fprintf p "@[<v 0>";
      List.iter (fprintf p "@;%a@;" print_node) prog;
      fprintf p "@]@."
  end
