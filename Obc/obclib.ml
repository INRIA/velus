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
open Veluscommon

type ident = Common.ident
let extern_atom = Camlcoq.extern_atom

module type SYNTAX =
  sig
    type typ
    type const
    type unop
    type binop

    type exp =
    | Var   of ident * typ
    | State of ident * typ
    | Const of const
    | Unop  of unop  * exp * typ
    | Binop of binop * exp * exp * typ
    
    type stmt =
    | Assign   of ident * exp
    | AssignSt of ident * exp
    | Ifte     of exp * stmt * stmt
    | Comp     of stmt * stmt
    | Call     of ident list * ident * ident * ident * exp list
    | Skip

    type coq_method = { m_name : ident;
                        m_in   : (ident * typ) list;
                        m_vars : (ident * typ) list;
                        m_out  : (ident * typ) list;
                        m_body : stmt }

    type coq_class = { c_name : ident;
                       c_mems : (ident * typ) list;
                       c_objs : (ident * ident) list;
                       c_methods : coq_method list }

    type program = coq_class list
  end

module PrintFun (Obc: SYNTAX)
                (PrintOps : PRINT_OPS with type typ   = Obc.typ
                                       and type const = Obc.const
                                       and type unop  = Obc.unop
                                       and type binop = Obc.binop) :
  sig
    val print_expr : formatter -> Obc.exp -> unit
    val print_stmt : formatter -> Obc.stmt -> unit
    val print_method  : Format.formatter -> Obc.coq_method -> unit
    val print_class   : Format.formatter -> Obc.coq_class -> unit
    val print_program : Format.formatter -> Obc.coq_class list -> unit
  end
  =
  struct

    let precedence = function
      | Obc.Var _   -> (16, NA)
      | Obc.State _ -> (16, NA)
      | Obc.Const _ -> (16, NA)
      | Obc.Unop (op, _, _)     -> PrintOps.prec_unop op
      | Obc.Binop (op, _, _, _) -> PrintOps.prec_binop op

    let rec expr p (prec, e) =
      let (prec', assoc) = precedence e in
      let (prec1, prec2) =
        if assoc = LtoR
        then (prec', prec' + 1)
        else (prec' + 1, prec') in
      if prec' < prec
      then fprintf p "@[<hov 2>("
      else fprintf p "@[<hov 2>";
      begin match e with
      | Obc.Var (id, _) ->
          fprintf p "%s" (extern_atom id)
      | Obc.State (id, _) ->
          fprintf p "state(%s)" (extern_atom id)
      | Obc.Const c ->
          PrintOps.print_const p c
      | Obc.Unop (op, e, _) ->
          PrintOps.print_unop p op expr (prec', e)
      | Obc.Binop (op, e1, e2, _) ->
          PrintOps.print_binop p op expr (prec1, e1) (prec2, e2)
      end;
      if prec' < prec then fprintf p ")@]" else fprintf p "@]"

    let print_expr p e = expr p (0, e)

    let rec print_expr_list p (first, rl) =
      match rl with
      | [] -> ()
      | r :: rl ->
          if not first then fprintf p ",@ ";
          expr p (2, r);
          print_expr_list p (false, rl)

    let print_list print_ele p =
      let rec print first rl =
        match rl with
        | [] -> ()
        | r :: rl ->
            (if first
             then print_ele p r
             else fprintf p ",@;<1 0>%a" print_ele r);
            print false rl
      in
      print true

    let print_decl_list print_ele p =
      List.iter (fun e->fprintf p "%a;@;" print_ele e)

    let print_ident p id = pp_print_string p (extern_atom id)

    let rec print_stmt p s =
      match s with
      | Obc.Assign (id, e) ->
          fprintf p "@[<hv 2>%s :=@ %a@]" (extern_atom id)
                                                    print_expr e
      | Obc.AssignSt (id, e) ->
          fprintf p "@[<hv 2>state(%s) :=@ %a@]" (extern_atom id)
                                                           print_expr e
      | Obc.Ifte (e, s1, s2) ->
          fprintf p
            "@[<v 2>if (%a) {@ %a@;<0 -2>} else {@ %a@;<0 -2>}@]"
            print_expr e
            print_stmt s1
            print_stmt s2
      | Obc.Comp (s1, s2) ->
          fprintf p "%a;@ %a" print_stmt s1 print_stmt s2
      | Obc.Call ([], cls, i, m, es) ->
          fprintf p
            "@[<hv 2>%s@,(@[<hov 0>%s@]).%s@,(@[<hov 0>%a@])@]"
            (extern_atom cls)
            (extern_atom i)
            (extern_atom m)
            print_expr_list (true, es)
      | Obc.Call (rs, cls, i, m, es) ->
          fprintf p
            "@[<hv 2>%a :=@ %s@,(@[<hov 0>%s@]).%s@,(@[<hov 0>%a@])@]"
            (print_list print_ident) rs
            (extern_atom cls)
            (extern_atom i)
            (extern_atom m)
            print_expr_list (true, es)
      | Obc.Skip ->
          fprintf p "skip"

    let print_decls =
      print_list
        (fun p (id, ty) ->
          fprintf p "%a@ : %a" print_ident id PrintOps.print_typ ty)

    let print_method p { Obc.m_name = name;
                         Obc.m_in   = inputs;
                         Obc.m_vars = locals;
                         Obc.m_out  = outputs;
                         Obc.m_body = body } =
     fprintf p "@[<v>";
     fprintf p "@[<hov>";
     fprintf p "@[<h>%a@,(@[<hov 0>%a@])@]@ " print_ident name print_decls inputs;
     if outputs <> [] then
       fprintf p "@[<h>returns (@[<hov 0>%a@])@]@ " print_decls outputs;
    if locals <> [] then
       fprintf p "@[<h>var @[<hov 0>%a@] in@]@ " print_decls locals;
     fprintf p "@]@;{@[<v 1>@;";
     print_stmt p body;
     fprintf p "@;<0 -2>}@]@]"

    let rec print_methods p first ms =
      match ms with
      | [] -> ()
      | m :: ms ->
          (if first
           then fprintf p "@[<h 2>%a@]" print_method m
           else fprintf p "@;@;@[<h 2>%a@]" print_method m);
          print_methods p false ms

    let print_class p { Obc.c_name    = name;
                        Obc.c_mems    = mems;
                        Obc.c_objs    = objs;
                        Obc.c_methods = meths } =
      fprintf p "@[<v 2>@[<h>class@ %a {@]@;" print_ident name;
      print_decl_list
        (fun p (id, cls) ->
          fprintf p "@[<h>instance %a@ : %a@]" print_ident id print_ident cls)
        p objs;
      print_decl_list
        (fun p (id, ty) ->
          fprintf p "@[<h>memory %a@ : %a@]" print_ident id PrintOps.print_typ ty)
        p mems;
      fprintf p "@;";
      print_methods p true meths;
      fprintf p "@;<0 -2>}@]"

    let print_program p prog =
      fprintf p "@[<v 0>";
      List.iter (fun cls->fprintf p "%a@;@;" print_class cls) prog;
      fprintf p "@]@."
  end

