(* *********************************************************************)
(*                                                                     *)
(*                 The Vélus verified Lustre compiler                  *)
(*                                                                     *)
(*             (c) 2019 Inria Paris (see the AUTHORS file)             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

open Format
open Veluscommon

type ident = ClockDefs.ident
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
    | Valid of ident * typ

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

module SyncFun (Obc: SYNTAX)
               (TypeFormats : TYPE_FORMATS with type typ = Obc.typ) :
 sig
   (* Takes the name of a global unsigned long, 'reaction', that tracks
      the number of reactions, and an Obc function, and generates a function
      that
        1. if 'reaction' > 0 then prints the output values.
        2. reads the inputs values.
        3. increments 'reaction'.
   *)
   (* val make : ident -> Obc.coq_method -> Clight.coq_function *)
   val print : Format.formatter -> Obc.coq_method -> unit
 end
 =
 struct

   let v_reactions = "num_reactions"

   let var_name f id =
     pp_print_string f (Camlcoq.extern_atom (Ident.Ids.glob_id id))

   let external_variable f (id, ty) =
     fprintf f "@[<hov 2>extern volatile %s %a;@]"
       (TypeFormats.type_decl ty)
       var_name id

   let print_output f (id, ty) =
     fprintf f "@[<hov 2>printf(\"%s=%s\\n\", %a);@]"
       (Camlcoq.extern_atom id)
       (TypeFormats.type_printf ty)
       var_name id

   let scan_input f (id, ty) =
     fprintf f "@[<hov 2>printf(\"%s? \");@]" (extern_atom id);
     fprintf f "@[<hov 2>scanf(\"%s\", &%a);@]"
       (TypeFormats.type_scanf ty)
       var_name id

   let print f {Obc.m_name; Obc.m_in; Obc.m_out} =
     let open Format in
     let print_body f =
       fprintf f "static unsigned int %s = 0;@,@," v_reactions;
       fprintf f "@[<hov 2>if (%s) {@]@," v_reactions;
       fprintf f "  @[<v 0>%a@]@," (pp_print_list print_output) m_out;
       fprintf f "@[<h>}@]@,@,";
       fprintf f "@[<hov 2>printf(\"--reaction %%d\\n\", %s);@]@,@," v_reactions;
       pp_print_list scan_input f m_in;
       fprintf f "@,@,@[<hov 2>%s += 1;@]" v_reactions
     in
     pp_open_vbox f 0;
     fprintf f "#include <stdio.h>@,@,";
     pp_print_list external_variable f m_in;
     pp_print_cut f ();
     pp_print_list external_variable f m_out;
     pp_print_cut f ();
     pp_print_cut f ();
     fprintf f "void sync()@,{@[<v 2>@,%t@]@,}@]@." print_body;
     pp_close_box f ()

   (* Working with strings is too tedious in the Clight AST, so
      we just provide a simple printer for now. *)
   (*
   let rec sequence ss =
     let open Clight in
     match ss with
     | []    -> Sskip
     | [s]   -> s
     | s::ss -> Ssequence (s, sequence ss)

   let tlong = Ctypes.(Tlong (Unsigned, noattr))
   let long_const x =
     Clight.Econst_long (Integers.Int.repr (Veluscommon.z_of_int x), tlong)

   let printf_output _ = Clight.Sskip
   let scanf_input _ = Clight.Sskip
   let print_reaction _ _ = Clight.Sskip

   let make v_init Obc.({m_name; m_in; m_out}) =
     let e_init = Clight.Evar (v_init, tlong) in
     Clight.({
         fn_return = Ctypes.Tvoid;
         fn_callconv = AST.cc_default;
         fn_params = [];
         fn_vars = [];
         fn_temps = [];
         fn_body =
           sequence [
             Sifthenelse (e_init,
                          sequence (List.map printf_output m_out), Sskip);
             sequence
              ((print_reaction v_init m_name
                 :: List.map scanf_input m_in)
              @ [ Sassign (e_init,
                           Ebinop (Cop.Oadd, e_init, long_const 1, tlong))])
           ]

       })
    *)

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
      | Obc.Valid _ -> (16, NA)

    let rec expr prec p e =
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
      | Obc.Unop (op, e, ty) ->
          PrintOps.print_unop p op ty (expr prec') e
      | Obc.Binop (op, e1, e2, ty) ->
          PrintOps.print_binop p op ty (expr prec1) e1 (expr prec2) e2
      | Obc.Valid (id, _) ->
          fprintf p "[%s]" (extern_atom id)
      end;
      if prec' < prec then fprintf p ")@]" else fprintf p "@]"

    let print_expr = expr 0

    let print_comma_list print =
      pp_print_list ~pp_sep:(fun p () -> fprintf p ",@ ") print

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
            "@[<v 2>if %a {@ %a@;<0 -2>} else {@ %a@;<0 -2>}@]"
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
            (print_comma_list print_expr) es
      | Obc.Call (rs, cls, i, m, es) ->
          fprintf p
            "@[<hv 2>%a :=@ @[<hv 2>%s@,(@[<hov 0>%s@]).%s@,(@[<hov 0>%a@])@]@]"
            (print_comma_list print_ident) rs
            (extern_atom cls)
            (extern_atom i)
            (extern_atom m)
            (print_comma_list print_expr) es
      | Obc.Skip ->
          fprintf p "skip"

    let print_decls =
      print_comma_list
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
     fprintf p "@]";
     if locals <> [] then
       fprintf p "@;@[<h>var @[<hov 0>%a@]@]@;" print_decls locals;
     fprintf p "{@;<0 2>@[<v>";
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
          fprintf p "@[<h>register %a@ : %a@]" print_ident id PrintOps.print_typ ty)
        p mems;
      fprintf p "@;";
      print_methods p true meths;
      fprintf p "@;<0 -2>}@]"

    let print_program p prog =
      fprintf p "@[<v 0>";
      List.iter (fprintf p "%a@;@;" print_class) prog;
      fprintf p "@]@."
  end
