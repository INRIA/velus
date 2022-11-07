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

open Datatypes
open BinNums
open BinPos
open FMapPositive

type ident = Common.ident
type idents = ident list

let extern_atom = Camlcoq.extern_atom

module type SYNTAX =
  sig
    type typ
    type ctype
    type cconst
    type unop
    type binop
    type enumtag

    type clock =
    | Cbase
    | Con of clock * ident * (typ * enumtag)

    type ann = typ * clock
    type lann = typ list * clock

    type exp =
    | Econst of cconst
    | Eenum of enumtag * typ
    | Evar   of ident * ann
    | Elast  of ident * ann
    | Eunop  of unop * exp * ann
    | Ebinop of binop * exp * exp * ann
    | Eextcall of ident * exp list * (ctype * clock)
    | Efby   of exp list * exp list * ann list
    | Earrow of exp list * exp list * ann list
    | Ewhen  of exp list * (ident * typ) * enumtag * lann
    | Emerge of (ident * typ) * (enumtag * exp list) list * lann
    | Ecase  of exp * (enumtag * exp list) list * exp list option * lann
    | Eapp   of ident * exp list * exp list * ann list

    type equation = idents * exp list

    type transition = exp * (enumtag * bool)

    type auto_type = Weak | Strong

    type 'a scope =
    | Scope of (ident * (((typ * clock) * ident) * (exp * ident) option)) list * 'a

    type 'a branch =
    | Branch of (ident * ident) list * 'a

    type block =
    | Beq of equation
    | Breset of block list * exp
    | Bswitch of exp * (enumtag * (block list) branch) list
    | Bauto of auto_type * clock * ((exp * enumtag) list * enumtag) *
               ((enumtag * ident) * (transition list * (block list * transition list) scope) branch) list
    | Blocal of (block list) scope

    type node = {
          n_name     : ident;
          n_hasstate : bool;
          n_in       : (ident * ((typ * clock) * ident)) list;
          n_out      : (ident * ((typ * clock) * ident)) list;
          n_block    : block;
        }

    type global = {
      types: typ list;
      externs: (ident * (ctype list * ctype)) list;
      nodes: node list
    }

    val typeof : exp -> typ list
  end

module PrintFun
    (PrintOps: PRINT_OPS)
    (L: SYNTAX with type typ     = PrintOps.typ
                and type ctype   = PrintOps.ctype
                and type cconst  = PrintOps.cconst
                and type unop    = PrintOps.unop
                and type binop   = PrintOps.binop
                and type enumtag = PrintOps.enumtag) :
  sig
    val print_fullclocks : bool ref
    val print_appclocks  : bool ref

    val print_exp        : formatter -> L.exp -> unit
    val print_equation   : formatter -> L.equation -> unit
    val print_node       : formatter -> L.node -> unit
    val print_global     : formatter -> L.global -> unit
  end
  =
  struct
    let print_fullclocks = ref false
    let print_appclocks  = ref false

    let precedence = function
      | L.Econst _ -> (16, NA)
      | L.Eenum _ -> (16, NA)
      | L.Evar _   -> (16, NA)
      | L.Elast _  -> (16, NA)
      | L.Eunop  (op, _, _)    -> PrintOps.prec_unop op
      | L.Ebinop (op, _, _, _) -> PrintOps.prec_binop op
      | L.Eextcall _ -> (4, NA)
      | L.Efby _   -> (14, RtoL) (* higher than * / % *)
      | L.Earrow _ -> (14, RtoL)
      | L.Ewhen _  -> (12, LtoR) (* precedence of + - *)
      | L.Emerge _ -> ( 5, LtoR) (* precedence of lor - 1 *)
      | L.Ecase _   -> ( 5, LtoR)
      | L.Eapp _   -> ( 4, NA)

    let print_ident p i = pp_print_string p (extern_atom i)

    let rec print_clock p ck =
      match ck with
      | L.Cbase -> fprintf p "."
      | L.Con (ck', x, (ty, c)) ->
        fprintf p "%a on (%a=%a)"
          print_clock ck'
          print_ident x
          PrintOps.print_enumtag (c, ty)

    let print_cks =
      pp_print_list ~pp_sep:(fun p () -> fprintf p " *@ ") print_clock

    let print_sep_list print =
      pp_print_list ~pp_sep:(fun p () -> fprintf p "@ ") print

    let print_comma_list p =
      pp_print_list ~pp_sep:(fun p () -> fprintf p ",@;") p

    let print_semicol_list p =
      pp_print_list ~pp_sep:(fun p () -> fprintf p ";@;") p

    let print_semicol_list_as name px p xs =
    if xs = [] then () else
      fprintf p "@[<h>%s @[<hov 4>%a@];@]@;"
        name
        (print_semicol_list px) xs

    let rec exp prec p e =
      let (prec', assoc) = precedence e in
      let (prec1, prec2) =
        if assoc = LtoR
        then (prec', prec' + 1)
        else (prec' + 1, prec') in
      if prec' < prec
      then fprintf p "@[<hov 2>("
      else fprintf p "@[<hov 2>";
      begin match e with
      | L.Econst c ->
        PrintOps.print_cconst p c
      | L.Eenum (c, ty) ->
        PrintOps.print_enumtag p (c, ty)
      | L.Evar (id, _) ->
        print_ident p id
      | L.Elast (id, _) ->
        fprintf p "last %a" print_ident id
      | L.Eunop  (op, e, (ty, _)) ->
        PrintOps.print_unop p op ty (exp prec') e
      | L.Ebinop (op, e1, e2, (ty, _)) ->
        PrintOps.print_binop p op ty (exp prec1) e1 (exp prec2) e2
      | L.Eextcall (f, es, _) ->
        fprintf p "external %a(%a)"
          print_ident f
          (exp_list prec2) es
      | L.Efby (e0s, es, _) ->
        fprintf p "%a fby@ %a" (exp_list prec1) e0s (exp_list prec2) es
      | L.Earrow (e0s, es, _) ->
        fprintf p "%a ->@ %a" (exp_list prec1) e0s (exp_list prec2) es
      | L.Ewhen (e, (x, tx), c, _) ->
        fprintf p "%a when %a(%a)"
          print_ident x
          (exp_list prec') e
          PrintOps.print_enumtag (c, tx)
      | L.Emerge ((id, ty), es, _) ->
        fprintf p "@[<v>merge %a @[<v>%a@]@]"
          print_ident id
          branches (ty, es, None)
      | L.Ecase (e, es, d, _) ->
        let ty = List.hd (L.typeof e) in
        fprintf p "@[<v>case %a of @[<v>%a@]@]"
          (exp 16) e
          branches (ty, es, d)
      | L.Eapp (f, es, [], anns) ->
        if !print_appclocks
        then fprintf p "%a@[<v 1>%a@ (* @[<hov>%a@] *)@]"
            print_ident f
            exp_arg_list es
            print_cks (List.map snd anns)
        else fprintf p "%a%a"
            print_ident f
            exp_arg_list es
      | L.Eapp (f, es, er, anns) ->
        if !print_appclocks
        then fprintf p "(restart@ %a@ every@ %a)@[<v 1>%a@ (* @[<hov>%a@] *)@]"
            print_ident f
            (exp_list prec') er
            exp_arg_list es
            print_cks (List.map snd anns)
        else fprintf p "(restart@ %a@ every@ %a)%a"
            print_ident f
            (exp_list prec') er
            exp_arg_list es
      end;
      if prec' < prec then fprintf p ")@]" else fprintf p "@]"

    and exp_list prec p es =
      match es with
      | [e] -> exp prec p e
      | _   -> exp_arg_list p es

    and exp_arg_list p es =
      fprintf p "(@[<hv 0>%a@])"
        (print_comma_list (exp 0)) es

    and exp_enclosed_list p es =
      fprintf p "@[<hv 0>%a@]"
        (print_comma_list (exp 0)) es

    and branches p (ty, brs, d) =
      print_sep_list (fun p (k, es) ->
          fprintf p "(%a => %a)"
            PrintOps.print_enumtag (k, ty)
            exp_enclosed_list es) p brs;
      match d with
      | None -> ()
      | Some es ->
        fprintf p "@ (_ => %a)"
          exp_enclosed_list es

    let print_exp = exp 0

    let print_clock_decl p ck =
      match ck with
      | L.Cbase -> ()
      | L.Con (ck', x, (ty, c)) ->
        if !print_fullclocks
        then fprintf p " :: @[<hov 3>%a@]" print_clock ck
        else fprintf p " when %a(%a)"
            PrintOps.print_enumtag (c, ty)
            print_ident x

    let print_decl p (id, ((ty, ck), _)) =
      fprintf p "%a@ : %a%a"
        print_ident id
        PrintOps.print_typ ty
        print_clock_decl ck

    let print_local_decl p (id, (((ty, ck), cx), o)) =
      match o with
      | Some (e, _) ->
        fprintf p "%a@ : %a%a"
          print_ident id
          PrintOps.print_typ ty
          print_clock_decl ck
      | None -> print_decl p (id, ((ty, ck), cx))

    let print_decl_list = print_semicol_list print_decl

    let print_pattern p xs =
      match xs with
      | [x] -> print_ident p x
      | xs  -> fprintf p "(@[<hv 0>%a@])"
                 (print_comma_list print_ident) xs

    let rec print_equation p (xs, es) =
      fprintf p "@[<hov 2>%a = %a@]"
        print_pattern xs (exp_list 0) es

    let print_state_tag p (c, ty) =
      print_ident p (List.nth ty (PrintOps.int_of_enumtag c))

    let print_initially ty p (ini, oth) =
      let rec aux p = function
        | [] -> fprintf p "otherwise %a"
                  print_state_tag (oth, ty)
        | (e, t)::inis ->
          fprintf p "if %a then %a;@;%a"
            print_exp e
            print_state_tag (t, ty)
            aux inis
      in if ini = [] then fprintf p "%a" print_state_tag (oth, ty)
      else aux p ini

    let print_transition ty p (e, (k, r)) =
      fprintf p "@[<h> %a %s %a@]"
        print_exp e
        (if r then "then" else "continue")
        print_state_tag (k, ty)

    let print_bar_list p =
      pp_print_list ~pp_sep:(fun p () -> fprintf p "@;|") p

    let print_until_list ty p xs =
      if xs = [] then () else
        fprintf p "@;@[<h>until@[<v -1>%a@]@]@;"
          (print_bar_list (print_transition ty)) xs

    let print_unless_list ty p xs =
      if xs = [] then () else
        fprintf p "@;@[<h>unless@[<v -1>%a@]@]@;"
          (print_bar_list (print_transition ty)) xs

    let rec print_block p = function
      | L.Beq eq -> print_equation p eq
      | L.Breset (blks, er) ->
        fprintf p "@[<v 2>reset@;%a@;<0 -2>@]every %a"
          print_blocks blks
          print_exp er
      | L.Bswitch (ec, brs) ->
        let ty = List.hd (L.typeof ec) in
        fprintf p "@[<v 0>@[<h 2>switch@ %a@]@ %a@]@ end"
          print_exp ec
          (pp_print_list (fun p blks -> print_switch_branch p (blks, ty))) brs
      | L.Bauto (_, _, ini, states) ->
        let ty = List.map (fun ((_, c), _) -> c) states in
        fprintf p "@[<v 2>automaton@;initially %a@;%a@;end@]"
          (print_initially ty) ini
          (pp_print_list (print_state ty)) states
      | L.Blocal (Scope (locals, blks)) ->
        fprintf p "do %a@[<v 2>in@ %a@;<0 -2>@]done"
          (print_semicol_list_as "var" print_local_decl) locals
          print_blocks blks

    and print_blocks p blks =
      print_semicol_list print_block p blks

    and print_switch_branch p ((e, Branch (_, blks)), ty) =
      fprintf p "@[<v 2>| %a do@ %a@]"
        PrintOps.print_enumtag (e, ty)
        print_blocks blks

    and print_state ty p ((_, e), Branch (_, (unl, Scope (locs, (blks, unt))))) =
      fprintf p "@[<v 2>state %a %ado@ %a%a%a@]"
        print_ident e
        (print_semicol_list_as "var" print_local_decl) locs
        (print_semicol_list print_block) blks
        (print_until_list ty) unt
        (print_unless_list ty) unl

    let print_top_block p = function
      | L.Blocal (Scope (locals, blks)) ->
        fprintf p "%a@[<v 2>let@ %a@;<0 -2>@]tel"
          (print_semicol_list_as "var" print_local_decl) locals
          print_blocks blks
      | blk -> print_block p blk

    let print_node p { L.n_name     = name;
                       L.n_hasstate = hasstate;
                       L.n_in       = inputs;
                       L.n_out      = outputs;
                       L.n_block    = blk } =
      fprintf p "@[<v>\
                 @[<hov 0>\
                 @[<h>%s %a (%a)@]@;\
                 @[<h>returns (%a)@]@;\
                 @]@;\
                 %a@]"
        (if hasstate then "node" else "fun")
        print_ident name
        print_decl_list inputs
        print_decl_list outputs
        print_top_block blk

    let print_extern_decl p (f, (tyins, tyout)) =
      fprintf p "external %a(%a) returns %a"
        print_ident f
        (print_comma_list PrintOps.print_ctype) tyins
        PrintOps.print_ctype tyout

    let print_global p prog =
      fprintf p "@[<v 0>";
      List.iter (fprintf p "%a@;@;" PrintOps.print_typ_decl) (List.rev prog.L.types);
      List.iter (fprintf p "%a@;@;" print_extern_decl) (List.rev prog.L.externs);
      List.iter (fprintf p "%a@;@;" print_node) (List.rev prog.L.nodes);
      fprintf p "@]@."
  end
