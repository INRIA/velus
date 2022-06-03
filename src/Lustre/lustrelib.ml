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
    | Efby   of exp list * exp list * ann list
    | Earrow of exp list * exp list * ann list
    | Ewhen  of exp list * ident * enumtag * lann
    | Emerge of (ident * typ) * (enumtag * exp list) list * lann
    | Ecase  of exp * (enumtag * exp list) list * exp list option * lann
    | Eapp   of ident * exp list * exp list * ann list

    type equation = idents * exp list

    type transition = exp * (enumtag * bool)

    type auto_type = Weak | Strong

    type 'a scope =
    | Scope of (ident * (((typ * clock) * ident) * (exp * ident) option)) list * (ident * ident) list * 'a

    type block =
    | Beq of equation
    | Breset of block list * exp
    | Bswitch of exp * (enumtag * (block list) scope) list
    | Bauto of auto_type * clock * ((exp * enumtag) list * enumtag) * (enumtag * (transition list * (block list * transition list) scope)) list
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
      nodes: node list
    }

    val typeof : exp -> typ list
  end

module PrintFun
    (PrintOps: PRINT_OPS)
    (L: SYNTAX with type typ     = PrintOps.typ
                and type cconst  = PrintOps.cconst
                and type unop    = PrintOps.unop
                and type binop   = PrintOps.binop
                and type enumtag = PrintOps.enumtag) :
  sig
    val print_fullclocks : bool ref
    val print_appclocks  : bool ref

    val print_exp        : (ident * L.typ) list -> formatter -> L.exp -> unit
    val print_equation   : (ident * L.typ) list -> formatter -> L.equation -> unit
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

    let print_comma_list p =
      pp_print_list ~pp_sep:(fun p () -> fprintf p ",@;") p

    let print_semicol_list p =
      pp_print_list ~pp_sep:(fun p () -> fprintf p ";@;") p

    let print_semicol_list_as name px p xs =
    if xs = [] then () else
      fprintf p "@[<h>%s @[<hov 4>%a@];@]@;"
        name
        (print_semicol_list px) xs

    let find_type tenv tx =
      List.assoc tx tenv

    let rec exp tenv prec p e =
      let exp = exp tenv and exp_list = exp_list tenv
      and exp_enclosed_list = exp_enclosed_list tenv and exp_arg_list = exp_arg_list tenv in
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
      | L.Efby (e0s, es, _) ->
        fprintf p "%a fby@ %a" (exp_list prec1) e0s (exp_list prec2) es
      | L.Earrow (e0s, es, _) ->
        fprintf p "%a ->@ %a" (exp_list prec1) e0s (exp_list prec2) es
      | L.Ewhen (e, x, c, _) ->
        fprintf p "%a when (%a=%a)"
          (exp_list prec') e
          print_ident x
          PrintOps.print_enumtag (c, find_type tenv x)
      | L.Emerge ((id, ty), es, _) ->
        fprintf p "@[<v>merge %a%a@]"
          print_ident id
          (PrintOps.print_branches exp_enclosed_list)
          (List.map (fun (i, ce) -> ((fun p -> PrintOps.print_enumtag p (i, ty)), Some ce)) es, None)
      | L.Ecase (e, es, d, _) ->
        let ty = List.hd (L.typeof e) in
        fprintf p "@[<v>case %a of%a@]"
          (exp 16) e
          (PrintOps.print_branches exp_enclosed_list)
          (List.map (fun (i, ce) -> ((fun p -> PrintOps.print_enumtag p (i, ty)), Some ce)) es, d)
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

    and exp_list tenv prec p es =
      match es with
      | [e] -> exp tenv prec p e
      | _   -> exp_arg_list tenv p es

    and exp_arg_list tenv p es =
      fprintf p "(@[<hv 0>%a@])"
        (print_comma_list (exp tenv 0)) es

    and exp_enclosed_list tenv p es =
      fprintf p "@[<hv 0>%a@]"
        (print_comma_list (exp tenv 0)) es

    let print_exp tenv = exp tenv 0

    let print_clock_decl p ck =
      match ck with
      | L.Cbase -> ()
      | L.Con (ck', x, (ty, c)) ->
        if !print_fullclocks
        then fprintf p " :: @[<hov 3>%a@]" print_clock ck
        else fprintf p " when (%a=%a)"
            print_ident x
            PrintOps.print_enumtag (c, ty)

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

    let rec print_equation tenv p (xs, es) =
      fprintf p "@[<hov 2>%a = %a@]"
        print_pattern xs (exp_list tenv 0) es

    let print_initially tenv p (ini, oth) =
      let rec aux p = function
        | [] -> fprintf p "otherwise %d"
                  (PrintOps.int_of_enumtag oth)
        | (e, t)::inis ->
          fprintf p "if %a then %d;@;%a"
            (print_exp tenv) e
            (PrintOps.int_of_enumtag t)
            aux inis
      in if ini = [] then fprintf p "%d" (PrintOps.int_of_enumtag oth)
      else aux p ini

    let print_transition tenv p (e, (k, r)) =
      fprintf p "@[<h> %a %s %d@]"
        (print_exp tenv) e
        (if r then "then" else "continue")
        (PrintOps.int_of_enumtag k)

    let print_bar_list p =
      pp_print_list ~pp_sep:(fun p () -> fprintf p "@;|") p

    let print_until_list tenv p xs =
      if xs = [] then () else
        fprintf p "@;@[<h>until@[<v -1>%a@]@]@;"
          (print_bar_list (print_transition tenv)) xs

    let print_unless_list tenv p xs =
      if xs = [] then () else
        fprintf p "@;@[<h>unless@[<v -1>%a@]@]@;"
          (print_bar_list (print_transition tenv)) xs

    let idty_of_locs =
      List.map (fun (x, (((ty, _), _), _)) -> (x, ty))

    let rec print_block tenv p = function
      | L.Beq eq -> (print_equation tenv) p eq
      | L.Breset (blks, er) ->
        fprintf p "@[<v 2>reset@;%a@;<0 -2>@]every %a"
          (print_blocks tenv) blks
          (print_exp tenv) er
      | L.Bswitch (ec, brs) ->
        let ty = List.hd (L.typeof ec) in
        fprintf p "@[<v 0>@[<h 2>switch@ %a@]@ %a@]@ end"
          (print_exp tenv) ec
          (pp_print_list (fun p blks -> print_switch_branch tenv p (blks, ty))) brs
      | L.Bauto (_, _, ini, states) ->
        fprintf p "@[<v 2>automaton@;initially %a@;%a@;end@]"
          (print_initially tenv) ini
          (pp_print_list (print_state tenv)) states
      | L.Blocal (Scope (locals, _, blks)) ->
        fprintf p "do %a@[<v 2>in@ %a@;<0 -2>@]done"
          (print_semicol_list_as "var" print_local_decl) locals
          (print_blocks (idty_of_locs locals@tenv)) blks

    and print_blocks tenv p blks =
      print_semicol_list (print_block tenv) p blks

    and print_switch_branch tenv p ((e, Scope (locs, _, blks)), ty) =
      fprintf p "@[<v 2>| %a %ado@ %a@]"
        PrintOps.print_enumtag (e, ty)
        (print_semicol_list_as "var" print_local_decl) locs
        (print_blocks (idty_of_locs locs@tenv)) blks

    and print_state tenv p (e, (unl, Scope (locs, _, (blks, unt)))) =
      let tenv = idty_of_locs locs@tenv in
      fprintf p "@[<v 2>state %d %ado@ %a%a%a@]"
        (PrintOps.int_of_enumtag e)
        (print_semicol_list_as "var" print_local_decl) locs
        (print_semicol_list (print_block tenv)) blks
        (print_until_list tenv) unt
        (print_unless_list tenv) unl

    let print_top_block tenv p = function
      | L.Blocal (Scope (locals, _, blks)) ->
        fprintf p "%a@[<v 2>let@ %a@;<0 -2>@]tel"
          (print_semicol_list_as "var" print_local_decl) locals
          (print_blocks (idty_of_locs locals@tenv)) blks
      | blk -> print_block tenv p blk

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
        (print_top_block (List.map (fun (x, ((ty, _), _)) -> (x, ty)) (inputs@outputs))) blk

    let print_global p prog =
      fprintf p "@[<v 0>";
      List.iter (fprintf p "%a@;@;" PrintOps.print_typ_decl) (List.rev prog.L.types);
      List.iter (fprintf p "%a@;@;" print_node) (List.rev prog.L.nodes);
      fprintf p "@]@."
  end
