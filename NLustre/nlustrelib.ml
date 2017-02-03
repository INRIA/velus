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
    type typ
    type const
    type unop
    type binop

    type clock =
    | Cbase
    | Con of clock * ident * bool

    type lexp =
    | Econst of const
    | Evar of ident * typ
    | Ewhen of lexp * ident * bool
    | Eunop of unop * lexp * typ
    | Ebinop of binop * lexp * lexp * typ

    type lexps = lexp list

    type cexp =
    | Emerge of ident * cexp * cexp
    | Eite of lexp * cexp * cexp
    | Eexp of lexp

    type equation =
    | EqDef of ident * clock * cexp
    | EqApp of idents * clock * ident * lexps
    | EqFby of ident * clock * const * lexp

    type node = {
      n_name : ident;
      n_in   : (ident * (typ * clock)) list;
      n_out  : (ident * (typ * clock)) list;
      n_vars : (ident * (typ * clock)) list;
      n_eqs  : equation list }

    type global = node list
  end

module PrintFun (NL: SYNTAX)
                (PrintOps : PRINT_OPS with type typ   = NL.typ
                                       and type const = NL.const
                                       and type unop  = NL.unop
                                       and type binop = NL.binop) :
  sig
    val print_fullclocks : bool ref
    val print_lexpr    : formatter -> NL.lexp -> unit
    val print_cexpr    : formatter -> NL.cexp -> unit
    val print_equation : formatter -> NL.equation -> unit
    val print_node     : Format.formatter -> NL.node -> unit
    val print_global   : Format.formatter -> NL.global -> unit
  end
  =
  struct
    let print_fullclocks = ref false

    let lprecedence = function
      | NL.Econst _ -> (16, NA)
      | NL.Evar _   -> (16, NA)
      | NL.Ewhen _  -> (12, LtoR) (* precedence of +/- *)
      | NL.Eunop  (op, _, _)    -> PrintOps.prec_unop op
      | NL.Ebinop (op, _, _, _) -> PrintOps.prec_binop op

    let cprecedence = function
      | NL.Emerge _ -> (5, LtoR) (* precedence of lor - 1 *)
      | NL.Eite _   -> (5, LtoR)
      | NL.Eexp _   -> (5, LtoR)

    let rec lexpr p (prec, e) =
      let (prec', assoc) = lprecedence e in
      let (prec1, prec2) =
        if assoc = LtoR
        then (prec', prec' + 1)
        else (prec' + 1, prec') in
      if prec' < prec
      then fprintf p "@[<hov 2>("
      else fprintf p "@[<hov 2>";
      begin match e with
      | NL.Econst c ->
          PrintOps.print_const p c
      | NL.Evar (id, _) ->
          fprintf p "%s" (extern_atom id)
      | NL.Ewhen (e, x, v) ->
          if v
          then fprintf p "%a when %s" lexpr (prec', e) (extern_atom x)
          else fprintf p "%a when not %s" lexpr (prec', e) (extern_atom x)
      | NL.Eunop  (op, e, ty) ->
          PrintOps.print_unop p op ty lexpr (prec', e)
      | NL.Ebinop (op, e1, e2, ty) ->
          PrintOps.print_binop p op ty lexpr (prec1, e1) (prec2, e2)
      end;
      if prec' < prec then fprintf p ")@]" else fprintf p "@]"

    let print_lexpr p e = lexpr p (0, e)

    let rec print_lexpr_list p (first, rl) =
      match rl with
      | [] -> ()
      | r :: rl ->
          if not first then fprintf p ",@ ";
          lexpr p (2, r);
          print_lexpr_list p (false, rl)

    let rec cexpr p (prec, e) =
      let (prec', assoc) = cprecedence e in
      if prec' < prec
      then fprintf p "@[<hov 2>("
      else fprintf p "@[<hov 2>";
      begin match e with
      | NL.Emerge (id, ce1, ce2) ->
          fprintf p "@[<hv 6>merge %s@ %a@ %a@]"
            (extern_atom id) cexpr (16, ce1) cexpr (16, ce2)
      | NL.Eite (e, ce1, ce2) ->
          fprintf p "@[<hv 0>if %a@ then %a@ else %a@]"
            lexpr (prec', e) cexpr (prec', ce1) cexpr (prec', ce2)
      | NL.Eexp e ->
          lexpr p (prec' + 1, e)
      end;
      if prec' < prec then fprintf p ")@]" else fprintf p "@]"

    let print_cexpr p e = cexpr p (0, e)

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

    let rec print_clock p ck =
      match ck with
      | NL.Cbase -> fprintf p "."
      | NL.Con (ck', x, b) ->
          fprintf p "%a %s %s"
            print_clock ck'
            (if b then "on" else "onot")
            (extern_atom x)

    let print_clock_decl p ck =
      match ck with
      | NL.Cbase -> ()
      | NL.Con (ck', x, b) ->
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

    let print_decl_list = print_list print_decl

    let print_ident p i = fprintf p "%s" (extern_atom i)

    let print_multiple_results p xs =
      match xs with
      | [x] -> print_ident p x
      | xs  -> fprintf p "(%a)" (print_list print_ident) xs

    let rec print_equation p eq =
      match eq with
      | NL.EqDef (x, ck, e) ->
          fprintf p "@[<hov 2>%s =@ %a;@]"
            (extern_atom x) print_cexpr e
      | NL.EqApp (xs, ck, f, es) ->
          fprintf p "@[<hov 2>%a =@ %s(@[<hv 0>%a@]);@]"
            print_multiple_results xs
            (extern_atom f)
            (print_list print_lexpr) es
      | NL.EqFby (x, ck, v0, e) ->
          fprintf p "@[<hov 2>%s =@ %a fby@ %a;@]"
            (extern_atom x) PrintOps.print_const v0 print_lexpr e

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
          print_decl_list inputs;
        fprintf p "@[<h>returns (%a)@]@;"
          print_decl_list outputs;
      fprintf p "@]@;";
      if List.length locals > 0 then
        fprintf p "@[<h>var @[<hov 4>%a@];@]@;"
          print_decl_list locals;
      fprintf p "@[<v 2>let@;%a@;<0 -2>@]" print_equations (List.rev eqs);
      fprintf p "tel@]"

    let print_global p prog =
      fprintf p "@[<v 0>";
      List.iter (fprintf p "@;%a@;" print_node) prog;
      fprintf p "@]@."
  end

module SchedulerFun (NL: SYNTAX) :
  sig
    val schedule : Common.ident -> NL.equation list -> BinNums.positive list
  end
  =
  struct
    (** Status information for each equation *)

    module EqSet = Set.Make (struct
      type t = int
      let compare = (Pervasives.compare : t -> t -> int)
    end)

    (* For each equation, we track
       - id: index in the array of equations;
       - clock_path: sequence of variable identifiers ordered from
             most rapid to least rapid and ignoring values, i.e.,
             both "base when a when b" and "base whenot a whenot b"
             become "[a; b]", reflecting the nesting of if/then/elses
             to be produced in the target code;
       - schedule: "None" when unscheduled and "Some i" when scheduled
             as the ith equation (from 1);
       - depends_on: these equations must be scheduled beforehand;
       - required_by: these equations must be scheduled afterward. *)

    type eq_status = {
      eq_id               : int;
      clock_path          : int list;
      mutable schedule    : positive option;
      mutable depends_on  : EqSet.t;
      mutable required_by : EqSet.t;
    }

    let drop_dep x eq =
      eq.depends_on <- EqSet.remove x eq.depends_on

    let grouping_clock_of_eq =
      let open NL in
      function
      (* Push merges/iftes down a level to improve grouping *)
      | EqDef (_, ck, Eite (Evar (y, _), _, _))
      | EqDef (_, ck, Emerge (y, _, _)) -> Con (ck, y, true)
      (* Standard cases *)
      | EqDef (_, ck, _)
      | EqApp (_, ck, _, _)
      | EqFby (_, ck, _, _) -> ck

    let rec clock_path = function
      | NL.Cbase -> []
      | NL.Con (ck, x, _) -> int_of_positive x :: clock_path ck

    let new_eq_status i eq =
    {
      eq_id = i;
      schedule = None;
      depends_on  = EqSet.empty;
      required_by = EqSet.empty;
      clock_path = clock_path (grouping_clock_of_eq eq)
    }

    (** Add dependencies between equations *)

    let add_clock_deps add_dep =
      let rec go = function
        | NL.Cbase -> ()
        | NL.Con (ck, x, _) -> (add_dep x; go ck)
      in
      go

    let add_exp_deps add_dep =
      let rec go = function
        | NL.Econst _ -> ()
        | NL.Evar (x, _) -> add_dep x
        | NL.Ewhen (e, x, _) -> (add_dep x; go e)
        | NL.Eunop (_, e, _) -> go e
        | NL.Ebinop (_, e1, e2, _) -> (go e1; go e2)
      in go

    let add_cexp_deps add_dep =
      let go_exp = add_exp_deps add_dep in 
      let rec go = function
        | NL.Emerge (x, ce1, ce2) -> (add_dep x; go ce1; go ce2)
        | NL.Eite (e, ce1, ce2) -> (go_exp e; go ce1; go ce2)
        | NL.Eexp e -> go_exp e
      in go

    let add_dependencies add_dep = function
      | NL.EqDef (_, ck, ce) ->
          add_clock_deps add_dep ck;
          add_cexp_deps add_dep ce
      | NL.EqApp (_, ck, _ , es) ->
          add_clock_deps add_dep ck;
          List.iter (add_exp_deps add_dep) es
      | NL.EqFby (_, ck, _ , e) ->
          add_clock_deps add_dep ck;
          add_exp_deps add_dep e

    (** Map variable identifiers to equation ids *)

    module PM = PositiveMap

    (* Each variable identifier is associated with a pair giving the
       equation (id) that defines it and whether that equation is a fby. *)
    let variable_map_from_eq (m, i) = function
      | NL.EqDef (x, _, _) ->
          (PM.add x (i, false) m, i + 1)
      | NL.EqApp (xs, _, _, _) ->
          (List.fold_left (fun m x -> PM.add x (i, false) m) m xs, i + 1)
      | NL.EqFby (x, _, _, _) ->
          (PM.add x (i, true) m, i + 1)

    let variable_map eqs =
      fst (List.fold_left variable_map_from_eq (PM.empty, 0) eqs)

    (** Queuing by clock *)

    (* We keep a queue of equations that can be scheduled (i.e., their
       dependencies have already been scheduled). The queue is organized
       as a tree according to the equation clock paths. Descending a level
       in the tree introduces an "if" the target code, while ascending
       closes one. The idea is to group equations according to their clock
       paths and schedule as many as possible without changing level.

       When there are no more equations to schedule in a sub-branch, the
       branch is dropped completely. This may generate more "garbage" than
       necessary. An alternative would be to add a mutable boolean field
       at each level indicating whether a subbranch contains equations
       to schedule. *)

    type clock_tree = {
      mutable ready_eqs : eq_status list;
      mutable subclocks : (int * clock_tree) list
    }

    let empty_clock_tree () = {
      ready_eqs = [];
      subclocks = []
    }

    (* If an equation is ready to schedule, place it in the queue according
       to its clock path. *)
    let enqueue_eq ct ({ depends_on; clock_path } as eq) =
      let rec seek ct = function
        | [] -> ct.ready_eqs <- eq :: ct.ready_eqs
        | x::ck ->
            match List.assoc x ct.subclocks with
            | ct' -> seek ct' ck
            | exception Not_found -> begin
                let ct' = empty_clock_tree () in
                ct.subclocks <- (x, ct') :: ct.subclocks;
                seek ct' ck
              end
      in
      if EqSet.is_empty depends_on then seek ct clock_path

    let schedule_from_queue ct eqs =
      let enqueue = enqueue_eq ct in

      let check_dep x y =
        let eq_y = eqs.(y) in
        drop_dep x eq_y;
        enqueue eq_y in

      (* Track the scheduled position. *)
      let next_pos = let np = ref Coq_xH in
                     fun () -> let r = !np in (np := Pos.succ !np; r) in

      (* Schedule an equation and update any that depend on it. *)
      let enschedule ({eq_id; required_by} as eq) =
        eq.schedule <- Some (next_pos ());
        EqSet.iter (check_dep eq_id) required_by in

      (* Iteratively schedule at the same level of the clock tree whenever
         possible (since it does not introduce new "if"s and it maximizes
         the chances of scheduling more equations later), otherwise descend
         into the tree if possible, and only ascend when absolutely
         necessary (since we would have to close and open "if"s to return
         to the same level). *)
      let rec continue ct =
        match ct.ready_eqs with
        | [] -> begin
            match ct.subclocks with
            | [] -> ()
            | (x, ct')::_ ->
                (* descend into clock tree / introduce an if *)
                continue ct';
                (* upon return we know that the subtree is done *)
                ct.subclocks <- List.remove_assoc x ct.subclocks;
                (* the "if" is closed, so reprocess the current level *)
                continue ct
            end
        | ready ->
            (* clear the list, ready to accept new additions *)
            ct.ready_eqs <- [];
            List.iter enschedule ready;
            continue ct
      in
      continue ct

    (** Find and print dependency loops *)

    (* This code exists only to print an explanatory error message when
       scheduling gets stuck. *)

    (* Use local exceptions in OCaml >= 4.04... *)
    exception Found of int
    exception Done of int list

    let find_unscheduled i { schedule } =
      match schedule with
      | None -> raise (Found i)
      | Some _ -> ()

    let find_next_none eqs deps =
      try
        EqSet.iter
          (fun i -> if eqs.(i).schedule = None then raise (Found i)) deps;
        None
      with Found i -> Some i

    let find_dep_loop eqs =
      try
        Array.iteri find_unscheduled eqs; []
      with Found start ->
        let rec track i =
          if EqSet.is_empty eqs.(i).depends_on
          then (eqs.(i).schedule <- Some Coq_xH; [i])
          else begin
            match find_next_none eqs eqs.(i).depends_on with
            | None -> failwith "find_dep_loop failed"
            | Some i' ->
                eqs.(i).depends_on <- EqSet.empty;
                let r = track i' in
                if eqs.(i).schedule <> None
                then (* cycle found; ignore any prefix leading to it. *)
                     raise (Done (i::r))
                else (* "rewind" along cycle *) i::r
          end
        in
        try track start
        with Done r -> r

    let print_eq_lhs nleqs fmt i =
      let open Format in
      match List.nth nleqs i with
      | NL.EqDef (x, _, _) ->
          pp_print_string fmt (extern_atom x)
      | NL.EqApp (xs, _, _ , _) ->
          fprintf fmt "{@[<hov 2>%a@]}"
            (pp_print_list ~pp_sep:pp_print_space pp_print_string)
            (List.map extern_atom xs)
      | NL.EqFby (x, _, _ , _) ->
          pp_print_string fmt (extern_atom x)

    let print_loop nleqs fmt eqs =
      Format.pp_print_list
        ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ -> ")
        (print_eq_lhs nleqs)
        fmt
        (find_dep_loop eqs)

    (** Scheduling algorithm *)

    exception IncompleteSchedule

    let extract_schedule { schedule } res =
      match schedule with
      | None -> raise IncompleteSchedule
      | Some s -> s::res

    let schedule f nleqs =
      let eqs = Array.of_list (List.mapi new_eq_status nleqs) in

      let varmap = variable_map nleqs in
      let add xi yi =
        eqs.(xi).depends_on  <- EqSet.add yi eqs.(xi).depends_on;
        eqs.(yi).required_by <- EqSet.add xi eqs.(yi).required_by
      in
      let add_dep xi y =
        match PM.find y varmap with
        | None -> ()  (* ignore inputs *)
        | Some (yi, false) -> add xi yi
        | Some (yi, true)  -> add yi xi (* reverse-deps for fby *)
      in
      ignore (List.fold_left
                (fun n e -> add_dependencies (add_dep n) e; n + 1) 0 nleqs);

      let ct = empty_clock_tree () in
      Array.iter (enqueue_eq ct) eqs;
      schedule_from_queue ct eqs;
      try
        Array.fold_right extract_schedule eqs []
      with IncompleteSchedule ->
        Format.eprintf
          "@[<hov 2>node %s@ has@ a@ dependency@ loop:@\n@[<hov 0>%a@].@]@."
          (extern_atom f) (print_loop nleqs) eqs;
        []

  end

