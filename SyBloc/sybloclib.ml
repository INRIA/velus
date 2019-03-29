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
    | EqNext of ident * clock * lexp
    | EqReset of ident * clock * ident
    | EqCall of ident * idents * clock * bool * ident * lexps

    type block = {
      b_name   : ident;
      b_in     : (ident * (typ * clock)) list;
      b_vars   : (ident * (typ * clock)) list;
      b_lasts  : (ident * (const * clock)) list;
      b_blocks : (ident * ident) list;
      b_out    : (ident * (typ * clock)) list;
      b_eqs    : equation list }

    type program = block list
  end

module PrintFun
    (CE: Coreexprlib.SYNTAX)
    (SB: SYNTAX with type clock = CE.clock
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
    val print_equation : formatter -> SB.equation -> unit
    val print_block    : Format.formatter -> SB.block -> unit
    val print_program   : Format.formatter -> SB.program -> unit
  end
  =
  struct

    include Coreexprlib.PrintFun (CE) (PrintOps)

    let print_clock_decl p ck =
      match ck with
      | CE.Cbase -> ()
      | CE.Con (ck', x, b) ->
        (* if !print_fullclocks *)
(* then *)
        fprintf p " :: @[<hov 3>%a@]" print_clock ck
        (* else fprintf p " when%s %s"
         *     (if b then "" else " not")
         *     (extern_atom x) *)

    let print_decl p (id, (ty, ck)) =
      fprintf p "%s@ : %a%a"
        (extern_atom id)
        PrintOps.print_typ ty
        print_clock_decl ck

    let print_decl_list = print_list print_decl

    let print_last p (id, (c0, ck)) =
      fprintf p "%s@ = %a:%a"
        (extern_atom id)
        PrintOps.print_const c0
        print_clock_decl ck

    let print_last_list = print_list print_last

    let print_block p (id, f) =
      fprintf p "<%s>@ : %s"
        (extern_atom id)
        (extern_atom f)

    let print_block_list = print_list print_block

    let print_ident p i = fprintf p "%s" (extern_atom i)

    let print_multiple_results p xs =
      match xs with
      | [x] -> print_ident p x
      | xs  -> fprintf p "(%a)" (print_list print_ident) xs

    let rec print_equation p eq =
      match eq with
      | SB.EqDef (x, ck, e) ->
        fprintf p "@[<hov 2>%s =@ %a;@]"
          (extern_atom x) print_cexpr e
      | SB.EqNext (x, ck, e) ->
        fprintf p "@[<hov 2>next@ %s =@ %a;@]"
          (extern_atom x) print_lexpr e
      | SB.EqReset (s, ck, f) ->
          fprintf p "@[<hov 2>reset<%s>(%s)@ every@ %a;@]"
            (extern_atom s)
            (extern_atom f)
            print_clock ck
      | SB.EqCall (s, xs, ck, _, f, es) ->
        fprintf p "@[<hov 2><next %s>@ %a =@ %s<%s>(@[<hv 0>%a@]);@]"
          (extern_atom s)
          print_multiple_results xs
          (extern_atom f)
          (extern_atom s)
          (print_list print_lexpr) es

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

    let print_block p { SB.b_name   = name;
                        SB.b_in     = inputs;
                        SB.b_out    = outputs;
                        SB.b_vars   = locals;
                        SB.b_lasts  = lasts;
                        SB.b_blocks = blocks;
                        SB.b_eqs    = eqs } =
      fprintf p "@[<v>";
      fprintf p "@[<hov 0>";
      fprintf p "@[<h>block %s<>(%a)@]@;"
        (extern_atom name)
        print_decl_list inputs;
      fprintf p "@[<h>returns (%a)@]@;"
        print_decl_list outputs;
      fprintf p "@]@;";
      if List.length locals > 0 then
        fprintf p "@[<h>var @[<hov 4>%a@];@]@;"
          print_decl_list locals;
      if List.length lasts > 0 then
        fprintf p "@[<h>init @[<hov 4>%a@];@]@;"
          print_last_list lasts;
      if List.length blocks > 0 then
        fprintf p "@[<h>sub @[<hov 4>%a@];@]@;"
          print_block_list blocks;
      fprintf p "@[<v 2>let@;%a@;<0 -2>@]" print_equations (List.rev eqs);
      fprintf p "tel@]"

    let print_program p prog =
      fprintf p "@[<v 0>";
      List.iter (fprintf p "@;%a@;" print_block) prog;
      fprintf p "@]@."
  end

module SchedulerFun (SB: SYNTAX) :
  sig
    val schedule : Common.ident -> SB.equation list -> BinNums.positive list
  end
  =
  struct

    let schedule f eqs =
      let next_pos = let np = ref Coq_xH in
        fun () -> let r = !np in (np := Pos.succ !np; r)
      in
      List.rev (List.map (fun _ -> next_pos ()) eqs)
    (* let debug = false
     *
     * (\** Status information for each equation *\)
     *
     * module EqSet = Set.Make (struct
     *   type t = int
     *   let compare = (Pervasives.compare : t -> t -> int)
     * end)
     *
     * (\* For each equation, we track
     *    - id: index in the array of equations;
     *    - clock_path: sequence of variable identifiers ordered from
     *          most rapid to least rapid and ignoring values, i.e.,
     *          both "base when a when b" and "base whenot a whenot b"
     *          become "[a; b]", reflecting the nesting of if/then/elses
     *          to be produced in the target code;
     *    - schedule: "None" when unscheduled and "Some i" when scheduled
     *          as the ith equation (from 1);
     *    - depends_on: these equations must be scheduled beforehand;
     *    - required_by: these equations must be scheduled afterward. *\)
     *
     * type eq_status = {
     *   eq_id               : int;
     *   clock_path          : int list;
     *   mutable schedule    : positive option;
     *   mutable depends_on  : EqSet.t;
     *   mutable required_by : EqSet.t;
     * }
     *
     * let drop_dep x eq =
     *   eq.depends_on <- EqSet.remove x eq.depends_on
     *
     * let rec resolve_variable e =
     *   let open NL in
     *   match e with
     *   | Evar (x, _) -> Some x
     *   | Ewhen (e, _, _) -> resolve_variable e
     *   | Econst _ | Eunop _ | Ebinop _ -> None
     *
     * let grouping_clock_of_eq =
     *   let open NL in
     *   function
     *   (\* Push merges/iftes down a level to improve grouping *\)
     *   | EqDef (_, ck, Emerge (y, _, _)) -> Con (ck, y, true)
     *   | EqDef (_, ck, Eite (e, _, _)) -> begin
     *       match resolve_variable e with
     *       | None -> ck
     *       | Some x -> Con (ck, x, true)
     *       end
     *   (\* Standard cases *\)
     *   | EqDef (_, ck, _)
     *   | EqApp (_, ck, _, _)
     *   | EqFby (_, ck, _, _) -> ck
     *
     * let rec clock_path acc = function
     *   | NL.Cbase -> acc
     *   | NL.Con (ck, x, _) -> clock_path (int_of_positive x :: acc) ck
     *
     * let new_eq_status i eq =
     * {
     *   eq_id = i;
     *   schedule = None;
     *   depends_on  = EqSet.empty;
     *   required_by = EqSet.empty;
     *   clock_path = clock_path [] (grouping_clock_of_eq eq)
     * }
     *
     * (\** Add dependencies between equations *\)
     *
     * let add_clock_deps add_dep =
     *   let rec go = function
     *     | NL.Cbase -> ()
     *     | NL.Con (ck, x, _) -> (add_dep x; go ck)
     *   in
     *   go
     *
     * let add_exp_deps add_dep =
     *   let rec go = function
     *     | NL.Econst _ -> ()
     *     | NL.Evar (x, _) -> add_dep x
     *     | NL.Ewhen (e, x, _) -> (add_dep x; go e)
     *     | NL.Eunop (_, e, _) -> go e
     *     | NL.Ebinop (_, e1, e2, _) -> (go e1; go e2)
     *   in go
     *
     * let add_cexp_deps add_dep =
     *   let go_exp = add_exp_deps add_dep in
     *   let rec go = function
     *     | NL.Emerge (x, ce1, ce2) -> (add_dep x; go ce1; go ce2)
     *     | NL.Eite (e, ce1, ce2) -> (go_exp e; go ce1; go ce2)
     *     | NL.Eexp e -> go_exp e
     *   in go
     *
     * let add_dependencies add_dep = function
     *   | NL.EqDef (_, ck, ce) ->
     *       add_clock_deps add_dep ck;
     *       add_cexp_deps add_dep ce
     *   | NL.EqApp (_, ck, _ , es) ->
     *       add_clock_deps add_dep ck;
     *       List.iter (add_exp_deps add_dep) es
     *   | NL.EqFby (x, ck, _ , e) ->
     *       add_clock_deps add_dep ck;
     *       add_exp_deps (fun y -> if y <> x then add_dep y) e
     *
     * (\** Map variable identifiers to equation ids *\)
     *
     * module PM = PositiveMap
     *
     * (\* Each variable identifier is associated with a pair giving the
     *    equation (id) that defines it and whether that equation is a fby. *\)
     * let variable_map_from_eq (m, i) = function
     *   | NL.EqDef (x, _, _) ->
     *       (PM.add x (i, false) m, i + 1)
     *   | NL.EqApp (xs, _, _, _) ->
     *       (List.fold_left (fun m x -> PM.add x (i, false) m) m xs, i + 1)
     *   | NL.EqFby (x, _, _, _) ->
     *       (PM.add x (i, true) m, i + 1)
     *
     * let variable_map eqs =
     *   fst (List.fold_left variable_map_from_eq (PM.empty, 0) eqs)
     *
     * (\** Queuing by clock *\)
     *
     * (\* We keep a queue of equations that can be scheduled (i.e., their
     *    dependencies have already been scheduled). The queue is organized
     *    as a tree according to the equation clock paths. Descending a level
     *    in the tree introduces an "if" the target code, while ascending
     *    closes one. The idea is to group equations according to their clock
     *    paths and schedule as many as possible without changing level.
     *
     *    When there are no more equations to schedule in a sub-branch, the
     *    branch is dropped completely. This may generate more "garbage" than
     *    necessary. An alternative would be to add a mutable boolean field
     *    at each level indicating whether a subbranch contains equations
     *    to schedule. *\)
     *
     * type clock_tree = {
     *   mutable ready_eqs : eq_status list;
     *   mutable subclocks : (int * clock_tree) list
     * }
     *
     * let empty_clock_tree () = {
     *   ready_eqs = [];
     *   subclocks = []
     * }
     *
     * let pp_print_eq_lhs nleqs fmt i =
     *   let open Format in
     *   match List.nth nleqs i with
     *   | NL.EqDef (x, _, _) ->
     *       pp_print_string fmt (extern_atom x)
     *   | NL.EqApp (xs, _, _ , _) ->
     *       fprintf fmt "{@[<hov 2>%a@]}"
     *         (pp_print_list ~pp_sep:pp_print_space pp_print_string)
     *         (List.map extern_atom xs)
     *   | NL.EqFby (x, _, _ , _) ->
     *       pp_print_string fmt (extern_atom x)
     *
     * let pp_eq_status f eq =
     *   Format.fprintf f "%d" eq.eq_id
     *
     * let pp_print_comma f () =
     *   Format.fprintf f ",@ "
     *
     * let rec pp_branch f (ck, ct) =
     *   Format.fprintf f "%d:%a" ck pp_clock_tree ct
     *
     * and pp_clock_tree f { ready_eqs; subclocks } =
     *   Format.fprintf f "{@[<hv 2>";
     *   if ready_eqs <> [] then begin
     *     Format.fprintf f "@[<hov 2>eqs=%a@]"
     *       (Format.pp_print_list ~pp_sep:pp_print_space pp_eq_status) ready_eqs;
     *     if subclocks <> [] then Format.fprintf f ",@ "
     *   end;
     *   if subclocks <> [] then
     *     Format.fprintf f "subs=%a"
     *       (Format.pp_print_list ~pp_sep:pp_print_comma pp_branch) subclocks;
     *   Format.fprintf f "@]}"
     *
     * (\* If an equation is ready to schedule, place it in the queue according
     *    to its clock path. *\)
     * let enqueue_eq ct ({ depends_on; clock_path } as eq) =
     *   let rec seek ct = function
     *     | [] -> ct.ready_eqs <- eq :: ct.ready_eqs
     *     | x::ck ->
     *         match List.assoc x ct.subclocks with
     *         | ct' -> seek ct' ck
     *         | exception Not_found -> begin
     *             let ct' = empty_clock_tree () in
     *             ct.subclocks <- (x, ct') :: ct.subclocks;
     *             seek ct' ck
     *           end
     *   in
     *   if EqSet.is_empty depends_on then seek ct clock_path
     *
     * let schedule_from_queue nleqs ct_t eqs =
     *   let enqueue = enqueue_eq ct_t in
     *
     *   let check_dep x y =
     *     let eq_y = eqs.(y) in
     *     drop_dep x eq_y;
     *     enqueue eq_y in
     *
     *   (\* Track the scheduled position. *\)
     *   let next_pos = let np = ref Coq_xH in
     *                  fun () -> let r = !np in (np := Pos.succ !np; r) in
     *
     *   (\* Schedule an equation and update any that depend on it. *\)
     *   let enschedule ({eq_id; required_by} as eq) =
     *     if debug then Format.eprintf "@;schedule %d (%a)"
     *                     eq_id (pp_print_eq_lhs nleqs) eq_id;
     *     eq.schedule <- Some (next_pos ());
     *     EqSet.iter (check_dep eq_id) required_by in
     *
     *   let pp_clock_int f x =
     *     Format.fprintf f "%d (%s)" x (extern_atom (positive_of_int x))
     *   in
     *
     *   (\* Iteratively schedule at the same level of the clock tree whenever
     *      possible (since it does not introduce new "if"s and it maximizes
     *      the chances of scheduling more equations later), otherwise descend
     *      into the tree if possible, and only ascend when absolutely
     *      necessary (since we would have to close and open "if"s to return
     *      to the same level). *\)
     *   let rec continue ct =
     *     if debug then Format.eprintf "@;@[<v 2>{ %a" pp_clock_tree ct_t;
     *     match ct.ready_eqs with
     *     | [] -> begin
     *         match ct.subclocks with
     *         | [] -> if debug then Format.eprintf " }@;<0 -2>@]"
     *         | (x, ct')::_ ->
     *             (\* descend into clock tree / introduce an if *\)
     *             if debug then Format.eprintf "@;down into %a" pp_clock_int x;
     *             continue ct';
     *             if debug then Format.eprintf "@;back from %a" pp_clock_int x;
     *             (\* upon return we know that the subtree is done *\)
     *             ct.subclocks <- List.remove_assoc x ct.subclocks;
     *             (\* the "if" is closed, so reprocess the current level *\)
     *             if debug then Format.eprintf " }@;<0 -2>@]";
     *             continue ct
     *         end
     *     | ready ->
     *         (\* clear the list, ready to accept new additions *\)
     *         ct.ready_eqs <- [];
     *         List.iter enschedule ready;
     *         if debug then Format.eprintf " }@;<0 -2>@]";
     *         continue ct
     *   in
     *   continue ct_t
     *
     * (\** Find and print dependency loops *\)
     *
     * (\* This code exists only to print an explanatory error message when
     *    scheduling gets stuck. *\)
     *
     * (\* Use local exceptions in OCaml >= 4.04... *\)
     * exception Found of int
     * exception Done of int list
     *
     * let find_unscheduled i { schedule } =
     *   match schedule with
     *   | None -> raise (Found i)
     *   | Some _ -> ()
     *
     * let find_next_none eqs deps =
     *   try
     *     EqSet.iter
     *       (fun i -> if eqs.(i).schedule = None then raise (Found i)) deps;
     *     None
     *   with Found i -> Some i
     *
     * let find_dep_loop eqs =
     *   try
     *     Array.iteri find_unscheduled eqs; []
     *   with Found start ->
     *     let rec track i =
     *       if EqSet.is_empty eqs.(i).depends_on
     *       then (eqs.(i).schedule <- Some Coq_xH; [i])
     *       else begin
     *         match find_next_none eqs eqs.(i).depends_on with
     *         | None -> failwith "find_dep_loop failed"
     *         | Some i' ->
     *             eqs.(i).depends_on <- EqSet.empty;
     *             let r = track i' in
     *             if eqs.(i).schedule <> None
     *             then (\* cycle found; ignore any prefix leading to it. *\)
     *                  raise (Done (i::r))
     *             else (\* "rewind" along cycle *\) i::r
     *       end
     *     in
     *     try track start
     *     with Done r -> r
     *
     * let print_loop nleqs fmt eqs =
     *   Format.pp_print_list
     *     ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ -> ")
     *     (pp_print_eq_lhs nleqs)
     *     fmt
     *     (find_dep_loop eqs)
     *
     * (\** Scheduling algorithm *\)
     *
     * exception IncompleteSchedule
     *
     * let extract_schedule { schedule } res =
     *   match schedule with
     *   | None -> raise IncompleteSchedule
     *   | Some s -> s::res
     *
     * let schedule f nleqs =
     *   let eqs = Array.of_list (List.mapi new_eq_status nleqs) in
     *
     *   if debug then begin
     *     Format.eprintf "@[<v>--scheduling %s" (extern_atom f);
     *     let show_eq i eq =
     *       Format.eprintf "@;%d: %a" i (pp_print_eq_lhs nleqs) i
     *     in
     *     Format.eprintf "@;@[<v 2>equations =";
     *     Array.iteri show_eq eqs;
     *     Format.eprintf "@]"
     *   end;
     *
     *   let varmap = variable_map nleqs in
     *   let add xi yi =
     *     eqs.(xi).depends_on  <- EqSet.add yi eqs.(xi).depends_on;
     *     eqs.(yi).required_by <- EqSet.add xi eqs.(yi).required_by
     *   in
     *   let add_dep xi y =
     *     match PM.find y varmap with
     *     | None -> ()  (\* ignore inputs *\)
     *     | Some (yi, false) -> add xi yi
     *     | Some (yi, true)  -> add yi xi (\* reverse-deps for fby *\)
     *   in
     *   ignore (List.fold_left
     *             (fun n e -> add_dependencies (add_dep n) e; n + 1) 0 nleqs);
     *
     *   let ct = empty_clock_tree () in
     *   Array.iter (enqueue_eq ct) eqs;
     *   schedule_from_queue nleqs ct eqs;
     *   if debug then Format.eprintf "@;--done@]@.";
     *   try
     *     Array.fold_right extract_schedule eqs []
     *   with IncompleteSchedule ->
     *     Format.eprintf
     *       "@[<hov 2>node %s@ has@ a@ dependency@ loop:@\n@[<hov 0>%a@].@]@."
     *       (extern_atom f) (print_loop nleqs) eqs;
     *     [] *)

  end
