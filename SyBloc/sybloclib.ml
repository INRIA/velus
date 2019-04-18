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

type ident = ClockDefs.ident
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
    val print_equation   : formatter -> SB.equation -> unit
    val print_block      : Format.formatter -> SB.block -> unit
    val print_program    : Format.formatter -> SB.program -> unit
    val print_fullclocks : bool ref
  end
  =
  struct

    include Coreexprlib.PrintFun (CE) (PrintOps)

    let print_last p (id, (c0, ck)) =
      fprintf p "%a@ = %a:%a"
        print_ident id
        PrintOps.print_const c0
        print_clock_decl ck

    let print_block p (id, f) =
      fprintf p "<%a>@ : %a"
        print_ident id
        print_ident f

    let rec print_equation p eq =
      match eq with
      | SB.EqDef (x, ck, e) ->
        fprintf p "@[<hov 2>%a =@ %a@]"
          print_ident x
          print_cexp e
      | SB.EqNext (x, ck, e) ->
        fprintf p "@[<hov 2>next@ %a =@ %a@]"
          print_ident x
          print_lexp e
      | SB.EqReset (s, ck, f) ->
        fprintf p "@[<hov 2>reset(%a<%a>)@ every@ (%a)@]"
            print_ident f
            print_ident s
            print_clock ck
      | SB.EqCall (s, xs, ck, _, f, es) ->
        fprintf p "@[<hov 2>%a =@ %a<%a>(@[<hv 0>%a@])@]"
          print_pattern xs
          print_ident f
          print_ident s
          (print_comma_list print_lexp) es

    let print_equations p =
      pp_print_list ~pp_sep:pp_force_newline print_equation p

    let print_block p { SB.b_name   = name;
                        SB.b_in     = inputs;
                        SB.b_out    = outputs;
                        SB.b_vars   = locals;
                        SB.b_lasts  = lasts;
                        SB.b_blocks = blocks;
                        SB.b_eqs    = eqs } =
      fprintf p "@[<v>\
                 @[<hov 0>\
                 @[<h>block %a (%a)@]@;\
                 @[<h>returns (%a)@]@;\
                 @]@;\
                 %a%a%a\
                 @[<v 2>let@;%a@;<0 -2>@]\
                 tel@]"
        print_ident name
        print_decl_list inputs
        print_decl_list outputs
        (print_comma_list_as "var" print_decl) locals
        (print_comma_list_as "init" print_last) lasts
        (print_comma_list_as "sub" print_block) blocks
        print_equations (List.rev eqs)

    let print_program p prog =
      fprintf p "@[<v 0>%a@]@."
        (pp_print_list ~pp_sep:(fun p () -> fprintf p "@;@;") print_block)
        (List.rev prog)
  end

module SchedulerFun
    (CE: Coreexprlib.SYNTAX)
    (SB: SYNTAX with type clock = CE.clock
                 and type typ   = CE.typ
                 and type const = CE.const
                 and type lexp  = CE.lexp
                 and type cexp  = CE.cexp
                 and type lexps = CE.lexps) :
  sig
    val schedule : ident -> SB.equation list -> BinNums.positive list
  end
  =
  struct

    open CE
    open SB

    let debug = false
    let eprint =
      let print = if debug then Format.fprintf else Format.ifprintf in
      fun x -> print Format.err_formatter x

    (** Status information for each equation *)

    module Int = struct
      type t = int
      let compare = (Pervasives.compare : t -> t -> int)
    end

    module EqSet = Set.Make (Int)

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

    let rec resolve_variable e =
      match e with
      | Evar (x, _) -> Some x
      | Ewhen (e, _, _) -> resolve_variable e
      | Econst _ | Eunop _ | Ebinop _ -> None

    let grouping_clock_of_eq =
      function
      (* Push merges/iftes down a level to improve grouping *)
      | EqDef (_, ck, Emerge (y, _, _)) -> Con (ck, y, true)
      | EqDef (_, ck, Eite (e, _, _)) -> begin
          match resolve_variable e with
          | None -> ck
          | Some x -> Con (ck, x, true)
          end
      (* Standard cases *)
      | EqDef (_, ck, _)
      | EqNext (_, ck, _)
      | EqReset (_, ck, _)
      | EqCall (_, _, ck, _, _, _) -> ck

    let rec clock_path acc = let open CE in function
      | Cbase -> acc
      | Con (ck, x, _) -> clock_path (int_of_positive x :: acc) ck

    let new_eq_status i eq = {
      eq_id = i;
      schedule = None;
      depends_on  = EqSet.empty;
      required_by = EqSet.empty;
      clock_path = clock_path [] (grouping_clock_of_eq eq)
    }

    (** Add dependencies between equations *)

    let add_clock_deps add_dep =
      let rec go = function
        | Cbase -> ()
        | Con (ck, x, _) -> add_dep x; go ck
      in
      go

    let add_exp_deps add_dep =
      let rec go = function
        | Econst _ -> ()
        | Evar (x, _) -> add_dep x
        | Ewhen (e, x, _) -> add_dep x; go e
        | Eunop (_, e, _) -> go e
        | Ebinop (_, e1, e2, _) -> go e1; go e2
      in go

    let add_cexp_deps add_dep =
      let go_exp = add_exp_deps add_dep in
      let rec go = function
        | Emerge (x, ce1, ce2) -> add_dep x; go ce1; go ce2
        | Eite (e, ce1, ce2) -> go_exp e; go ce1; go ce2
        | Eexp e -> go_exp e
      in go

    let add_dependencies add_dep_var add_dep_state = function
      | EqDef (_, ck, ce) ->
        add_clock_deps add_dep_var ck;
        add_cexp_deps add_dep_var ce
      | EqNext (x, ck, e) ->
        add_clock_deps add_dep_var ck;
        add_exp_deps (fun y -> if y <> x then add_dep_var y) e
      | EqReset (_, ck, _) ->
        add_clock_deps add_dep_var ck
      | EqCall (s, _, ck, _, _, es) ->
        add_clock_deps add_dep_var ck;
        List.iter (add_exp_deps add_dep_var) es;
        add_dep_state s

    (** Map variable identifiers to equation ids *)

    module PM = PositiveMap

    (* Each variable identifier is associated with a pair giving the
       equation (id) that defines it and whether that equation is a fby. *)
    let variable_state_maps_from_eq i (vars, states) = function
      | EqDef (x, _, _) ->
        PM.add x (i, false) vars, states
      | EqNext (x, _, _) ->
        PM.add x (i, true) vars, states
      | EqReset (s, _, _) ->
        vars, PM.add s i states
      | EqCall (_, xs, _, _, _, _) ->
        List.fold_left (fun m x -> PM.add x (i, false) m) vars xs, states

    let fold_left_i f acc l =
      List.fold_left (fun (acc, i) x -> f i acc x, i + 1) (acc, 0) l
      |> fst

    let variable_state_maps eqs =
      fold_left_i variable_state_maps_from_eq (PM.empty, PM.empty) eqs

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

    module IM = Map.Make (Int)

    type clock_tree = {
      mutable ready_eqs : eq_status list;
      mutable subclocks : clock_tree IM.t
    }

    let empty_clock_tree () = {
      ready_eqs = [];
      subclocks = IM.empty
    }

    let pp_print_arrow f () = Format.fprintf f "@ ->@ "

    let pp_clock_int f x = Format.fprintf f "%d (%s)" x (extern_atom (positive_of_int x))

    let pp_clock_path f = function
      | [] -> pp_print_string f "."
      | cp -> pp_print_list ~pp_sep:pp_print_arrow pp_clock_int f cp

    let pp_print_eq_lhs nleqs fmt i =
      let open Format in
      match List.nth nleqs i with
      | EqDef (x, _, _) ->
        pp_print_string fmt (extern_atom x)
      | EqNext (x, _, _) ->
        pp_print_string fmt (extern_atom x)
      | EqReset (_, _, _) ->
        pp_print_string fmt "_"
      | EqCall (_, xs, _, _, _, _) ->
        fprintf fmt "{@[<hov 2>%a@]}"
          (pp_print_list ~pp_sep:pp_print_space pp_print_string)
          (List.map extern_atom xs)

    let pp_eq_status f eq = Format.fprintf f "%d" eq.eq_id

    let pp_print_comma f () = Format.fprintf f ",@ "

    let rec pp_branch f (ck, ct) =
      Format.fprintf f "%a:%a" pp_clock_int ck pp_clock_tree ct

    and pp_clock_tree f { ready_eqs; subclocks } =
      let open Format in
      fprintf f "{@[<hv 2>";
      if ready_eqs <> [] then begin
        fprintf f "@[<hov 2>eqs=%a@]"
          (pp_print_list ~pp_sep:pp_print_space pp_eq_status) ready_eqs;
        if not (IM.is_empty subclocks) then fprintf f ",@ "
      end;
      if not (IM.is_empty subclocks) then
        fprintf f "subs=%a"
          (pp_print_list ~pp_sep:pp_print_comma pp_branch) (IM.bindings subclocks);
      fprintf f "@]}"


    (* If an equation is ready to schedule, place it in the queue according
       to its clock path. *)
    let enqueue_eq ct ({ depends_on; clock_path } as eq) =
      let rec seek ct = function
        | [] -> ct.ready_eqs <- eq :: ct.ready_eqs
        | x :: ck ->
          match IM.find x ct.subclocks with
          | ct' -> seek ct' ck
          | exception Not_found -> begin
              let ct' = empty_clock_tree () in
              ct.subclocks <- IM.add x ct' ct.subclocks;
              seek ct' ck
            end
      in
      if EqSet.is_empty depends_on then seek ct clock_path

    let schedule_from_queue sbeqs ct_t eqs =
      let enqueue = enqueue_eq ct_t in

      let check_dep x y =
        let eq_y = eqs.(y) in
        drop_dep x eq_y;
        enqueue eq_y
      in

      (* Track the scheduled position. *)
      let next_pos =
        let np = ref Coq_xH in
        fun () -> let r = !np in (np := Pos.succ !np; r)
      in

      (* Schedule an equation and update any that depend on it. *)
      let enschedule ({eq_id; required_by} as eq) =
        eprint "@;schedule %d (%a)" eq_id (pp_print_eq_lhs sbeqs) eq_id;
        eq.schedule <- Some (next_pos ());
        EqSet.iter (check_dep eq_id) required_by
      in

      (* Iteratively schedule at the same level of the clock tree whenever
         possible (since it does not introduce new "if"s and it maximizes
         the chances of scheduling more equations later), otherwise descend
         into the tree if possible, and only ascend when absolutely
         necessary (since we would have to close and open "if"s to return
         to the same level). *)
      let rec continue ct =
        eprint "@;@[<v 2>{ %a" pp_clock_tree ct_t;
        match ct.ready_eqs with
        | [] -> begin
            match IM.choose ct.subclocks with
            | exception Not_found -> eprint " }@;<0 -2>@]"
            | (x, ct') ->
                (* descend into clock tree / introduce an if *)
                eprint "@;down into %a" pp_clock_int x;
                continue ct';
                eprint "@;back from %a" pp_clock_int x;
                (* upon return we know that the subtree is done *)
                ct.subclocks <- IM.remove x ct.subclocks;
                (* the "if" is closed, so reprocess the current level *)
                eprint " }@;<0 -2>@]";
                continue ct
            end
        | ready ->
            (* clear the list, ready to accept new additions *)
            ct.ready_eqs <- [];
            List.iter enschedule ready;
            eprint " }@;<0 -2>@]";
            continue ct
      in
      continue ct_t

    module M = Map.Make(Int)

    (** Find and print dependency loops *)

    (* This code exists only to print an explanatory error message when
       scheduling gets stuck. *)

    (* Use local exceptions in OCaml >= 4.04... *)
    exception Found of int
    exception Done of int list

    let find_unscheduled i { schedule } =
      if schedule = None then raise (Found i)

    let find_next_none eqs deps =
      try
        EqSet.iter (fun i -> find_unscheduled i eqs.(i)) deps;
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
                     raise (Done (i :: r))
                else (* "rewind" along cycle *) i :: r
          end
        in
        try track start
        with Done r -> r

    let print_loop nleqs fmt eqs =
      Format.pp_print_list
        ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ -> ")
        (pp_print_eq_lhs nleqs)
        fmt
        (find_dep_loop eqs)

    (** Scheduling algorithm *)

    exception IncompleteSchedule

    let extract_schedule { schedule } res =
      match schedule with
      | None -> raise IncompleteSchedule
      | Some s -> s :: res

    let show_eq eqs i eq =
      eprint "@;%d: %a :: %a" i (pp_print_eq_lhs eqs) i pp_clock_path eq.clock_path

    let schedule f sbeqs =
      let eqs = Array.of_list (List.mapi new_eq_status sbeqs) in

      eprint "@[<v>--scheduling %s" (extern_atom f);
      eprint "@;@[<v 2>equations =";
      Array.iteri (show_eq sbeqs) eqs;
      eprint "@]";

      let varmap, statemap = variable_state_maps sbeqs in

      let add xi yi =
        eqs.(xi).depends_on  <- EqSet.add yi eqs.(xi).depends_on;
        eqs.(yi).required_by <- EqSet.add xi eqs.(yi).required_by
      in
      let add_dep_var xi y =
        match PM.find y varmap with
        | None -> ()  (* ignore inputs *)
        | Some (yi, false) -> add xi yi
        | Some (yi, true)  -> add yi xi (* reverse-deps for fby *)
      in
      let add_dep_state xi y =
        match PM.find y statemap with
        | None -> ()             (* ignore simple calls *)
        | Some yi -> add xi yi
      in
      List.iteri (fun n -> add_dependencies (add_dep_var n) (add_dep_state n)) sbeqs;

      let ct = empty_clock_tree () in
      Array.iter (enqueue_eq ct) eqs;
      schedule_from_queue sbeqs ct eqs;
      eprint "@;--done@]@.";
      try
        Array.fold_right extract_schedule eqs []
      with IncompleteSchedule ->
        Format.eprintf
          "@[<hov 2>node %s@ has@ a@ dependency@ loop:@\n@[<hov 0>%a@].@]@."
          (extern_atom f) (print_loop sbeqs) eqs;
        []

  end
