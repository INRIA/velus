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
    type exp
    type cexp

    type trconstr =
    | TcDef   of ident * clock * cexp
    | TcNext  of ident * clock * exp
    | TcReset of ident * clock * ident
    | TcCall  of ident * idents * clock * bool * ident * exp list

    type system = {
      s_name : ident;
      s_in   : (ident * (typ * clock)) list;
      s_vars : (ident * (typ * clock)) list;
      s_lasts: (ident * (const * clock)) list;
      s_subs : (ident * ident) list;
      s_out  : (ident * (typ * clock)) list;
      s_tcs  : trconstr list }

    type program = system list
  end

module PrintFun
    (CE: Coreexprlib.SYNTAX)
    (Stc: SYNTAX with type clock = CE.clock
                  and type typ   = CE.typ
                  and type const = CE.const
                  and type exp   = CE.exp
                  and type cexp  = CE.cexp)
    (PrintOps: PRINT_OPS with type typ   = CE.typ
                          and type const = CE.const
                          and type unop  = CE.unop
                          and type binop = CE.binop) :
  sig
    val print_trconstr   : formatter -> Stc.trconstr -> unit
    val print_system     : Format.formatter -> Stc.system -> unit
    val print_program    : Format.formatter -> Stc.program -> unit
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

    let print_system p (id, f) =
      fprintf p "<%a>@ : %a"
        print_ident id
        print_ident f

    let rec print_trconstr p tc =
      match tc with
      | Stc.TcDef (x, ck, e) ->
        fprintf p "@[<hov 2>%a =@ %a@]"
          print_ident x
          print_cexp e
      | Stc.TcNext (x, ck, e) ->
        fprintf p "@[<hov 2>next@ %a =@ %a@]"
          print_ident x
          print_exp e
      | Stc.TcReset (s, ck, f) ->
        fprintf p "@[<hov 2>reset(%a<%a>)@ every@ (%a)@]"
            print_ident f
            print_ident s
            print_clock ck
      | Stc.TcCall (s, xs, ck, _, f, es) ->
        fprintf p "@[<hov 2>%a =@ %a<%a>(@[<hv 0>%a@])@]"
          print_pattern xs
          print_ident f
          print_ident s
          (print_comma_list print_exp) es

    let print_trconstrs p =
      pp_print_list ~pp_sep:pp_force_newline print_trconstr p

    let print_system p { Stc.s_name   = name;
                         Stc.s_in     = inputs;
                         Stc.s_out    = outputs;
                         Stc.s_vars   = locals;
                         Stc.s_lasts  = lasts;
                         Stc.s_subs   = subs;
                         Stc.s_tcs    = tcs } =
      fprintf p "@[<v>\
                 @[<hov 0>\
                 @[<h>system %a (%a)@]@;\
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
        (print_comma_list_as "sub" print_system) subs
        print_trconstrs (List.rev tcs)

    let print_program p prog =
      fprintf p "@[<v 0>%a@]@."
        (pp_print_list ~pp_sep:(fun p () -> fprintf p "@;@;") print_system)
        (List.rev prog)
  end

module SchedulerFun
    (CE: Coreexprlib.SYNTAX)
    (Stc: SYNTAX with type clock = CE.clock
                 and type typ   = CE.typ
                 and type const = CE.const
                 and type exp  = CE.exp
                 and type cexp  = CE.cexp) :
  sig
    val schedule : ident -> Stc.trconstr list -> BinNums.positive list
  end
  =
  struct

    open CE
    open Stc

    let debug = false
    let eprint =
      let print = if debug then Format.fprintf else Format.ifprintf in
      fun x -> print Format.err_formatter x

    (** Status information for each trconstr *)

    module Int = struct
      type t = int
      let compare = (Pervasives.compare : t -> t -> int)
    end

    module TcSet = Set.Make (Int)

    (* For each trconstr, we track
       - id: index in the array of trconstrs;
       - clock_path: sequence of variable identifiers ordered from
             most rapid to least rapid and ignoring values, i.e.,
             both "base when a when b" and "base whenot a whenot b"
             become "[a; b]", reflecting the nesting of if/then/elses
             to be produced in the target code;
       - schedule: "None" when unscheduled and "Some i" when scheduled
             as the ith trconstr (from 1);
       - depends_on: these trconstrs must be scheduled beforehand;
       - required_by: these trconstrs must be scheduled afterward. *)

    type tc_status = {
      tc_id               : int;
      clock_path          : int list;
      mutable schedule    : positive option;
      mutable depends_on  : TcSet.t;
      mutable required_by : TcSet.t;
    }

    let drop_dep x tc =
      tc.depends_on <- TcSet.remove x tc.depends_on

    let rec resolve_variable e =
      match e with
      | Evar (x, _) -> Some x
      | Ewhen (e, _, _) -> resolve_variable e
      | Econst _ | Eunop _ | Ebinop _ -> None

    let grouping_clock_of_tc =
      function
      (* Push merges/iftes down a level to improve grouping *)
      | TcDef (_, ck, Emerge (y, _, _)) -> Con (ck, y, true)
      | TcDef (_, ck, Eite (e, _, _)) -> begin
          match resolve_variable e with
          | None -> ck
          | Some x -> Con (ck, x, true)
          end
      (* Standard cases *)
      | TcDef (_, ck, _)
      | TcNext (_, ck, _)
      | TcReset (_, ck, _)
      | TcCall (_, _, ck, _, _, _) -> ck

    let rec clock_path acc = let open CE in function
      | Cbase -> acc
      | Con (ck, x, _) -> clock_path (int_of_positive x :: acc) ck

    let new_tc_status i tc = {
      tc_id = i;
      schedule = None;
      depends_on  = TcSet.empty;
      required_by = TcSet.empty;
      clock_path = clock_path [] (grouping_clock_of_tc tc)
    }

    (** Add dependencies between trconstrs *)

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
      | TcDef (_, ck, ce) ->
        add_clock_deps add_dep_var ck;
        add_cexp_deps add_dep_var ce
      | TcNext (x, ck, e) ->
        add_clock_deps add_dep_var ck;
        add_exp_deps (fun y -> if y <> x then add_dep_var y) e
      | TcReset (_, ck, _) ->
        add_clock_deps add_dep_var ck
      | TcCall (s, _, ck, _, _, es) ->
        add_clock_deps add_dep_var ck;
        List.iter (add_exp_deps add_dep_var) es;
        add_dep_state s

    (** Map variable identifiers to trconstr ids *)

    module PM = PositiveMap

    (* Each variable identifier is associated with a pair giving the
       trconstr (id) that defines it and whether that trconstr is a fby. *)
    let variable_state_maps_from_tc i (vars, states) = function
      | TcDef (x, _, _) ->
        PM.add x (i, false) vars, states
      | TcNext (x, _, _) ->
        PM.add x (i, true) vars, states
      | TcReset (s, _, _) ->
        vars, PM.add s i states
      | TcCall (_, xs, _, _, _, _) ->
        List.fold_left (fun m x -> PM.add x (i, false) m) vars xs, states

    let fold_left_i f acc l =
      List.fold_left (fun (acc, i) x -> f i acc x, i + 1) (acc, 0) l
      |> fst

    let variable_state_maps tcs =
      fold_left_i variable_state_maps_from_tc (PM.empty, PM.empty) tcs

    (** Queuing by clock *)

    (* We keep a queue of trconstrs that can be scheduled (i.e., their
       dependencies have already been scheduled). The queue is organized
       as a tree according to the trconstr clock paths. Descending a level
       in the tree introduces an "if" the target code, while ascending
       closes one. The idea is to group trconstrs according to their clock
       paths and schedule as many as possible without changing level.

       When there are no more trconstrs to schedule in a sub-branch, the
       branch is dropped completely. This may generate more "garbage" than
       necessary. An alternative would be to add a mutable boolean field
       at each level indicating whether a subbranch contains trconstrs
       to schedule. *)

    module IM = Map.Make (Int)

    type clock_tree = {
      mutable ready_tcs : tc_status list;
      mutable subclocks : clock_tree IM.t
    }

    let empty_clock_tree () = {
      ready_tcs = [];
      subclocks = IM.empty
    }

    let pp_print_arrow f () = Format.fprintf f "@ ->@ "

    let pp_clock_int f x = Format.fprintf f "%d (%s)" x (extern_atom (positive_of_int x))

    let pp_clock_path f = function
      | [] -> pp_print_string f "."
      | cp -> pp_print_list ~pp_sep:pp_print_arrow pp_clock_int f cp

    let pp_print_tc_lhs nltcs fmt i =
      let open Format in
      match List.nth nltcs i with
      | TcDef (x, _, _) ->
        pp_print_string fmt (extern_atom x)
      | TcNext (x, _, _) ->
        pp_print_string fmt (extern_atom x)
      | TcReset (_, _, _) ->
        pp_print_string fmt "_"
      | TcCall (_, xs, _, _, _, _) ->
        fprintf fmt "{@[<hov 2>%a@]}"
          (pp_print_list ~pp_sep:pp_print_space pp_print_string)
          (List.map extern_atom xs)

    let pp_tc_status f tc = Format.fprintf f "%d" tc.tc_id

    let pp_print_comma f () = Format.fprintf f ",@ "

    let rec pp_branch f (ck, ct) =
      Format.fprintf f "%a:%a" pp_clock_int ck pp_clock_tree ct

    and pp_clock_tree f { ready_tcs; subclocks } =
      let open Format in
      fprintf f "{@[<hv 2>";
      if ready_tcs <> [] then begin
        fprintf f "@[<hov 2>tcs=%a@]"
          (pp_print_list ~pp_sep:pp_print_space pp_tc_status) ready_tcs;
        if not (IM.is_empty subclocks) then fprintf f ",@ "
      end;
      if not (IM.is_empty subclocks) then
        fprintf f "subs=%a"
          (pp_print_list ~pp_sep:pp_print_comma pp_branch) (IM.bindings subclocks);
      fprintf f "@]}"


    (* If an trconstr is ready to schedule, place it in the queue according
       to its clock path. *)
    let enqueue_tc ct ({ depends_on; clock_path } as tc) =
      let rec seek ct = function
        | [] -> ct.ready_tcs <- tc :: ct.ready_tcs
        | x :: ck ->
          match IM.find x ct.subclocks with
          | ct' -> seek ct' ck
          | exception Not_found -> begin
              let ct' = empty_clock_tree () in
              ct.subclocks <- IM.add x ct' ct.subclocks;
              seek ct' ck
            end
      in
      if TcSet.is_empty depends_on then seek ct clock_path

    let schedule_from_queue sbtcs ct_t tcs =
      let enqueue = enqueue_tc ct_t in

      let check_dep x y =
        let tc_y = tcs.(y) in
        drop_dep x tc_y;
        enqueue tc_y
      in

      (* Track the scheduled position. *)
      let next_pos =
        let np = ref Coq_xH in
        fun () -> let r = !np in (np := Pos.succ !np; r)
      in

      (* Schedule an trconstr and update any that depend on it. *)
      let enschedule ({tc_id; required_by} as tc) =
        eprint "@;schedule %d (%a)" tc_id (pp_print_tc_lhs sbtcs) tc_id;
        tc.schedule <- Some (next_pos ());
        TcSet.iter (check_dep tc_id) required_by
      in

      (* Iteratively schedule at the same level of the clock tree whenever
         possible (since it does not introduce new "if"s and it maximizes
         the chances of scheduling more trconstrs later), otherwise descend
         into the tree if possible, and only ascend when absolutely
         necessary (since we would have to close and open "if"s to return
         to the same level). *)
      let rec continue ct =
        eprint "@;@[<v 2>{ %a" pp_clock_tree ct_t;
        match ct.ready_tcs with
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
            ct.ready_tcs <- [];
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

    let find_next_none tcs deps =
      try
        TcSet.iter (fun i -> find_unscheduled i tcs.(i)) deps;
        None
      with Found i -> Some i

    let find_dep_loop tcs =
      try
        Array.iteri find_unscheduled tcs; []
      with Found start ->
        let rec track i =
          if TcSet.is_empty tcs.(i).depends_on
          then (tcs.(i).schedule <- Some Coq_xH; [i])
          else begin
            match find_next_none tcs tcs.(i).depends_on with
            | None -> failwith "find_dep_loop failed"
            | Some i' ->
                tcs.(i).depends_on <- TcSet.empty;
                let r = track i' in
                if tcs.(i).schedule <> None
                then (* cycle found; ignore any prefix leading to it. *)
                     raise (Done (i :: r))
                else (* "rewind" along cycle *) i :: r
          end
        in
        try track start
        with Done r -> r

    let print_loop nltcs fmt tcs =
      Format.pp_print_list
        ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ -> ")
        (pp_print_tc_lhs nltcs)
        fmt
        (find_dep_loop tcs)

    (** Scheduling algorithm *)

    exception IncompleteSchedule

    let extract_schedule { schedule } res =
      match schedule with
      | None -> raise IncompleteSchedule
      | Some s -> s :: res

    let show_tc tcs i tc =
      eprint "@;%d: %a :: %a" i (pp_print_tc_lhs tcs) i pp_clock_path tc.clock_path

    let schedule f sbtcs =
      let tcs = Array.of_list (List.mapi new_tc_status sbtcs) in

      eprint "@[<v>--scheduling %s" (extern_atom f);
      eprint "@;@[<v 2>trconstrs =";
      Array.iteri (show_tc sbtcs) tcs;
      eprint "@]";

      let varmap, statemap = variable_state_maps sbtcs in

      let add xi yi =
        tcs.(xi).depends_on  <- TcSet.add yi tcs.(xi).depends_on;
        tcs.(yi).required_by <- TcSet.add xi tcs.(yi).required_by
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
      List.iteri (fun n -> add_dependencies (add_dep_var n) (add_dep_state n)) sbtcs;

      let ct = empty_clock_tree () in
      Array.iter (enqueue_tc ct) tcs;
      schedule_from_queue sbtcs ct tcs;
      eprint "@;--done@]@.";
      try
        Array.fold_right extract_schedule tcs []
      with IncompleteSchedule ->
        Format.eprintf
          "@[<hov 2>node %s@ has@ a@ dependency@ loop:@\n@[<hov 0>%a@].@]@."
          (extern_atom f) (print_loop sbtcs) tcs;
        []

  end
