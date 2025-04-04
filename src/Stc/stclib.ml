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
    type ctype
    type const
    type exp
    type cexp
    type rhs

    type resetconstr =
    | ResState of ident * typ * const
    | ResInst of ident * ident

    type updateconstr =
    | UpdLast of ident * cexp
    | UpdNext of ident * exp
    | UpdInst of ident * ident list * ident * exp list

    type trconstr =
    | TcDef   of clock * ident * rhs
    | TcReset  of clock * resetconstr
    | TcUpdate of clock * clock list * updateconstr

    type system = {
      s_name : ident;
      s_in   : (ident * (typ * clock)) list;
      s_vars : (ident * (typ * clock)) list;
      s_lasts: (ident * ((const * typ) * clock)) list;
      s_nexts: (ident * ((const * typ) * clock)) list;
      s_subs : (ident * ident) list;
      s_out  : (ident * (typ * clock)) list;
      s_tcs  : trconstr list }

    type program = {
      types: typ list;
      externs: (ident * (ctype list * ctype)) list;
      systems: system list
    }
  end

module PrintFun
    (Ops: PRINT_OPS)
    (CE : Coreexprlib.SYNTAX with type typ     = Ops.typ
                              and type ctype   = Ops.ctype
                              and type cconst  = Ops.cconst
                              and type unop    = Ops.unop
                              and type binop   = Ops.binop
                              and type enumtag = Ops.enumtag)
    (Stc: SYNTAX with type clock = CE.clock
                  and type typ   = Ops.typ
                  and type ctype = Ops.ctype
                  and type const = Ops.const
                  and type exp   = CE.exp
                  and type cexp  = CE.cexp
                  and type rhs = CE.rhs)
  :
  sig
    val print_trconstr   : Format.formatter -> Stc.trconstr -> unit
    val print_system     : Format.formatter -> Stc.system -> unit
    val print_program    : Format.formatter -> Stc.program -> unit
    val print_fullclocks : bool ref
    val print_clocktypes : bool ref
  end
  =
  struct

    include Coreexprlib.PrintFun (CE) (Ops)

    let print_clocktypes = ref false

    let print_clocktype fmt ck =
      if !print_clocktypes
      then Format.fprintf fmt "@[<hov 8>(* :: %a *)@]@ " print_clock ck

    let print_reset p (id, ((c0, ty), ck)) =
      fprintf p "%a@ = %a%a"
        print_ident id
        Ops.print_const (c0, ty)
        print_clock_decl ck

    let print_subsystem p (id, f) =
      fprintf p "<%a>@ : %a"
        print_ident id
        print_ident f

    let rec print_trconstr p tc =
      match tc with
      | Stc.TcDef (ck, x, e) ->
        fprintf p "@[<hov 2>%a =@ %a%a@]"
          print_ident x
          print_clocktype ck
          print_rhs e
      | Stc.TcReset (ckr, Stc.ResState (x, ty, c0)) ->
        fprintf p "@[<hov 2>reset@ %a = %a every@ (%a)@]"
          print_ident x
          Ops.print_const (c0, ty)
          print_clock ckr
      | Stc.TcReset (ckr, Stc.ResInst (s, f)) ->
        fprintf p "@[<hov 2>reset(%a<%a>)@ every@ (%a)@]"
            print_ident f
            print_ident s
            print_clock ckr
      | Stc.TcUpdate (ck, _, Stc.UpdLast (x, e)) ->
        fprintf p "@[<hov 2>update@ %a =@ %a%a@]"
          print_ident x
          print_clocktype ck
          print_cexp e
      | Stc.TcUpdate (ck, _, Stc.UpdNext (x, e)) ->
        fprintf p "@[<hov 2>next@ %a =@ %a%a@]"
          print_ident x
          print_clocktype ck
          print_exp e
      | Stc.TcUpdate (ck, _, Stc.UpdInst (i, xs, f, es)) ->
        fprintf p "@[<hov 2>%a =@ %a%a<%a>(@[<hv 0>%a@])@]"
          print_pattern xs
          print_clocktype ck
          print_ident f
          print_ident i
          (print_comma_list print_exp) es

    let print_trconstrs p =
      pp_print_list ~pp_sep:pp_force_newline print_trconstr p

    let print_system p { Stc.s_name   = name;
                         Stc.s_in     = inputs;
                         Stc.s_out    = outputs;
                         Stc.s_vars   = locals;
                         Stc.s_lasts  = lasts;
                         Stc.s_nexts  = nexts;
                         Stc.s_subs   = subs;
                         Stc.s_tcs    = tcs } =
      fprintf p "@[<v>\
                 @[<v 2>system %a {@;\
                 @[<v>\
                 %a%a%a\
                 @[<hov 0>\
                 @[<h>transition(%a)@]@;\
                 @[<h>returns (%a)@]\
                 @]@;\
                 %a\
                 @[<v 2>{@;%a@;<0 -2>@]\
                 }@]@]@]@;}"
        print_ident name
        (print_comma_list_as "init" print_reset) lasts
        (print_comma_list_as "init" print_reset) nexts
        (print_comma_list_as "sub" print_subsystem) subs
        print_decl_list inputs
        print_decl_list outputs
        (print_comma_list_as "var" print_decl) locals
        print_trconstrs (List.rev tcs)

    let print_extern_decl p (f, (tyins, tyout)) =
      fprintf p "external %a(%a) returns %a"
        print_ident f
        (print_comma_list Ops.print_ctype) tyins
        Ops.print_ctype tyout

    let print_program p prog =
      fprintf p "@[<v 0>";
      List.iter (fprintf p "%a@;@;" Ops.print_typ_decl) (List.rev prog.Stc.types);
      List.iter (fprintf p "%a@;@;" print_extern_decl) (List.rev prog.Stc.externs);
      List.iter (fprintf p "%a@;@;" print_system) (List.rev prog.Stc.systems);
      fprintf p "@]@."
  end

module SchedulerFun
    (CE: Coreexprlib.SYNTAX)
    (Stc: SYNTAX with type clock = CE.clock
                 and type typ    = CE.typ
                 and type exp    = CE.exp
                 and type cexp   = CE.cexp
                 and type rhs    = CE.rhs) :
  sig
    val cutting_points : ident list -> ident list -> Stc.trconstr list -> ident list
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

    type 'a _node = {
      n_id                  : int;
      n_clock_path          : int list;
      mutable n_visited     : bool;
      mutable n_schedule    : positive option;
      mutable n_depends_on  : 'a;
      mutable n_required_by : 'a;
    }

    module rec OrderedNode :
      Set.OrderedType with type t = NodeSet.t _node =
    struct
      type t = NodeSet.t _node
      let compare n1 n2 = Int.compare n1.n_id n2.n_id
    end
    and NodeSet : Set.S with type elt = OrderedNode.t = Set.Make(OrderedNode)

    type node = OrderedNode.t

    let linked g1 g2 =
      (NodeSet.mem g2 g1.n_depends_on) || (NodeSet.mem g1 g2.n_depends_on)
      || (NodeSet.mem g2 g1.n_required_by) || (NodeSet.mem g1 g2.n_required_by)

    let add_depends node1 node2 =
      if not (node1.n_id = node2.n_id) then (
        node1.n_depends_on <- NodeSet.add node2 node1.n_depends_on;
        node2.n_required_by <- NodeSet.add node1 node2.n_required_by;
      )

    let drop_dep x tc =
      tc.n_depends_on <- NodeSet.remove x tc.n_depends_on

    let rec resolve_variable e =
      match e with
      | Evar (x, _)                   -> Some x
      | Ewhen (e, _, _)               -> resolve_variable e
      | Econst _ | Eenum _ | Elast _ | Eunop _ | Ebinop _ -> None

    let rec clock_path acc = let open CE in function
      | Cbase          -> acc
      | Con (ck, x, _) -> clock_path (int_of_positive x :: acc) ck

    let clock_path_of_tc = function
      | TcDef (ck, _, Ecexp (Emerge ((y, _), _, _)))
      | TcUpdate (ck, _, (UpdLast (_, Emerge ((y, _), _, _)))) ->
        clock_path [int_of_positive y] ck
      | TcDef (ck, _, Ecexp (Ecase (e, _, _)))
      | TcUpdate (ck, _, (UpdLast (_, Ecase (e, _, _)))) -> begin
          match resolve_variable e with
          | None -> clock_path [] ck
          | Some x -> clock_path [int_of_positive x] ck
          end
      | TcDef (ck, _, _)
      | TcReset (ck, _)
      | TcUpdate (ck, _, _) -> clock_path [] ck

    let new_tc_node i tc = {
      n_id       = i;
      n_clock_path  = clock_path_of_tc tc;
      n_visited = false;
      n_schedule    = None;
      n_depends_on  = NodeSet.empty;
      n_required_by = NodeSet.empty;
    }

    (** Add dependencies between trconstrs *)

    let add_clock_deps add_dep =
      let rec go = function
        | Cbase          -> ()
        | Con (ck, x, _) -> add_dep x; go ck
      in
      go

    let add_exp_deps add_dep add_last_dep =
      let rec go = function
        | Econst _
        | Eenum _               -> ()
        | Evar (x, _)           -> add_dep x
        | Elast (x, _)          -> add_last_dep x
        | Ewhen (e, (x, _), _)  -> add_dep x; go e
        | Eunop (_, e, _)       -> go e
        | Ebinop (_, e1, e2, _) -> go e1; go e2
      in go

    let add_cexp_deps add_dep add_last_dep =
      let go_exp = add_exp_deps add_dep add_last_dep in
      let rec go = function
        | Emerge ((x, _), ces, _) -> add_dep x; List.iter go ces
        | Ecase (e, ces, d) ->
          go_exp e;
          List.iter (function Some e -> go e | None -> ()) ces;
          go d
        | Eexp e         -> go_exp e
      in go

    let add_rhs_deps add_dep add_last_dep = function
      | Eextcall (_, es, _) -> List.iter (add_exp_deps add_dep add_last_dep) es
      | Ecexp e -> add_cexp_deps add_dep add_last_dep e

    let add_dependencies add_dep_var add_dep_last add_dep_inst = function
      | TcDef (ck, _, ce) ->
        add_clock_deps add_dep_var ck;
        add_rhs_deps add_dep_var add_dep_last ce
      | TcReset (ckr, _) ->
        add_clock_deps add_dep_var ckr
      | TcUpdate (ck, _, UpdLast (x, ce)) ->
        add_clock_deps add_dep_var ck;
        add_cexp_deps add_dep_var (fun y -> if y <> x then add_dep_last y) ce
      | TcUpdate (ck, _, UpdNext (x, e)) ->
        add_clock_deps add_dep_var ck;
        add_exp_deps (fun y -> if y <> x then add_dep_var y) add_dep_last e
      | TcUpdate (ck, _, UpdInst (i, _, _, es)) ->
        add_clock_deps add_dep_var ck;
        List.iter (add_exp_deps add_dep_var add_dep_last) es;
        add_dep_inst i

    (** Map variable identifiers to trconstr ids *)

    module PM = PositiveMap

    let pm_update key value (map : ('a list) PM.t) =
      match PM.find key map with
      | None -> PM.add key [value] map
      | Some l -> PM.add key (value::l) map

    type def_type = Reset | Def | Last | Next

    (* Each variable identifier is associated with a list of pairs giving the
       trconstr (id) that define (def, step, reset), and possibly remove it (next). *)
    let variable_inst_maps_from_tc id (vars, insts) = function
      | TcDef (_, x, _) ->
        PM.add x [(id, Def)] vars, insts
      | TcReset (_, ResState (x, _, _)) ->
        pm_update x (id, Reset) vars, insts
      | TcReset (_, ResInst (i, _)) ->
        vars, pm_update i (id, false) insts
      | TcUpdate (_, _, UpdLast (x, _)) ->
        pm_update x (id, Last) vars, insts
      | TcUpdate (_, _, UpdNext (x, _)) ->
        pm_update x (id, Next) vars, insts
      | TcUpdate (_, _, UpdInst (i, xs, _, _)) ->
        List.fold_left (fun m x -> PM.add x [(id, Def)] m) vars xs,
        pm_update i (id, true) insts

    let fold_left_i f acc l =
      List.fold_left (fun (acc, i) x -> f i acc x, i + 1) (acc, 0) l
      |> fst

    let variable_inst_maps tcs =
      fold_left_i variable_inst_maps_from_tc (PM.empty, PM.empty) tcs

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
      mutable ready_tcs : node list;
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
      | TcDef (_, x, _) ->
        pp_print_string fmt (extern_atom x)
      | TcReset (_, ResState (x, _, _)) ->
        fprintf fmt "reset %s" (extern_atom x)
      | TcReset (_, ResInst(f, _)) ->
        fprintf fmt "reset(%s)" (extern_atom f)
      | TcUpdate (_, _, UpdLast (x, _)) ->
        fprintf fmt "update %s" (extern_atom x)
      | TcUpdate (_, _, UpdNext (x, _)) ->
        fprintf fmt "next %s" (extern_atom x)
      | TcUpdate (_, _, UpdInst (_, xs, _, _)) ->
        fprintf fmt "{@[<hov 2>%a@]}"
          (pp_print_list ~pp_sep:pp_print_space pp_print_string)
          (List.map extern_atom xs)

    let pp_tc_status f tc = Format.fprintf f "%d" tc.n_id

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
    let enqueue_tc ct tc =
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
      if NodeSet.is_empty tc.n_depends_on then seek ct tc.n_clock_path

    let schedule_from_queue sbtcs ct_t tcs =
      let enqueue = enqueue_tc ct_t in

      let check_dep n_x n_y =
        drop_dep n_x n_y;
        enqueue n_y
      in

      (* Track the scheduled position. *)
      let next_pos =
        let np = ref Coq_xH in
        fun () -> let r = !np in (np := Pos.succ !np; r)
      in

      (* Schedule an trconstr and update any that depend on it. *)
      let enschedule n =
        eprint "@;schedule %d (%a)" n.n_id (pp_print_tc_lhs sbtcs) n.n_id;
        n.n_schedule <- Some (next_pos ());
        NodeSet.iter (check_dep n) n.n_required_by
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

    let find_unscheduled i { n_schedule } =
      if n_schedule = None then raise (Found i)

    let find_next_none tcs deps =
      try
        NodeSet.iter (fun { n_id } -> find_unscheduled n_id tcs.(n_id)) deps;
        None
      with Found i -> Some i

    let find_dep_loop tcs =
      try
        Array.iteri find_unscheduled tcs; []
      with Found start ->
        let rec track i =
          if NodeSet.is_empty tcs.(i).n_depends_on
          then (tcs.(i).n_schedule <- Some Coq_xH; [i])
          else begin
            match find_next_none tcs tcs.(i).n_depends_on with
            | None -> failwith "find_dep_loop failed"
            | Some i' ->
                tcs.(i).n_depends_on <- NodeSet.empty;
                let r = track i' in
                if tcs.(i).n_schedule <> None
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

    let extract_schedule { n_schedule } res =
      match n_schedule with
      | None -> raise IncompleteSchedule
      | Some s -> s :: res

    let show_tc tcs i tc =
      eprint "@;%d: %a :: %a" i (pp_print_tc_lhs tcs) i pp_clock_path tc.n_clock_path

    (** First candidate schedule *)

    let schedule_with_queue f sbtcs tcs =
      let ct = empty_clock_tree () in
      Array.iter (enqueue_tc ct) tcs;
      schedule_from_queue sbtcs ct tcs;

      let _ = (* checks that the schedule is complete *)
        try
          Array.fold_right extract_schedule tcs []
        with IncompleteSchedule ->
          Format.eprintf
            "@[<hov 2>node %s@ has@ a@ dependency@ loop:@\n@[<hov 0>%a@].@]@."
            (extern_atom f) (print_loop sbtcs) tcs;
          []
      in

      let node_compare_sch n1 n2 =
        match n1.n_schedule, n2.n_schedule with
        | Some p1, Some p2 -> Camlcoq.P.compare p1 p2
        | _, _ -> invalid_arg "node_compare_sch"
      in

      let node_list = Array.to_list tcs in
      List.sort node_compare_sch node_list

    (** Recooking algorithm from heptagon *)

    let recooking node_list =

      (* possible overlapping between clocks *)
      let rec clock_score p1 p2 =
        match p1, p2 with
        | x1 :: p1, x2 :: p2 when x1 = x2 -> 1 + clock_score p1 p2
        | _ -> 0
      in

      let rec insert node s = function
        | [] -> raise Not_found
        | node1 :: node_list ->
          if linked node node1 then raise Not_found
          else
            let ns = clock_score (List.rev node.n_clock_path) (List.rev node1.n_clock_path) in
            try
              node1 :: (insert node ns node_list)
            with
            | Not_found ->
              if ns > s
              then node :: node1 :: node_list
              else raise Not_found in

      let rec recook = function
        | [] -> []
        | node :: node_list ->
          let node_list' = recook node_list in
          try
            insert node 0 node_list'
          with
            Not_found -> node :: node_list'
      in

      node_list |> recook |> List.rev |> recook |> List.rev

    (** Full scheduling *)
    let schedule f sbtcs =
      let tcs = Array.of_list (List.mapi new_tc_node sbtcs) in

      eprint "@[<v>--scheduling %s" (extern_atom f);
      eprint "@;@[<v 2>trconstrs =";
      Array.iteri (show_tc sbtcs) tcs;
      eprint "@]";

      let varmap, instmap = variable_inst_maps sbtcs in

      let add xi yi = add_depends tcs.(xi) tcs.(yi) in
      let add_dep_var xi y =
        match PM.find y varmap with
        | None             -> ()        (* ignore inputs *)
        | Some ys ->
          List.iter (fun (yi, typ) ->
              match typ with
              | Next -> add yi xi (* reverse dep for next *)
              | _ -> add xi yi) ys
      in
      let add_dep_last xi y =
        match PM.find y varmap with
        | None -> ()
        | Some ys ->
          List.iter (fun (yi, typ) ->
              match typ with
              | Last -> add yi xi
              | _ -> add xi yi) ys
      in
      let add_dep_inst xi y =
          match PM.find y instmap with
          | None    -> ()                 (* ignore simple steps *)
          | Some ys -> List.iter (fun (yi, isstep) ->
              if yi = xi then ()
              else if isstep then add yi xi else add xi yi) ys
      in

      (* Add dependencies to free variables *)
      List.iteri (fun n -> add_dependencies (add_dep_var n) (add_dep_last n) (add_dep_inst n)) sbtcs;

      let node_list = schedule_with_queue f sbtcs tcs in
      (* let node_list = recooking node_list in *)

      List.iteri (fun i n -> tcs.(n.n_id).n_schedule <- Some (Camlcoq.P.of_int (i+1))) node_list;

      eprint "@;--done@]@.";

      Array.fold_right extract_schedule tcs []


    (** Cutting next and update cycles *)

    open Graph

    module V = struct
      type t = ident

      let compare = Camlcoq.P.compare
      let hash = Camlcoq.P.to_int
      let equal = (=)
    end

    module G = Persistent.Digraph.Concrete(V)
    module Viz = Graphviz.Dot(struct
        include G

        let graph_attributes _ = []
        let default_vertex_attributes _ = []
        let vertex_name = extern_atom
        let vertex_attributes _ = []
        let get_subgraph _ = None
        let default_edge_attributes _ = []
        let edge_attributes _ = []

      end)

    module Fashwo = Cycles.Fashwo(struct
        module G = G
        include G
        let weight _ = Cycles.Normal 1
        let empty () = G.empty
        let copy g = g (* Its persistent right ? *)
      end)

    (** Calculates dependencies between updates of last and next variables *)
    (** The calculated graph is a subset of the graph calculated for scheduling *)
    (** We are only concerned about the dependency relations between state variables *)
    (** For each expression, we consider the set of identifiers that must be updated/defined *)
    (** before Bef(e) and after Aft(e) the expression is calculated *)
    (** - Bef(x) = {  } if x in nexts, { x } otherwise *)
    (** - Aft(x) = { x } if x in nexts, {  } otherwise *)
    (** - Bef(last x) = {  } *)
    (** - After(last x) = { x } *)
    (** all other cases are morphisms *)
    (** The dependencies are computed as follow: *)
    (** reset _ : { } *)
    (** update y = e : { x -> y | x in Bef(e) } u { y -> x | x in Aft(e) } *)
    (** next y = e : { x -> y | x in Bef(e) } u { y -> x | x in Aft(e) } *)
    (** _ = e : { x -> y | x in Bef(e), y in Aft(e) } *)
    (** _ = f(es) : { x -> y | x in Bef(es), y in Aft(es) } *)
    (** In the last two cases, we induce dependencies to treat the case where *)
    (** `x` and `last x` both appear in the same expression *)
    (** (in which case a copy must be added for `last x`) *)

    let add_tc_dep nexts gr tc =

      let add_dep = G.add_edge in
      let add_dep_if_diff gr x y =
        if x <> y then add_dep gr x y else gr
      in

      let rec free_exp acc = function
        | Econst _ | Eenum _ -> acc
        | Evar (x, _) ->
          if PM.mem x nexts then fst acc, x::snd acc else x::fst acc, snd acc
        | Elast (x, _) -> fst acc, x::snd acc
        | Eunop (_, e, _) -> free_exp acc e
        | Ebinop (_, e1, e2, _) ->
          free_exp (free_exp acc e1) e2
        | Ewhen (e, _, _) -> free_exp acc e
      in

      let free_exps = List.fold_left free_exp in

      let rec free_cexp acc = function
        | Emerge (_, es, _) -> List.fold_left free_cexp acc es
        | Ecase (e, es, d) ->
          List.fold_left
            (fun acc -> Option.fold ~none:acc ~some:(free_cexp acc))
            (free_cexp (free_exp acc e) d) es
        | Eexp e -> free_exp acc e
      in

      let rec free_rhs acc = function
        | Eextcall (_, es, _) -> free_exps acc es
        | Ecexp e -> free_cexp acc e
      in

      match tc with
      | TcReset _ -> gr
      | TcDef (_, y, e) ->
        let (bef, aft) = free_rhs ([], []) e in
        List.fold_left (fun gr x -> List.fold_left (fun gr -> add_dep gr x) gr aft) gr bef
      | TcUpdate (_, _, UpdInst (_, _, _, es)) ->
        let (bef, aft) = free_exps ([], []) es in
        List.fold_left (fun gr x -> List.fold_left (fun gr -> add_dep gr x) gr aft) gr bef
      | TcUpdate (_, _, UpdLast (x, ce)) ->
        let (bef, aft) = free_cexp ([], []) ce in
        let gr = List.fold_left (fun gr y -> add_dep_if_diff gr y x) gr bef in
        List.fold_left (fun gr y -> add_dep_if_diff gr x y) gr aft
      | TcUpdate (_, _, UpdNext (x, e)) ->
        let (bef, aft) = free_exp ([], []) e in
        let gr = List.fold_left (fun gr y -> add_dep_if_diff gr y x) gr bef in
        List.fold_left (fun gr y -> add_dep_if_diff gr x y) gr aft

    let cutting_points _ nexts trconstrs =
      let nexts = List.fold_left (fun nexts x -> PM.add x () nexts) PM.empty nexts in
      let graph =
        List.fold_left (add_tc_dep nexts) G.empty trconstrs in
      (* Viz.fprint_graph Format.std_formatter graph; *)
      (* Format.fprintf Format.std_formatter "\n"; *)
      let args = Fashwo.feedback_arc_set graph in
      List.map fst args

  end
