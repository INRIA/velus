(* *********************************************************************)
(*                                                                     *)
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

open Frustre

module PP = Frustre_pp

let sprintf = Format.asprintf
let pp_loc = Frustre_of_ast.formatloc

exception ClockingError

let error loc s =
  Format.eprintf "@[%a:%s@.@]" pp_loc loc s;
  raise ClockingError

let ckvar env loc x = try (Env.find x env).v_clk with Not_found ->
  error loc (sprintf "undeclared variable '%a'" PP.ident x)

let stripname = function
  | Cstream ck -> ck
  | Cnamed (_, ck) -> ck

let stripnames = List.map stripname

let hidename = function
  | Cnamed (_, ck) -> Cstream ck
  | sck -> sck

let hidenames = List.map hidename

let expected_same loc ck cks =
  error loc (sprintf "mismatched clocks: expected [%a] got [@[%a@]]"
                PP.sclock ck PP.sclocks (stripnames cks))

let expected_got loc cks1 cks2 =
  error loc (sprintf "mismatched clocks: expected [@[%a@]] got [@[%a@]]"
                PP.sclocks (stripnames cks1) PP.sclocks (stripnames cks2))

let unify_nclocks nck1 nck2 = unify_clocks (stripname nck1) (stripname nck2)

let unify_nclocks' ck ncks =
  List.iter (fun nck -> unify_clocks ck (stripname nck)) ncks

let mk_isub env (x, _) eck =
  match eck with
  | Cnamed (i, sck) -> Env.add x i env
  | Cstream _ -> env

let reset_oindex, new_oindex =
  let index = ref 0 in
  (fun () -> index := 0),
  (fun () -> incr index; !index)

let mk_osub env (y, _) =
  Env.add y (Vidx (new_oindex ())) env

let inst_clock bck sub =
  let rec f = function
    | Cbase -> bck
    | Con (ck', b, x) ->
        try
          Son (f ck', b, Env.find x sub)
        with Not_found ->
          failwith (sprintf "parameter '%a' appears in clocks but is not \
                             instantiated by a variable" PP.ident x)
  in
  f

let check_input bck isub (x, xck) ck =
  let xck = inst_clock bck isub xck in
  try
    unify_clocks xck (stripname ck)
  with Unify ->
      failwith (sprintf "mismatched clocks: expected %a got %a"
                  PP.sclock xck PP.sclock (stripname ck))

let exp genv env =
  let rec f e =
    let ckvar = ckvar env e.e_loc in
    let clks =
      match e.e_desc with
      | Econst c -> [Cstream (fresh_clock ())]
      | Evar x   -> [Cnamed (Vnm x, ckvar x)]

      | Eunop (op, e') -> hidenames (f e')
                          (* typing ensures number of flows = 1 *)

      | Ebinop (op, e1, e2) ->
          (match f e1, f e2 with
           | [ck1] as cks, [ck2] ->
               (try unify_nclocks ck1 ck2; hidenames cks
                with Unify -> error e.e_loc
                  (sprintf "mismatched clocks: %a versus %a"
                      PP.sclock (stripname ck1) PP.sclock (stripname ck2)))
           | _, _ -> assert false (* guaranteed by typing *))

      | Efby (e0s, es) | Earrow (e0s, es) ->
          let ck0s = List.(concat (map f e0s)) in
          let cks  = List.(concat (map f es)) in
          (try List.iter2 unify_nclocks ck0s cks
           with Unify -> expected_got e.e_loc ck0s cks);
          ck0s

      (* | Epre es ->
       *    List.(concat (map f es)) *)

      | Ewhen (es, x, b) ->
          let xck = ckvar x in
          let cks = List.(concat (map f es)) in
          (try unify_nclocks' xck cks
           with Unify -> expected_same e.e_loc xck cks);
          let ck' = Cstream (Son (xck, b, Vnm x)) in
          List.map (fun _ -> ck') cks

      | Emerge (x, ets, efs) ->
          let xck = ckvar x in
          let ckts = List.(concat (map f ets)) in
          let ckfs = List.(concat (map f efs)) in
          let ckt = Son (xck, true, Vnm x) in
          (try unify_nclocks' ckt ckts
           with Unify -> expected_same e.e_loc ckt ckts);
          let ckf = Son (xck, false, Vnm x) in
          (try unify_nclocks' ckf ckfs
           with Unify -> expected_same e.e_loc ckf ckfs);
          let xck = Cstream xck in
          List.map (fun _ -> xck) ckts

      | Eite (e, ets, efs) ->
          (match f e with
           | [ck] -> begin
               let ck' = stripname ck in
               let ckts = List.(concat (map f ets)) in
               let ckfs = List.(concat (map f efs)) in
               (try unify_nclocks' ck' ckts
                with Unify -> expected_same e.e_loc ck' ckts);
               (try unify_nclocks' ck' ckfs
                with Unify -> expected_same e.e_loc ck' ckfs);
               List.map (fun _ -> ck) ckts
             end
          | _ -> assert false (* guaranteed by typing *))

      | Eapp (n, es, er) ->
          let cks = List.(concat (map f es)) in
          let (icks, ocks) = try Env.find n genv
            with Not_found -> error e.e_loc
              (sprintf "use of undeclared node '%a'" PP.ident n)
          in
          let isub = List.fold_left2 mk_isub Env.empty icks cks in
          let osub = List.fold_left mk_osub isub ocks in
          let bck = fresh_clock () in
          let clks =
            (try
               List.iter2 (check_input bck isub) icks cks;
               List.map (fun (y, yck) ->
                   Cnamed (Env.find y osub, inst_clock bck osub yck)) ocks
             with Failure s -> error e.e_loc s) in
          (match er with
           | None -> ()
           | Some er -> (match (f er) with
               | [erck] -> (try unify_clocks bck (stripname erck)
                            with _ -> error e.e_loc
                                        (sprintf "mismatched reset clock: %a versus %a"
                                           PP.sclock (stripname erck) PP.sclock bck))
               | _ -> error e.e_loc "bad reset clock"));
          clks
    in
    e.e_clk <- clks;
    clks
  in
  f

module IMap = Map.Make(struct type t = int let compare = compare end)

let mk_psub env eck x =
  match eck with
  | Cstream sck -> env
  | Cnamed (Vidx i, _) -> IMap.add i x env
  | Cnamed (Vnm _, _) -> env

let inst_indexes psub =
  let rec f ck =
    match ck with
    | Sbase | Svar _ -> ck
    | Son (ck, b, x) ->
        Son (f ck, b, match x with Vidx i -> Vnm (IMap.find i psub) | _ -> x)
  in
  f

let equation genv env { eq_desc = (xs, es); eq_loc } =
  let () = reset_oindex () in
  let ckvar = ckvar env eq_loc in
  let xcks = List.map ckvar xs in
  let ecks = List.(concat (map (exp genv env) es)) in
  let psub = List.fold_left2 mk_psub IMap.empty ecks xs in
  let ecks = try List.map (fun ck -> inst_indexes psub (stripname ck)) ecks
    with Not_found -> error eq_loc "dependent clock escapes scope"
  in
  try unify_clocks_list xcks ecks
  with Unify -> error eq_loc
    (sprintf "mismatched clocks:@[<hov>expected [@[%a@]]@ got [@[%a@]]@]"
                 PP.sclocks xcks PP.sclocks ecks)

let freeze_to_base ck =
  let ck = find_clock ck in
  match ck with
  | Svar ({ contents = Sindex _ } as link) -> (link := Slink Sbase)
  | _ -> ()

let rec gen_clock ck =
  match find_clock ck with
  | Sbase -> Cbase
  | Son (ck', b, Vnm x) -> Con (gen_clock ck', b, x)
  | _ -> assert false
         (* All clock variables introduced by Frustre_of_ast.add_decls have
            been "frozen" to Sbase and anonymous clocks (Vidx i) cannot
            escape expressions. *)

let build_whens loc e tys =
  let rec f ck =
    match find_clock ck with
    | Sbase -> e
    | Son (ck, b, Vnm x) ->
        Ewhen ([{ e_desc = f ck; e_loc = loc;
                  e_typ = tys; e_clk = [Cstream ck] }], x, b)
    | _ ->
        error loc ("constant sampled on anonymous clock")
  in
  f

(* The clock variables introduced for constants will definitely have
   been instantiated after the equation containing them is clocked (since they
   will have been unified against the clocks of variables in the pattern on
   the RHs of the equation, and any variables in the clocks of those variables
   are frozen after all node equations are clocked). *)
let rec infer_whens e =
  match e.e_desc with
  | Econst c ->
      (match e.e_clk with
       | [ck] -> { e with e_desc =
                          build_whens e.e_loc e.e_desc e.e_typ (stripname ck) }
       | _ -> assert false)
  | Evar x -> e
  | Eunop (op, e') ->
      { e with e_desc = Eunop (op, infer_whens e') }
  | Ebinop (op, e1, e2) ->
      { e with e_desc = Ebinop (op, infer_whens e1, infer_whens e2) }
  | Efby (e0s, es) ->
      { e with e_desc = Efby (List.map infer_whens e0s,
                              List.map infer_whens es) }
  | Earrow (e0s, es) ->
     { e with e_desc = Earrow (List.map infer_whens e0s,
                               List.map infer_whens es) }
  (* | Epre es ->
   *    { e with e_desc = Epre (List.map infer_whens es) } *)
  | Ewhen (es, x, b) ->
      { e with e_desc = Ewhen (List.map infer_whens es, x, b) }
  | Emerge (x, ets, efs) ->
      { e with e_desc = Emerge (x, List.map infer_whens ets,
                                   List.map infer_whens efs) }
  | Eite (e', ets, efs) ->
      { e with e_desc = Eite (infer_whens e', List.map infer_whens ets,
                                              List.map infer_whens efs) }
  | Eapp (n, es, None) ->
    { e with e_desc = Eapp (n, List.map infer_whens es, None) }
  | Eapp (n, es, Some er) ->
    { e with e_desc = Eapp (n, List.map infer_whens es, Some (infer_whens er)) }

let infer_whens_in_equation ({ eq_desc = (xs, es) } as eq) =
  { eq with eq_desc = (xs, List.map infer_whens es) }

(* Assumes that Frustre_of_ast.add_decls has done its thing. *)
let node loc genv
    ({ n_name; n_hasstate; n_in; n_out; n_vars; n_eqs; n_env } as n)
  =
  let ckvar = ckvar n_env loc in
  try
    List.iter (equation genv n_env) n_eqs;
    List.iter (fun x -> freeze_to_base (ckvar x)) n_in;
    let icks = List.map (fun x -> (x, gen_clock (ckvar x))) n_in in
    let ocks = List.map (fun x -> (x, gen_clock (ckvar x))) n_out in
    n.n_eqs <- List.map infer_whens_in_equation n_eqs;
    Env.add n_name (icks, ocks) genv
  with ClockingError ->
    (Format.eprintf "clocking error in node '%a'@." PP.ident n_name; exit 1)

let implementation genv { desc; loc } =
  match desc with
  | Enodedecl n -> node loc genv n

let global = List.fold_left implementation Env.empty

