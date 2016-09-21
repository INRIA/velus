open Common
open DataflowToClight.SynDF
open Interface
open Camlcoq

type lexp' =
  | Econst' of Op.const
  | Evar' of ident
  | Ewhen' of lexp' * ident * bool
  | Eunop' of Op.unop * lexp'
  | Ebinop' of Op.binop * lexp' * lexp'

type cexp' =
  | Emerge' of ident * cexp' * cexp'
  | Eite' of lexp' * cexp' * cexp'
  | Eexp' of lexp'

type lexps' = lexp' list
    
type equation' =
  | EqDef' of ident * clock * cexp'
  | EqApp' of ident * clock * ident * lexps'
  | EqFby' of ident * clock * Op.const * lexp'

type node' = {
  n_name' : ident;
  n_in' : (ident * Op.coq_type) list;
  n_out' : (ident * Op.coq_type);
  n_vars' : (ident * Op.coq_type) list;
  n_eqs' : equation' list }

type global = node' list

let find x env =
  try List.assoc x env
  with Not_found -> failwith (extern_atom x ^ ": undefined id.")
                                           
let sup t1 t2 =
  match t1, t2 with
  | Op.Tfloat s, _ | _, Op.Tfloat s -> Op.Tfloat s
  | Op.Tlong s, _ | _, Op.Tlong s -> Op.Tlong s
  | Op.Tint (i, s) , _ | _, Op.Tint (i, s) -> Op.Tint (i, s)
    
let rec infer tenv le =
  let aux = infer tenv in
  match le with
  | Econst' c -> Op.type_const c
  | Evar' x -> find x tenv
  | Ewhen' (e, _, _) -> aux e
  | Eunop' (_, e) -> aux e
  | Ebinop' (_, e1, e2) -> sup (aux e1) (aux e2)

let rec elab_lexpr tenv le =
  let ty = infer tenv le in
  let aux = elab_lexpr tenv in
  match le with
  | Econst' c -> Econst c
  | Evar' x -> Evar (x, ty)
  | Ewhen' (e, x, b) -> Ewhen (aux e, x, b)
  | Eunop' (op, e) -> Eunop (op, aux e, ty)
  | Ebinop' (op, e1, e2) -> Ebinop (op, aux e1, aux e2, ty)

let rec elab_cexpr tenv ce =
  let aux = elab_cexpr tenv in
  match ce with
  | Emerge' (x, ce1, ce2) -> Emerge (x, find x tenv, aux ce1, aux ce2)
  | Eite' (le, ce1, ce2) -> Eite (elab_lexpr tenv le, aux ce1, aux ce2)
  | Eexp' le -> Eexp (elab_lexpr tenv le)
  
let elab_eq cenv tenv = function
  | EqDef' (x, ck, ce) ->
    ignore (find x tenv);
    EqDef (x, ck, elab_cexpr tenv ce)
  | EqApp' (x, ck, f, les) ->
    ignore (find x tenv);
    EqApp (x, ck, f, List.map (elab_lexpr tenv) les, find f cenv)
  | EqFby' (x, ck, c, le) ->
    ignore (find x tenv);
    EqFby (x, ck, c, elab_lexpr tenv le)

let get_tenv node =
  node.n_out' :: node.n_vars' @ node.n_in'
  
let elab_node cenv node =
  let tenv = get_tenv node in
  { n_name = node.n_name';
    n_in = node.n_in';
    n_out = node.n_out';
    n_vars = node.n_vars';
    n_eqs = List.map (elab_eq cenv tenv) node.n_eqs'}

let get_cenv =
  List.fold_left
    (fun cenv {n_name'; n_out'} -> (n_name', snd n_out') :: cenv) [] 
    
let elab_global global =
  let cenv = get_cenv global in
  List.map (elab_node cenv) global
