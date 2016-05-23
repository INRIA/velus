open Common
open DF2CL.SynDF
open Interface
open Nelist
    
type lexp' =
  | Econst' of Op.coq_val
  | Evar' of ident
  | Ewhen' of lexp' * ident * bool
  | Eunop' of unary_op' * lexp'
  | Ebinop' of binary_op' * lexp' * lexp'

type cexp' =
  | Emerge' of ident * cexp' * cexp'
  | Eite' of lexp' * cexp' * cexp'
  | Eexp' of lexp'

type lexps' = lexp' nelist
    
type equation' =
  | EqDef' of ident * clock * cexp'
  | EqApp' of ident * clock * ident * lexps'
  | EqFby' of ident * clock * Op.coq_val * lexp'

type node' = {
  n_name' : ident;
  n_input' : (ident * Op.typ) nelist;
  n_output' : (ident * Op.typ);
  n_vars' : (ident * Op.typ) list;
  n_eqs' : equation' list }

type global = node' list
    
let sup t1 t2 =
  match t1, t2 with
  | Tfloat, _ | _, Tfloat -> Tfloat
  | Tint, _ | _, Tint -> Tint
  | Tbool, _ | _, Tbool -> Tbool
  | _, _ -> Tvoid
    
let rec infer tenv le =
  let aux = infer tenv in
  match le with
  | Econst' v -> Op.typ_of_val v
  | Evar' x -> List.assoc x tenv
  | Ewhen' (e, _, _) -> aux e
  | Eunop' (_, e) -> aux e
  | Ebinop' (_, e1, e2) -> sup (aux e1) (aux e2)

let rec elab_lexpr tenv le =
  let ty = infer tenv le in
  let aux = elab_lexpr tenv in
  match le with
  | Econst' v -> Econst (v, ty)
  | Evar' x -> Evar (x, ty)
  | Ewhen' (e, x, b) -> Ewhen (aux e, x, b)
  | Eunop' (op, e) -> Eunop (op, aux e, ty)
  | Ebinop' (op, e1, e2) -> Ebinop (op, aux e1, aux e2, ty)

let rec elab_cexpr tenv ce =
  let aux = elab_cexpr tenv in
  match ce with
  | Emerge' (x, ce1, ce2) -> Emerge (x, List.assoc x tenv, aux ce1, aux ce2)
  | Eite' (le, ce1, ce2) -> Eite (elab_lexpr tenv le, aux ce1, aux ce2)
  | Eexp' le -> Eexp (elab_lexpr tenv le)
  
let elab_eq cenv tenv = function
  | EqDef' (x, ck, ce) ->
    EqDef (x, ck, elab_cexpr tenv ce)
  | EqApp' (x, ck, f, les) ->
    EqApp (x, ck, f, Nelist.map (elab_lexpr tenv) les, List.assoc f cenv)
  | EqFby' (x, ck, c, le) ->
    EqFby (x, ck, c, elab_lexpr tenv le)

let get_tenv node =
  let ins = nelist2list node.n_input' in
  node.n_output' :: node.n_vars' @ ins
  
let elab_node cenv node =
  let tenv = get_tenv node in
  { n_name = node.n_name';
    n_input = node.n_input';
    n_output = node.n_output';
    n_vars = node.n_vars';
    n_eqs = List.map (elab_eq cenv tenv) node.n_eqs'}

let get_cenv =
  List.fold_left
    (fun cenv {n_name'; n_output'} -> (n_name', snd n_output') :: cenv) [] 
    
let elab_global global =
  let cenv = get_cenv global in
  List.map (elab_node cenv) global
