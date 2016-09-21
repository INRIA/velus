open LS
open CoqList

(*
(* Map from aexp_list to aexp_list *)
let rec map_aexp_list2 f = function
        | Enil -> Enil
        | Econs (ae, tail) -> Econs ((f ae), (map_aexp_list2 f tail))
;;

(* Map from aexp_list to Coq list *)
let rec map_aexp_list f = function
        | Enil -> Coq_nil
        | Econs (ae, tail) -> Coq_cons ((f ae), (map_aexp_list f tail))
;;

(* Map from Coq list to aexp_list *)
let rec map_coqlist_to_aexp_list f = function
        | Coq_nil -> Enil
        | Coq_cons (a, tail) -> Econs((f a), (map_coqlist_to_aexp_list f tail))
;;

let coqlist_of_aexp_list l = map_aexp_list (fun a->a) l;;

(* Map from pat_list to Coq list *)
let rec map_pat_list f = function
        | Pnil -> Coq_nil
        | Pcons (p, tail) -> Coq_cons ((f p), (map_pat_list f tail))
;;

 *)
