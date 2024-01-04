open Format
open Camlcoq
open Ctypes
open Interface
open Interface.Cks
open Instantiator.L.Syn

(* This program draws on the work of Xavier Leroy for the CompCert
   project (CompCert/clightgen/ExportClight.ml). *)

(** Export Lustre as a Coq file *)

(* Options, lists, pairs *)

let print_option fn p = function
  | None -> fprintf p "None"
  | Some x -> fprintf p "(Some %a)" fn x

let print_pair fn1 fn2 p (x1, x2) =
  fprintf p "@[<hov 1>(%a,@ %a)@]" fn1 x1 fn2 x2

let print_list fn p l =
  match l with
  | [] ->
      fprintf p "[]"
  | hd :: tl ->
      fprintf p "@[<hov 1>[%a" fn hd;
      let rec plist = function
      | [] -> ()
      | hd :: tl -> fprintf p ";@ %a" fn hd; plist tl
      in plist tl;
      fprintf p "]@]"

(* Identifiers *)

let prid p id =
  try
    let s = Hashtbl.find string_of_atom id in
    fprintf p "_%s" s
  with Not_found -> fprintf p "%ld%%positive" (P.to_int32 id)

let iter_hashtbl_sorted (h: ('a, string) Hashtbl.t) (f: 'a * string -> unit) =
  List.iter f
    (List.fast_sort (fun (k1, d1) (k2, d2) -> String.compare d1 d2)
      (Hashtbl.fold (fun k d accu -> (k, d) :: accu) h []))

let define_idents p =
  iter_hashtbl_sorted
    string_of_atom
    (fun (id, name) ->
        fprintf p "Definition _%s : ident := %ld%%positive.@ "
          name (P.to_int32 id));
  fprintf p "@ "

(* Numbers *)

let coqint p n =
  let n = camlint_of_coqint n in
  if n >= 0l
  then fprintf p "(Int.repr %ld)" n
  else fprintf p "(Int.repr (%ld))" n

let coqint64 p n =
  let n = camlint64_of_coqint n in
  if n >= 0L
  then fprintf p "(Int64.repr %Ld)" n
  else fprintf p "(Int64.repr (%Ld))" n

let coqfloat p n =
  fprintf p "(Float.of_bits %a)" coqint64 (Floats.Float.to_bits n)

let coqsingle p n =
  fprintf p "(Float32.of_bits %a)" coqint (Floats.Float32.to_bits n)

(* Lustre objects *)

let prbool p (b : bool) =
  match b with
  | true -> fprintf p "true"
  | false -> fprintf p "false"

(* TODO: ce n'est plus vrai *)
(* These types are defined in Ldefs.v *)
let name_ctype (ty : Interface.Op.ctype) =
  match ty with
  | Tint (sz,sg) ->
     (match sz, sg with
      | I8, Signed -> "tschar"
      | I8, Unsigned -> "tuchar"
      | I16, Signed -> "tshort"
      | I16, Unsigned -> "tushort"
      | I32, Signed -> "tint"
      | I32, Unsigned -> "tuint"
      | IBool, _ -> "tbool")
  | Tlong sg ->
     (match sg with
      | Signed -> "tlong"
      | Unsigned -> "tulong")
  | Tfloat sz ->
     (match sz with
      | F32 -> "tfloat"
      | F64 -> "tdouble")

let prtype p ty =
  match ty with
  | Op.Tprimitive ty -> fprintf p "(Tprimitive %s)" (name_ctype ty)
  | Op.Tenum (id,ids) ->  fprintf p "(Tenum %s)" (name_ctype ty)

(* let pritype p ty = *)
(*   fprintf p "%s" (string_of_type ty) *)

let name_size (sz : intsize) =
  match sz with
  | I8 -> "I8"
  | I16 -> "I16"
  | I32 -> "I32"
  | IBool -> "IBool"

let name_sign (sg : signedness) =
  match sg with
  | Signed -> "Signed"
  | Unsigned -> "Unsigned"

let prtag p (t : Op.enumtag) =
  fprintf p "%s" (string_of_int (Nat.to_int t))

let rec prclock p (ck : clock) =
  match ck with
  | Cbase ->
     fprintf p "Cbase"
  | Con (ck,id,tyt) ->
     fprintf p "(Con %a@ %a@ %a)" prclock ck prid id (print_pair prtype prtag) tyt

(* Une autre façon de produire les constantes serait de
 * construire les fonctions mk_schar:Z->const, mk_int:Z->const,
 * mk_tfloat:float->const, etc. dans Ldefs.v et
 * d'écrire directement mk_uint <nombre>, mk_tfloat <flottant>
 *)
let prconst p (c : Interface.Op.constant) =
  match c with
  | Cint (x,sz,sg) ->
     fprintf p "(Cint %a@ %s@ %s)" coqint x (name_size sz) (name_sign sg)
  | Clong (x,sg) ->
     fprintf p "(Clong %a@ %s)" coqint64 x (name_sign sg)
  | Cfloat x ->
     fprintf p "(Cfloat %a@)" coqfloat x
  | Csingle x ->
     fprintf p "(Csingle %a@)" coqsingle x

let name_unop (op : Interface.Op.unop) =
  match op with
  | UnaryOp o ->
     sprintf "(UnaryOp %s)"
       (match o with
        | Onotbool -> "Onotbool"
        | Onotint -> "Onotint"
        | Oneg -> "Oneg"
        | Oabsfloat -> "Oabsfloat")
  | CastOp ty ->
     sprintf "(CastOp %s)" (name_ctype ty)

let name_binop (op : Interface.Op.binop) =
  match op with
  | Oadd -> "Oadd"
  | Osub -> "Osub"
  | Omul -> "Omul"
  | Odiv -> "Odiv"
  | Omod -> "Omod"
  | Oand -> "Oand"
  | Oor -> "Oor"
  | Oxor -> "Oxor"
  | Oshl -> "Oshl"
  | Oshr -> "Oshr"
  | Oeq -> "Oeq"
  | Cop.One -> "One"
  | Olt -> "Olt"
  | Ogt -> "Ogt"
  | Ole -> "Ole"
  | Oge -> "Oge"

(* let prnclock p (nc : nclock) = *)
(*   fprintf p "%a" (print_pair prclock (print_option prid)) nc *)

let prann p (a : ann) =
  fprintf p "%a" (print_pair prtype prclock) a

let prlann p (la : lann) =
  fprintf p "%a" (print_pair (print_list prtype) prclock) la

let rec prexp p (e : exp) =
  match e with
  | Econst c ->
     fprintf p "@[<hov 2>(Econst %a)@]" prconst c
  | Eenum (tag,ty) ->
     fprintf p "(Eenum %a@ %a)" prtag tag prtype ty
  | Evar (id,ann) ->
     fprintf p "(Evar %a@ %a)" prid id prann ann
  | Elast _ ->
     assert false
  | Eunop (uop,e,ann) ->
     fprintf p "@[<hov 2>(Eunop %s@ %a@ %a)@]"
       (name_unop uop) prexp e prann ann
  | Ebinop (bop,e1,e2,ann) ->
     fprintf p "@[<hov 2>(Ebinop %s@ %a@ %a@ %a)@]"
       (name_binop bop) prexp e1 prexp e2 prann ann
  | Eextcall _ ->
     assert false
  | Efby (e0s,es,anns) ->
     fprintf p "@[<hov 2>(Efby %a@ %a@ %a)@]"
       (print_list prexp) e0s
       (print_list prexp) es
       (print_list prann) anns
  | Earrow (e0s,es,anns) ->
     fprintf p "@[<hov 2>(Earrow %a@ %a@ %a)@]"
       (print_list prexp) e0s
       (print_list prexp) es
       (print_list prann) anns
  | Ewhen (es,idty,tag,lann) ->
     fprintf p "@[<hov 2>(Ewhen %a@ %a@ %a@ %a)@]"
       (print_list prexp) es
       (print_pair prid prtype) idty
       prtag tag
       prlann lann
  | Emerge (idty,ies,lann) ->
     fprintf p "@[<hov 2>(Emerge %a@ %a@ %a)@]"
       (print_pair prid prtype) idty
       (print_list (print_pair prtag (print_list prexp))) ies
       prlann lann
  | Ecase (e,ies,eds,lann) ->
     fprintf p "@[<hov 2>(Emerge %a@ %a@ %a@ %a)@]"
       prexp e
       (print_list (print_pair prtag (print_list prexp))) ies
       (print_option (print_list prexp)) eds
       prlann lann
  | Eapp (id,es,res,anns) ->
     fprintf p "@[<hov 2>(Eapp %a@ %a@ %a@ %a)@]"
       prid id
       (print_list prexp) es
       (print_list prexp) res
       (print_list prann) anns

let prequation p (eqn : equation) =
  fprintf p "@[<hov 2>%a@]"
    (print_pair (print_list prid) (print_list prexp)) eqn

let prdecl p (d : decl) =
  fprintf p "%a" (print_pair prid (print_pair (print_pair (print_pair prtype prclock) prid) (print_option prid))) d

let rec prblock p (blk : block) =
  match blk with
  | Beq eq ->
     fprintf p "Beq %a@" prequation eq
  | Blocal (Scope (decls, blks)) ->
     fprintf p "@[<hov 2>(Blocal (Scope (%a))@]"
       (print_pair (print_list prdecl) (print_list prblock)) (decls,blks)
  | _ -> assert false

let print_node p (n : node) =
  let nname = extern_atom n.n_name in
  let nblk = sprintf "blk_%s" nname in
  let nin = sprintf "in_%s" nname in
  let nout = sprintf "out_%s" nname in
  fprintf p "@[<v 0>";
  fprintf p "(* Definition of node [%s] *)@ @ " nname;
  (* n_in *)
  fprintf p "@[<hov 2>Definition %s := %a.@]@ " nin
    (print_list (print_pair prid (print_pair (print_pair prtype prclock) prid))) n.n_in;
  (* n_out *)
  fprintf p "@[<hov 2>Definition %s := %a.@]@ " nout
    (print_list prdecl) n.n_out;
  fprintf p "@ ";
  (* n_block *)
  fprintf p "Definition %s :=@ " nblk;
  prblock p n.n_block;
  fprintf p ".@ @ ";

  (* (\* define node & obligations *\)
   * fprintf p "@[<hov 2>Program Definition node_%s :=@ " nname;
   * fprintf p "let ndefd_%s := build_defd %s %s %s Logic.I in@ "
   *   nname neqs nvars nout;
   * fprintf p "let nnodup_%s := build_nodup %s %s %s %s Logic.I in@ "
   *   nname neqs nin nvars nout;
   * fprintf p "let ngood_%s := build_good %s %s %s %a in@ "
   *   nname nin nvars nout prid n.n_name;
   * fprintf p "@[<hov 2>mk_node %a %a@ %s@ %s@ %s@ %s@ _ _ ndefd_%s@ \
   *            nnodup_%s@ ngood_%s.@]@]"
   *   prid n.n_name prbool n.n_hasstate nin nout nvars neqs
   *   nname nname nname; *)
  fprintf p "@ @ @]"

let print_externs p exts =
  assert false

let prglobal p (g : global) =
  fprintf p "@[<hov 2>Definition G : global :=@ Global %a@ %a@ %a.@]"
    (print_list prtype) g.types
    print_externs g.externs
    (print_list (fun p n -> fprintf p "node_%s" (extern_atom n.n_name))) g.nodes

(* let prologue = "\
 * From Coq Require Import List ZArith.\n\
 * Import ListNotations.\n\
 * From compcert Require Import Integers Ctypes cfrontend.Cop.\n\
 * From Velus Require Import Lustre Ident ObcToClight.Interface ClockDefs.\n\
 * From Velus Require Import Verif.\n\
 * \n\
 * (\* Build the [n_defd], [n_nodup] and [n_vout] obligations of NLustre nodes *\)\n\
 * Definition build_defd neqs (nvars nout : list (ident * (type * clock))) H :=\n\
 *   build_permutation_prop (vars_defined neqs) (List.map fst (nvars ++ nout)) H.\n\
 * \n\
 * Definition build_nodup neqs (nin nvars nout : list (ident * (type * clock))) H :=\n\
 *   build_nodupmembers_prop (nin ++ nvars ++ nout ++ anon_in_eqs neqs) H.\n\n\
 * Axiom build_good : forall nin nvars nout nname,
 *   Forall (@ValidId (type * clock)) (nin ++ nvars ++ nout) /\\ valid nname.\n
 * \n\
 * " *)
let prologue = ""

(* TODO:
 * Tester toutes les constructions. (floats, cast, etc.)
 *)
let print_program p (g : global) =
  (* let p = std_formatter in (\* debug *\) *)
  fprintf p "@[<v 0>";
  fprintf p "%s" prologue;
  fprintf p "(* Variables defined in the program *)@ ";
  define_idents p;
  List.iter (print_node p) g.nodes;
  fprintf p "%a@ " prglobal g;
  fprintf p "@]@."
