
(* Shared definitions *)

type associativity = LtoR | RtoL | NA

let fmt_coqstring p s = List.iter (Format.pp_print_char p) s

module type PRINT_OPS =
  sig
    type ctype
    type typ
    type cconst
    type const
    type unop
    type binop
    type enumtag

    val enumtag_of_int    : int -> enumtag
    val int_of_enumtag    : enumtag -> int

    val print_ctype       : Format.formatter -> ctype -> unit
    val print_typ         : Format.formatter -> typ -> unit
    val print_typ_decl    : Format.formatter -> typ -> unit
    val print_cconst      : Format.formatter -> cconst -> unit
    val print_const       : Format.formatter -> (const * typ) -> unit
    val print_enumtag     : Format.formatter -> (enumtag * typ) -> unit
    val print_unop        : Format.formatter -> unop -> typ
                            -> (Format.formatter -> 'a -> unit) -> 'a -> unit
    val print_binop       : Format.formatter -> binop -> typ
                            -> (Format.formatter -> 'a -> unit) -> 'a
                            -> (Format.formatter -> 'a -> unit) -> 'a
                            -> unit
    val print_branches    : (Format.formatter -> 'a -> unit) -> Format.formatter
                            -> ((Format.formatter -> unit) * 'a option) list * 'a option -> unit

    val prec_unop   : unop  -> int * associativity
    val prec_binop  : binop -> int * associativity
  end

module type TYPE_FORMATS =
  sig
    type typ
    val type_decl   : typ -> string
    val type_printf : typ -> string
    val type_scanf  : typ -> string
  end

let int_of_positive =
  let rec go w r = function
    | BinNums.Coq_xI p -> go (w lsl 1) (r + w) p
    | BinNums.Coq_xO p -> go (w lsl 1) r p
    | BinNums.Coq_xH -> r + w
  in
  go 1 0

let rec positive_of_int n =
  if n = 1 then BinNums.Coq_xH
  else if n land 1 = 0 then BinNums.Coq_xO (positive_of_int (n lsr 1))
  else BinNums.Coq_xI (positive_of_int (n lsr 1))

let z_of_int n =
  if n = 0 then BinNums.Z0
  else if n < 0 then BinNums.Zneg (positive_of_int n)
  else BinNums.Zpos (positive_of_int n)

(** Prefixing an identifier with another
    There are two properties to verify:
    - ~atom (prefix pre x)
    - pre <> pre' \/ x <> x' -> prefix pre id <> prefix pre' id'
*)
let prefix pre x =
  let open Camlcoq in
  (* Both pre and x should be in the table to guarantee injectivity *)
  if (not (Hashtbl.mem string_of_atom pre) || not (Hashtbl.mem string_of_atom x))
  then invalid_arg "prefix: both identifier should be in the table";
  (* pre should be an atom to guarantee injectivity *)
  let pres = extern_atom pre and xs = extern_atom x in
  if String.contains pres '$' then invalid_arg "prefix: should be an atom";
  intern_string (pres^"$"^xs)

(** Generation of a fresh identifier.
    Countrary to prefix, we dont get the prefixed ident from the table :
    it's just a number.
    If a hint is passed, it will be inserted in the identifier
    There are two properties to verify:
    - ~atom (gensym pre hint x)
    - pre <> pre' \/ x <> x' -> gensym pre hint id <> gensym pre' hint' id'
*)
let gensym pre hint x =
  let open Camlcoq in
  let pres = extern_atom pre in
  (* pre should be an atom to guarantee injectivity *)
  if String.contains pres '$'
  then invalid_arg "gensym: the prefix should be an atom";
  match hint with
  | None -> intern_string (pres^"$"^string_of_int (P.to_int x))
  | Some hint -> intern_string (pres^"$"^extern_atom hint^"$"^string_of_int (P.to_int x))
