
(* Shared definitions *)

type associativity = LtoR | RtoL | NA

let fmt_coqstring p s = List.iter (Format.pp_print_char p) s

module type PRINT_OPS =
  sig
    type typ
    type const
    type unop
    type binop

    val print_typ   : Format.formatter -> typ   -> unit
    val print_const : Format.formatter -> const -> unit
    val print_unop  : Format.formatter -> unop -> typ
                        -> (Format.formatter -> 'a -> unit) -> 'a -> unit
    val print_binop : Format.formatter -> binop -> typ
                        -> (Format.formatter -> 'a -> unit)
                        -> 'a -> 'a -> unit

    val prec_unop   : unop  -> int * associativity
    val prec_binop  : binop -> int * associativity
  end

