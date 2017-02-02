
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

