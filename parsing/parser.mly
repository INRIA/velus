%{

open Common
open Location
open DF2CL.SynDF
open Nelist
open Interface
open Integers
open Camlcoq
open Elab
	   
let id = intern_string
let id' (s, a) = (id s, a)
	  
let positive_of_int i =
  (* we define the auxiliary function inside the body,
     so that we ensure a call with a positive value;
     declaring it outside may have required more case,
     as I am not sure of the result with a negative call. *)
  let rec positive_of_int_aux i =
    let q = i / 2 in
    if q = 0
    then BinNums.Coq_xH
    else let m = i mod 2 in
         let p = positive_of_int_aux q in
	(* not tail recursive, but less than 32 calls, so... *)
         if m = 0
         then BinNums.Coq_xO(p)
         else BinNums.Coq_xI(p)
  in
  if i > 0 then positive_of_int_aux i
  else failwith "[mlUtils:positive_of_int] the argument is non positive\n"
				
let z_of_int i =
  if i = 0 then 
    BinNums.Z0
  else if i > 0 then
    BinNums.Zpos (positive_of_int i)
  else
    BinNums.Zneg (positive_of_int (-i))

let elab_float_constant f =
  let open Cabs in
  let open C in
  let ty = match f.suffix_FI with
    | Some ("l"|"L") -> FLongDouble
    | Some ("f"|"F") -> FFloat
    | None -> FDouble
    | _ -> assert false (* The lexer should not accept anything else. *)
  in
  let v = {
    hex=f.isHex_FI;
    intPart=begin match f.integer_FI with Some s -> s | None -> "0" end;
    fracPart=begin match f.fraction_FI with Some s -> s | None -> "0" end;
    exp=begin match f.exponent_FI with Some s -> s | None -> "0" end }
  in
  (v, ty)

(** Floating point constants *)

let convertFloat f kind =
  let open C2C in
  let open C in
  let open Floats in
  let mant = z_of_str f.C.hex (f.C.intPart ^ f.C.fracPart) 0 in
  match mant with
    | Z.Z0 ->
      begin match kind with
      | FFloat -> Float.to_single Float.zero
      | FDouble | FLongDouble -> assert false
      end
    | Z.Zpos mant ->
      let sgExp = match f.C.exp.[0] with '+' | '-' -> true | _ -> false in
      let exp = z_of_str false f.C.exp (if sgExp then 1 else 0) in
      let exp = if f.C.exp.[0] = '-' then Z.neg exp else exp in
      let shift_exp =
		(if f.C.hex then 4 else 1) * String.length f.C.fracPart in
      let exp = Z.sub exp (Z.of_uint shift_exp) in
      let base = P.of_int (if f.C.hex then 2 else 10) in
      begin
		match kind with
		| FFloat ->
		   let f = Float32.from_parsed base mant exp in
           checkFloatOverflow f;
           f
		| FDouble | FLongDouble -> failwith "Double or LongDouble constant"
	  end
	| Z.Zneg _ -> assert false

			   
%}

%token LPAREN RPAREN COLON COLONS SEMICOL 
%token EQUAL COMMA LET TEL ON BASE
%token <string> IDENT
%token <int> INT
%token <Cabs.floatInfo> FLOAT
%token <bool> BOOL
%token NODE VARS RETURNS
%token FBY MERGE WHEN WHENNOT
%token IF THEN ELSE	   
%token EOF
%token TBOOL TINT TFLOAT
%token NOT ADD SUB MUL DIV
	   
%left MERGE
%left WHEN
%left FBY
%left ON
%nonassoc BASE

%start program
%type <Elab.global> program

%%

ne_list(X):
  | x = X                  { Coq_nebase x}
  | x = X; xs = ne_list(X) { Coq_necons (x, xs) }
		  
ne_sep_list(sep, X):
  | x = X                                { Coq_nebase x}
  | x = X; sep; xs = ne_sep_list(sep, X) { Coq_necons (x, xs) }

par(X): x = delimited(LPAREN, X, RPAREN) { x }

program: ns = terminated(list(terminated(node_dec, SEMICOL)), EOF) { ns }

node_dec:
  NODE; f = IDENT; ins = par(ne_sep_list(COMMA, param)); 
  RETURNS; out = par(param);
  vars = loption(VARS; xs = separated_list(COMMA, param) {xs}); SEMICOL;
  LET; eqs = list(terminated(equ, SEMICOL)); TEL
  { { n_name' = id f;
	  n_input' = ins;
	  n_output' = out;
	  n_vars' = vars;
	  n_eqs' = eqs } }
  
param: p = separated_pair(IDENT, COLON, typ) { id' p }				 

typ:
  | TBOOL  { Tbool }
  | TINT   { Tint }
  | TFLOAT { Tfloat } 

equ:
  | x = pat; EQUAL; ce = cexp
    { EqDef' (fst x, snd x, ce) }
  | x = pat; EQUAL; f = IDENT; les = par(ne_sep_list(COMMA, lexp))
	{ EqApp' (fst x, snd x, id f, les) }
  | x = pat; EQUAL; c = const; FBY; le = lexp
	{ EqFby' (fst x, snd x, c, le) }

pat: p = separated_pair(IDENT, COLONS, clock) { id' p }

clock:
  | BASE                          { Cbase }
  | c = clock; ON; x = IDENT      { Con (c, id x, Tbool, true) }
  | c = clock; ON; NOT; x = IDENT { Con (c, id x, Tbool, false) }

cexp:
  | MERGE; x = IDENT; ce1 = cexp; ce2 = cexp      { Emerge' (id x, ce1, ce2) }
  | IF; le = lexp; THEN; t = cexp; ELSE; f = cexp { Eite' (le, t, f) }
  | le = lexp                                     { Eexp' le }
	
lexp:
  | le = par(lexp)                     { le }
  | x = IDENT                          { Evar' (id x) }
  | c = const                          { Econst' c }
  | op = unop; le = lexp               { Eunop' (op, le) }
  | le1 = lexp; op = binop; le2 = lexp { Ebinop' (op, le1, le2) }
  | le = lexp; WHEN; x = IDENT         { Ewhen' (le, id x, true) }
  | le = lexp;  WHENNOT; x = IDENT     { Ewhen' (le, id x, false) }

unop:
  | SUB {Opposite}
  | NOT {Negation}

binop:  
  | ADD {Add}
  | SUB {Sub}
  | MUL {Mul}
  | DIV {Div}

const:
  | i = INT  { Op.Val (Vint (Int.repr (z_of_int i))) }
  | b = BOOL { Op.Vbool b }
  | f = FLOAT { let (v, fk) = elab_float_constant f in
				let f = convertFloat v fk in
				Op.Val (Vfloat f) }

%%
