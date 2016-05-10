%{

(* open Global *)
open Common
open Location
open DF2CL.SynDF
open Nelist
open Interface
open Integers
open Camlcoq
	   
let id = (* SymTable.id Global.table *)intern_string

type lexp' =
  | Econst' of Op.coq_val
  | Evar' of ident
  | Eunop' of unary_op' * lexp
  | Ebinop' of binary_op' * lexp * lexp

let make_exp le ty = match le with
  | Econst' v -> Econst (v, ty)
  | Evar' x -> Evar (x, ty)
  | Eunop' (op, le) -> Eunop (op, le, ty)
  | Ebinop' (op, le1, le2) -> Ebinop (op, le1, le2, ty)

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
(* let rec exp_to_const e = *)
(*   match e with *)
(*     | Aexp(_, Econst c) -> c *)
(*     | _ -> raise Parse_error *)
%}

%token LPAREN RPAREN COLON COLONS SEMICOL 
%token EQUAL COMMA LET TEL ON BASE
%token <string> IDENT
%token <int> INT
%token <float> FLOAT
%token <bool> BOOL
%token NODE RETURNS
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
%type <DF2CL.SynDF.global> program

%%

program:
  | node_decs EOF { $1 }
;

node_decs:
  | /* empty */        { [] }
  | node_dec node_decs { $1 :: $2 }
;

node_dec:
  | NODE IDENT LPAREN in_params RPAREN 
    RETURNS LPAREN out_param RPAREN SEMICOL
    LET equs TEL SEMICOL
      { { n_name = id $2;
	  n_input = $4;
	  n_output = $8;
	  n_eqs    = $12 } }
;

in_params:
  | ioparams { $1 }
;

out_param:
  | param { $1 }
;

ioparams:
  | param                { Coq_nebase $1 }
  | param COMMA ioparams { Coq_necons ($1, $3) }
;

param:
  | IDENT COLON typ { (id $1, $3) }
;

typ:
  | TBOOL  { Tbool }
  | TINT   { Tint }
  | TFLOAT { Tfloat } 
;

(* opt_clock: *)
(*   | /* empty */ { Clocks.Cbase } *)
(*   | LBRACKET ck RBRACKET { $2 } *)
(* ; *)

clock:
  | BASE               { Cbase }
  | clock ON IDENT     { Con ($1, id $3, Interface.Tbool, true) }
  | clock ON NOT IDENT { Con ($1, id $4, Interface.Tbool, false) }
;


equs:
  | { [] }
  | IDENT COLONS clock EQUAL cexp SEMICOL equs                     { EqDef (id $1, $3, $5) :: $7 }
  | IDENT COLONS clock EQUAL IDENT node_app COLON typ SEMICOL equs { EqApp (id $1, $3, id $5, $6, $8) :: $10 }
  | IDENT COLONS clock EQUAL const FBY lexp SEMICOL equs           { EqFby (id $1, $3, $5, $7) :: $9 }
;

cexp:
  | MERGE LPAREN param RPAREN LPAREN cexp RPAREN LPAREN cexp RPAREN { Emerge (fst $3, snd $3, $6, $9) }
  | IF lexp THEN cexp ELSE cexp                       { Eite ($2, $4, $6) }
  | lexp                                              { Eexp $1 }
;
	
lexp:
  | LPAREN lexp RPAREN             { $2 }
  | LPAREN lexp_e COLON typ RPAREN { make_exp $2 $4 }
  | lexp WHEN IDENT                { Ewhen ($1, id $3, true) }
  | lexp WHENNOT IDENT             { Ewhen ($1, id $3, false) }
;
	
lexp_e:
  | IDENT                   { Evar' (id $1) }
  | const                   { Econst' $1 }
  | LPAREN lexp_e RPAREN    { $2 }
  | unop lexp               { Eunop' ($1, $2) }
  | lexp binop lexp         { Ebinop' ($2, $1, $3) }
;

unop:
  | SUB {Opposite}
  | NOT {Negation}
;

binop:  
  | ADD {Add}
  | SUB {Sub}
  | MUL {Mul}
  | DIV {Div}
  
node_app:
  | LPAREN ne_lexps RPAREN { $2 }
;
	
ne_lexps:
  | lexp                { Coq_nebase $1 }
  | lexp COMMA ne_lexps { Coq_necons ($1, $3)} 
;

const:
  | INT { Op.Val (Vint (Int.repr (z_of_int $1))) }
  | BOOL { Op.Vbool $1 }
;

%%
