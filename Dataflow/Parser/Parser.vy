/* *********************************************************************/
/*                                                                     */
/*                    The Velus Lustre compiler                        */
/*                                                                     */
/*  Copyright Institut National de Recherche en Informatique et en     */
/*  Automatique.  All rights reserved.  This file is distributed       */
/*  under the terms of the GNU General Public License as published by  */
/*  the Free Software Foundation, either version 2 of the License, or  */
/*  (at your option) any later version.  This file is also distributed */
/*  under the terms of the INRIA Non-Commercial License Agreement.     */
/*                                                                     */
/* *********************************************************************/

/* This parser draws on the work of Jacques-Henri Jourdan for the CompCert
   project (CompCert/cparser/Parser.vy), and of Erwan Jahier, Pascal Raymond,
   and Nicolas Halbwachs in the Lustre v6 reference manual (2016). */

%{
Require Import Rustre.Dataflow.Parser.Ast.

(* Ensure correct Syntax module is loaded later (and not Obc.Syntax). *)
Require Import Coq.Program.Syntax.
%}

%token<string * astloc> VAR_NAME
%token<constant * astloc> CONSTANT
%token<astloc> LEQ GEQ EQ NEQ LT GT PLUS MINUS STAR SLASH COLON
%token<astloc> LSL LSR LAND LXOR LOR LNOT XOR NOT AND OR MOD
%token<astloc> IF THEN ELSE

%token<astloc> LPAREN RPAREN COMMA SEMICOLON
%token<astloc> BOOL INT8_T UINT8_T INT16_T UINT16_T INT32_T UINT32_T
  INT64_T UINT64_T FLOAT DOUBLE

%token<astloc> LET TEL NODE RETURNS VAR FBY
%token<astloc> WHEN WHENOT MERGE ON ONOT DOT

%token EOF

%type<expression> primary_expression postfix_expression
    fby_expression unary_expression cast_expression
    multiplicative_expression additive_expression shift_expression
    when_expression relational_expression equality_expression AND_expression
    exclusive_OR_expression inclusive_OR_expression logical_AND_expression
    logical_OR_expression expression
%type<list expression> argument_expression_list 
%type<unary_operator * astloc> unary_operator
%type<var_decls> var_decl
%type<var_decls> var_decl_list
%type<var_decls> local_var_decl
%type<list string (* Reverse order *)> identifier_list
%type<type_name * astloc> type_name
%type<clock> declared_clock
%type<clock> clock
%type<var_decls> local_decl
%type<var_decls> local_decl_list
%type<var_decls (* Reverse order *)> parameter_list
%type<list string> pattern
%type<equation> equation
%type<list equation> equations
%type<unit> optsemicolon
%type<declaration> declaration
%type<list declaration> translation_unit

%start<list declaration> translation_unit_file
%%

(* Actual grammar *)

(* Expressions: taken directly from CompCert/C99 with the exceptions:
   - Casts are not written "(int8_t)e" but rather "(e : int8_t)" as in Scade.
     This differs from Lustre which has "int e" and "real e".

   - For operators, the Scade/Lustre syntax is used (the middle column below),
     but we keep the structure of the CompCert parsing rules (i.e., we adopt
     the priorities of C99).

        C operator          Scade             Lustre
        ----------        ---------         ----------
           &&                and                 and
           ||                or                  or
        (e?e1:e2)         if/then/else       if/then/else
          (int)/             /                  div
           ==               =                  =
           !=                <>                  <>
           !                 not                 not
           %                 mod                 mod
           ^               lxor, xor          xor, ^
           ~                 lnot                
           <<                lsl
           >>                lsr
           &                 land
           |                 lor                 |

      There is no real difference between not/lnot, and/land, or/lor, lxor/xor
      since the bool type is a kind of 1-bit integer (even if it is stored in 8
      bits).

   - Expressions may contain the fby and merge operators.
*)

primary_expression:
| var=VAR_NAME
    { VARIABLE (fst var) (snd var) }
| cst=CONSTANT
    { CONSTANT (fst cst) (snd cst) }
| loc=LPAREN expr=expression RPAREN
    { expr }

(* 6.5.2 *)
postfix_expression:
| expr=primary_expression
    { expr }
| fn=VAR_NAME LPAREN args=argument_expression_list RPAREN
    { CALL (fst fn) (rev args) (snd fn) }

(* Semantic value is in reverse order. *)
argument_expression_list:
| expr=expression
    { [expr] }
| exprs=argument_expression_list COMMA expr=expression
    { expr::exprs }

(* Lustre fby operator *)
fby_expression:
| expr=postfix_expression
    { expr }
| cst=CONSTANT loc=FBY expr=postfix_expression
    { FBY (fst cst) expr loc }

(* 6.5.3 *)
unary_expression:
| expr=fby_expression
    { expr }
| op=unary_operator expr=cast_expression
    { UNARY (fst op) expr (snd op) }

unary_operator:
| loc=PLUS
    { (PLUS, loc) }
| loc=MINUS
    { (MINUS, loc) }
| loc=LNOT
    { (BNOT, loc) }
| loc=NOT
    { (NOT, loc) }

(* 6.5.4 *)
cast_expression:
| expr=unary_expression
    { expr }
| LPAREN expr=cast_expression loc=COLON typ=type_name RPAREN
    { CAST (fst typ) expr loc }

(* 6.5.5 *)
multiplicative_expression:
| expr=cast_expression
    { expr }
| expr1=multiplicative_expression loc=STAR expr2=cast_expression
    { BINARY MUL expr1 expr2 loc }
| expr1=multiplicative_expression loc=SLASH expr2=cast_expression
    { BINARY DIV expr1 expr2 loc }
| expr1=multiplicative_expression loc=MOD expr2=cast_expression
    { BINARY MOD expr1 expr2 loc }

(* 6.5.6 *)
additive_expression:
| expr=multiplicative_expression
    { expr }
| expr1=additive_expression loc=PLUS expr2=multiplicative_expression
    { BINARY ADD expr1 expr2 loc }
| expr1=additive_expression loc=MINUS expr2=multiplicative_expression
    { BINARY SUB expr1 expr2 loc }

(* 6.5.7 *)
shift_expression:
| expr=additive_expression
    { expr }
| expr1=shift_expression loc=LSL expr2=additive_expression
    { BINARY LSL expr1 expr2 loc }
| expr1=shift_expression loc=LSR expr2=additive_expression
    { BINARY LSR expr1 expr2 loc }

(* Lustre when operators *)
when_expression:
| expr=shift_expression
    { expr }
| expr=when_expression loc=WHEN id=VAR_NAME
    { WHEN expr true (fst id) loc }
| expr=when_expression loc=WHENOT id=VAR_NAME
    { WHEN expr false (fst id) loc }

(* 6.5.8 *)
relational_expression:
| expr=when_expression
    { expr }
| expr1=relational_expression loc=LT expr2=when_expression
    { BINARY LT expr1 expr2 loc }
| expr1=relational_expression loc=GT expr2=when_expression
    { BINARY GT expr1 expr2 loc }
| expr1=relational_expression loc=LEQ expr2=when_expression
    { BINARY LE expr1 expr2 loc }
| expr1=relational_expression loc=GEQ expr2=when_expression
    { BINARY GE expr1 expr2 loc }

(* 6.5.9 *)
equality_expression:
| expr=relational_expression
    { expr }
| expr1=equality_expression loc=EQ expr2=relational_expression
    { BINARY EQ expr1 expr2 loc }
| expr1=equality_expression loc=NEQ expr2=relational_expression
    { BINARY NE expr1 expr2 loc }

(* 6.5.10 *)
AND_expression:
| expr=equality_expression
    { expr }
| expr1=AND_expression loc=LAND expr2=equality_expression
    { BINARY BAND expr1 expr2 loc }

(* 6.5.11 *)
exclusive_OR_expression:
| expr=AND_expression
    { expr }
| expr1=exclusive_OR_expression loc=LXOR expr2=AND_expression
    { BINARY XOR expr1 expr2 loc }
| expr1=exclusive_OR_expression loc=XOR expr2=AND_expression
    { BINARY XOR expr1 expr2 loc }

(* 6.5.12 *)
inclusive_OR_expression:
| expr=exclusive_OR_expression
    { expr }
| expr1=inclusive_OR_expression loc=LOR expr2=exclusive_OR_expression
    { BINARY BOR expr1 expr2 loc }

(* 6.5.13 *)
logical_AND_expression:
| expr=inclusive_OR_expression
    { expr }
| expr1=logical_AND_expression loc=AND expr2=inclusive_OR_expression
    { BINARY LAND expr1 expr2 loc }

(* 6.5.14 *)
logical_OR_expression:
| expr=logical_AND_expression
    { expr }
| expr1=logical_OR_expression loc=OR expr2=logical_AND_expression
    { BINARY LOR expr1 expr2 loc }

(* 6.5.15/16/17, 6.6 + Lustre merge operator *)
expression:
| expr=logical_OR_expression
    { expr }
| loc=IF expr1=expression THEN expr2=expression ELSE expr3=expression
    { IFTE expr1 expr2 expr3 loc }
| loc=MERGE id=VAR_NAME expr1=primary_expression expr2=primary_expression
    { MERGE (fst id) expr1 expr2 loc }

(* Declarations are much simpler than in C. We do not have arrays,
   structs/unions, or pointers. We do not have storage-class specifiers,
   type-qualifiers, or alignment specifiers. Nor are our type-specifiers lists
   (e.g., "unsigned short int"), since we use the type names from
   stdint.h/Scade (e.g., "uint_16"). *)

var_decl:
| ids=identifier_list COLON ty=type_name clk=declared_clock
    { map (fun id=> (id, fst ty, clk)) ids }

var_decl_list:
| vars=var_decl
    { vars }
| vars_list=var_decl_list SEMICOLON vars=var_decl
    { vars ++ vars_list }

local_var_decl:
| loc=VAR vars_list=var_decl_list SEMICOLON
    { vars_list }

identifier_list:
| id=VAR_NAME
    { [fst id] }
| idl=identifier_list COMMA id=VAR_NAME
    { fst id :: idl }

type_name:
| loc=INT8_T
    { (Tint8, loc) }
| loc=UINT8_T
    { (Tuint8, loc) }
| loc=INT16_T
    { (Tint16, loc) }
| loc=UINT16_T
    { (Tuint16, loc) }
| loc=INT32_T
    { (Tint32, loc) }
| loc=UINT32_T
    { (Tuint32, loc) }
| loc=INT64_T
    { (Tint64, loc) }
| loc=UINT64_T
    { (Tuint64, loc) }
| loc=FLOAT
    { (Tfloat, loc) }
| loc=DOUBLE
    { (Tdouble, loc) }
| loc=BOOL
    { (Tbool, loc) }

declared_clock:
| /* empty */
    { BASE }
| WHEN clk=clock
    { clk }

clock:
| DOT
    { BASE }
| clk=clock ON id=VAR_NAME
    { ON clk true (fst id) }
| clk=clock ONOT id=VAR_NAME
    { ON clk false (fst id) }

local_decl:
| vd=local_var_decl
    { vd }

local_decl_list:
| /* empty */
    { [] }
| dl=local_decl_list d=local_decl
    { d ++ dl }

parameter_list:
| pl=var_decl_list
    { pl }

(* Semantic value is in reverse order. *)
pattern:
| id=VAR_NAME
    { [fst id] }
| pat=pattern COMMA id=VAR_NAME
    { fst id::pat }

equation:
| pat=pattern loc=EQ exp=expression SEMICOLON
    { (rev pat, exp, loc) }
| LPAREN pat=pattern RPAREN loc=EQ exp=expression SEMICOLON
    { (rev pat, exp, loc) }

equations:
| /* empty */
    { [] }
| eqs=equations eq=equation
    { eq::eqs }

optsemicolon:
| /* empty */
    { () }
| SEMICOLON
    { () }

declaration:
| loc=NODE id=VAR_NAME LPAREN iparams=parameter_list RPAREN optsemicolon
  RETURNS LPAREN oparams=parameter_list RPAREN SEMICOLON
  locals=local_decl_list LET eqns=equations TEL
    { NODE (fst id) iparams oparams locals eqns }

translation_unit:
| def=declaration
    { [def] }
| defq=translation_unit deft=declaration
    { deft::defq }

translation_unit_file:
| lst=translation_unit EOF
    { lst }
| EOF
    { [] }

