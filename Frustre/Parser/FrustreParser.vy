/* *********************************************************************/
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
   and Nicolas Halbwachs in the Frustre v6 reference manual (2016). */

/* TODO: tweak the priority of type casting, (1 + 2 : uint8)
         should give ((1 + 2) : uint8) ? */
/* TODO: tweak the priority of land? (x land y = 0) should give
 	  ((x land y) = 0) and not (x land (y = 0)) */

%{
Require Velus.Frustre.Parser.FrustreAst.

(* Ensure correct Syntax module is loaded later (and not Obc.Syntax). *)
Require Import Coq.Program.Syntax.

Require Import List.
Import ListNotations.
%}

%token<FrustreAst.ident * FrustreAst.astloc> VAR_NAME
%token<FrustreAst.constant * FrustreAst.astloc> CONSTANT
%token<FrustreAst.astloc> TRUE FALSE
%token<FrustreAst.astloc> LEQ GEQ EQ NEQ LT GT PLUS MINUS STAR SLASH COLON COLONCOLON
%token<FrustreAst.astloc> RARROW
%token<FrustreAst.astloc> LSL LSR LAND LXOR LOR LNOT XOR NOT AND OR MOD
%token<FrustreAst.astloc> IF THEN ELSE

%token<FrustreAst.astloc> LPAREN RPAREN COMMA SEMICOLON
%token<FrustreAst.astloc> BOOL INT8 UINT8 INT16 UINT16 INT32 UINT32
  INT64 UINT64 FLOAT32 FLOAT64

%token<FrustreAst.astloc> LET TEL NODE FUNCTION RETURNS VAR FBY
%token<FrustreAst.astloc> WHEN WHENOT MERGE ON ONOT DOT
%token<FrustreAst.astloc> ASSERT

%token<FrustreAst.astloc> EOF

%type<list FrustreAst.expression> primary_expression postfix_expression
    fby_expression unary_expression cast_expression
    multiplicative_expression additive_expression shift_expression
    when_expression relational_expression equality_expression AND_expression
    exclusive_OR_expression inclusive_OR_expression logical_AND_expression
    logical_OR_expression expression
%type<FrustreAst.constant * FrustreAst.astloc> bool_constant
%type<FrustreAst.constant * FrustreAst.astloc> constant
%type<list FrustreAst.expression> expression_list
%type<FrustreAst.unary_operator * FrustreAst.astloc> unary_operator
%type<FrustreAst.var_decls> var_decl
%type<FrustreAst.var_decls> var_decl_list
%type<FrustreAst.var_decls> local_var_decl
%type<list FrustreAst.ident (* Reverse order *)> identifier_list
%type<FrustreAst.type_name * FrustreAst.astloc> type_name
%type<FrustreAst.preclock> declared_clock
%type<FrustreAst.clock> clock
%type<FrustreAst.var_decls> local_decl
%type<FrustreAst.var_decls> local_decl_list
%type<FrustreAst.var_decls (* Reverse order *)> parameter_list oparameter_list
%type<list FrustreAst.ident> pattern
%type<FrustreAst.equation> equation
%type<list FrustreAst.equation> equations
%type<unit> optsemicolon
%type<bool * FrustreAst.astloc> node_or_function
%type<FrustreAst.declaration> declaration
%type<list FrustreAst.declaration> translation_unit

%start<list FrustreAst.declaration> translation_unit_file
%%

(* Actual grammar *)

(* Expressions: taken directly from CompCert/C99 with the exceptions:
   - Casts are not written "(int8)e" but rather "(e : int8)" as in Scade.
     This differs from Frustre which has "int e" and "real e".

   - For operators, the Scade/Frustre syntax is used (the middle column below),
     but we keep the structure of the CompCert parsing rules (i.e., we adopt
     the priorities of C99).

        C operator          Scade             Frustre
        ----------        ---------         ----------
           &&                and                 and
           ||                or                  or
        (e?e1:e2)         if/then/else       if/then/else
          (int)/             /                  div
           ==                =                   =
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

bool_constant:
| loc=TRUE
    { (FrustreAst.CONST_BOOL true, loc) }
| loc=FALSE
    { (FrustreAst.CONST_BOOL false, loc) }

constant:
| cst=CONSTANT
    { cst }
| cst=bool_constant
    { cst }

primary_expression:
| var=VAR_NAME
    { [FrustreAst.VARIABLE (fst var) (snd var)] }
| cst=constant
    { [FrustreAst.CONSTANT (fst cst) (snd cst)] }
| loc=LPAREN expr=expression_list RPAREN
    { rev expr }

(* 6.5.2 *)
postfix_expression:
| expr=primary_expression
    { expr }
| fn=VAR_NAME LPAREN args=expression_list RPAREN
    { [FrustreAst.APP (fst fn) (rev args) (snd fn)] }

(* Semantic value is in reverse order. *)
expression_list:
| expr=expression
    { expr }
| exprs=expression_list COMMA expr=expression
    { expr ++ exprs }

(* 6.5.3 *)
unary_expression:
| expr=postfix_expression
    { expr }
| op=unary_operator expr=cast_expression
    { [FrustreAst.UNARY (fst op) expr (snd op)] }

unary_operator:
| loc=MINUS
    { (FrustreAst.MINUS, loc) }
| loc=LNOT
    { (FrustreAst.NOT, loc) }
| loc=NOT
    { (FrustreAst.BNOT, loc) }

(* 6.5.4 *)
cast_expression:
| expr=unary_expression
    { expr }
| LPAREN expr=cast_expression loc=COLON typ=type_name RPAREN
    { [FrustreAst.CAST (fst typ) expr loc] }

(* Frustre fby operator *)
fby_expression:
| expr=cast_expression
    { expr }
| v0=cast_expression loc=FBY expr=fby_expression
    { [FrustreAst.FBY v0 expr loc] }

(* 6.5.5 *)
multiplicative_expression:
| expr=fby_expression
    { expr }
| expr1=multiplicative_expression loc=STAR expr2=fby_expression
    { [FrustreAst.BINARY FrustreAst.MUL expr1 expr2 loc] }
| expr1=multiplicative_expression loc=SLASH expr2=fby_expression
    { [FrustreAst.BINARY FrustreAst.DIV expr1 expr2 loc] }
| expr1=multiplicative_expression loc=MOD expr2=fby_expression
    { [FrustreAst.BINARY FrustreAst.MOD expr1 expr2 loc] }

(* 6.5.6 *)
additive_expression:
| expr=multiplicative_expression
    { expr }
| expr1=additive_expression loc=PLUS expr2=multiplicative_expression
    { [FrustreAst.BINARY FrustreAst.ADD expr1 expr2 loc] }
| expr1=additive_expression loc=MINUS expr2=multiplicative_expression
    { [FrustreAst.BINARY FrustreAst.SUB expr1 expr2 loc] }

(* 6.5.7 *)
shift_expression:
| expr=additive_expression
    { expr }
| expr1=shift_expression loc=LSL expr2=additive_expression
    { [FrustreAst.BINARY FrustreAst.LSL expr1 expr2 loc] }
| expr1=shift_expression loc=LSR expr2=additive_expression
    { [FrustreAst.BINARY FrustreAst.LSR expr1 expr2 loc] }

(* Frustre when operators *)
when_expression:
| expr=shift_expression
    { expr }
| expr=when_expression loc=WHEN id=VAR_NAME
    { [FrustreAst.WHEN expr (fst id) true loc] }
| expr=when_expression loc=WHEN NOT id=VAR_NAME
    { [FrustreAst.WHEN expr (fst id) false loc] }
| expr=when_expression loc=WHENOT id=VAR_NAME
    { [FrustreAst.WHEN expr (fst id) false loc] }

(* 6.5.8 *)
relational_expression:
| expr=when_expression
    { expr }
| expr1=relational_expression loc=LT expr2=when_expression
    { [FrustreAst.BINARY FrustreAst.LT expr1 expr2 loc] }
| expr1=relational_expression loc=GT expr2=when_expression
    { [FrustreAst.BINARY FrustreAst.GT expr1 expr2 loc] }
| expr1=relational_expression loc=LEQ expr2=when_expression
    { [FrustreAst.BINARY FrustreAst.LE expr1 expr2 loc] }
| expr1=relational_expression loc=GEQ expr2=when_expression
    { [FrustreAst.BINARY FrustreAst.GE expr1 expr2 loc] }

(* 6.5.9 *)
equality_expression:
| expr=relational_expression
    { expr }
| expr1=equality_expression loc=EQ expr2=relational_expression
    { [FrustreAst.BINARY FrustreAst.EQ expr1 expr2 loc] }
| expr1=equality_expression loc=NEQ expr2=relational_expression
    { [FrustreAst.BINARY FrustreAst.NE expr1 expr2 loc] }

(* 6.5.10 *)
AND_expression:
| expr=equality_expression
    { expr }
| expr1=AND_expression loc=LAND expr2=equality_expression
    { [FrustreAst.BINARY FrustreAst.BAND expr1 expr2 loc] }

(* 6.5.11 *)
exclusive_OR_expression:
| expr=AND_expression
    { expr }
| expr1=exclusive_OR_expression loc=LXOR expr2=AND_expression
    { [FrustreAst.BINARY FrustreAst.XOR expr1 expr2 loc] }
| expr1=exclusive_OR_expression loc=XOR expr2=AND_expression
    { [FrustreAst.BINARY FrustreAst.XOR expr1 expr2 loc] }

(* 6.5.12 *)
inclusive_OR_expression:
| expr=exclusive_OR_expression
    { expr }
| expr1=inclusive_OR_expression loc=LOR expr2=exclusive_OR_expression
    { [FrustreAst.BINARY FrustreAst.BOR expr1 expr2 loc] }

(* 6.5.13 *)
logical_AND_expression:
| expr=inclusive_OR_expression
    { expr }
| expr1=logical_AND_expression loc=AND expr2=inclusive_OR_expression
    { [FrustreAst.BINARY FrustreAst.LAND expr1 expr2 loc] }

(* 6.5.14 *)
logical_OR_expression:
| expr=logical_AND_expression
    { expr }
| expr1=logical_OR_expression loc=OR expr2=logical_AND_expression
    { [FrustreAst.BINARY FrustreAst.LOR expr1 expr2 loc] }

(* 6.5.15/16/17, 6.6 + Frustre merge operator *)
expression:
| expr=logical_OR_expression
    { expr }
| loc=IF expr1=expression THEN expr2=expression ELSE expr3=expression
    { [FrustreAst.IFTE expr1 expr2 expr3 loc] }
| loc=MERGE id=VAR_NAME expr1=primary_expression expr2=primary_expression
    { [FrustreAst.MERGE (fst id) expr1 expr2 loc] }
| loc=MERGE id=VAR_NAME LPAREN TRUE  RARROW expr1=expression RPAREN
			LPAREN FALSE RARROW expr2=expression RPAREN
    { [FrustreAst.MERGE (fst id) expr1 expr2 loc] }

(* Declarations are much simpler than in C. We do not have arrays,
   structs/unions, or pointers. We do not have storage-class specifiers,
   type-qualifiers, or alignment specifiers. Nor are our type-specifiers lists
   (e.g., "unsigned short int"), since we use the type names from
   stdint.h/Scade (e.g., "uint_16"). *)

var_decl:
| ids=identifier_list loc=COLON ty=type_name clk=declared_clock
    { map (fun id=> (id, (fst ty, clk, loc))) (rev ids) }

var_decl_list:
| vars=var_decl
    { vars }
| vars_list=var_decl_list SEMICOLON vars=var_decl
    { vars_list ++ vars }

local_var_decl:
| loc=VAR vars_list=var_decl_list SEMICOLON
    { vars_list }

identifier_list:
| id=VAR_NAME
    { [fst id] }
| idl=identifier_list COMMA id=VAR_NAME
    { fst id :: idl }

type_name:
| loc=INT8
    { (FrustreAst.Tint8, loc) }
| loc=UINT8
    { (FrustreAst.Tuint8, loc) }
| loc=INT16
    { (FrustreAst.Tint16, loc) }
| loc=UINT16
    { (FrustreAst.Tuint16, loc) }
| loc=INT32
    { (FrustreAst.Tint32, loc) }
| loc=UINT32
    { (FrustreAst.Tuint32, loc) }
| loc=INT64
    { (FrustreAst.Tint64, loc) }
| loc=UINT64
    { (FrustreAst.Tuint64, loc) }
| loc=FLOAT32
    { (FrustreAst.Tfloat32, loc) }
| loc=FLOAT64
    { (FrustreAst.Tfloat64, loc) }
| loc=BOOL
    { (FrustreAst.Tbool, loc) }

declared_clock:
| /* empty */
    { FrustreAst.FULLCK FrustreAst.BASE }
| WHEN id=VAR_NAME
    { FrustreAst.WHENCK (fst id) true }
| WHEN NOT id=VAR_NAME
    { FrustreAst.WHENCK (fst id) false }
| WHENOT id=VAR_NAME
    { FrustreAst.WHENCK (fst id) false }
| COLONCOLON clk=clock
    { FrustreAst.FULLCK clk }

clock:
| DOT
    { FrustreAst.BASE }
| clk=clock ON id=VAR_NAME
    { FrustreAst.ON clk (fst id) true }
| clk=clock ONOT id=VAR_NAME
    { FrustreAst.ON clk (fst id) false }

local_decl:
| vd=local_var_decl
    { vd }

local_decl_list:
| /* empty */
    { [] }
| dl=local_decl_list d=local_decl
    { d ++ dl }

parameter_list:
| vars=var_decl
    { vars }
| vars_list=parameter_list SEMICOLON vars=var_decl
    { vars_list ++ vars }

oparameter_list:
| /* empty */
    { [] }
| vars_list=parameter_list
    { vars_list }

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
| eqs=equations ASSERT expression SEMICOLON
    { eqs (* ignore assert statements for now *) }

optsemicolon:
| /* empty */
    { () }
| SEMICOLON
    { () }

node_or_function:
| loc=NODE
    { (true, loc) }
| loc=FUNCTION
    { (false, loc) }

declaration:
| is_node=node_or_function id=VAR_NAME
  LPAREN iparams=oparameter_list RPAREN optsemicolon
  RETURNS LPAREN oparams=oparameter_list RPAREN optsemicolon
  locals=local_decl_list LET eqns=equations TEL optsemicolon
    { FrustreAst.NODE
        (fst id) (fst is_node) iparams oparams locals eqns (snd is_node) }

translation_unit:
| def=declaration
    { [def] }
| defq=translation_unit deft=declaration
    { deft::defq }

translation_unit_file:
| lst=translation_unit EOF
    { List.rev lst }
| EOF
    { [] }
