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
   and Nicolas Halbwachs in the Lustre v6 reference manual (2016). */

/* TODO: tweak the priority of type casting, (1 + 2 : uint8)
         should give ((1 + 2) : uint8) ? */
/* TODO: tweak the priority of land? (x land y = 0) should give
 	  ((x land y) = 0) and not (x land (y = 0)) */

%{
From Velus Require Import Common.
From Velus Require Ident.
From Velus Require LustreAst.

(* Ensure correct Syntax module is loaded later (and not Obc.Syntax). *)
From Coq Require Import Program.Syntax.

From Coq Require Import String.
From Coq Require Import List.
Import ListNotations.

Definition true_id := Ident.str_to_pos "True"%string.
Definition false_id := Ident.str_to_pos "False"%string.
%}

%token<Common.ident * LustreAst.astloc> VAR_NAME
%token<Common.ident * LustreAst.astloc> ENUM_NAME
%token<LustreAst.constant * LustreAst.astloc> CONSTANT
(* %token<Common.ident * LustreAst.astloc> TRUE FALSE *)
%token<LustreAst.astloc> LEQ GEQ EQ NEQ LT GT PLUS MINUS STAR SLASH COLON COLONCOLON
%token<LustreAst.astloc> HASH
%token<LustreAst.astloc> BAR
%token<LustreAst.astloc> RARROW UNDERSCORE
%token<LustreAst.astloc> LSL LSR LAND LXOR LOR LNOT XOR NOT AND OR MOD
%token<LustreAst.astloc> IFTE THEN ELSE CASE OF

%token<LustreAst.astloc> LPAREN RPAREN COMMA SEMICOLON
(* %token<Common.ident * LustreAst.astloc> BOOL *)
%token<LustreAst.astloc> INT8 UINT8 INT16 UINT16 INT32 UINT32
  INT64 UINT64 FLOAT32 FLOAT64

%token<LustreAst.astloc> LET TEL NODE FUNCTION RETURNS VAR LAST FBY
%token<LustreAst.astloc> TYPE
%token<LustreAst.astloc> WHEN WHENOT MERGE ON ONOT DOT
%token<LustreAst.astloc> ASSERT

%token<LustreAst.astloc> RESET RESTART EVERY
%token<LustreAst.astloc> SWITCH END
%token<LustreAst.astloc> AUTOMATON INITIALLY OTHERWISE STATE DO UNTIL RESUME

%token<LustreAst.astloc> EOF

%type<list LustreAst.expression> primary_expression postfix_expression
    fby_expression unary_expression cast_expression
    multiplicative_expression additive_expression shift_expression
    when_expression relational_expression equality_expression AND_expression
    exclusive_OR_expression inclusive_OR_expression logical_AND_expression
    logical_OR_expression arrow_expression expression
%type<list Common.ident> constructor_list
%type<list (Common.ident * list LustreAst.expression)> branch_list
%type<list (Common.ident * list LustreAst.expression) * list LustreAst.expression> branch_list_with_default
%type<LustreAst.constant * LustreAst.astloc> enum
(* %type<LustreAst.constant * LustreAst.astloc> bool_constant *)
%type<LustreAst.constant * LustreAst.astloc> constant
%type<list LustreAst.expression> expression_list
%type<LustreAst.unary_operator * LustreAst.astloc> unary_operator
%type<LustreAst.var_decls> var_decl
%type<list Common.ident (* Reverse order *)> identifier_list
%type<LustreAst.type_name * LustreAst.astloc> type_name
%type<LustreAst.preclock> declared_clock
%type<LustreAst.clock> clock
%type<LustreAst.local_decls> last_var_decl
%type<LustreAst.local_decls> var_decl_list
%type<LustreAst.local_decls> local_var_decl
%type<LustreAst.local_decls> local_decl
%type<LustreAst.local_decls> local_decl_list
%type<LustreAst.var_decls (* Reverse order *)> parameter_list oparameter_list
%type<list Common.ident> pattern
%type<LustreAst.equation> equation
%type<LustreAst.block> block
%type<list LustreAst.block> blocks
%type<list (Common.ident * list LustreAst.block)> switch_branch_list
%type<list (list LustreAst.expression * Common.ident * LustreAst.astloc) * Common.ident> initially
%type<LustreAst.transition> transition
%type<list LustreAst.transition> transitions
%type<Common.ident * (list LustreAst.block * list LustreAst.transition)> auto_state
%type<list (Common.ident * (list LustreAst.block * list LustreAst.transition))> auto_state_list
%type<unit> optsemicolon optbar
%type<bool * LustreAst.astloc> node_or_function
%type<LustreAst.declaration> declaration
%type<list LustreAst.declaration> translation_unit

%start<list LustreAst.declaration> translation_unit_file
%%

(* Actual grammar *)

(* Expressions: taken directly from CompCert/C99 with the exceptions:
   - Casts are not written "(int8)e" but rather "(e : int8)" as in Scade.
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

(* bool_constant:
 * | b=TRUE
 *     { (LustreAst.CONST_ENUM (fst b), snd b) }
 * | b=FALSE
 *     { (LustreAst.CONST_ENUM (fst b), snd b) } *)

enum:
| c=ENUM_NAME
    { (LustreAst.CONST_ENUM (fst c), snd c) }
(* | b=bool_constant
 *     { b } *)

constant:
| cst=CONSTANT
    { cst }
| c=enum
    { c }

primary_expression:
| var=VAR_NAME
    { [LustreAst.VARIABLE (fst var) (snd var)] }
| LAST var=VAR_NAME
    { [LustreAst.LAST (fst var) (snd var)] }
| cst=constant
    { [LustreAst.CONSTANT (fst cst) (snd cst)] }
| loc=LPAREN expr=expression_list RPAREN
    { rev expr }

(* 6.5.2 *)
postfix_expression:
| expr=primary_expression
    { expr }
| fn=VAR_NAME LPAREN args=expression_list RPAREN
    { [LustreAst.APP (fst fn) (rev args) [] (snd fn)] }
| LPAREN RESTART fn=VAR_NAME EVERY e=expression RPAREN
  LPAREN args=expression_list RPAREN
    { [LustreAst.APP (fst fn) (rev args) e (snd fn)] }

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
    { [LustreAst.UNARY (fst op) expr (snd op)] }
| loc=HASH LPAREN args=expression_list RPAREN
    {
      (* Macro expand the Lustre # operator (mutual exclusion: at most
         one of the variable number of arguments may be true). Compare
         with "true" to ensure that non-bool arguments are properly
 	       treated. Is there a prettier way to do this?
 	       TODO: This should be done during elaboration. *)
       [LustreAst.BINARY
         LustreAst.LE
         [fold_right (fun es e => LustreAst.BINARY LustreAst.ADD [e] [es] loc)
 	       (LustreAst.CONSTANT (LustreAst.CONST_INT LustreAst.string_zero) loc)
 	       (map (fun e =>
                LustreAst.CASE [e]
                 [(Ident.Ids.true_id, [LustreAst.CONSTANT (LustreAst.CONST_INT LustreAst.string_one) loc]);
                  (Ident.Ids.false_id, [LustreAst.CONSTANT (LustreAst.CONST_INT LustreAst.string_zero) loc])] [] loc)
              args)]
 	    [LustreAst.CONSTANT (LustreAst.CONST_INT LustreAst.string_one) loc]
 	   loc]
     }

unary_operator:
| loc=MINUS
    { (LustreAst.MINUS, loc) }
| loc=LNOT
    { (LustreAst.NOT, loc) }
| loc=NOT
    { (LustreAst.BNOT, loc) }

(* 6.5.4 *)
cast_expression:
| expr=unary_expression
    { expr }
| LPAREN expr=cast_expression loc=COLON typ=type_name RPAREN
    { [LustreAst.CAST (fst typ) expr loc] }

(* Lustre fby operator *)
fby_expression:
| expr=cast_expression
    { expr }
| v0=cast_expression loc=FBY expr=fby_expression
    { [LustreAst.FBY v0 expr loc] }

(* 6.5.5 *)
multiplicative_expression:
| expr=fby_expression
    { expr }
| expr1=multiplicative_expression loc=STAR expr2=fby_expression
    { [LustreAst.BINARY LustreAst.MUL expr1 expr2 loc] }
| expr1=multiplicative_expression loc=SLASH expr2=fby_expression
    { [LustreAst.BINARY LustreAst.DIV expr1 expr2 loc] }
| expr1=multiplicative_expression loc=MOD expr2=fby_expression
    { [LustreAst.BINARY LustreAst.MOD expr1 expr2 loc] }

(* 6.5.6 *)
additive_expression:
| expr=multiplicative_expression
    { expr }
| expr1=additive_expression loc=PLUS expr2=multiplicative_expression
    { [LustreAst.BINARY LustreAst.ADD expr1 expr2 loc] }
| expr1=additive_expression loc=MINUS expr2=multiplicative_expression
    { [LustreAst.BINARY LustreAst.SUB expr1 expr2 loc] }

(* 6.5.7 *)
shift_expression:
| expr=additive_expression
    { expr }
| expr1=shift_expression loc=LSL expr2=additive_expression
    { [LustreAst.BINARY LustreAst.LSL expr1 expr2 loc] }
| expr1=shift_expression loc=LSR expr2=additive_expression
    { [LustreAst.BINARY LustreAst.LSR expr1 expr2 loc] }

(* Lustre when operators *)
when_expression:
| expr=shift_expression
    { expr }
| expr=when_expression loc=WHEN c=ENUM_NAME LPAREN id=VAR_NAME RPAREN
    { [LustreAst.WHEN expr (fst id) (fst c) loc] }
| expr=when_expression loc=WHEN id=VAR_NAME
    { [LustreAst.WHEN expr (fst id) true_id loc] }
| expr=when_expression loc=WHEN NOT id=VAR_NAME
    { [LustreAst.WHEN expr (fst id) false_id loc] }
| expr=when_expression loc=WHENOT id=VAR_NAME
    { [LustreAst.WHEN expr (fst id) false_id loc] }

(* 6.5.8 *)
relational_expression:
| expr=when_expression
    { expr }
| expr1=relational_expression loc=LT expr2=when_expression
    { [LustreAst.BINARY LustreAst.LT expr1 expr2 loc] }
| expr1=relational_expression loc=GT expr2=when_expression
    { [LustreAst.BINARY LustreAst.GT expr1 expr2 loc] }
| expr1=relational_expression loc=LEQ expr2=when_expression
    { [LustreAst.BINARY LustreAst.LE expr1 expr2 loc] }
| expr1=relational_expression loc=GEQ expr2=when_expression
    { [LustreAst.BINARY LustreAst.GE expr1 expr2 loc] }

(* 6.5.9 *)
equality_expression:
| expr=relational_expression
    { expr }
| expr1=equality_expression loc=EQ expr2=relational_expression
    { [LustreAst.BINARY LustreAst.EQ expr1 expr2 loc] }
| expr1=equality_expression loc=NEQ expr2=relational_expression
    { [LustreAst.BINARY LustreAst.NE expr1 expr2 loc] }

(* 6.5.10 *)
AND_expression:
| expr=equality_expression
    { expr }
| expr1=AND_expression loc=AND expr2=equality_expression
    { [LustreAst.BINARY LustreAst.BAND expr1 expr2 loc] }

(* 6.5.11 *)
exclusive_OR_expression:
| expr=AND_expression
    { expr }
| expr1=exclusive_OR_expression loc=LXOR expr2=AND_expression
    { [LustreAst.BINARY LustreAst.XOR expr1 expr2 loc] }
| expr1=exclusive_OR_expression loc=XOR expr2=AND_expression
    { [LustreAst.BINARY LustreAst.XOR expr1 expr2 loc] }

(* 6.5.12 *)
inclusive_OR_expression:
| expr=exclusive_OR_expression
    { expr }
| expr1=inclusive_OR_expression loc=LOR expr2=exclusive_OR_expression
    { [LustreAst.BINARY LustreAst.BOR expr1 expr2 loc] }

(* 6.5.13 *)
logical_AND_expression:
| expr=inclusive_OR_expression
    { expr }
| expr1=logical_AND_expression loc=LAND expr2=inclusive_OR_expression
    { [LustreAst.BINARY LustreAst.LAND expr1 expr2 loc] }

(* 6.5.14 *)
logical_OR_expression:
| expr=logical_AND_expression
    { expr }
| expr1=logical_OR_expression loc=OR expr2=logical_AND_expression
    { [LustreAst.BINARY LustreAst.LOR expr1 expr2 loc] }

(* Lustre Arrow Operator *)
arrow_expression:
| expr=logical_OR_expression
    { expr }
| e0=logical_OR_expression loc=RARROW e1=arrow_expression
    { [LustreAst.ARROW e0 e1 loc] }

branch_list:
| LPAREN c=ENUM_NAME RARROW expr=expression RPAREN
    { [(fst c, expr)] }
| LPAREN c=ENUM_NAME RARROW expr=expression RPAREN bs=branch_list
    { (fst c, expr) :: bs }

branch_list_with_default:
| LPAREN UNDERSCORE RARROW expr=expression RPAREN
    { [], expr }
| LPAREN c=ENUM_NAME RARROW expr=expression RPAREN
    { [(fst c, expr)], [] }
| LPAREN c=ENUM_NAME RARROW expr=expression RPAREN bs=branch_list_with_default
    { (fst c, expr) :: (fst bs), (snd bs) }

(* 6.5.15/16/17, 6.6 + Lustre merge operator *)
expression:
| expr=arrow_expression
    { expr }
| loc=IFTE expr1=expression THEN expr2=expression ELSE expr3=expression
    { [LustreAst.CASE expr1 [(true_id, expr2); (false_id, expr3)] [] loc] }
| loc=CASE expr=expression OF brs=branch_list_with_default
    { [LustreAst.CASE expr (fst brs) (snd brs) loc] }
| loc=MERGE LPAREN id=VAR_NAME SEMICOLON expr1=expression SEMICOLON expr2=expression RPAREN
    { [LustreAst.MERGE (fst id) [(true_id, expr1); (false_id, expr2)] loc] }
| loc=MERGE id=VAR_NAME bs=branch_list
    { [LustreAst.MERGE (fst id) bs loc] }

(* Declarations are much simpler than in C. We do not have arrays,
   structs/unions, or pointers. We do not have storage-class specifiers,
   type-qualifiers, or alignment specifiers. Nor are our type-specifiers lists
   (e.g., "unsigned short int"), since we use the type names from
   stdint.h/Scade (e.g., "uint_16"). *)

var_decl:
| ids=identifier_list loc=COLON ty=type_name clk=declared_clock
    { map (fun id => (id, (fst ty, clk, loc))) (rev ids) }

last_var_decl:
| vars=var_decl
   { map (fun '(id, (ty, ck, loc)) => (id, (ty, ck, [], loc))) vars }
| LAST id=VAR_NAME loc=COLON ty=type_name clk=declared_clock EQ e=expression
   { [(fst id, (fst ty, clk, e, loc))] }

var_decl_list:
| vars=last_var_decl
    { vars }
| vars_list=var_decl_list SEMICOLON vars=last_var_decl
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
    { (LustreAst.Tint8, loc) }
| loc=UINT8
    { (LustreAst.Tuint8, loc) }
| loc=INT16
    { (LustreAst.Tint16, loc) }
| loc=UINT16
    { (LustreAst.Tuint16, loc) }
| loc=INT32
    { (LustreAst.Tint32, loc) }
| loc=UINT32
    { (LustreAst.Tuint32, loc) }
| loc=INT64
    { (LustreAst.Tint64, loc) }
| loc=UINT64
    { (LustreAst.Tuint64, loc) }
| loc=FLOAT32
    { (LustreAst.Tfloat32, loc) }
| loc=FLOAT64
    { (LustreAst.Tfloat64, loc) }
| t=VAR_NAME
    { (LustreAst.Tenum_name (fst t), snd t) }

declared_clock:
| /* empty */
    { LustreAst.FULLCK LustreAst.BASE }
| WHEN c=ENUM_NAME LPAREN id=VAR_NAME RPAREN
    { LustreAst.WHENCK (fst id) (fst c) }
| WHEN id=VAR_NAME
    { LustreAst.WHENCK (fst id) true_id }
| WHEN NOT id=VAR_NAME
    { LustreAst.WHENCK (fst id) false_id }
| WHENOT id=VAR_NAME
    { LustreAst.WHENCK (fst id) false_id }
| COLONCOLON clk=clock
    { LustreAst.FULLCK clk }

clock:
| DOT
    { LustreAst.BASE }
| clk=clock ON c=ENUM_NAME LPAREN id=VAR_NAME RPAREN
    { LustreAst.ON clk (fst id) (fst c) }
| clk=clock ON id=VAR_NAME
    { LustreAst.ON clk (fst id) true_id }
| clk=clock ONOT id=VAR_NAME
    { LustreAst.ON clk (fst id) false_id }

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
| pat=pattern loc=EQ exp=expression
    { (rev pat, exp, loc) }
| LPAREN pat=pattern RPAREN loc=EQ exp=expression
    { (rev pat, exp, loc) }

switch_branch_list:
| BAR c=ENUM_NAME RARROW blk=blocks
    { [(fst c, blk)] }
| BAR c=ENUM_NAME RARROW blk=blocks bs=switch_branch_list
    { (fst c, blk) :: bs }

initially:
| c=ENUM_NAME
  { ([], fst c) }
| OTHERWISE c=ENUM_NAME
  { ([], fst c) }
| loc=IFTE e=expression THEN c=ENUM_NAME SEMICOLON ini=initially
  { let '(ini, oth) := ini in ((e, fst c, loc)::ini, oth) }

transition:
| loc=UNTIL e=expression RESUME c=ENUM_NAME
  { (e, (fst c, false), loc) }
| loc=UNTIL e=expression RESTART c=ENUM_NAME
  { (e, (fst c, true), loc) }

transitions:
| /* empty */
  { [] }
| tr=transition
  { [tr] }
| tr=transition SEMICOLON trs=transitions
  { tr::trs }

auto_state:
| loc=STATE c=ENUM_NAME DO blks=blocks trs=transitions
  { (fst c, (blks, trs)) }

auto_state_list:
| st=auto_state { [st] }
| st=auto_state sts=auto_state_list { st::sts }

block:
| eq=equation
   { LustreAst.BEQ eq } 
| RESET blks=blocks loc=EVERY er=expression
   { LustreAst.BRESET blks er loc }
| loc=SWITCH ec=expression brs=switch_branch_list END
   { LustreAst.BSWITCH ec brs loc }
| loc=AUTOMATON INITIALLY ini=initially states=auto_state_list END
   { LustreAst.BAUTO ini states loc }
| locals=local_decl_list loc=LET blks=blocks TEL
   { LustreAst.BLOCAL locals blks loc }

blocks:
| /* empty */
    { [] }
| blk=block
    { [blk] }
| blk=block SEMICOLON blks=blocks
    { blk::blks }
|  ASSERT expression SEMICOLON blks=blocks
    { blks (* ignore assert statements for now *) }

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

constructor_list:
| id=ENUM_NAME
    { [fst id] }
| id=ENUM_NAME BAR idl=constructor_list
    { fst id :: idl }

optbar:
| /* empty */
    { () }
| BAR
    { () }

declaration:
| is_node=node_or_function id=VAR_NAME
  LPAREN iparams=oparameter_list RPAREN optsemicolon
  RETURNS LPAREN oparams=oparameter_list RPAREN optsemicolon
  locals=local_decl_list loc=LET blks=blocks TEL optsemicolon
    { LustreAst.NODE
        (fst id) (fst is_node) iparams oparams (LustreAst.BLOCAL locals blks loc) (snd is_node) }
| loc=TYPE id=VAR_NAME EQ optbar cs=constructor_list
    { LustreAst.TYPE (fst id) cs loc }

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
