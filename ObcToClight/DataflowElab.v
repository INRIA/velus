Require Import Rustre.Common.
Require Import Rustre.Operators.

Require Import Rustre.Dataflow.
Require Import Rustre.Dataflow.Parser.Ast.

Require Import Rustre.ObcToClight.Interface.
Require Import Rustre.Ident.

Module Export OpAux := OperatorsAux Interface.Op.
Module Export Syn := SyntaxFun Ident.Ids Interface.Op.

(* Elaborate an AST into a well-typed Dataflow program. *)

(* CompCert: cparser/Elab: elab_int_constant + cfrontend/C2C: convertIkind *)
Axiom elab_const_int : astloc -> string -> const.
(* CompCert: cparser/Elab: elab_float_constant + cfrontend/C2C: convertIkind *)
Axiom elab_const_float : floatInfo -> const.
(* CompCert: cparser/Elab: elab_char_constant + cfrontend/C2C: convertIkind *)
Axiom elab_const_char : astloc -> bool -> list char_code -> const.
                   
Module Type ELABORATION
       (Import Ids    : IDS)
       (Import Op     : OPERATORS)
       (Import Syn    : SYNTAX Ids Op)
       (Import Typing : TYPING Ids Op Syn).

  

End ELABORATION.
