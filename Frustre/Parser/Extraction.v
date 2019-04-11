Require Velus.Frustre.Parser.Ast.
Require Velus.Frustre.Parser.Parser.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Extraction Blacklist List.

Cd "extraction".

Extract Constant Ast.astloc =>
"{ ast_lnum  : int;
   ast_fname : string;
   ast_bol   : int;
   ast_cnum  : int;
   ast_ident : int; }".

Extract Constant Ast.string => "String.t".
Extract Constant Ast.char_code => "int64".

Extraction Library Ast.

Separate Extraction
  Parser.translation_unit_file.

