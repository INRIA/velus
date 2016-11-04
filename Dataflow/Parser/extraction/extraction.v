Require Rustre.Dataflow.Parser.Ast.
Require Rustre.Dataflow.Parser.Parser.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Extraction Blacklist List.

Cd "extraction".

Extract Constant Ast.astloc =>
"{ lineno : int;
   filename: string;
   byteno: int;
   ident : int;
 }".
Extract Constant Ast.string => "String.t".
Extract Constant Ast.char_code => "int64".

Extraction Library Ast.

Separate Extraction
  Parser.translation_unit_file.

