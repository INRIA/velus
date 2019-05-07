Require Velus.Frustre.FSyntax.
Require Velus.Frustre.FTransform.
Require Velus.Frustre.Parser.FrustreAst.
Require Velus.Frustre.Parser.FrustreParser.

Require ZArith.BinIntDef.
Require lib.Floats.
Require cfrontend.Ctypes.
Require cfrontend.Ctyping.
Require cparser.Cabs.
Require common.Errors.
Require ia32.SelectOp. (* Arch-specific *)

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Extraction Blacklist Int String List.

Cd "extraction/extracted".

Extract Constant FrustreAst.astloc =>
"{ ast_lnum  : int;
   ast_fname : string;
   ast_bol   : int;
   ast_cnum  : int;
   ast_ident : int; }".

Extract Constant FrustreAst.string => "String.t".
Extract Constant FrustreAst.char_code => "int64".

(* Cabs *)
Extract Constant Cabs.cabsloc =>
"{ lineno : int;
   filename: string;
   byteno: int;
   ident : int;
 }".
Extract Constant Cabs.string => "String.t".
Extract Constant Cabs.char_code => "int64".

Recursive Extraction Library FSyntax.
Recursive Extraction Library FrustreAst.
Recursive Extraction Library FTransform.
Recursive Extraction Library Cabs.

Separate Extraction
  ZArith.BinIntDef
  Coq.Init.Datatypes
  Floats.float Floats.float32 Floats.Float.of_bits Floats.Float32.of_bits
  Fappli_IEEE.B2FF
  Integers.Int.int Integers.Int64.int
  Ctypes.type Ctypes.noattr Ctypes.mk_attr
  Ctypes.intsize Ctypes.signedness Ctypes.floatsize
  Ctyping.check_cast Ctyping.type_unop Ctyping.type_binop
  Ctyping.econst_single Ctyping.econst_float
  SelectOp.builtin_arg
  Errors.res
  FrustreParser.translation_unit_file.

