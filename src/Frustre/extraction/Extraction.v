From Velus Require Frustre.FSyntax.
From Velus Require Frustre.FTransform.
From Velus Require Frustre.FtoLustre.
From Velus Require Frustre.Parser.FrustreAst.
From Velus Require Frustre.Parser.FrustreParser.
From Velus Require Instantiator.

From Coq Require ZArith.BinIntDef.
From Coq Require Lists.Streams.

From compcert Require lib.Floats.
From compcert Require cfrontend.Ctypes.
From compcert Require cfrontend.Ctyping.
From compcert Require cparser.Cabs.
From compcert Require common.Errors.
From compcert Require x86.SelectOp. (* Arch-specific *)

From Coq Require Import ExtrOcamlBasic.
From Coq Require Import ExtrOcamlString.

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
Extract Constant Cabs.loc =>
"{ lineno : int;
   filename: string;
   byteno: int;
   ident : int;
 }".
Extract Constant Cabs.string => "String.t".
Extract Constant Cabs.char_code => "int64".

Extract Constant Ident.pos_of_str => "(fun str -> Camlcoq.(str |> camlstring_of_coqstring |> intern_string))".
Extract Constant Ident.pos_to_str => "(fun pos -> Camlcoq.(pos |> extern_atom |> coqstring_of_camlstring))".

Recursive Extraction Library FSyntax.
Recursive Extraction Library FrustreAst.
Recursive Extraction Library FTransform.
Recursive Extraction Library FtoLustre.
Recursive Extraction Library Cabs.

(* Extraction is not easy... *)
Separate Extraction
         (* Coq *)
         PeanoNat.Nat Bool
         BinInt.Z BinPos.Pos
         Coq.Init.Datatypes
         Binary.B2FF
         Integers.Int64 Integers.Ptrofs.signed
         Floats.Float Floats.Float32
         MSetProperties
         OrdersEx
         DecidableType
         (* CompCert *)
         Ctypes.type Ctypes.noattr Ctypes.mk_attr
         Ctypes.intsize Ctypes.signedness Ctypes.floatsize
         Ctyping.check_cast Ctyping.type_unop Ctyping.type_binop
         Ctyping.econst_single Ctyping.econst_float
         SelectOp.builtin_arg
         Errors.res
         FrustreParser.translation_unit_file
         (* Velus *)
         Common Environment Memory Ident CoindStreams Interface
         LSyntax LTyping LClocking LNormalization
.
