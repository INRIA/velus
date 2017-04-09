Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import Velus.VelusCorrectness.
Require Import Coq.ZArith.BinInt.
Require Import Velus.ObcToClight.Generation.
Require Import Velus.ObcToClight.NLustreElab.
Require Import Lustre.Parser.LustreParser.

Require arm.Machregs arm.Conventions1
        cfrontend.Initializers cfrontend.Ctyping
        backend.Selection backend.RTLgen
        driver.Compiler cparser.Cabs.
Require ZArith.BinIntDef.
        
Cd "extraction/extracted".

Extraction Blacklist Int String List.

(* Selection *)
Extract Constant Selection.compile_switch => "Switchaux.compile_switch".

(* RTLgen *)
Extract Constant RTLgen.more_likely => "RTLgenaux.more_likely".

(* Compopts *)
Extract Constant Compopts.optim_for_size =>
  "fun _ -> !Clflags.option_Osize".
Extract Constant Compopts.va_strict =>
  "fun _ -> false".
Extract Constant Compopts.propagate_float_constants =>
  "fun _ -> !Clflags.option_ffloatconstprop >= 1".
Extract Constant Compopts.generate_float_constants =>
  "fun _ -> !Clflags.option_ffloatconstprop >= 2".
Extract Constant Compopts.optim_tailcalls =>
  "fun _ -> !Clflags.option_ftailcalls".
Extract Constant Compopts.optim_constprop =>
  "fun _ -> !Clflags.option_fconstprop".
Extract Constant Compopts.optim_CSE =>
"fun _ -> !Clflags.option_fcse".
Extract Constant Compopts.optim_redundancy =>
  "fun _ -> !Clflags.option_fredundancy".
Extract Constant Compopts.debug =>
  "fun _ -> !Clflags.option_g".

(* Compiler *)
Extract Constant Compiler.print_Clight => "PrintClight.print_if".
Extract Constant Compiler.print_Cminor => "PrintCminor.print_if".
Extract Constant Compiler.print_RTL => "PrintRTL.print_if".
Extract Constant Compiler.print_LTL => "PrintLTL.print_if".
Extract Constant Compiler.print_Mach => "PrintMach.print_if".
Extract Constant Compiler.print => "fun (f: 'a -> unit) (x: 'a) -> f x; x".

(* Inlining *)
Extract Inlined Constant Inlining.should_inline => "Inliningaux.should_inline".

(* Allocation *)
Extract Constant Allocation.regalloc => "Regalloc.regalloc".

(* Linearize *)
Extract Constant Linearize.enumerate_aux => "Linearizeaux.enumerate_aux".

Extract Constant Archi.abi =>
  "begin match Configuration.abi with
   | ""eabi"" -> Softfloat
   | ""hardfloat"" -> Hardfloat
   | _ -> assert false
   end".

Extract Constant Compopts.thumb =>
  "fun _ -> !Clflags.option_mthumb".

Extract Constant Ident.pos_of_str => "(fun str -> Camlcoq.(str |> camlstring_of_coqstring |> intern_string))".
Extract Constant Ident.pos_to_str => "(fun pos -> Camlcoq.(pos |> extern_atom |> coqstring_of_camlstring))".

(* Lexing/Parsing/Elaboration *)
Extract Constant LustreAst.astloc =>
"{ ast_lnum  : int;
   ast_fname : string;
   ast_bol   : int;
   ast_cnum  : int;
   ast_ident : int; }".
Extract Constant LustreAst.string => "String.t".
Extract Constant LustreAst.string_zero => """0""".
Extract Constant LustreAst.string_one => """1""".
Extract Constant LustreAst.char_code => "int64".
Extract Constant string_of_astloc =>
  "fun loc -> Camlcoq.coqstring_of_camlstring (LustreLexer.string_of_loc loc)".
Extract Constant cabsloc_of_astloc =>
  "fun { LustreAst.ast_lnum = lno;  LustreAst.ast_fname = fname;
         LustreAst.ast_cnum = cnum; LustreAst.ast_ident = id } ->
       { Cabs.lineno  = lno;  Cabs.filename = fname;
         Cabs.byteno  = cnum; Cabs.ident    = id }".
Extract Constant cabs_floatinfo =>
  "fun { LustreAst.isHex_FI    = ishex;
         LustreAst.integer_FI  = integer;
         LustreAst.fraction_FI = fraction;
         LustreAst.exponent_FI = exponent;
         LustreAst.suffix_FI   = suffix } ->
       { Cabs.isHex_FI    = ishex;
         Cabs.integer_FI  = integer;
         Cabs.fraction_FI = fraction;
         Cabs.exponent_FI = exponent;
         Cabs.suffix_FI   = suffix }".

Extract Constant elab_const_int =>
  "fun loc str ->
    let (v, k) = Elab.elab_int_constant loc str in
    match k with
    | C.ILongLong ->
        Interface.Op.Clong (Camlcoq.coqint_of_camlint64 v, Ctypes.Signed)
    | C.IULongLong ->
        Interface.Op.Clong (Camlcoq.coqint_of_camlint64 v, Ctypes.Unsigned)
    | _ ->
        let (sg, sz) = C2C.convertIkind k in
        Interface.Op.Cint (C2C.convertInt v, sz, sg)".

Extract Constant elab_const_float =>
  "fun fi ->
    let (f, k) = Elab.elab_float_constant fi in
    if k = C.FLongDouble && not !Clflags.option_flongdouble then
      C2C.unsupported ""'long double' floating-point literal"";
    match C2C.convertFloat f k with
    | Csyntax.Eval (Values.Vfloat n, Ctypes.Tfloat(Ctypes.F64, _)) ->
        Interface.Op.Cfloat n
    | Csyntax.Eval (Values.Vsingle n, Ctypes.Tfloat(Ctypes.F32, _)) ->
        Interface.Op.Csingle n
    | _ -> assert false".

Extract Constant elab_const_char =>
  "fun loc wide chars ->
    let (v, k) = Elab.elab_char_constant loc wide chars in
    let (sg, sz) = C2C.convertIkind k in
    Interface.Op.Cint (C2C.convertInt v, sz, sg)".

(* Cabs *)
Extract Constant Cabs.cabsloc =>
"{ lineno : int;
   filename: string;
   byteno: int;
   ident : int;
 }".
Extract Constant Cabs.string => "String.t".
Extract Constant Cabs.char_code => "int64".

Extract Constant VelusCorrectness.print_snlustre =>
  "Veluslib.print_snlustre_if".
Extract Constant VelusCorrectness.print_obc => "Veluslib.print_obc_if".
Extract Constant VelusCorrectness.do_fusion => "Veluslib.do_fusion".
Extract Constant VelusCorrectness.do_sync => "Veluslib.do_sync".
Extract Constant VelusCorrectness.do_expose => "Veluslib.do_expose".
Extract Constant VelusCorrectness.schedule =>
  "Interfacelib.Scheduler.schedule".

(* builtins *)
Extract Constant VelusCorrectness.add_builtins => "Veluslib.add_builtins".

Separate Extraction
         ZArith.BinIntDef
         Compiler.transf_clight_program Cabs
         AST.signature_main
         VelusCorrectness.compile elab_declarations translation_unit_file
         Initializers.transl_init
         Ctyping.typecheck_program Ctyping.epostincr Ctyping.epostdecr Ctyping.epreincr Ctyping.epredecr
         Machregs.two_address_op Machregs.mregs_for_operation Machregs.mregs_for_builtin Machregs.is_stack_reg
         Conventions1.dummy_int_reg Conventions1.dummy_float_reg
         Conventions1.int_callee_save_regs Conventions1.int_caller_save_regs
         Conventions1.float_callee_save_regs Conventions1.float_caller_save_regs.
