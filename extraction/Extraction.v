From Coq Require Import ExtrOcamlBasic.
From Coq Require Import ExtrOcamlString.
From Coq Require Import ZArith.BinInt.
From Coq Require ZArith.BinIntDef.

From Velus Require Import Velus.
From Velus Require Import ObcToClight.Generation.
From Velus Require Import Lustre.LustreElab.
From Velus Require Import Lustre.Parser.LustreParser.

From compcert Require
     cfrontend.Initializers cfrontend.Ctyping
     backend.Selection backend.RTLgen
     driver.Compiler cparser.Cabs.

(* Processor-specific extraction directives *)
Load extractionMachdep.

Set Extraction Output Directory "extraction/extracted".

Extraction Blacklist Int String List.

(* Selection *)
Extract Constant Selection.compile_switch => "Switchaux.compile_switch".
Extract Constant Selection.if_conversion_heuristic => "Selectionaux.if_conversion_heuristic".

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
Extract Constant Compopts.thumb =>
  "fun _ -> !Clflags.option_mthumb".
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
Extract Inlined Constant Inlining.inlining_info => "Inliningaux.inlining_info".
Extract Inlined Constant Inlining.inlining_analysis => "Inliningaux.inlining_analysis".
Extraction Inline Inlining.ret Inlining.bind.

(* Allocation *)
Extract Constant Allocation.regalloc => "Regalloc.regalloc".

(* Linearize *)
Extract Constant Linearize.enumerate_aux => "Linearizeaux.enumerate_aux".

Extract Constant Ident.str_to_pos => "(fun str -> Camlcoq.(str |> camlstring_of_coqstring |> intern_string))".
Extract Constant Ident.pos_to_str => "(fun pos -> Camlcoq.(pos |> extern_atom |> coqstring_of_camlstring))".
Extract Constant Ident.Ids.prefix => "Veluscommon.prefix".
Extract Constant Ident.Ids.gensym => "Veluscommon.gensym".

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
    match C2C.convertIkind k Ctypes.noattr with
    | Ctypes.Tint (sz, sg, _) ->
        Interface.Op.Cint (C2C.convertInt32 v, sz, sg)
    | Ctypes.Tlong (sg, _) ->
        Interface.Op.Clong (C2C.convertInt64 v, sg)
    | _ -> assert false".

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
    match C2C.convertIkind k Ctypes.noattr with
    | Ctypes.Tint (sz, sg, _) ->
	Interface.Op.Cint (C2C.convertInt32 v, sz, sg)
    | _ -> assert false".

(* Cabs *)
Extract Constant Cabs.loc =>
"{ lineno : int;
   filename: string;
   byteno: int;
   ident : int;
 }".
Extract Constant Cabs.string => "String.t".
Extract Constant Cabs.char_code => "int64".

(* Extract Constant LustreElab.do_add_when_to_constants => *)
(*     "Veluslib.do_add_when_to_constants". *)

Extract Constant Velus.print_lustre => "Veluslib.print_lustre_if".
Extract Constant Velus.print_complete => "Veluslib.print_complete_if".
Extract Constant Velus.print_noauto => "Veluslib.print_noauto_if".
Extract Constant Velus.print_noswitch => "Veluslib.print_noswitch_if".
Extract Constant Velus.print_nolocal => "Veluslib.print_nolocal_if".
Extract Constant Velus.print_unnested => "Veluslib.print_unnested_if".
Extract Constant Velus.print_normlast => "Veluslib.print_normlast_if".
Extract Constant Velus.print_normfby => "Veluslib.print_normfby_if".
Extract Constant Velus.print_nlustre => "Veluslib.print_nlustre_if".
Extract Constant Velus.print_stc => "Veluslib.print_stc_if".
Extract Constant Velus.print_cut => "Veluslib.print_cut_if".
Extract Constant Velus.print_sch => "Veluslib.print_sch_if".
Extract Constant Velus.print_obc => "Veluslib.print_obc_if".
Extract Constant Velus.print_header => "Veluslib.print_header_if".
Extract Constant Velus.do_exp_inlining => "Veluslib.do_exp_inlining".
Extract Constant Velus.do_dce => "Veluslib.do_dce".
Extract Constant Velus.do_dupregrem => "Veluslib.do_dupregrem".
Extract Constant Velus.do_fusion => "Veluslib.do_fusion".
Extract Constant Velus.do_norm_switches => "Veluslib.do_normalize_switches".
Extract Constant Velus.do_obc_dce => "Veluslib.do_obc_dce".
Extract Constant Velus.do_sync   => "Veluslib.do_sync".
Extract Constant Velus.do_expose => "Veluslib.do_expose".
Extract Constant Velus.cutting_points => "Interfacelib.Scheduler.cutting_points".
Extract Constant Velus.schedule  => "Interfacelib.Scheduler.schedule".

(* builtins *)
Extract Constant Velus.add_builtins => "Veluslib.add_builtins".

Separate Extraction
  ZArith.BinIntDef
  Floats.Float.of_bits Floats.Float.to_bits
  Floats.Float32.of_bits Floats.Float32.to_bits
  Floats.Float32.from_parsed Floats.Float.from_parsed
  FMapPositive.PositiveMap.add FMapPositive.PositiveMap.empty
  FMapPositive.PositiveMap.find
  Compiler.transf_clight_program Cabs
  AST.signature_main
  Velus.compile elab_declarations translation_unit_file
  Initializers.transl_init
  Ctypes.layout_struct
  Ctyping.eselection
  Ctyping.typecheck_program Ctyping.epostincr Ctyping.epostdecr Ctyping.epreincr Ctyping.epredecr
  Machregs.two_address_op Machregs.mregs_for_operation Machregs.mregs_for_builtin Machregs.is_stack_reg
  Machregs.destroyed_at_indirect_call
  Conventions1.is_float_reg Conventions1.callee_save_type
  Conventions1.dummy_int_reg Conventions1.dummy_float_reg
  Conventions1.int_callee_save_regs Conventions1.int_caller_save_regs
  Conventions1.float_callee_save_regs Conventions1.float_caller_save_regs
  Conventions1.allocatable_registers
  Clight.type_of_function
  Instantiator.check_restr
  Instantiator.check_op.

Extraction Library Ordered.
