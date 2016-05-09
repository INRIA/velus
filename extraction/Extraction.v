Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import Rustre.DF2CL.
Require Import Rustre.MP2CL.Translation.

Require ia32.Machregs ia32.Conventions1
        cfrontend.Initializers cfrontend.Ctyping
        backend.Selection backend.RTLgen
        driver.Compiler cparser.Cabs.
Require ZArith.BinIntDef.

Cd "extraction/extract".

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

(* Inlining *)
Extract Inlined Constant Inlining.should_inline => "Inliningaux.should_inline".

(* Allocation *)
Extract Constant Allocation.regalloc => "Regalloc.regalloc".

(* Linearize *)
Extract Constant Linearize.enumerate_aux => "Linearizeaux.enumerate_aux".

(* SelectOp *)
Extract Constant SelectOp.symbol_is_external =>
  "fun id -> Configuration.system = ""macosx"" && C2C.atom_is_extern id".

Extract Constant pos_of_str => "(fun str -> Camlcoq.(str |> camlstring_of_coqstring |> intern_string))".
Extract Constant pos_to_str => "(fun pos -> Camlcoq.(pos |> extern_atom |> coqstring_of_camlstring))".

Separate Extraction
         ZArith.BinIntDef
         Compiler.transf_clight_program (* Cabs *)
         DF2CL
         Initializers.transl_init
         Ctyping.typecheck_program Ctyping.epostincr Ctyping.epostdecr Ctyping.epreincr Ctyping.epredecr
         Machregs.two_address_op Machregs.mregs_for_operation Machregs.mregs_for_builtin Machregs.is_stack_reg
         Conventions1.dummy_int_reg Conventions1.dummy_float_reg.
