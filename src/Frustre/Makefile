include ../../variables.mk
include ../../Makefile.config

RUSTRE_ABSDIR=$(COMPCERTDIR)/..
# TODO: compcert.ia32/arm/powerpc are ARCH-specific...
COQLIBS=\
	-R "$(RUSTRE_ABSDIR)/CompCert/lib"       compcert.lib\
	-R "$(RUSTRE_ABSDIR)/CompCert/common"    compcert.common\
	-R "$(RUSTRE_ABSDIR)/CompCert/backend"   compcert.backend\
	-R "$(RUSTRE_ABSDIR)/CompCert/cfrontend" compcert.cfrontend\
	-R "$(RUSTRE_ABSDIR)/CompCert/driver"    compcert.driver\
	-R "$(RUSTRE_ABSDIR)/CompCert/flocq"     compcert.flocq\
	-R "$(RUSTRE_ABSDIR)/CompCert/cparser"   compcert.cparser\
	-R "$(RUSTRE_ABSDIR)/CompCert/x86"    	 compcert.x86\
	-R "$(RUSTRE_ABSDIR)/CompCert/x86_64"    compcert.x86_64\
	-R "$(RUSTRE_ABSDIR)/src" Velus

VELUS_VFILES=../Common/Common.v\
	     ../Operators.v\
	     ../Clocks.v\

FRUSTRE_VFILES=FSyntax.v\
	       FTransform.v\
		     FtoLustre.v\
	       Parser/FrustreAst.v\
	       Parser/FrustreParser.v

FRUSTRE_MLFILES=FSyntax_of_frustre.ml\
		FSyntax_pp.ml\
		frustre.ml\
		frustre_of_ast.ml\
		frustre_pp.ml\
		frustre_test.ml\
		frustre_typing.ml\
		frustre_clocking.ml

VFILES=$(VELUS_VFILES) $(FRUSTRE_VFILES)

FRUSTRE_VOFILES:=$(FRUSTRE_VFILES:.v=.vo)
VOFILES:=$(VFILES:.v=.vo)

# Most of these are needed for Elab.ml*
COMPCERT_MLFILES=\
	lib/Camlcoq.ml\
	cparser/C.mli\
	lib/Readconfig.ml\
	lib/Readconfig.mli\
	lib/Responsefile.ml\
	lib/Responsefile.mli\
	common/Sections.ml\
	common/Sections.mli\
	driver/Configuration.ml\
	driver/Configuration.mli\
	driver/Clflags.ml\
	driver/Commandline.ml\
	driver/Commandline.mli\
	driver/Version.ml\
	debug/Debug.ml\
	debug/Debug.mli\
	debug/DwarfTypes.mli\
	cparser/Env.ml\
	cparser/Env.mli\
	cparser/Machine.ml\
	cparser/Ceval.ml\
	cparser/Ceval.mli\
	cparser/Cflow.ml\
	cparser/Cflow.mli\
	cparser/Checks.ml\
	cparser/Checks.mli\
	cparser/Cleanup.ml\
	cparser/Cleanup.mli\
	cparser/Cutil.ml\
	cparser/Cutil.mli\
	cparser/Cprint.ml\
	cparser/Cprint.mli\
	cparser/Cabshelper.ml\
	cparser/Diagnostics.ml\
	cparser/Diagnostics.mli\
	cparser/Elab.mli\
	cparser/Elab.ml

# VARIABLES

DOCDIR=doc
COQDEP="$(COQBIN)coqdep" -c
COQFLAGS=-q $(COQLIBS) $(OTHERFLAGS)
COQC="$(COQBIN)coqc"
COQEXEC="$(COQBIN)coqtop" $(COQFLAGS) -batch -load-vernac-source
$(shell mkdir -p $(DOCDIR) >/dev/null)
export $(COQEXEC)

INCLUDES = -I extraction/extracted
OCAMLC=ocamlc $(INCLUDES)
OCAMLOPT=ocamlopt $(INCLUDES)
OCAMLDEP=ocamldep $(INCLUDES)

# RULES
all: frustre_test.native

clean:
	$(MAKE) -C Parser clean
	rm -f $(FRUSTRE_VOFILES) $(DOCDIR)/*.glob .depend .depend.extr
	rm -rf extraction/extracted
	rm -f extraction/STAMP
	rm -f *.cmi *.cmx *.o *.vo

.depend: $(VFILES)
	@echo "Analyzing Coq dependencies"
	$(COQDEP) $(COQLIBS) $^ > .depend

-include .depend

%.vo %.glob: %.v
	@echo "COQC $*.v"
	$(COQC) -dump-glob $(DOCDIR)/$(*F).glob $(COQFLAGS) $*

Parser/FrustreParser.v: Parser/FrustreParser.vy
	$(MENHIR) --no-stdlib --coq $<

Parser/FrustreLexer.ml: Parser/FrustreLexer.mll
	ocamllex $<

extraction/STAMP: .depend $(VOFILES) Parser/FrustreLexer.ml extraction/Extraction.v
	rm -f extraction/extracted/*.ml*
	$(COQEXEC) Frustre/extraction/Extraction.v
	cp -f Parser/FrustreLexer.ml extraction/extracted/
	cp -f $(COMPCERT_MLFILES:%=$(COMPCERTDIR)/%) extraction/extracted/
	touch extraction/STAMP

extraction: extraction/STAMP

.depend.extr: frustre_test.ml extraction/STAMP $(FRUSTRE_MLFILES)
	@echo "Analyzing OCaml dependencies"
	@$(OCAMLDEP) extraction/extracted/*.ml extraction/extracted/*.mli *.ml > .depend.extr

ifeq ($(wildcard .depend.extr),.depend.extr)

MODORDER=$(COMPCERTDIR)/tools/modorder .depend.extr
FRUSTRE_OBJS:=$(shell $(MODORDER) frustre_test.cmx)
LIBS=str.cmxa unix.cmxa

endif

frustre_test.native : .depend.extr $(FRUSTRE_OBJS)
	@echo "Linking $@"
	@$(OCAMLOPT) -o $@ $(LIBS) $+

-include .depend.extr

%.cmi: %.mli
	@echo "OCAMLC $<"
	@$(OCAMLC) -c $<

%.cmx: %.ml
	@echo "$(OCAMLOPT) $<"
	@$(OCAMLOPT) -c $<

tests: frustre_test.native
	-@for f in ../tests/ko_*; do echo "${blue}--$$f${normal}"; \
	    ./$< $$f 2>/dev/null && echo "${red}FAIL${normal}"; done
	-@for f in ../tests/ok_*; do echo "${blue}--$$f${normal}"; \
	    ./$< $$f >/dev/null || echo "${red}FAIL${normal}"; done

.PHONY: all clean
