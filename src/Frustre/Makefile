
include ../variables.mk

RUSTRE_ABSDIR=/home/tbourke/Projects/rustre-master # FIXME
# TODO: compcert.ia32/arm/powerpc are ARCH-specific...
COQLIBS=-R "$RUSTRE_ABSDIR/CompCert/lib"       compcert.lib\
	-R "$RUSTRE_ABSDIR/CompCert/common"    compcert.common\
	-R "$RUSTRE_ABSDIR/CompCert/backend"   compcert.backend\
	-R "$RUSTRE_ABSDIR/CompCert/cfrontend" compcert.cfrontend\
	-R "$RUSTRE_ABSDIR/CompCert/driver"    compcert.driver\
	-R "$RUSTRE_ABSDIR/CompCert/flocq"     compcert.flocq\
	-R "$RUSTRE_ABSDIR/CompCert/cparser"   compcert.cparser\
	-R "$RUSTRE_ABSDIR/CompCert/ia32"      compcert.ia32\
	-exclude-dir arm\
	-exclude-dir powerpc\
	-R "$RUSTRE_ABSDIR" Velus

VELUS_VFILES=../Common.v\
	     ../Operators.v\
	     ../Clocks.v\

FRUSTRE_VFILES=FSyntax.v\
	       FTransform.v\
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
	common/Sections.ml\
	common/Sections.mli\
	driver/Configuration.ml\
	driver/Configuration.mli\
	driver/Clflags.ml\
	debug/Debug.ml\
	debug/Debug.mli\
	debug/DwarfTypes.mli\
	cparser/Env.ml\
	cparser/Env.mli\
	cparser/Builtins.ml\
	cparser/Builtins.mli\
	cparser/Machine.ml\
	cparser/Ceval.ml\
	cparser/Ceval.mli\
	cparser/Cleanup.ml\
	cparser/Cleanup.mli\
	cparser/Cerrors.ml\
	cparser/Cerrors.mli\
	cparser/Cutil.ml\
	cparser/Cutil.mli\
	cparser/Cprint.ml\
	cparser/Cprint.mli\
	cparser/Cabshelper.ml\
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

# RULES

.PHONY: all clean depend

all: frustre_test.native

clean: 
	$(MAKE) -C Parser clean
	rm -f $(FRUSTRE_VOFILES) $(DOCDIR)/*.glob .depend
	rm -f extraction/extracted/*.ml*
	rm -f extraction/STAMP

depend: $(VFILES)
	@echo "Analyzing Coq dependencies"
	$(COQDEP) -slash $(COQLIBS) $^ > .depend

%.vo %.glob: %.v
	@echo "COQC $*.v"
	$(COQC) -dump-glob $(DOCDIR)/$(*F).glob $(COQFLAGS) $*

frustre_test.native: frustre_test.ml $(VOFILES) $(VELUS_VILES) \
    			$(FRUSTRE_MLFILES) extraction/STAMP
	ocamlbuild -tag debug -I extraction/extracted $@

tests: frustre_test.native
	-@for f in ../tests/ko_*; do echo "${blue}--$$f${normal}"; \
	    ./$< $$f 2>/dev/null && echo "${red}FAIL${normal}"; done
	-@for f in ../tests/ok_*; do echo "${blue}--$$f${normal}"; \
	    ./$< $$f >/dev/null || echo "${red}FAIL${normal}"; done

extraction: extraction/STAMP

extraction/STAMP: $(VOFILES) Parser/FrustreLexer.ml extraction/Extraction.v
	rm -f extraction/extracted/*.ml*
	$(COQEXEC) Frustre/extraction/Extraction.v
	cp -f Parser/FrustreLexer.ml extraction/extracted/
	cp -f $(COMPCERT_MLFILES:%=$(COMPCERTDIR)/%) extraction/extracted/
	touch extraction/STAMP

Parser/FrustreParser.v: Parser/FrustreParser.vy
	$(MENHIR) --no-stdlib --coq $<

Parser/FrustreLexer.ml: Parser/FrustreLexer.mll
	ocamllex $<

-include .depend
