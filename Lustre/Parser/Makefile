MENHIR?=$(OCAMLBIN)menhir
OCAMLFIND?=$(OCAMLBIN)ocamlfind
OCAMLLEX?=$(OCAMLBIN)ocamllex
OCAMLDEP?=$(OCAMLBIN)ocamldep
OCAMLC?=$(OCAMLBIN)ocamlc
OCAMLOPT?=$(OCAMLBIN)ocamlopt
COQC?=$(COQBIN)coqc

COQ_LOAD_PATH=-R . Velus.NLustre.LustreParser \
  	      -R ../../CompCert/cparser/validator compcert.cparser.validator

default: LustreParser.vo Lexer.cmo LustreParser2.cmo extraction/LustreParser.cma

extraction/LustreParser.ml: extraction/extraction.v LustreParser.vo LustreAst.vo
	$(COQC) $(COQ_LOAD_PATH) $(<:.v=)
	(cd extraction; ocamldep *.ml *.mli > depend)

LustreParser.v: LustreParser.vy
	$(MENHIR) --no-stdlib --coq $<

LustreParser2.mly: LustreParser.vy
	$(MENHIR) --no-stdlib --coq --only-preprocess-u $< > $@

LustreParser2.ml LustreParser2.mli: LustreParser2.mly
	$(MENHIR) --no-stdlib --table $<

LustreParser2.cmi: OCAMLFLAGS+=-package menhirLib
LustreParser2.cmi: LustreParser2.mli

LustreParser2.cmo: OCAMLFLAGS+=-package menhirLib
LustreParser2.cmo: IEXTRACTION:=-I extraction
LustreParser2.cmo: LustreParser2.ml LustreParser2.cmi extraction/LustreAst.cmi

LustreParser2.cmx: OCAMLFLAGS+=-package menhirLib
LustreParser2.cmx: IEXTRACTION:=-I extraction
LustreParser2.cmx: LustreParser2.ml LustreParser2.cmi extraction/LustreAst.cmi

Lexer.ml: Lexer.mll
	$(OCAMLLEX) $<

Relexer.cmi: Relexer.ml
Relexer.cmo: IEXTRACTION:=-I extraction
Relexer.cmo: Relexer.ml extraction/LustreAst.cmi extraction/LustreParser.cmi \
    		LustreParser2.cmi
Relexer.cmx: IEXTRACTION:=-I extraction
Relexer.cmx: Relexer.ml extraction/LustreAst.cmi extraction/LustreParser.cmi \
    		LustreParser2.cmi

extraction/LustreParser.cmo: extraction/LustreParser.ml
extraction/LustreParser.cmx: extraction/LustreParser.ml
extraction/LustreParser.cma: extraction/LustreParser.cmo
extraction/LustreParser.cmxa: extraction/LustreParser.cmx

Lexer.cmo: Lexer.ml extraction/LustreAst.cmo extraction/LustreParser.cmo
Lexer.cmo: IEXTRACTION:=-I extraction
Lexer.cmx: Lexer.ml extraction/LustreAst.cmx extraction/LustreParser.cmx
Lexer.cmx: IEXTRACTION:=-I extraction

LustreParser.vo: LustreParser.v LustreAst.vo
	$(COQC) $(COQ_LOAD_PATH) $(<:.v=)

LustreAst.vo: LustreAst.v
	$(COQC) $(COQ_LOAD_PATH) $(<:.v=)

clean:
	@rm -rf LustreParser.vo LustreParser.v LustreParser.glob
	@rm -rf LustreParser2.mly LustreParser2.ml LustreParser2.mli
	@rm -rf LustreParser2.cmi LustreParser2.cmo LustreParser2.cmx
	@rm -rf LustreParser2.o
	@rm -rf LustreAst.vo LustreAst.glob
	@rm -rf Lexer.ml Lexer.cmi Lexer.cmo Lexer.cmx
	@rm -rf Relexer.cmi Relexer.cmo Relexer.cmx Relexer.o
	@make -C extraction clean_extraction

## Rules

extraction/%:
	make -C ./extraction $(@:extraction/%=%)

.SUFFIXES : .mli .ml .cmi .cmo .cmx

.mli.cmi:
	$(OCAMLFIND) $(OCAMLC) -c $(IEXTRACTION) $(OCAMLFLAGS) $<

.ml.cmo:
	$(OCAMLFIND) $(OCAMLC) -c $(IEXTRACTION) $(OCAMLFLAGS) $<

.ml.cmx:
	$(OCAMLFIND) $(OCAMLOPT) -c $(IEXTRACTION) $(OCAMLFLAGS) $<

