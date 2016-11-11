MENHIR?=$(OCAMLBIN)menhir
OCAMLFIND?=$(OCAMLBIN)ocamlfind
OCAMLLEX?=$(OCAMLBIN)ocamllex
OCAMLDEP?=$(OCAMLBIN)ocamldep
OCAMLC?=$(OCAMLBIN)ocamlc
OCAMLOPT?=$(OCAMLBIN)ocamlopt
COQC?=$(COQBIN)coqc

COQ_LOAD_PATH=-R . Rustre.Dataflow.Parser \
  	      -R ../../CompCert/cparser/validator compcert.cparser.validator

default: Parser.vo Lexer.cmo Parser2.cmo extraction/Parser.cma

extraction/Parser.ml: extraction/extraction.v Parser.vo Ast.vo
	$(COQC) $(COQ_LOAD_PATH) $(<:.v=)
	(cd extraction; ocamldep *.ml *.mli > depend)

Parser.v: Parser.vy
	$(MENHIR) --no-stdlib --coq $<

Parser2.mly: Parser.vy
	$(MENHIR) --no-stdlib --coq --only-preprocess-u $< > $@

Parser2.ml Parser2.mli: Parser2.mly
	$(MENHIR) --no-stdlib --table $<

Parser2.cmi: OCAMLFLAGS+=-package menhirLib
Parser2.cmi: Parser2.mli

Parser2.cmo: OCAMLFLAGS+=-package menhirLib
Parser2.cmo: IEXTRACTION:=-I extraction
Parser2.cmo: Parser2.ml Parser2.cmi extraction/Ast.cmi

Parser2.cmx: OCAMLFLAGS+=-package menhirLib
Parser2.cmx: IEXTRACTION:=-I extraction
Parser2.cmx: Parser2.ml Parser2.cmi extraction/Ast.cmi

Lexer.ml: Lexer.mll
	$(OCAMLLEX) $<

Relexer.cmi: Relexer.ml
Relexer.cmo: IEXTRACTION:=-I extraction
Relexer.cmo: Relexer.ml extraction/Ast.cmi extraction/Parser.cmi \
    		Parser2.cmi
Relexer.cmx: IEXTRACTION:=-I extraction
Relexer.cmx: Relexer.ml extraction/Ast.cmi extraction/Parser.cmi \
    		Parser2.cmi

extraction/Parser.cmo: extraction/Parser.ml
extraction/Parser.cmx: extraction/Parser.ml
extraction/Parser.cma: extraction/Parser.cmo
extraction/Parser.cmxa: extraction/Parser.cmx

Lexer.cmo: Lexer.ml extraction/Ast.cmo extraction/Parser.cmo
Lexer.cmo: IEXTRACTION:=-I extraction
Lexer.cmx: Lexer.ml extraction/Ast.cmx extraction/Parser.cmx
Lexer.cmx: IEXTRACTION:=-I extraction

Parser.vo: Parser.v Ast.vo
	$(COQC) $(COQ_LOAD_PATH) $(<:.v=)

Ast.vo: Ast.v
	$(COQC) $(COQ_LOAD_PATH) $(<:.v=)

clean:
	@rm -rf Parser.vo Parser.v Parser.glob
	@rm -rf Parser2.mly Parser2.ml Parser2.mli
	@rm -rf Parser2.cmi Parser2.cmo Parser2.cmx Parser2.o
	@rm -rf Ast.vo Ast.glob
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

