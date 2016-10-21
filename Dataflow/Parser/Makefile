MENHIR?=$(OCAMLBIN)menhir
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
	$(MENHIR) --no-stdlib $<

Parser2.cmi: Parser2.mli
Parser2.cmo: Parser2.ml Parser2.cmi extraction/Ast.cmi
Parser2.cmo: IEXTRACTION:=-I extraction
Parser2.cmxa: Parser2.ml Parser2.cmi extraction/Ast.cmi
Parser2.cmxa: IEXTRACTION:=-I extraction

Lexer.ml: Lexer.mll
	$(OCAMLLEX) $<

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
	@rm -rf Parser2.mly Parser2.ml Parser2.mli Parser2.cmi Parser2.cmo
	@rm -rf Ast.vo Ast.glob
	@rm -rf Lexer.ml Lexer.cmi Lexer.cmo
	@make -C extraction clean_extraction

## Rules

extraction/%:
	make -C ./extraction $(@:extraction/%=%)

.SUFFIXES : .mli .ml .cmi .cmo .cmx

.mli.cmi:
	$(OCAMLC) -c $(IEXTRACTION) $(OCAMLFLAGS) $<

.ml.cmo:
	$(OCAMLC) -c $(IEXTRACTION) $(OCAMLFLAGS) $<

.ml.cmx:
	$(OCAMLOPT) -c $(IEXTRACTION) $(OCAMLFLAGS) $<

