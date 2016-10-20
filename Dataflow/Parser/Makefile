MENHIR?=$(OCAMLBIN)menhir
OCAMLLEX?=$(OCAMLBIN)ocamllex
OCAMLDEP?=$(OCAMLBIN)ocamldep
OCAMLC?=$(OCAMLBIN)ocamlc
OCAMLOPT?=$(OCAMLBIN)ocamlopt
COQC?=$(COQBIN)coqc

COQ_LOAD_PATH=-R . Rustre.Dataflow.Parser \
  	      -R ../../CompCert/cparser/validator compcert.cparser.validator

default: Parser.vo Lexer.cmo extraction/Parser.cma

extraction/Parser.ml: extraction/extraction.v Parser.vo Ast.vo
	$(COQC) $(COQ_LOAD_PATH) $(<:.v=)
	(cd extraction; ocamldep *.ml *.mli > depend)

Parser.v: Parser.vy
	$(MENHIR) --no-stdlib --coq $<

Lexer.ml: Lexer.mll
	$(OCAMLLEX) $<

extraction/Parser.cmo: extraction/Parser.ml
extraction/Parser.cmx: extraction/Parser.ml
extraction/Parser.cma: extraction/Parser.cmo
extraction/Parser.cmxa: extraction/Parser.cmx

Lexer.cmo: extraction/Ast.cmo extraction/Parser.cmo Lexer.ml
Lexer.cmo: IEXTRACTION:=-I extraction
Lexer.cmx: extraction/Ast.cmx extraction/Parser.cmx Lexer.ml
Lexer.cmx: IEXTRACTION:=-I extraction

Parser.vo: Parser.v Ast.vo
	$(COQC) $(COQ_LOAD_PATH) $(<:.v=)

Ast.vo: Ast.v
	$(COQC) $(COQ_LOAD_PATH) $(<:.v=)

clean:
	@rm -rf Parser.vo Parser.v Parser.glob
	@rm -rf Ast.vo Ast.glob
	@rm -rf Lexer.ml
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

