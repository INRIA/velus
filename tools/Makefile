# Makefile for rat
# TODO: put rules in velus/Makefile instead?

# avoid some findlib warnings about compiler-libs module names
export OCAMLFIND_IGNORE_DUPS_IN = $(shell ocamlc -where)/compiler-libs

OCAMLOPT=ocamlfind ocamlopt -package compiler-libs.common -linkpkg
OCAMLLEX=ocamllex

rat: rat.cmx
	$(OCAMLOPT) -o rat rat.cmx

%.cmx: %.ml
	$(OCAMLOPT) -c $*.ml

%.ml: %.mll
	$(OCAMLLEX) $*.mll

clean:
	rm -f rat
	rm -f rat.ml
	rm -f rat.o rat.cm?

# PREFIX=/usr/local
# BINDIR=$(PREFIX)/bin

# install:
# 	install rat $(BINDIR)/rat
