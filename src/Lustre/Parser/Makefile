include ../../../variables.mk

.PHONY: all clean

all: LustreParser.v LustreLexer.ml LustreParser2.ml LustreParser2.mli

clean:
	rm -f LustreParser.v LustreLexer.ml LustreParser2.ml LustreParser2.mli LustreParser2.mly

LustreParser.v: LustreParser.vy
	$(MENHIR) --no-stdlib --coq-lib-path compcert.cparser.MenhirLib --coq $<

LustreParser2.mly: LustreParser.vy
	$(MENHIR) --no-stdlib --coq --only-preprocess-u $< > $@

LustreLexer.ml: LustreLexer.mll
	ocamllex $<

LustreParser2.ml LustreParser2.mli: LustreParser2.mly
	$(MENHIR) --no-stdlib --table $<
