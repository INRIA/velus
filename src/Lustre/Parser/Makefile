include ../../../variables.mk

.PHONY: all clean

all: LustreParser.v LustreLexer.ml LustreParser2.ml LustreParser2.mli

clean:
	rm -f LustreParser.v LustreLexer.ml LustreParser2.ml LustreParser2.mli LustreParser2.mly

cleanall: clean

LustreParser.v: LustreParser.vy
	$(MENHIR) --explain --no-stdlib --coq --coq-no-version-check $<

LustreParser2.mly: LustreParser.vy
	$(MENHIR) --no-stdlib --coq --only-preprocess-u $< > $@

LustreLexer.ml: LustreLexer.mll
	ocamllex $<

LustreParser2.ml LustreParser2.mli: LustreParser2.mly
	$(MENHIR) --no-stdlib --table $<
