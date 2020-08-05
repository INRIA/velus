include ../../../variables.mk

.PHONY: all clean

all: FrustreParser.v FrustreLexer.ml FrustreParser2.ml FrustreParser2.mli

clean:
	rm -f FrustreParser.v FrustreLexer.ml FrustreParser2.ml \
	      FrustreParser2.mli FrustreParser2.mly \
	      *.vo

FrustreParser.v: FrustreParser.vy
	$(MENHIR) --no-stdlib --coq --coq-no-complete $<

FrustreParser2.mly: FrustreParser.vy
	$(MENHIR) --no-stdlib --coq --only-preprocess-u $< > $@

FrustreLexer.ml: FrustreLexer.mll
	ocamllex $<

FrustreParser2.ml FrustreParser2.mli: FrustreParser2.mly
	$(MENHIR) --no-stdlib --table $<

