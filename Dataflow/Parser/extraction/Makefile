
PARSER_FILES=			\
	Peano.cmo		\
	Bool.cmo		\
	Datatypes.cmo		\
	Specif.cmo		\
	Orders.cmo		\
	OrdersTac.cmo		\
	OrdersFacts.cmo		\
	List0.cmo		\
	BinPos.cmo		\
	BinNat.cmo		\
	BinInt.cmo		\
	ZArith_dec.cmo 		\
	Int.cmo			\
	Int31.cmo		\
	Compare_dec.cmo 	\
	MSetInterface.cmo	\
	OrdersAlt.cmo		\
	OrderedType.cmo		\
	FMapList.cmo		\
	FMapAVL.cmo		\
	Alphabet.cmo		\
	Streams.cmo		\
	Tuples.cmo		\
	MSetAVL.cmo		\
	FSetAVL.cmo		\
	Validator_complete.cmo	\
	Interpreter_complete.cmo\
	Interpreter_correct.cmo	\
	Validator_safe.cmo	\
	Interpreter_safe.cmo	\
	Interpreter.cmo		\
	Main.cmo		\
	Parser.cmo

donotrun:
	 
Parser.cma: $(PARSER_FILES)
	$(OCAMLC) -a -o $@ $^

Parser.cmxa: $(PARSER_FILES:.cmo=.cmx)
	$(OCAMLOPT) -a -o $@ $^

clean_extraction:
	@rm -rf *.mli *.ml
	@rm -rf *.cmi *.cmo *.cmx *.cma *.cmxa *.o *.a
	@rm -rf extraction.glob extraction.vo

include ../Makefile
include depend
