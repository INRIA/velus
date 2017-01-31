.PHONY: all clean

all: LustreParser.v

clean:
	rm -f LustreParser.v

LustreParser.v: LustreParser.vy
	$(MENHIR) --no-stdlib --coq $<
