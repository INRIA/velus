VELUSMAIN=velusmain

COMPCERTDIR=CompCert
COMPCERTFLAGS=-s -C $(COMPCERTDIR) -j 8
COMPCERTTARGET=ia32-linux

PARSERDIR=Lustre/Parser

MAKEFILEAUTO=Makefile.auto
COQPROJECT=_CoqProject

EXTRACTION=extraction
EXTRACTED=$(EXTRACTION)/extracted
$(shell mkdir -p $(EXTRACTED) >/dev/null)

# Menhir includes from CompCert
include $(COMPCERTDIR)/Makefile.menhir
export MENHIR

comma:= ,
empty:=
space:= $(empty) $(empty)
MENHIR_INCLUDES:= $(subst $(space),$(comma),$(MENHIR_INCLUDES))

# flag to prevent coqc from taking CompCert directories into account
OTHERFLAGS=-exclude-dir $(COMPCERTDIR)
export OTHERFLAGS

.PHONY: all clean compcert parser proof extraction velus

all: velus

# COMPCERT COQ
compcert: $(COMPCERTDIR)/Makefile.config
	@$(MAKE) $(COMPCERTFLAGS) compcert.ini driver/Version.ml proof

$(COMPCERTDIR)/Makefile.config:
	@cd $(COMPCERTDIR); ./configure $(COMPCERTTARGET)

# LUSTRE PARSER
parser:
	@echo "Building parser"
	@$(MAKE) -s -C $(PARSERDIR) all

# VELUS COQ
proof: compcert $(MAKEFILEAUTO)
	@test -f .depend || $(MAKE) -s -f $(MAKEFILEAUTO) depend
	@$(MAKE) -s -f $(MAKEFILEAUTO) all

$(MAKEFILEAUTO): automake $(COQPROJECT)
	@./$< -e $(EXTRACTION)/Extraction.v -f $(EXTRACTED) -o $@ $(COQPROJECT)

# EXTRACTION
extraction: parser proof
	@$(MAKE) -s -f $(MAKEFILEAUTO) $@
	@cp -t $(EXTRACTED) $(PARSERDIR)/LustreLexer.ml\
						$(PARSERDIR)/Relexer.ml\
						$(PARSERDIR)/LustreParser2.ml\
						$(PARSERDIR)/LustreParser2.mli\
						NLustre/nlustrelib.ml\
						Obc/obclib.ml\
						ObcToClight/interfacelib.ml
# VELUS
velus: extraction $(VELUSMAIN).ml veluslib.ml
	@find $(COMPCERTDIR) -name '*.cm*' -delete
	@ocamlbuild -use-ocamlfind -j 8 -cflags $(MENHIR_INCLUDES),-w,-3,-w,-20 $(VELUSMAIN).native
	@mv $(VELUSMAIN).native $@
	@cp $(COMPCERTDIR)/compcert.ini _build/compcert.ini


# TOOLS
automake: tools/automake.ml
	@ocamlopt -o $@ $<

tools/automake.ml: tools/automake.mll
	@echo "Building 'automake' tool"
	@ocamllex $<

# CLEAN
clean:
	@test -f $(MAKEFILEAUTO) && $(MAKE) -s -f $(MAKEFILEAUTO) $@
	@rm -f $(MAKEFILEAUTO)
	@rm -f automake tools/automake.ml tools/automake.cm* tools/automake.o
	@$(MAKE) -s -C $(PARSERDIR) $@
	@ocamlbuild -clean
