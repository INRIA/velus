VELUSMAIN=velusmain

CORES=-j 4

COMPCERTDIR=CompCert
COMPCERTFLAGS=-s -C $(COMPCERTDIR) $(CORES)
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

# ocamlbuild flags
FLAGS=-use-ocamlfind $(CORES) -cflags $(MENHIR_INCLUDES),-w,-3,-w,-20
TARGET=native
BUILDDIR=_build

# flag to prevent coqc from taking CompCert directories into account
OTHERFLAGS=-exclude-dir $(COMPCERTDIR)
export OTHERFLAGS

bold=$(shell tput bold)
normal=$(shell tput sgr0)

.PHONY: all clean compcert parser proof extraction velus

all: velus

# COMPCERT COQ
compcert: $(COMPCERTDIR)/Makefile.config
	@echo "${bold}Building CompCert...${normal}"
	@$(MAKE) $(COMPCERTFLAGS) compcert.ini driver/Version.ml proof

$(COMPCERTDIR)/Makefile.config:
	@cd $(COMPCERTDIR); ./configure $(COMPCERTTARGET)

# LUSTRE PARSER
parser:
	@echo "${bold}Building Lustre parser...${normal}"
	@$(MAKE) -s -C $(PARSERDIR) all

# VELUS COQ
proof: compcert parser $(MAKEFILEAUTO)
	@echo "${bold}Building Velus proof...${normal}"
	@test -f .depend || $(MAKE) -s -f $(MAKEFILEAUTO) depend
	@$(MAKE) -s -f $(MAKEFILEAUTO) all

$(MAKEFILEAUTO): automake $(COQPROJECT)
	@./$< -e $(EXTRACTION)/Extraction.v -f $(EXTRACTED) -o $@ $(COQPROJECT)

# EXTRACTION
extraction: proof
	@echo "${bold}Extracting Velus Ocaml code...${normal}"
	@$(MAKE) -s -f $(MAKEFILEAUTO) $@
	@cp -f -t $(EXTRACTED)\
		$(PARSERDIR)/LustreLexer.ml\
		$(PARSERDIR)/Relexer.ml\
		$(PARSERDIR)/LustreParser2.ml\
		$(PARSERDIR)/LustreParser2.mli\
		NLustre/nlustrelib.ml\
		Obc/obclib.ml\
		ObcToClight/interfacelib.ml\
		CompCert/lib/*.ml*\
		CompCert/cfrontend/*.ml*\
		CompCert/backend/*.ml*\
		CompCert/common/*.ml*\
		CompCert/driver/*.ml*\
		CompCert/ia32/*.ml*\
		CompCert/arm/*.ml*\
		CompCert/powerpc/*.ml*\
		CompCert/cparser/*.ml*\
		CompCert/debug/*.ml*

# VELUS
velus: extraction $(VELUSMAIN).ml veluslib.ml
	@echo "${bold}Building Velus...${normal}"
#	@find $(COMPCERTDIR) -name '*.cm*' -delete
	@ocamlbuild $(FLAGS) $(VELUSMAIN).$(TARGET)
	@mv $(VELUSMAIN).$(TARGET) $@
	@cp $(COMPCERTDIR)/compcert.ini $(BUILDDIR)/compcert.ini

# TOOLS
automake: tools/automake.ml
	@ocamlopt -o $@ $<

tools/automake.ml: tools/automake.mll
	@echo "${bold}Building automake tool...${normal}"
	@ocamllex $<

# CLEAN
clean:
	@if [ -f $(MAKEFILEAUTO) ] ; then $(MAKE) -s -f $(MAKEFILEAUTO) $@; fi;
	@rm -f $(MAKEFILEAUTO)
	@rm -f automake tools/automake.ml tools/automake.cm* tools/automake.o
	@$(MAKE) -s -C $(PARSERDIR) $@
	@ocamlbuild -clean
