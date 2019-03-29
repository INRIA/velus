#
# invoke make with 'VERBOSE=1' to verbose the output
#

VELUSMAIN=velusmain
VELUS=velus

MAKEFILEAUTO=Makefile.auto
MAKEFILECONFIG=Makefile.config
COQPROJECT=_CoqProject
include $(MAKEFILECONFIG)

# CompCert flags
COMPCERTFLAGS=$(SILENT) -C $(COMPCERTDIR)
COMPCERT_INCLUDES=lib cfrontend backend common driver cparser debug $(ARCH)

PARSERDIR=Lustre/Parser
PARSERFLAGS=$(SILENT) -C $(PARSERDIR)

TOOLSDIR=tools
AUTOMAKE=automake

EXTRACTION=extraction
EXTRACTED=$(EXTRACTION)/extracted
$(shell mkdir -p $(EXTRACTED) >/dev/null)

EXAMPLESDIR=examples
EXAMPLESFLAGS=$(SILENT) -C $(EXAMPLESDIR)

# Menhir includes from CompCert
include $(COMPCERTDIR)/Makefile.menhir
export MENHIR
comma:= ,
empty:=
space:= $(empty) $(empty)
MENHIR_INCLUDES:= $(subst $(space),$(comma),$(MENHIR_INCLUDES))

# ocamlbuild flags
VERBOSITY=-verbose 1
FLAGS=-use-ocamlfind -use-menhir -pkgs str,unix,menhirLib \
	-cflags $(MENHIR_INCLUDES)$(WARNINGS) \
	-I $(EXTRACTED) -no-hygiene $(VERBOSITY)
TARGET=native
BUILDDIR=_build

# flag to prevent coqc from taking CompCert directories into account (see Makefile.auto)
export OTHERFLAGS=-exclude-dir $(COMPCERTDIR)

bold=$(shell tput bold)
normal=$(shell tput sgr0)

.PHONY: all clean compcert parser proof extraction $(VELUS) $(EXAMPLESDIR)

all: $(VELUS)

ifndef VERBOSE
SILENT=-s
WARNINGS=,-w,-3-20
VERBOSITY=
.SILENT:
endif

# COMPCERT COQ
compcert: $(COMPCERTDIR)/Makefile.config
	@echo "${bold}Building CompCert...${normal}"
	$(MAKE) $(COMPCERTFLAGS) #compcert.ini driver/Version.ml proof

# LUSTRE PARSER
parser:
	@echo "${bold}Building Lustre parser...${normal}"
	$(MAKE) $(PARSERFLAGS) all

# VELUS COQ
proof: compcert parser $(MAKEFILEAUTO) $(MAKEFILECONFIG)
	@echo "${bold}Building Velus proof...${normal}"
	test -f .depend || $(MAKE) -s -f $(MAKEFILEAUTO) depend
	$(MAKE) -s -f $(MAKEFILEAUTO) all

$(MAKEFILEAUTO): automake $(COQPROJECT)
	./$< -e $(EXTRACTION)/Extraction.v -f $(EXTRACTED) -o $@ $(COQPROJECT)

# EXTRACTION
extraction: proof
	@echo "${bold}Extracting Velus Ocaml code...${normal}"
	$(MAKE) -s -f $(MAKEFILEAUTO) $@
	cp -f $(PARSERDIR)/LustreLexer.ml\
		$(PARSERDIR)/Relexer.ml\
		$(PARSERDIR)/LustreParser2.ml\
		$(PARSERDIR)/LustreParser2.mli\
		CoreExpr/coreexprlib.ml\
		NLustre/nlustrelib.ml\
		SyBloc/sybloclib.ml\
		Obc/obclib.ml\
		ObcToClight/interfacelib.ml\
		$(COMPCERT_INCLUDES:%=$(COMPCERTDIR)/%/*.ml*)\
		$(EXTRACTED)

# VELUS
$(VELUS): extraction $(VELUSMAIN).ml veluslib.ml
	@echo "${bold}Building Velus...${normal}"
	ocamlbuild $(FLAGS) $(VELUSMAIN).$(TARGET)
	mv $(VELUSMAIN).$(TARGET) $@
	cp $(COMPCERTDIR)/compcert.ini $(BUILDDIR)/compcert.ini
	@echo "${bold}Done.${normal}"

# TOOLS
$(AUTOMAKE): $(TOOLSDIR)/$(AUTOMAKE).ml
	ocamlopt -o $@ $<

$(TOOLSDIR)/$(AUTOMAKE).ml: $(TOOLSDIR)/$(AUTOMAKE).mll
	@echo "${bold}Building automake tool...${normal}"
	ocamllex $<

# EXAMPLES
$(EXAMPLESDIR): $(VELUS)
	$(MAKE) $(EXAMPLESFLAGS)

# CLEAN
clean:
	if [ -f $(MAKEFILEAUTO) ] ; then $(MAKE) -s -f $(MAKEFILEAUTO) $@; fi;
	rm -f $(MAKEFILEAUTO)
	rm -f $(AUTOMAKE) $(TOOLSDIR)/$(AUTOMAKE).ml $(TOOLSDIR)/$(AUTOMAKE).cm* $(TOOLSDIR)/$(AUTOMAKE).o
	$(MAKE) $(PARSERFLAGS) $@
	$(MAKE) $(EXAMPLESFLAGS) $@
	ocamlbuild -clean

realclean: clean
	rm -f $(MAKEFILECONFIG) $(COQPROJECT)
	$(MAKE) $(COMPCERTFLAGS) $<
	$(MAKE) $(EXAMPLESFLAGS) $@
