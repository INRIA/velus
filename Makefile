#
# invoke make with 'VERBOSE=1' to verbose the output
#

include variables.mk

.PHONY: all clean compcert parser proof extraction $(VELUS) $(EXAMPLESDIR)

all: $(VELUS)

# COMPCERT COQ
compcert: $(COMPCERTDIR)/Makefile.config
	@echo "${bold}Building CompCert...${normal}"
	$(MAKE) $(COMPCERTFLAGS) #compcert.ini driver/Version.ml proof
	@echo "${bold}OK.${normal}"

# LUSTRE PARSER
parser:
	@echo "${bold}Building Lustre parser...${normal}"
	$(MAKE) $(PARSERFLAGS) all
	@echo "${bold}OK.${normal}"

# VELUS COQ
proof: compcert parser $(MAKEFILEAUTO) $(MAKEFILECONFIG)
	@echo "${bold}Building Velus proof...${normal}"
	test -f .depend || $(MAKE) -s -f $(MAKEFILEAUTO) depend
	$(MAKE) -s -f $(MAKEFILEAUTO) all
	@echo "${bold}OK.${normal}"

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
		Lustre/lustrelib.ml\
		NLustre/nlustrelib.ml\
		SyBloc/sybloclib.ml\
		Obc/obclib.ml\
		ObcToClight/interfacelib.ml\
		$(COMPCERT_INCLUDES:%=$(COMPCERTDIR)/%/*.ml*)\
		$(EXTRACTED)
	@echo "${bold}OK.${normal}"

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
