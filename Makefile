#
# invoke make with 'VERBOSE=1' to verbose the output
#

include variables.mk

.PHONY: all clean compcert parser proof extraction $(VELUS) $(EXAMPLESDIR) documentation

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
	./$< -e ./$(EXTRACTION)/Extraction.v -f $(EXTRACTED) -o $@ $(COQPROJECT)

# EXTRACTION
extraction: proof
	@echo "${bold}Extracting Velus Ocaml code...${normal}"
	$(MAKE) -s -f $(MAKEFILEAUTO) $@
	cp -f $(PARSERDIR)/LustreLexer.ml\
		$(PARSERDIR)/Relexer.ml\
		$(PARSERDIR)/LustreParser2.ml\
		$(PARSERDIR)/LustreParser2.mli\
		$(SRC_DIR)/CoreExpr/coreexprlib.ml\
		$(SRC_DIR)/Lustre/lustrelib.ml\
		$(SRC_DIR)/NLustre/nlustrelib.ml\
		$(SRC_DIR)/Stc/stclib.ml\
		$(SRC_DIR)/Obc/obclib.ml\
		$(SRC_DIR)/ObcToClight/interfacelib.ml\
		$(COMPCERT_INCLUDES:%=$(COMPCERTDIR)/%/*.ml*)\
		$(EXTRACTED)
	@echo "${bold}OK.${normal}"

# VELUS
$(VELUS): extraction $(SRC_DIR)/$(VELUSMAIN).ml $(SRC_DIR)/veluslib.ml
	@echo "${bold}Building Velus...${normal}"
	ocamlbuild $(FLAGS) $(VELUSMAIN).$(TARGET)
	mv $(VELUSMAIN).$(TARGET) $@
	cp $(COMPCERTDIR)/compcert.ini $(BUILDDIR)/$(SRC_DIR)/compcert.ini
	@echo "${bold}Done.${normal}"

# TOOLS
$(AUTOMAKE): $(TOOLSDIR)/$(AUTOMAKE).ml
	ocamlopt -o $@ $<

$(TOOLSDIR)/$(AUTOMAKE).ml: $(TOOLSDIR)/$(AUTOMAKE).mll
	@echo "${bold}Building automake tool...${normal}"
	ocamllex $<

velustotex: extraction tools/velustotex.ml
	@echo "${bold}Building velustotex...${normal}"
	ocamlbuild $(FLAGS) -I tools $@.$(TARGET)
	mv $@.$(TARGET) $@
	cp $(COMPCERTDIR)/compcert.ini $(BUILDDIR)/tools/compcert.ini
	@echo "${bold}Done.${normal}"

# lus to v
lusgen: extraction tools/lusgen.ml tools/exportLustre.ml
	@echo "${bold}Building lusgen...${normal}"
	ocamlbuild $(FLAGS) -I tools $@.$(TARGET)
	mv $@.$(TARGET) $@
	cp $(COMPCERTDIR)/compcert.ini $(BUILDDIR)/tools/compcert.ini
	@echo "${bold}Done.${normal}"

# EXAMPLES
$(EXAMPLESDIR): $(VELUS)
	$(MAKE) $(EXAMPLESFLAGS)

# DOCUMENTATION
documentation: proof $(MAKEFILEAUTO)
	@echo "${bold}Exporting CompCert HTML doc...${normal}"
	$(MAKE) $(COMPCERTFLAGS) documentation
	@echo "${bold}OK.${normal}"
	@echo "${bold}Exporting Velus HTML doc...${normal}"
	mkdir -p doc/html
	rm -f doc/html/*.html
	make -s -f $(MAKEFILEAUTO) $@
	@echo "${bold}OK.${normal}"

# ARTIFACT
velus.tar.gz: cleanall
	tar -czf $@ \
	    CompCert \
	    readme.md \
	    configure \
	    includes \
	    variables.mk \
	    tools/automake.mll \
	    Makefile \
	    vfiles \
	    src/ \
	    extraction/ \
	    tests/*.lus \
	    examples/ \
	    doc/

# CLEAN
clean:
	if [ -f $(MAKEFILEAUTO) ] ; then $(MAKE) -s -f $(MAKEFILEAUTO) $@; fi;
	rm -f $(MAKEFILEAUTO)
	rm -f $(AUTOMAKE) $(TOOLSDIR)/$(AUTOMAKE).ml $(TOOLSDIR)/$(AUTOMAKE).cm* $(TOOLSDIR)/$(AUTOMAKE).o
	$(MAKE) $(PARSERFLAGS) $@
	$(MAKE) -C examples $@
	$(MAKE) -C tools $@
	$(MAKE) -C tests $@
	$(MAKE) -C benchs $@
	$(MAKE) -C src/Lustre/Parser $@
	ocamlbuild -clean

cleanall: clean
	rm -f $(MAKEFILECONFIG) $(COQPROJECT)
	$(MAKE) -C CompCert distclean
	$(MAKE) -C examples $@
	$(MAKE) -C tools $@
	$(MAKE) -C benchs $@
	$(MAKE) -C src/Lustre/Parser $@
	$(MAKE) -C tests $@

distclean: cleanall

realclean: cleanall

