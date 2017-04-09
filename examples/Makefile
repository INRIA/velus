VELUS=../velus
VELUS_OPT=-dobc -dclight -lib

COMPCERT=$(realpath ../CompCert)
CCOMP=$(COMPCERT)/ccomp
CCOMP_OPT=-stdlib $(COMPCERT)/runtime

OTAWA_PATH?=/opt/otawa-core

GCC=arm-none-eabi-gcc

# Requires lustre-compat branch
HEPT_PATH?=$(HOME)/Projects/heptagon-working
HEPT_FLAGS?=-stdlib $(HEPT_PATH)/lib

# For building ARM executables
CCOMP_EXTRA=-WUl,--specs=nosys.specs

EXAMPLES= avgvelocity.lus \
	  count.lus \
	  cruise.lus \
	  emsoft03.lus \
	  halbwachs.lus \
	  kind_functionalChain.lus \
	  landing_gear.lus \
	  minus.lus \
	  pip_ex.lus \
	  prodcell.lus \
	  tracker.lus \
	  ums_verif.lus \
	  cocospec_mono_system.lus \
	  new_watch.lus

all: $(EXAMPLES:.lus=.exe)

wcet: $(EXAMPLES:.lus=.velus.wcet)

heptagon: $(EXAMPLES:.lus=.hept.exe)
hept.wcet: $(EXAMPLES:.lus=.hept.wcet)

heptagon-gcc: $(EXAMPLES:.lus=.heptgcc.exe)
heptagon-gcc.wcet: $(EXAMPLES:.lus=.heptgcc.wcet)

realclean: clean
	@rm -f $(EXAMPLES:.lus=.exe) $(EXAMPLES:.lus=.ff)
	@rm -f $(EXAMPLES:.lus=.hept.exe) $(EXAMPLES:.lus=.hept.ff)
	@rm -f $(EXAMPLES:.lus=.heptgcc.exe) $(EXAMPLES:.lus=.heptgcc.ff)
	@rm -f $(EXAMPLES:.lus=.velus.wcet) $(EXAMPLES:.lus=.hept.wcet)

clean:
	@rm -f $(EXAMPLES:.lus=.obc) $(EXAMPLES:.lus=.sn.lus)
	@rm -f $(EXAMPLES:.lus=.light.c) $(EXAMPLES:.lus=.sync.c)
	@rm -f $(EXAMPLES:.lus=.sync.bkp) $(EXAMPLES:.lus=.ff.bkp)
	@rm -f $(EXAMPLES:.lus=.s) $(EXAMPLES:.lus=.o)
	@rm -f $(EXAMPLES:.lus=.sync.o) $(EXAMPLES:.lus=.sync.c.bkp)
	@rm -f $(EXAMPLES:.lus=.s) $(EXAMPLES:.lus=.s.bkp)
	@rm -f $(EXAMPLES:.lus=hept.ff) $(EXAMPLES:.lus=.hept.ff.bkp)
	@rm -f $(EXAMPLES:.lus=.obc) $(EXAMPLES:.lus=.epci)
	@rm -rf $(EXAMPLES:.lus=_c) $(EXAMPLES:.lus=.mls)

# rules

%.velus.wcet: %.exe %.ff
	for f in $$(nm $< | grep fun_ | cut -d ' ' -f 3); do \
	    $(OTAWA_PATH)/bin/owcet --script generic -f $(<:.exe=.ff) $< $$f \
		| sed -e "s/^\(WCET\[\)fun_/\1$(<:.exe=)./"; \
	done >$@

%.hept.wcet: %.hept.exe %.hept.ff
	for f in $$(nm $< | grep -i $(<:.hept.exe=)__ | cut -d ' ' -f 3); do \
	    $(OTAWA_PATH)/bin/owcet --script generic -f $(<:.exe=.ff) $< $$f \
		| sed -e "s/^\(WCET\[\).*__/\1$(<:.hept.exe=)./"; \
	done >$@

%.heptgcc.wcet: %.hept.exe %.hept.ff
	for f in $$(nm $< | grep -i $(<:.hept.exe=)__ | cut -d ' ' -f 3); do \
	    $(OTAWA_PATH)/bin/owcet --script generic -f $(<:.exe=.ff) $< $$f \
		| sed -e "s/^\(WCET\[\).*__/\1$(<:.hept.exe=)./"; \
	done >$@

%.ff: %.exe
	$(OTAWA_PATH)/bin/mkff $< >$@
	sed -i.bkp -e 's/?/1/g' $@

%.s: %.lus
	$(VELUS) $(VELUS_OPT) -sync $<
	sed -i.bkp -e 's/\$$/_/g' $(<:.lus=.sync.c)
	sed -i.bkp -e 's/\$$/_/g' $@

%.exe: %.s
	$(CCOMP) -v $(CCOMP_OPT) -Wl,-emain_sync $(CCOMP_EXTRA) \
	    -o $@ $(@:.exe=.sync.c) $<

%.hept.exe: %.lus
	$(HEPT_PATH)/heptc $(HEPT_FLAGS) -s $(<:.lus=) -target c $<
	(cd $(<:.lus=_c); \
	 $(CCOMP) -stdlib $(COMPCERT) \
		 -WUl,-L$(COMPCERT)/runtime $(CCOMP_EXTRA) \
		 -I $(HEPT_PATH)/lib/c -o ../$@ \
		 $(<:.lus=)_types.c $(<:.lus=).c _main.c)

%.heptgcc.exe: %.lus
	$(HEPT_PATH)/heptc $(HEPT_FLAGS) -s $(<:.lus=) -target c $<
	(cd $(<:.lus=_c); \
	 $(GCC) -O2 --specs=nosys.specs -I $(HEPT_PATH)/lib/c -o ../$@ \
		 $(<:.lus=)_types.c $(<:.lus=).c _main.c)

