VELUS=../velus
VELUS_OPT=-dobc -dclight

COMPCERT=../CompCert
CCOMP=$(COMPCERT)/ccomp
CCOMP_OPT=-stdlib $(COMPCERT)/runtime

OTAWA_PATH?=/opt/otawa-core

# For building ARM executables
#EXTRA_CCOMP_ARGS=-WUl,--specs=nosys.specs

EXAMPLES= avgvelocity.lus \
	  cocospec_mono_system.lus \
	  count.lus \
	  cruise.lus \
	  emsoft03.lus \
	  halbwachs.lus \
	  kind_functionalChain.lus \
	  landing_gear.lus \
	  minus.lus \
	  new_watch.lus \
	  pip_ex.lus \
	  prodcell.lus \
	  tracker.lus \
	  ums_verif.lus

all: $(EXAMPLES:.lus=.exe)

wcet: $(EXAMPLES:.lus=.wcet)

realclean: clean
	@rm -f $(EXAMPLES:.lus=.exe) $(EXAMPLES:.lus=.ff)

clean:
	@rm -f $(EXAMPLES:.lus=.obc) $(EXAMPLES:.lus=.sn.lus)
	@rm -f $(EXAMPLES:.lus=.light.c) $(EXAMPLES:.lus=.sync.c)
	@rm -f $(EXAMPLES:.lus=.sync.bkp)
	@rm -f $(EXAMPLES:.lus=.s) $(EXAMPLES:.lus=.o)
	@rm -f $(EXAMPLES:.lus=.sync.o)
	@rm -f $(EXAMPLES:.lus=.s) $(EXAMPLES:.lus=.s.bkp)

# rules

%.wcet: %.exe %.ff
	for f in $$(nm $< | grep fun_ | cut -d ' ' -f 3); do \
	    $(OTAWA_PATH)/bin/owcet --script generic -f $(<:.exe=.ff) $< $$f \
		| sed -e "s/^\(WCET\[\)/\1$(<:.exe=)./"; \
	done >$@

%.ff: %.exe
	$(OTAWA_PATH)/bin/mkff $< >$@
	sed -i.bkp -e 's/?/1/g' $@

%.s: %.lus
	$(VELUS) $(VELUS_OPT) -sync $<
	sed -i.bkp -e 's/\$$/_/g' $(<:.lus=.sync.c)
	sed -i.bkp -e 's/\$$/_/g' $@

%.exe: %.s
	$(CCOMP) $(CCOMP_OPT) -Wl,-emain_sync $(EXTRA_CCOMP_ARGS) \
	    -o $@ $(@:.exe=.sync.c) $<

