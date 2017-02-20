VELUS=../velus
VELUS_OPT=-dobc -dclight

COMPCERT=../CompCert
CCOMP=$(COMPCERT)/ccomp
CCOMP_OPT=-stdlib $(COMPCERT)/runtime

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

realclean: clean
	@rm -f $(EXAMPLES:.lus=.exe)

clean:
	@rm -f $(EXAMPLES:.lus=.obc) $(EXAMPLES:.lus=.sn.lus)
	@rm -f $(EXAMPLES:.lus=.light.c) $(EXAMPLES:.lus=.sync.c)
	@rm -f $(EXAMPLES:.lus=.s) $(EXAMPLES:.lus=.o)
	@rm -f $(EXAMPLES:.lus=.sync.o)

# rules

%.s: %.lus
	$(VELUS) $(VELUS_OPT) -sync $<

%.exe: %.s
	$(CCOMP) $(CCOMP_OPT) -Wl,-emain_sync -o $@ $(@:.exe=.sync.c) $<

