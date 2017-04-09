
## local configuration

OTAWA_PATH?=/opt/otawa-core
GCC?=arm-none-eabi-gcc

# Requires lustre-compat branch
HEPT_PATH?=$(HOME)/Projects/heptagon-working
HEPT_FLAGS?=-stdlib $(HEPT_PATH)/lib

# For building ARM executables
CCOMP_EXTRA=-WUl,--specs=nosys.specs

# Compiling with Lustre requires both the v4 and v6 distributions
#
# Configure Lustre v4 as usual (see distribution README):
#    export LUSTRE_INSTALL=/usr/local/lustre-v4-II.xx-yyyy
#    source $LUSTRE_INSTALL/setenv.sh
#
# Install Lustre v6 from opam following the instructions at
#   http://www-verimag.imag.fr/Lustre-V6.html

## standard definitions

VELUS=../velus
VELUS_OPT=-dobc -dclight -lib

COMPCERT=$(realpath ../CompCert)
CCOMP=$(COMPCERT)/ccomp
CCOMP_OPT=-stdlib $(COMPCERT)/runtime

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
	  # new_watch.lus

all: $(EXAMPLES:.lus=.exe)
wcet: $(EXAMPLES:.lus=.velus.wcet)

hept: $(EXAMPLES:.lus=.hept.exe)
hept.wcet: $(EXAMPLES:.lus=.hept.wcet)

hept-gcc: $(EXAMPLES:.lus=.hept-gcc.exe)
hept-gcc.wcet: $(EXAMPLES:.lus=.hept-gcc.wcet)

lus6: $(EXAMPLES:.lus=.lus6.exe)
lus6.wcet: $(EXAMPLES:.lus=.lus6.wcet)

lus6-gcc: $(EXAMPLES:.lus=.lus6-gcc.exe)
lus6-gcc.wcet: $(EXAMPLES:.lus=.lus6-gcc.wcet)

realclean: clean
	@rm -f $(EXAMPLES:.lus=.exe) $(EXAMPLES:.lus=.ff)
	@rm -f $(EXAMPLES:.lus=.hept.exe) $(EXAMPLES:.lus=.hept.ff)
	@rm -f $(EXAMPLES:.lus=.hept-gcc.exe) $(EXAMPLES:.lus=.hept-gcc.ff)
	@rm -f $(EXAMPLES:.lus=.lus6.exe) $(EXAMPLES:.lus=.lus6.ff)
	@rm -f $(EXAMPLES:.lus=.lus6-gcc.exe) $(EXAMPLES:.lus=.lus6-gcc.ff)
	@rm -f $(EXAMPLES:.lus=.velus.wcet) $(EXAMPLES:.lus=.hept.wcet)
	@rm -f $(EXAMPLES:.lus=.lus6.wcet) $(EXAMPLES:.lus=.lus6-gcc.wcet)

clean:
	@rm -f $(EXAMPLES:.lus=.obc) $(EXAMPLES:.lus=.sn.lus)
	@rm -f $(EXAMPLES:.lus=.light.c) $(EXAMPLES:.lus=.sync.c)
	@rm -f $(EXAMPLES:.lus=.sync.bkp) $(EXAMPLES:.lus=.ff.bkp)
	@rm -f $(EXAMPLES:.lus=.s) $(EXAMPLES:.lus=.o)
	@rm -f $(EXAMPLES:.lus=.sync.o) $(EXAMPLES:.lus=.sync.c.bkp)
	@rm -f $(EXAMPLES:.lus=.s) $(EXAMPLES:.lus=.s.bkp)
	@rm -f $(EXAMPLES:.lus=.hept.ff.bkp) $(EXAMPLES:.lus=.hept-gcc.ff.bkp)
	@rm -f $(EXAMPLES:.lus=.lus6.ff.bkp) $(EXAMPLES:.lus=.lus6-gcc.ff.bkp)
	@rm -f $(EXAMPLES:.lus=.obc) $(EXAMPLES:.lus=.epci)
	@rm -rf $(EXAMPLES:.lus=_c) $(EXAMPLES:.lus=.mls)
	@rm -f lustre_consts.c lustre_consts.h lustre_consts.o lustre_types.h
	for f in $(EXAMPLES:.lus=); do \
	    rm -f "$${f}_$${f}.c" "$${f}_$${f}.h" "$${f}_$${f}_loop.c" \
	    	"$${f}_$${f}.o" "$${f}_$${f}_loop.o"; \
	done

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

%.hept-gcc.wcet: %.hept-gcc.exe %.hept-gcc.ff
	for f in $$(nm $< | grep -i $(<:.hept-gcc.exe=)__ | cut -d ' ' -f 3); do \
	    $(OTAWA_PATH)/bin/owcet --script generic -f $(<:.exe=.ff) $< $$f \
		| sed -e "s/^\(WCET\[\).*__/\1$(<:.hept-gcc.exe=)./"; \
	done >$@

%.lus6.wcet: %.lus6.exe %.lus6.ff
	for f in $$(nm $< | egrep -i "$(<:.lus6.exe=)_.*(step|_ctx_reset)" \
	  | cut -d ' ' -f 3); do \
	    $(OTAWA_PATH)/bin/owcet --script generic -f $(<:.exe=.ff) $< $$f \
		| sed -e "s/^\(WCET\[\)$(<:.lus6.exe=)_/\1$(<:.lus6.exe=)./" \
		      -e "s/_ctx_reset/_reset/"; \
	done >$@

%.lus6-gcc.wcet: %.lus6-gcc.exe %.lus6-gcc.ff
	for f in $$(nm $< | egrep -i "$(<:.lus6-gcc.exe=)_.*(step|_ctx_reset)" \
	  | cut -d ' ' -f 3); do \
	    $(OTAWA_PATH)/bin/owcet --script generic -f $(<:.exe=.ff) $< $$f \
		| sed -e "s/^\(WCET\[\)$(<:.lus6-gcc.exe=)_/\1$(<:.lus6-gcc.exe=)./" \
		      -e "s/_ctx_reset/_reset/"; \
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

%.hept-gcc.exe: %.lus
	$(HEPT_PATH)/heptc $(HEPT_FLAGS) -s $(<:.lus=) -target c $<
	(cd $(<:.lus=_c); \
	 $(GCC) -O2 --specs=nosys.specs -I $(HEPT_PATH)/lib/c -o ../$@ \
		 $(<:.lus=)_types.c $(<:.lus=).c _main.c)

%.lus6.exe: %.lus
	-lus2lic -2c -o $(<:.lus=.c) \
	    -n $$(sed -ne  's/^node \([^ (]*\).*/\1/p' <$< | tail -1) $<
	 $(CCOMP) -stdlib $(COMPCERT) \
		 -WUl,-L$(COMPCERT)/runtime $(CCOMP_EXTRA) \
		 -o $@ lustre_consts.c \
		 $(<:.lus=)_$(<:.lus=).c $(<:.lus=)_$(<:.lus=)_loop.c

%.lus6-gcc.exe: %.lus
	-lus2lic -2c -o $(<:.lus=.c) \
	    -n $$(sed -ne  's/^node \([^ (]*\).*/\1/p' <$< | tail -1) $<
	 $(GCC) -O2 --specs=nosys.specs -o $@ lustre_consts.c \
		 $(<:.lus=)_$(<:.lus=).c $(<:.lus=)_$(<:.lus=)_loop.c

