.PRECIOUS: %.s

## Local configuration

OTAWA_PATH?=/opt/otawa-core
GCC?=arm-none-eabi-gcc

# Requires lustre-compat branch
HEPT_PATH?=$(HOME)/Projects/heptagon-working
HEPT_FLAGS?=-stdlib $(HEPT_PATH)/lib -memalloc

# For building ARM executables
CCOMP_EXTRA=-WUl,--specs=nosys.specs

# Verbose or not
V?=

# Compiling with Lustre requires both the v4 and v6 distributions
#
# Configure Lustre v4 as usual (see distribution README):
#    export LUSTRE_INSTALL=/usr/local/lustre-v4-II.xx-yyyy
#    source $LUSTRE_INSTALL/setenv.sh
#
# Install Lustre v6 from opam following the instructions at
#   http://www-verimag.imag.fr/Lustre-V6.html

## Derived Configuration

MAIN_NODES := $(shell cut -d ' ' -f 2 main.txt)
MAIN_NODES_SHORT := $(shell sed -e 's/.* [^.]*\.\(.*\)_step/\1/' main.txt)

comma := ,
empty :=
space := $(empty) $(empty)
bar := |

ARCH_FLAGS=-mfloat-abi=hard -march=armv7-a -mfpu=vfpv3-d16

VELUS=../velus
VELUS_OPT=-dobc -dclight -lib

COMPCERT=$(realpath ../CompCert)
CCOMP=$(COMPCERT)/ccomp
CCOMP_OPT=-stdlib $(COMPCERT)/runtime \
	    -Wa$(comma)$(subst $(space),$(comma),$(ARCH_FLAGS))

GCC_NOINLINING?=-fno-inline-functions \
	      -fno-inline-functions-called-once \
	      -fno-inline-small-functions
GCC_FLAGS=-O1 $(GCC_NOINLINING) $(ARCH_FLAGS)

OWCET_FLAGS=--script trivial

EXAMPLES= avgvelocity.lus \
	  count.lus \
	  cruise.lus \
	  emsoft03.lus \
	  emsoft05.lus \
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

## Main targets

all: velus
wcet: velus.wcet

velus: $(EXAMPLES:.lus=.exe)
velus.wcet: $(EXAMPLES:.lus=.velus.wcet)

hept: $(EXAMPLES:.lus=.hept.exe)
hept.wcet: $(EXAMPLES:.lus=.hept.wcet)

hept-gcc: $(EXAMPLES:.lus=.hept-gcc.exe)
hept-gcc.wcet: $(EXAMPLES:.lus=.hept-gcc.wcet)

lus6: $(EXAMPLES:.lus=.lus6.exe)
lus6.wcet: $(EXAMPLES:.lus=.lus6.wcet)

lus6-gcc: $(EXAMPLES:.lus=.lus6-gcc.exe)
lus6-gcc.wcet: $(EXAMPLES:.lus=.lus6-gcc.wcet)

realclean: clean
	@rm -f $(EXAMPLES:.lus=.exe)
	@rm -f $(EXAMPLES:.lus=.hept.exe) $(EXAMPLES:.lus=.hept-gcc.exe)
	@rm -f $(EXAMPLES:.lus=.hept-gcci.exe)
	@rm -f $(EXAMPLES:.lus=.lus6.exe) $(EXAMPLES:.lus=.lus6-gcc.exe)
	@rm -f $(EXAMPLES:.lus=.lus6-gcci.exe)
	@rm -f $(EXAMPLES:.lus=.velus.wcet)
	@rm -f $(EXAMPLES:.lus=.hept.wcet) $(EXAMPLES:.lus=.hept-gcc.wcet)
	@rm -f $(EXAMPLES:.lus=.hept-gcci.wcet)
	@rm -f $(EXAMPLES:.lus=.lus6.wcet) $(EXAMPLES:.lus=.lus6-gcc.wcet)
	@rm -f  $(EXAMPLES:.lus=.lus6-gcci.wcet)

clean:
	@rm -f $(EXAMPLES:.lus=.light.c) $(EXAMPLES:.lus=.s)
	@rm -f $(EXAMPLES:.lus=.hept.s) $(EXAMPLES:.lus=.hept-gcc.s)
	@rm -f $(EXAMPLES:.lus=.lus6.s) $(EXAMPLES:.lus=.lus6-gcc.s)
	@rm -f $(EXAMPLES:.lus=.mls) $(EXAMPLES:.lus=.c)
	@rm -f $(EXAMPLES:.lus=.hept.c) $(EXAMPLES:.lus=.hept-gcc.c)
	@rm -f $(EXAMPLES:.lus=.lus6.c) $(EXAMPLES:.lus=.lus6-gcc.c)
	@rm -f $(EXAMPLES:.lus=.hept.ff) $(EXAMPLES:.lus=.hept-gcc.ff)
	@rm -f $(EXAMPLES:.lus=.lus6.ff) $(EXAMPLES:.lus=.lus6-gcc.ff)
	@rm -f $(EXAMPLES:.lus=.ff)
	@rm -f $(EXAMPLES:.lus=.sync.c)
	@rm -f $(EXAMPLES:.lus=.obc) $(EXAMPLES:.lus=.sn.lus)
	@rm -f $(EXAMPLES:.lus=.sync.bkp) $(EXAMPLES:.lus=.ff.bkp)
	@rm -f $(EXAMPLES:.lus=.o) $(EXAMPLES:.lus=.s.bkp)
	@rm -f $(EXAMPLES:.lus=.sync.o) $(EXAMPLES:.lus=.sync.c.bkp)
	@rm -f $(EXAMPLES:.lus=.hept.ff.bkp) $(EXAMPLES:.lus=.hept-gcc.ff.bkp)
	@rm -f $(EXAMPLES:.lus=.lus6.ff.bkp) $(EXAMPLES:.lus=.lus6-gcc.ff.bkp)
	@rm -f $(EXAMPLES:.lus=.epci) $(EXAMPLES:.lus=.h)
	@rm -f $(EXAMPLES:.lus=_loop.c) $(EXAMPLES:.lus=_loop.o)
	@rm -rf $(EXAMPLES:.lus=_c)
	@rm -f lustre_consts.c lustre_consts.h lustre_consts.o lustre_types.h
	@for f in $(EXAMPLES:.lus=); do \
	    rm -f "$${f}_$${f}.c" "$${f}_$${f}.h" \
	    	"$${f}_$${f}_loop.c" "$${f}_$${f}.o" "$${f}_$${f}_loop.o"; \
	done
	@rm -f $(MAIN_NODES_SHORT:=.sh)

# Utilities

wcet-help:
	@echo "# Preparation:"
	@echo "git format-patch -1 heptagon-hacks"
	@echo "git format-patch -1 idiv-hacks"
	@echo "patch -p2 < 0001-Avoid-integer-division-and-modulo-operators.patch"
	@echo "# WCET builds:"
	@echo "1. make realclean"
	@echo "2. patch -p2 < 0001-Patch-to-compile-examples-with-Heptagon.patch"
	@echo "3. make hept.wcet"
	@echo "4. make clean GCC_NOINLINING= hept-gcc.wcet rename-inlining.hept"
	@echo "5. make clean hept-gcc.wcet"
	@echo "6. git checkout *.lus; patch -p2 < 0001-Avoid-integer-division-and-modulo-operators.patch"
	@echo "7. make clean GCC_NOINLINING= lus6-gcc.wcet rename-inlining.lus6"
	@echo "8. make clean velus.wcet lus6.wcet lus6-gcc.wcet"
	@echo "9. make groupwcet"

groupwcet:
	@./groupwcet.ml | \
	    egrep "^function|$(subst $(space),$(bar),$(MAIN_NODES))" | \
	    sed -e 's/_step/.step/' | column -t

rename-inlining: rename-inlining.lus6 rename-inlining.hept

rename-inlining.lus6:
	@for f in $(EXAMPLES:.lus=); do \
	    [ -e $$f.lus6-gcc.wcet ] && mv $$f.lus6-gcc.wcet $$f.lus6-gcci.wcet; \
	    [ -e $$f.lus6-gcc.exe  ] && mv $$f.lus6-gcc.exe  $$f.lus6-gcci.exe;  \
	done

rename-inlining.hept:
	@for f in $(EXAMPLES:.lus=); do \
	    [ -e $$f.hept-gcc.wcet ] && mv $$f.hept-gcc.wcet $$f.hept-gcci.wcet; \
	    [ -e $$f.hept-gcc.exe  ] && mv $$f.hept-gcc.exe  $$f.hept-gcci.exe;  \
	done

# Rules

%.velus.wcet: %.exe %.ff
	for f in $$(nm $< | grep fun_ | cut -d ' ' -f 3); do \
	    $(OTAWA_PATH)/bin/owcet $(OWCET_FLAGS) -f $(<:.exe=.ff) $< $$f \
		| sed -e "s/^\(WCET\[\)fun_/\1$(<:.exe=)./"; \
	done >$@

%.hept.wcet: %.hept.exe %.hept.ff
	for f in $$(nm $< | grep -i $(<:.hept.exe=)__ | cut -d ' ' -f 3); do \
	    $(OTAWA_PATH)/bin/owcet $(OWCET_FLAGS) -f $(<:.exe=.ff) $< $$f \
		| sed -e "s/^\(WCET\[\).*__/\1$(<:.hept.exe=)./"; \
	done >$@

%.hept-gcc.wcet: %.hept-gcc.exe %.hept-gcc.ff
	for f in $$(nm $< | grep -i $(<:.hept-gcc.exe=)__ | cut -d ' ' -f 3); do \
	    $(OTAWA_PATH)/bin/owcet $(OWCET_FLAGS) -f $(<:.exe=.ff) $< $$f \
		| sed -e "s/^\(WCET\[\).*__/\1$(<:.hept-gcc.exe=)./"; \
	done >$@

%.lus6.wcet: %.lus6.exe %.lus6.ff
	for f in $$(nm $< | egrep -i "$(<:.lus6.exe=)_.*(step|_ctx_reset)" \
	  | cut -d ' ' -f 3); do \
	    $(OTAWA_PATH)/bin/owcet $(OWCET_FLAGS) -f $(<:.exe=.ff) $< $$f \
		| sed -e "s/^\(WCET\[\)$(<:.lus6.exe=)_/\1$(<:.lus6.exe=)./" \
		      -e "s/_ctx_reset/_reset/"; \
	done >$@

%.lus6-gcc.wcet: %.lus6-gcc.exe %.lus6-gcc.ff
	for f in $$(nm $< | egrep -i "$(<:.lus6-gcc.exe=)_.*(step|_ctx_reset)" \
	  | cut -d ' ' -f 3); do \
	    $(OTAWA_PATH)/bin/owcet $(OWCET_FLAGS) -f $(<:.exe=.ff) $< $$f \
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
	$(CCOMP) $(V) $(CCOMP_OPT) -Wl,-emain_sync $(CCOMP_EXTRA) \
	    -o $@ $(@:.exe=.sync.c) $<

%.hept.exe %.hept.c %.hept.s: %.lus
	$(HEPT_PATH)/heptc $(HEPT_FLAGS) -s $(<:.lus=) -target c $<
	(cd $(<:.lus=_c); \
	 $(CCOMP) $(V) $(CCOMP_OPT) -S -I $(HEPT_PATH)/lib/c \
		 -o ../$(<:.lus=.hept.s) $(<:.lus=).c; \
	 $(CCOMP) $(V) $(CCOMP_OPT) \
		 -WUl,-L$(COMPCERT)/runtime $(CCOMP_EXTRA) \
		 -I $(HEPT_PATH)/lib/c -o ../$@ \
		 $(<:.lus=_types.c) $(<:.lus=.c) _main.c; \
	 cp $(<:.lus=.c) ../$(<:.lus=.hept.c))

%.hept-gcc.exe %.hept-gcc.c %.hept-gcc.s: %.lus
	$(HEPT_PATH)/heptc $(HEPT_FLAGS) -s $(<:.lus=) -target c $<
	(cd $(<:.lus=_c); \
	 $(GCC) $(V) -S -I $(HEPT_PATH)/lib/c -o ../$(<:.lus=.hept-gcc.s) \
		 $(GCC_FLAGS) $(<:.lus=).c; \
	 $(GCC) $(V) --specs=nosys.specs \
		-I $(HEPT_PATH)/lib/c -o ../$@ \
		 $(GCC_FLAGS) $(<:.lus=_types.c) $(<:.lus=.c) _main.c; \
	 cp $(<:.lus=.c) ../$(<:.lus=.hept-gcc.c))

%.lus6.exe %.lus6.c %.lus6.s: %.lus
	-lus2lic -2c -o $(<:.lus=.c) \
	    -n $$(sed -ne  's/^node \([^ (]*\).*/\1/p' <$< | tail -1) $<
	 $(CCOMP) $(V) $(CCOMP_OPT) -S -o \
		 $(<:.lus=.lus6.s) $(<:.lus=).c; \
	 $(CCOMP) $(V) $(CCOMP_OPT) \
		 -WUl,-L$(COMPCERT)/runtime $(CCOMP_EXTRA) \
		 -o $@ lustre_consts.c $(<:.lus=).c $(<:.lus=)_loop.c
	 cp $(<:.lus=.c) $(<:.lus=.lus6.c)

%.lus6-gcc.exe %.lus6-gcc.c %.lus6-gcc.s: %.lus
	-lus2lic -2c -o $(<:.lus=.c) \
	    -n $$(sed -ne  's/^node \([^ (]*\).*/\1/p' <$< | tail -1) $<
	 $(GCC) $(V) -o $(<:.lus=.lus6-gcc.s) -S $(GCC_FLAGS) $(<:.lus=).c
	 $(GCC) $(V) --specs=nosys.specs -o $@ lustre_consts.c $(GCC_FLAGS) \
		$(<:.lus=).c $(<:.lus=)_loop.c
	 cp $(<:.lus=.c) $(<:.lus=.lus6-gcc.c)

