.PRECIOUS: %.s

# Velus

VELUS=../velus
VELUS_OPT=-lib -dsch -dobc

# CompCert

ARCH_FLAGS=-mfloat-abi=hard -march=armv7-a -mfpu=vfpv3-d16

COMPCERT=$(realpath ../CompCert)
CCOMP=$(COMPCERT)/ccomp
CCOMP_OPT=-stdlib $(COMPCERT)/runtime

# For building ARM executables
CCOMP_EXTRA=-WUl,--specs=nosys.specs

# Heptagon

HEPT_LIB?=/usr/local/lib/heptagon
HEPT_FLAGS?=-stdlib $(HEPT_LIB) -deadcode -memalloc

# With GCC

GCC?=arm-none-eabi-gcc
GCC_NOINLINING?=-fno-inline-functions \
	      -fno-inline-functions-called-once \
	      -fno-inline-small-functions
GCC_FLAGS=-O1 $(GCC_NOINLINING) $(ARCH_FLAGS)
GCC_IFLAGS=-O1 $(ARCH_FLAGS)

# WCET

OTAWA_PATH?=~/Programming/synchrone/otawa/otawa

OWCET_FLAGS=--script trivial

EXAMPLES = \
	avgvelocity.lus \
	count.lus \
	tracker.lus \
	pip_ex.lus \
	cocospec_mono_system.lus \
	emsoft03.lus \
	emsoft05.lus \
	halbwachs.lus \
	rer.lus \
	kind_functionalChain.lus \
	landing_gear.lus \
	minus.lus \
	prodcell.lus \
	ums_verif.lus \
	\
	chrono.lus \
	cruise.lus \
	heater.lus \
	stopwatch.lus \
	buttons.lus \
	stepper_motor.lus

## Main targets

all: wcet

realclean: clean
	@rm -f *.wcet

clean:
	@rm -f *.exe
	@rm -f *.parsed.lus *.n.lus *.stc *.obc
	@rm -f *.light.c *.sync.c *.s *.o
	@rm -rf *_c/ *.mls *.epci *.log
	@rm -rf *.hept.* *.hept-gcc.*
	@rm -f *.bkp *.ff

%.s: %.lus
	$(VELUS) $(VELUS_OPT) -sync $<

%.exe: %.s
	$(CCOMP) $(V) $(CCOMP_OPT) -Wl,-emain_sync $(CCOMP_EXTRA) \
	    -o $@ $(@:.exe=.sync.c) $<

%.velus.s: %.lus
	$(VELUS) $(VELUS_OPT) -nomain $<
	mv $(<:.lus=.s) $@
	sed -i.bkp -e 's/\$$/_/g' $@

%.velus.exe: main.c %.velus.s
	$(CCOMP) $(V) $(CCOMP_OPT) -Wl,-emain_sync $(CCOMP_EXTRA) \
	    -o $@ $^

## Heptagon

%.hept.exe %.hept.c %.hept.s: %.ept
	heptc $(HEPT_FLAGS) -s $(<:.ept=) -target c $<
	(cd $(<:.ept=_c); \
	 $(CCOMP) $(V) $(CCOMP_OPT) -S -I $(HEPT_LIB)/c \
		 -o ../$(<:.ept=.hept.s) $(<:.ept=).c; \
	 $(CCOMP) $(V) $(CCOMP_OPT) \
		 -WUl,-L$(COMPCERT)/runtime $(CCOMP_EXTRA) \
		 -I $(HEPT_LIB)/c -o ../$@ \
		 $(<:.ept=_types.c) $(<:.ept=.c) _main.c; \
	 cp $(<:.ept=.c) ../$(<:.ept=.hept.c))

%.hept-gcc.exe %.hept-gcc.c %.hept-gcc.s: %.ept
	heptc $(HEPT_FLAGS) -s $(<:.ept=) -target c $<
	(cd $(<:.ept=_c); \
	 $(GCC) $(V) -S -I $(HEPT_LIB)/c -o ../$(<:.ept=.hept-gcc.s) \
		 $(GCC_FLAGS) $(<:.ept=).c; \
	 $(GCC) $(V) --specs=nosys.specs \
		-I $(HEPT_LIB)/c -o ../$@ \
		 $(GCC_FLAGS) $(<:.ept=_types.c) $(<:.ept=.c) _main.c; \
	 cp $(<:.ept=.c) ../$(<:.ept=.hept-gcc.c))

%.hept-gcci.exe %.hept-gcc.c %.hept-gcc.s: %.ept
	heptc $(HEPT_FLAGS) -s $(<:.ept=) -target c $<
	(cd $(<:.ept=_c); \
	 $(GCC) $(V) -S -I $(HEPT_LIB)/c -o ../$(<:.ept=.hept-gcc.s) \
		 $(GCC_IFLAGS) $(<:.ept=).c; \
	 $(GCC) $(V) --specs=nosys.specs \
		-I $(HEPT_LIB)/c -o ../$@ \
		 $(GCC_IFLAGS) $(<:.ept=_types.c) $(<:.ept=.c) _main.c; \
	 cp $(<:.ept=.c) ../$(<:.ept=.hept-gcc.c))

## WCET

wcet: velus.wcet hept.wcet hept-gcc.wcet hept-gcci.wcet

velus: $(EXAMPLES:.lus=.exe)
velus.wcet: $(EXAMPLES:.lus=.velus.wcet)

hept: $(EXAMPLES:.lus=.hept.exe)
hept.wcet: $(EXAMPLES:.lus=.hept.wcet)

hept-gcc: $(EXAMPLES:.lus=.hept-gcc.exe)
hept-gcc.wcet: $(EXAMPLES:.lus=.hept-gcc.wcet)

hept-gcci: $(EXAMPLES:.lus=.hept-gcci.exe)
hept-gcci.wcet: $(EXAMPLES:.lus=.hept-gcci.wcet)

%.ff: %.exe
	$(OTAWA_PATH)/bin/mkff -DBG $< >$@
	sed -i.bkp -e 's/?/1/g' $@

%.velus.wcet: %.velus.exe %.velus.ff
	for f in $$(nm $< | grep fun_ | cut -d ' ' -f 3); do \
	    $(OTAWA_PATH)/bin/owcet $(OWCET_FLAGS) -f $(<:.exe=.ff) $< $$f \
		| sed -e "s/^\(WCET\[\)fun_step_\(\w*\)/\1$(<:.velus.exe=).\2_step/" \
        | sed -e "s/^\(WCET\[\)fun_reset_\(\w*\)/\1$(<:.velus.exe=).\2_reset/"; \
	done >$@

%.hept.wcet: %.hept.exe %.hept.ff
	for f in $$(nm $< | grep -i "$(<:.hept.exe=).*\(step\|reset\)" | cut -d ' ' -f 3); do \
	    $(OTAWA_PATH)/bin/owcet $(OWCET_FLAGS) -f $(<:.exe=.ff) $< $$f \
		| sed -e "s/^\(WCET\[\).*__/\1$(<:.hept.exe=)./"; \
	done >$@

%.hept-gcc.wcet: %.hept-gcc.exe %.hept-gcc.ff
	for f in $$(nm $< | grep -i "$(<:.hept-gcc.exe=).*\(step\|reset\)" | cut -d ' ' -f 3); do \
	    $(OTAWA_PATH)/bin/owcet $(OWCET_FLAGS) -f $(<:.exe=.ff) $< $$f \
		| sed -e "s/^\(WCET\[\).*__/\1$(<:.hept-gcc.exe=)./"; \
	done >$@

%.hept-gcci.wcet: %.hept-gcci.exe %.hept-gcci.ff
	for f in $$(nm $< | grep -i "$(<:.hept-gcci.exe=).*\(step\|reset\)" | cut -d ' ' -f 3); do \
	    $(OTAWA_PATH)/bin/owcet $(OWCET_FLAGS) -f $(<:.exe=.ff) $< $$f \
		| sed -e "s/^\(WCET\[\).*__/\1$(<:.hept-gcci.exe=)./"; \
	done >$@

MAIN_NODES := $(shell cut -d ' ' -f 2 main.txt)

empty :=
space := $(empty) $(empty)
bar := |

groupwcet:
	@./groupwcet.ml | \
	    grep -E "^function|$(subst $(space),$(bar),$(MAIN_NODES))" | \
	    sed -e 's/_step/.step/' | \
		column -t

groupwcet.latex:
	@$(MAKE) --silent groupwcet \
	    | sed -e 's/^\(.*\)\.\(.*\)\.step/\2/' \
	    	  -e 's/  */ \& /g' \
			  -e 's/\(controller_2\)/heater~\\citep{lucy:manual:2006}/g' \
		      -e 's/\(cruisecontrol\)/\1~\\citep{lucy:manual:2006}/g' \
	    	  -e 's/\(chrono\)/\1~\\citep{ColacoPagPou:StateMachines:2005}/g' \
			  -e 's/\(stopwatch\)/stopwatch~\\citep{ColacoPagPou:SCADE:2017}/g' \
			  -e 's/\(buttons\)/\1~\\citep{ColacoPagPou:SCADE:2017}/g' \
	    	  -e 's/_/\\_/g' \
		  -e 's/$$/ \\\\/'
