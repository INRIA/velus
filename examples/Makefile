.PRECIOUS: %.s

# Velus

VELUS=../velus
VELUS_OPT=-lib -dsch -dobc

# CompCert

ARCH_FLAGS=-mfloat-abi=hard -march=armv7-a -mfpu=vfpv3-d16

COMPCERT=$(realpath ../CompCert)
CCOMP=$(COMPCERT)/ccomp
CCOMP_OPT=-stdlib $(COMPCERT)/runtime

EXAMPLES = \
	avgvelocity.lus \
	count.lus \
	rer.lus \
	rer-reset.lus \
	cruise.lus \
	emsoft03.lus \
	emsoft05.lus \
	halbwachs.lus \
	kind_functionalChain.lus \
	landing_gear.lus \
	minus.lus \
	nav.lus \
	pip_ex.lus \
	prodcell.lus \
	tracker.lus \
	ums_verif.lus \
	cocospec_mono_system.lus \
	new_watch.lus \
	stopwatch.lus \
	abro.lus \
	colors.lus \
	chrono.lus \
	stepper-motor.lus \

## Main targets

all: velus

velus: $(EXAMPLES:.lus=.exe)

cleanall: clean
	@rm -f $(EXAMPLES:.lus=.exe)

clean:
	@rm -f *.exe
	@rm -f *.parsed.lus *.n.lus *.stc *.obc
	@rm -f *.light.c *.sync.c *.s *.o

%.s: %.lus
	$(VELUS) $(VELUS_OPT) -sync $<

%.exe: %.s
	$(CCOMP) $(V) $(CCOMP_OPT) $(CCOMP_EXTRA) \
	    -o $@ $(@:.exe=.sync.c) $<
