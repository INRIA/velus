VELUS = ../../velus

TESTS := decl.ept float.ept const.ept record.ept static.ept array.ept

all: $(TESTS:.ept=.s)

%.s: %.ept
	$(VELUS) -heptc -dlustre $<

clean:
	rm -f *.obc *.lus *.s *.log *.mls *epci
