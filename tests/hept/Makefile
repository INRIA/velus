VELUS = ../../velus

TESTS := decl.ept float.ept const.ept

all: $(TESTS:.ept=.s)

%.s: %.ept
	$(VELUS) -heptc $<

clean:
	rm -f *.obc *.lus *.s *.log *.mls *epci
