VELUS = ../../velus

TESTS := decl.ept float.ept const.ept record.ept static.ept array.ept ledseq.ept

all: $(TESTS:.ept=.s) ledseq.exe

%.s %.h: %.ept
	$(VELUS) -heptc -dlustre -header -nomain $<

%.exe: %.s %.main.c
	gcc -o $@ $^

clean:
	rm -f *.obc *.lus *.s *.log *.mls *epci
