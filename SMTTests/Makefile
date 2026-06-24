.PHONY: test clean

test:
	./runboth

clean:
	rm -f tempout scripts/tempout
	rm -f tests/*.actual scripts/*.actual

build:
	$(MAKE) -C ../SMT build
	
