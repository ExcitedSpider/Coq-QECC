all: 
	@dune build mathcomp
	
barebone:
	@dune build barebone

clean:
	@dune clean

install:
	@dune install

uninstall:
	@dune uninstall

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all clean force
