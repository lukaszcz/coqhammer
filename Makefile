all: Makefile.coq Makefile.coq.tactics Makefile.coq.local
	$(MAKE) -f Makefile.coq.tactics
	$(MAKE) -f Makefile.coq

install: install-tactics install-plugin

install-plugin: Makefile.coq Makefile.coq.local
	$(MAKE) -f Makefile.coq install

install-tactics: Makefile.coq.tactics
	$(MAKE) -f Makefile.coq.tactics install

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

Makefile.coq.tactics: _CoqProject.tactics
	coq_makefile -f _CoqProject.tactics -o Makefile.coq.tactics

tests:
	cd tests && $(MAKE) -B

clean: Makefile.coq Makefile.coq.tactics Makefile.coq.local
	$(MAKE) -f Makefile.coq cleanall
	$(MAKE) -f Makefile.coq.tactics cleanall
	rm -f Makefile.coq Makefile.coq.conf Makefile.coq.tactics Makefile.coq.tactics.conf

.PHONY: all install install-tactics install-plugin clean tests
