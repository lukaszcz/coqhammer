default: all

all: Makefile.coq Makefile.coq.local
	$(MAKE) -f Makefile.coq

tactics: Makefile.coq.tactics
	$(MAKE) -f Makefile.coq.tactics

plugin: Makefile.coq.plugin Makefile.coq.plugin.local
	$(MAKE) -f Makefile.coq.plugin

install: Makefile.coq Makefile.coq.local
	$(MAKE) -f Makefile.coq install

install-tactics: Makefile.coq.tactics
	$(MAKE) -f Makefile.coq.tactics install

install-plugin: Makefile.coq.plugin Makefile.coq.plugin.local
	$(MAKE) -f Makefile.coq.plugin install

uninstall: Makefile.coq Makefile.coq.local
	$(MAKE) -f Makefile.coq uninstall

uninstall-tactics: Makefile.coq.tactics
	$(MAKE) -f Makefile.coq.tactics uninstall

uninstall-plugin: Makefile.coq.plugin Makefile.coq.plugin.local
	$(MAKE) -f Makefile.coq.plugin uninstall

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

Makefile.coq.plugin: _CoqProject.plugin
	coq_makefile -f _CoqProject.plugin -o Makefile.coq.plugin

Makefile.coq.tactics: _CoqProject.tactics
	coq_makefile -f _CoqProject.tactics -o Makefile.coq.tactics

tests:
	cd tests && $(MAKE) -B

clean: Makefile.coq Makefile.coq.local
	$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf Makefile.coq.tactics Makefile.coq.tactics.conf Makefile.coq.plugin Makefile.coq.plugin.conf

.PHONY: default all tactics plugin install install-tactics install-plugin uninstall uninstall-tactics uninstall-plugin tests clean
