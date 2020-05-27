default: all

all: Makefile.coq Makefile.coq.local
	$(MAKE) -f Makefile.coq

tactics: Makefile.coq.tactics
	$(MAKE) -f Makefile.coq.tactics

plugin: Makefile.coq.plugin Makefile.coq.plugin.local
	$(MAKE) -f Makefile.coq.plugin

mathcomp: Makefile.coq.mathcomp
	$(MAKE) -f Makefile.coq.mathcomp

install: Makefile.coq Makefile.coq.local
	$(MAKE) -f Makefile.coq install

install-tactics: Makefile.coq.tactics
	$(MAKE) -f Makefile.coq.tactics install

install-plugin: Makefile.coq.plugin Makefile.coq.plugin.local
	$(MAKE) -f Makefile.coq.plugin install

install-mathcomp: Makefile.coq.mathcomp
	$(MAKE) -f Makefile.coq.mathcomp install

uninstall: Makefile.coq Makefile.coq.local
	$(MAKE) -f Makefile.coq uninstall

uninstall-tactics: Makefile.coq.tactics
	$(MAKE) -f Makefile.coq.tactics uninstall

uninstall-plugin: Makefile.coq.plugin Makefile.coq.plugin.local
	$(MAKE) -f Makefile.coq.plugin uninstall

uninstall-mathcomp: Makefile.coq.mathcomp
	$(MAKE) -f Makefile.coq.mathcomp uninstall

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

Makefile.coq.plugin: _CoqProject.plugin
	coq_makefile -f _CoqProject.plugin -o Makefile.coq.plugin

Makefile.coq.tactics: _CoqProject.tactics
	coq_makefile -f _CoqProject.tactics -o Makefile.coq.tactics

Makefile.coq.mathcomp: _CoqProject.mathcomp
	coq_makefile -f _CoqProject.mathcomp -o Makefile.coq.mathcomp

tests:
	cd tests && $(MAKE) -B

quicktest: test-plugin test-tactics

test-plugin:
	$(MAKE) -B -C tests plugin_test.vo

test-tactics:
	$(MAKE) -B -C tests tactics_test.vo

clean: Makefile.coq Makefile.coq.local Makefile.coq.mathcomp
	$(MAKE) -f Makefile.coq cleanall
	-$(MAKE) -f Makefile.coq.mathcomp cleanall
	rm -f Makefile.coq Makefile.coq.conf Makefile.coq.tactics Makefile.coq.tactics.conf Makefile.coq.plugin Makefile.coq.plugin.conf Makefile.coq.mathcomp Makefile.coq.mathcomp.conf

.PHONY: default all tactics plugin mathcomp install install-tactics install-plugin install-mathcomp uninstall uninstall-tactics uninstall-plugin tests quicktest test-plugin test-tactics clean
