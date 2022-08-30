default: all

all: tactics plugin

tactics: Makefile.coq.tactics
	$(MAKE) -f Makefile.coq.tactics

plugin: install-tactics Makefile.coq.plugin Makefile.coq.plugin.local
	$(MAKE) -f Makefile.coq.plugin

mathcomp: Makefile.coq.mathcomp
	$(MAKE) -f Makefile.coq.mathcomp

install: install-plugin

install-tactics: tactics
	$(MAKE) -f Makefile.coq.tactics install

install-plugin: plugin
	$(MAKE) -f Makefile.coq.plugin install

install-mathcomp: Makefile.coq.mathcomp
	$(MAKE) -f Makefile.coq.mathcomp install

uninstall: uninstall-tactics uninstall-plugin

uninstall-tactics: Makefile.coq.tactics
	$(MAKE) -f Makefile.coq.tactics uninstall

uninstall-plugin: Makefile.coq.plugin Makefile.coq.plugin.local
	$(MAKE) -f Makefile.coq.plugin uninstall

uninstall-mathcomp: Makefile.coq.mathcomp
	$(MAKE) -f Makefile.coq.mathcomp uninstall

Makefile.coq.plugin: _CoqProject.plugin
	coq_makefile -f _CoqProject.plugin -o Makefile.coq.plugin

Makefile.coq.tactics: _CoqProject.tactics
	coq_makefile -f _CoqProject.tactics -o Makefile.coq.tactics

Makefile.coq.mathcomp: _CoqProject.mathcomp
	coq_makefile -f _CoqProject.mathcomp -o Makefile.coq.mathcomp

tests: tests-plugin tests-tactics

tests-plugin:
	$(MAKE) -B -C tests/plugin

tests-tactics:
	$(MAKE) -B -C tests/tactics

quicktest: test-plugin test-tactics

test-plugin:
	$(MAKE) -B -C tests/plugin plugin_test.vo

test-tactics:
	$(MAKE) -B -C tests/tactics tactics_test.vo

clean: Makefile.coq.tactics Makefile.coq.plugin Makefile.coq.plugin.local Makefile.coq.mathcomp
	$(MAKE) -f Makefile.coq.tactics cleanall
	-$(MAKE) -f Makefile.coq.plugin cleanall
	-$(MAKE) -f Makefile.coq.mathcomp cleanall
	rm -f Makefile.coq.tactics Makefile.coq.tactics.conf Makefile.coq.plugin Makefile.coq.plugin.conf Makefile.coq.mathcomp Makefile.coq.mathcomp.conf

.PHONY: default all tactics plugin mathcomp install install-tactics install-plugin install-mathcomp uninstall uninstall-tactics uninstall-plugin tests tests-plugin tests-tactics quicktest test-plugin test-tactics clean
