
BINDIR ?= $(if $(COQBIN),$(COQBIN),`rocq c -where | xargs dirname | xargs dirname`/bin/)
DUNE ?= dune

default: all

all:
	$(MAKE) tactics
	$(MAKE) install-tactics
	$(MAKE) plugin

tactics: Makefile.coq.tactics
	-rm -f META
	$(MAKE) -f Makefile.coq.tactics

plugin: Makefile.coq.plugin Makefile.coq.plugin.local
	-rm -f META
	$(MAKE) -f Makefile.coq.plugin

mathcomp: Makefile.coq.mathcomp
	$(MAKE) -f Makefile.coq.mathcomp

install: install-tactics install-plugin

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
	rocq makefile -f _CoqProject.plugin -o Makefile.coq.plugin

Makefile.coq.tactics: _CoqProject.tactics
	rocq makefile -f _CoqProject.tactics -o Makefile.coq.tactics

Makefile.coq.mathcomp: _CoqProject.mathcomp
	rocq makefile -f _CoqProject.mathcomp -o Makefile.coq.mathcomp

tests: install test-unit tests-plugin tests-tactics

tests-plugin: install
	$(MAKE) -B -C tests/plugin

tests-tactics: install
	$(MAKE) -B -C tests/tactics

quicktest: install test-unit test-plugin test-tactics

# OCaml unit tests: compiled from the sources, so they need no installation
# and no external prover.
test-unit:
	$(MAKE) -B -C tests/unit

test-plugin: install
	$(MAKE) -B -C tests/plugin plugin_test.vo

test-plugin-release: test-unit test-plugin test-extraction

test-extraction: install
	$(MAKE) -B -C tests/plugin test-extraction

test-consistency: install
	$(MAKE) -C tests/plugin test-consistency

test-tactics: install
	$(MAKE) -B -C tests/tactics tactics_test.vo

clean: Makefile.coq.tactics Makefile.coq.plugin Makefile.coq.plugin.local Makefile.coq.mathcomp
	$(MAKE) -f Makefile.coq.tactics cleanall
	-$(MAKE) -f Makefile.coq.plugin cleanall
	-$(MAKE) -f Makefile.coq.mathcomp cleanall
	-rm -rf _build
	rm -f Makefile.coq.tactics Makefile.coq.tactics.conf Makefile.coq.plugin Makefile.coq.plugin.conf Makefile.coq.mathcomp Makefile.coq.mathcomp.conf META

dune: dune-tactics dune-plugin

dune-tactics:
	$(DUNE) build -p coq-hammer-tactics

dune-plugin:
	$(DUNE) build -p coq-hammer-tactics,coq-hammer

dune-test-plugin: install test-unit
	$(DUNE) build @tests/plugin/runtest

dune-install: dune-install-tactics dune-install-plugin

dune-install-tactics: dune-tactics
	$(DUNE) install coq-hammer-tactics

dune-install-plugin: dune-plugin
	$(DUNE) install coq-hammer

dune-uninstall:
	$(DUNE) uninstall coq-hammer coq-hammer-tactics

dune-uninstall-tactics:
	$(DUNE) uninstall coq-hammer-tactics

dune-uninstall-plugin:
	$(DUNE) uninstall coq-hammer

dune-clean:
	$(DUNE) clean
	$(MAKE) -C eval clean
	$(MAKE) -C tests/plugin clean
	$(MAKE) -C tests/tactics clean
	$(MAKE) -C tests/unit clean

.PHONY: default all tactics plugin mathcomp install install-tactics install-plugin install-mathcomp uninstall uninstall-tactics uninstall-plugin tests tests-plugin tests-tactics quicktest test-unit test-plugin test-plugin-release test-tactics test-extraction test-consistency clean dune dune-tactics dune-plugin dune-test-plugin dune-install dune-install-tactics dune-install-plugin dune-clean install-extra dune-uninstall dune-uninstall-tactics dune-uninstall-plugin
