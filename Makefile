
BINDIR ?= $(if $(COQBIN),$(COQBIN),`coqc -where | xargs dirname | xargs dirname`/bin/)

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
	-rm -rf _build
	rm -f Makefile.coq.tactics Makefile.coq.tactics.conf Makefile.coq.plugin Makefile.coq.plugin.conf Makefile.coq.mathcomp Makefile.coq.mathcomp.conf

dune: dune-tactics dune-plugin predict htimeout

dune-tactics:
	dune build -p coq-hammer-tactics

dune-plugin: dune-install-tactics predict htimeout
	dune build -p coq-hammer

dune-install: dune-install-tactics dune-install-plugin

dune-install-tactics: dune-tactics
	dune install coq-hammer-tactics

dune-install-plugin: dune-plugin install-extra
	dune install coq-hammer

dune-uninstall:
	dune build -p coq-hammer
	dune uninstall coq-hammer
	dune build -p coq-hammer-tactics
	dune uninstall coq-hammer-tactics
	-rm -f $(DESTDIR)$(BINDIR)predict
	-rm -f $(DESTDIR)$(BINDIR)htimeout

dune-uninstall-tactics:
	dune build -p coq-hammer-tactics
	dune uninstall coq-hammer-tactics

dune-uninstall-plugin:
	dune build -p coq-hammer
	dune uninstall coq-hammer
	-rm -f $(DESTDIR)$(BINDIR)predict
	-rm -f $(DESTDIR)$(BINDIR)htimeout

predict: src/predict/main.cpp src/predict/predictor.cpp src/predict/format.cpp src/predict/knn.cpp src/predict/nbayes.cpp src/predict/rforest.cpp src/predict/tfidf.cpp src/predict/dtree.cpp
	c++ -std=c++11 -DCOQ_MODE -O2 -Wall src/predict/main.cpp -o predict

htimeout: src/htimeout/htimeout.c
	cc -O2 -Wall src/htimeout/htimeout.c -o htimeout

install-extra: predict htimeout
	install -d $(DESTDIR)$(BINDIR)
	install -m 0755 predict $(DESTDIR)$(BINDIR)predict
	install -m 0755 htimeout $(DESTDIR)$(BINDIR)htimeout

dune-clean:
	dune clean
	-rm -f predict htimeout
	$(MAKE) -C eval clean
	$(MAKE) -C tests/plugin clean
	$(MAKE) -C tests/tactics clean

.PHONY: default all tactics plugin mathcomp install install-tactics install-plugin install-mathcomp uninstall uninstall-tactics uninstall-plugin tests tests-plugin tests-tactics quicktest test-plugin test-tactics clean dune dune-tactics dune-plugin dune-install dune-install-tactics dune-install-plugin dune-clean install-extra dune-uninstall dune-uninstall-tactics dune-uninstall-plugin
