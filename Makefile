
BINDIR ?= $(if $(COQBIN),$(COQBIN),`coqc -where | xargs dirname | xargs dirname`/bin/)

default: all

all: tactics plugin predict htimeout

tactics:
	dune build -p coq-hammer-tactics

plugin: install-tactics predict htimeout
	dune build -p coq-hammer

install: install-tactics install-plugin

install-tactics: tactics
	dune install coq-hammer-tactics

install-plugin: plugin install-extra
	dune install coq-hammer

uninstall:
	dune build -p coq-hammer
	dune uninstall coq-hammer
	dune build -p coq-hammer-tactics
	dune uninstall coq-hammer-tactics
	-rm -f $(DESTDIR)$(BINDIR)predict
	-rm -f $(DESTDIR)$(BINDIR)htimeout

uninstall-tactics:
	dune build -p coq-hammer-tactics
	dune uninstall coq-hammer-tactics

uninstall-plugin:
	dune build -p coq-hammer
	dune uninstall coq-hammer
	-rm -f $(DESTDIR)$(BINDIR)predict
	-rm -f $(DESTDIR)$(BINDIR)htimeout

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

predict: src/predict/main.cpp src/predict/predictor.cpp src/predict/format.cpp src/predict/knn.cpp src/predict/nbayes.cpp src/predict/rforest.cpp src/predict/tfidf.cpp src/predict/dtree.cpp
	c++ -std=c++11 -DCOQ_MODE -O2 -Wall src/predict/main.cpp -o predict

htimeout: src/htimeout/htimeout.c
	cc -O2 -Wall src/htimeout/htimeout.c -o htimeout

install-extra: predict htimeout
	install -d $(DESTDIR)$(BINDIR)
	install -m 0755 predict $(DESTDIR)$(BINDIR)predict
	install -m 0755 htimeout $(DESTDIR)$(BINDIR)htimeout

clean:
	dune clean
	-rm -f predict htimeout
	$(MAKE) -C eval clean
	$(MAKE) -C tests/plugin clean
	$(MAKE) -C tests/tactics clean

.PHONY: default all tactics plugin mathcomp install install-tactics install-plugin install-mathcomp uninstall uninstall-tactics uninstall-plugin tests tests-plugin tests-tactics quicktest test-plugin test-tactics clean
