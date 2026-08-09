# OCaml unit tests for the parts of the plugin that need nothing from Rocq.
# They are compiled straight from the sources rather than linked against the
# installed plugin: coq_makefile installs hammer_plugin.cmxa without the
# companion .a, so the installed package cannot be linked into an executable.
# Hammer_lib is packed under the name the plugin sources open it by; its
# error module is a stub (see stubs/hammer_errors.ml).

OCAMLFIND ?= ocamlfind
ROOT := ../..
BUILD := _build

# modules packed into Hammer_lib, in dependency order
LIB := hhlib hammer_errors
# plugin modules compiled from $(ROOT)/src/plugin, in dependency order; every
# test is linked against all of them
MODULES := atp_names coq_transl_opts coqterms hashing paired_output
TESTS := test_atp_names test_hashing_match test_paired_output

.PHONY: all clean

all:
	@set -e; \
	rm -rf $(BUILD); \
	mkdir -p $(BUILD); \
	cp $(ROOT)/src/lib/hhlib.ml stubs/hammer_errors.ml $(BUILD)/; \
	for m in $(MODULES); do \
	  if [ -f $(ROOT)/src/plugin/$$m.mli ]; then \
	    cp $(ROOT)/src/plugin/$$m.mli $(BUILD)/; \
	  fi; \
	  cp $(ROOT)/src/plugin/$$m.ml $(BUILD)/; \
	done; \
	for t in $(TESTS); do cp $$t.ml $(BUILD)/; done; \
	cd $(BUILD); \
	for m in $(LIB); do \
	  $(OCAMLFIND) ocamlopt -package str,unix -for-pack Hammer_lib -c $$m.ml; \
	done; \
	$(OCAMLFIND) ocamlopt -package str,unix -pack -o hammer_lib.cmx \
	  $(addsuffix .cmx,$(LIB)); \
	for m in $(MODULES); do \
	  if [ -f $$m.mli ]; then $(OCAMLFIND) ocamlopt -package str,unix -c $$m.mli; fi; \
	  $(OCAMLFIND) ocamlopt -package str,unix -c $$m.ml; \
	done; \
	for t in $(TESTS); do \
	  $(OCAMLFIND) ocamlopt -package str,unix -linkpkg -o $$t \
	    hammer_lib.cmx $(addsuffix .cmx,$(MODULES)) $$t.ml; \
	  ./$$t; \
	done

clean:
	rm -rf $(BUILD)
