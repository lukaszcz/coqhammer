# OCaml unit tests for the parts of the plugin that need nothing from Rocq.
# They are compiled straight from the sources rather than linked against the
# installed plugin: coq_makefile installs hammer_plugin.cmxa without the
# companion .a, so the installed package cannot be linked into an executable.
# Hhlib is packed under the name the plugin sources open it by.

OCAMLFIND ?= ocamlfind
ROOT := ../..
BUILD := _build

TESTS := test_atp_names

.PHONY: all clean

all:
	@set -e; \
	rm -rf $(BUILD); \
	mkdir -p $(BUILD); \
	cp $(ROOT)/src/lib/hhlib.ml $(BUILD)/; \
	cp $(ROOT)/src/plugin/atp_names.mli $(ROOT)/src/plugin/atp_names.ml $(BUILD)/; \
	for t in $(TESTS); do cp $$t.ml $(BUILD)/; done; \
	cd $(BUILD); \
	$(OCAMLFIND) ocamlopt -package str -for-pack Hammer_lib -c hhlib.ml; \
	$(OCAMLFIND) ocamlopt -package str -pack -o hammer_lib.cmx hhlib.cmx; \
	$(OCAMLFIND) ocamlopt -package str -c atp_names.mli atp_names.ml; \
	for t in $(TESTS); do \
	  $(OCAMLFIND) ocamlopt -package str -linkpkg -o $$t \
	    hammer_lib.cmx atp_names.cmx $$t.ml; \
	  ./$$t; \
	done

clean:
	rm -rf $(BUILD)
