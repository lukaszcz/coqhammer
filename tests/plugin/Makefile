LOCAL_ROCQLIB ?= ../../_check-install/coq
ifeq ($(USE_LOCAL_INSTALL),1)
ifneq ($(wildcard $(LOCAL_ROCQLIB)/theories),)
COQC ?= rocq c -coqlib $(LOCAL_ROCQLIB)
else
$(error USE_LOCAL_INSTALL=1 but LOCAL_ROCQLIB=$(LOCAL_ROCQLIB) has no theories directory)
endif
else
COQC ?= rocq c
endif

EXTRACTION_VOS := extraction_matches.vo extraction_deptypes.vo extraction_transl.vo
PLUGIN_VOS := transl.vo plugin_test.vo lemma_choice.vo basic.vo bugs.vo prover_selection.vo hashing.vo arith.vo zarith.vo lists.vo misc.vo $(EXTRACTION_VOS)

all: $(PLUGIN_VOS)
	COQC="$(COQC)" ./check-consistency.sh

test-extraction: $(EXTRACTION_VOS)

transl.vo: transl.v
	$(COQC) transl.v > transl.out 2>&1
	@if grep -q 'Init\.Logic\.' transl.out; then \
	  echo "Translation sanity check FAILED: logical constants not translated to FOL:"; \
	  cat transl.out; rm -f transl.vo transl.out; exit 1; \
	fi
	@rm -f transl.out

plugin_test.vo: plugin_test.v
	$(COQC) plugin_test.v

lemma_choice.vo: lemma_choice.v
	$(COQC) lemma_choice.v

basic.vo: basic.v
	$(COQC) basic.v

bugs.vo: bugs.v
	$(COQC) bugs.v

prover_selection.vo: prover_selection.v
	$(COQC) prover_selection.v

hashing.vo: hashing.v
	$(COQC) hashing.v

arith.vo: arith.v
	$(COQC) arith.v

zarith.vo: zarith.v
	$(COQC) zarith.v

lists.vo: lists.v
	$(COQC) lists.v

misc.vo: misc.v
	$(COQC) misc.v

extraction_matches.vo: extraction_matches.v
	$(COQC) extraction_matches.v

extraction_deptypes.vo: extraction_deptypes.v
	$(COQC) extraction_deptypes.v

extraction_transl.vo: extraction_transl.v extraction_matches.vo extraction_deptypes.vo check-extraction-transl.sh
	@set -e; \
	tmp=$$(mktemp -d); \
	trap 'rm -rf "$$tmp"' EXIT; \
	COQHAMMER_DUMP_DIR="$$tmp" $(COQC) extraction_transl.v > extraction_transl.out 2>&1 || { \
	  cat extraction_transl.out; rm -f extraction_transl.vo extraction_transl.out; exit 1; }; \
	if ! ./check-extraction-transl.sh extraction_transl.out; then \
	  cat extraction_transl.out; rm -f extraction_transl.vo extraction_transl.out; exit 1; \
	fi; \
	if ! grep -Eq '^fof\(.*conjecture' "$$tmp/hammer_dump_smoke.p"; then \
	  echo "Hammer_dump smoke check FAILED"; cat "$$tmp/hammer_dump_smoke.p" 2>/dev/null || true; \
	  cat extraction_transl.out; rm -f extraction_transl.vo extraction_transl.out; exit 1; \
	fi; \
	rm -f extraction_transl.out

clean:
	-rm -f *.vo *.glob *.out .*.aux

.PHONY: all test-extraction clean
