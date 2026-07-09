COQC ?= rocq c

all: transl.vo plugin_test.vo lemma_choice.vo basic.vo bugs.vo prover_selection.vo hashing.vo arith.vo zarith.vo lists.vo misc.vo extraction_transl.vo consistency-canary-dumps
	./check-consistency.sh
	@rm -f consistency-idiv.p consistency-h.p consistency-eq-rect.p consistency-nat-add.p

test-extraction: extraction_matches.vo extraction_deptypes.vo extraction_transl.vo consistency-canary-dumps
	./check-consistency.sh
	@rm -f consistency-idiv.p consistency-h.p consistency-eq-rect.p consistency-nat-add.p

consistency-canary-dumps: consistency_canaries.v extraction_deptypes.vo
	@rm -f consistency-idiv.p consistency-h.p consistency-eq-rect.p consistency-nat-add.p
	$(COQC) consistency_canaries.v

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
	@rm -f hammer_dump_smoke.p
	$(COQC) extraction_transl.v > extraction_transl.out 2>&1
	@if ! ./check-extraction-transl.sh extraction_transl.out; then \
	  cat extraction_transl.out; rm -f extraction_transl.vo extraction_transl.out hammer_dump_smoke.p; exit 1; \
	fi
	@if ! grep -Eq '^fof\(.*conjecture' hammer_dump_smoke.p; then \
	  echo "Hammer_dump smoke check FAILED"; cat hammer_dump_smoke.p 2>/dev/null || true; \
	  cat extraction_transl.out; rm -f extraction_transl.vo extraction_transl.out hammer_dump_smoke.p; exit 1; \
	fi
	@rm -f extraction_transl.out hammer_dump_smoke.p

clean:
	-rm -f *.vo *.glob *.out .*.aux hammer_dump_smoke.p consistency-idiv.p consistency-h.p consistency-eq-rect.p consistency-nat-add.p

.PHONY: all test-extraction consistency-canary-dumps clean
