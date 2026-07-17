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

EXTRACTION_VOS := extraction_matches.vo extraction_deptypes.vo case_prop_transl.vo extraction_transl.vo
PLUGIN_VOS := transl.vo plugin_test.vo lemma_choice.vo basic.vo bugs.vo prover_selection.vo hashing.vo arith.vo zarith.vo lists.vo misc.vo $(EXTRACTION_VOS)

all: $(PLUGIN_VOS)
	COQC="$(COQC)" ./check-consistency.sh

test-extraction: $(EXTRACTION_VOS)
	COQC="$(COQC)" ./check-consistency.sh

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

case_prop_transl.vo: case_prop_transl.v
	@set -e; \
	tmp=$$(mktemp -d); \
	trap 'rm -rf "$$tmp"' EXIT; \
	COQHAMMER_DUMP_DIR="$$tmp" $(COQC) case_prop_transl.v > case_prop_transl.out 2>&1 || { \
	  cat case_prop_transl.out; rm -f case_prop_transl.vo case_prop_transl.out; exit 1; }; \
	grep -Eq '^\$$_def_case_prop_transl\.case_prop[$$]lower:' case_prop_transl.out || { \
	  echo "proposition-valued case lower-bound check FAILED"; cat case_prop_transl.out; \
	  rm -f case_prop_transl.vo case_prop_transl.out; exit 1; }; \
	grep -Eq '^\$$_def_case_prop_transl\.case_prop[$$]upper:' case_prop_transl.out || { \
	  echo "proposition-valued case upper-bound check FAILED"; cat case_prop_transl.out; \
	  rm -f case_prop_transl.vo case_prop_transl.out; exit 1; }; \
	grep -Eq '^\$$_def_case_prop_transl\.compound_case_prop[$$]link:' case_prop_transl.out || { \
	  echo "compound proposition case link check FAILED"; cat case_prop_transl.out; \
	  rm -f case_prop_transl.vo case_prop_transl.out; exit 1; }; \
	grep -Eq '^\$$_case_Corelib\.Init\.Datatypes\.nat[$$][0-9]+[$$]lower:.*[$$]HasType.*Corelib\.Init\.Datatypes\.nat' case_prop_transl.out || { \
	  echo "compound proposition case typed auxiliary check FAILED"; cat case_prop_transl.out; \
	  rm -f case_prop_transl.vo case_prop_transl.out; exit 1; }; \
	grep -Eq '^\$$_def_case_prop_transl\.false_case_prop[$$]lower:.*[$$]False' case_prop_transl.out || { \
	  echo "empty proposition case inhabitation-guard check FAILED"; cat case_prop_transl.out; \
	  rm -f case_prop_transl.vo case_prop_transl.out; exit 1; }; \
	grep -Eq '^\$$_def_case_prop_transl\.false_case_prop[$$]upper:.*[$$]False' case_prop_transl.out || { \
	  echo "empty proposition case upper-bound check FAILED"; cat case_prop_transl.out; \
	  rm -f case_prop_transl.vo case_prop_transl.out; exit 1; }; \
	grep -Eq '^\$$_def_case_prop_transl\.eq_case_prop[$$]lower:' case_prop_transl.out || { \
	  echo "indexed proposition case lower-bound check FAILED"; cat case_prop_transl.out; \
	  rm -f case_prop_transl.vo case_prop_transl.out; exit 1; }; \
	grep -Eq '^\$$_def_case_prop_transl\.eq_case_prop[$$]upper:' case_prop_transl.out || { \
	  echo "indexed proposition case upper-bound check FAILED"; cat case_prop_transl.out; \
	  rm -f case_prop_transl.vo case_prop_transl.out; exit 1; }; \
	if grep -Eq '^\$$_def_case_prop_transl\.eq_case_prop[$$](lower|upper):.*3_e' case_prop_transl.out; then \
	  echo "indexed proposition case leaked its erased proof variable"; cat case_prop_transl.out; \
	  rm -f case_prop_transl.vo case_prop_transl.out; exit 1; \
	fi; \
	two_false_line=$$(grep -E '^\$$_def_case_prop_transl\.two_false_case_props:' case_prop_transl.out); \
	false_case_occurrences=$$(printf '%s\n' "$$two_false_line" | \
	  grep -Eo '\$$_case_Corelib\.Init\.Logic\.False[$$][0-9]+' | wc -l); \
	false_case_symbols=$$(printf '%s\n' "$$two_false_line" | \
	  grep -Eo '\$$_case_Corelib\.Init\.Logic\.False[$$][0-9]+' | sort -u | wc -l); \
	if [ "$$false_case_occurrences" -ne 2 ] || [ "$$false_case_symbols" -ne 2 ]; then \
	  echo "distinct proof-dependent case occurrence identity check FAILED"; cat case_prop_transl.out; \
	  rm -f case_prop_transl.vo case_prop_transl.out; exit 1; \
	fi; \
	grep -Eq '^\$$_def_case_prop_transl\.sumbool_case_prop[$$]lower:' case_prop_transl.out || { \
	  echo "proof-payload proposition case lower-bound check FAILED"; cat case_prop_transl.out; \
	  rm -f case_prop_transl.vo case_prop_transl.out; exit 1; }; \
	grep -Eq '^\$$_def_case_prop_transl\.sumbool_case_prop[$$]upper:' case_prop_transl.out || { \
	  echo "proof-payload proposition case upper-bound check FAILED"; cat case_prop_transl.out; \
	  rm -f case_prop_transl.vo case_prop_transl.out; exit 1; }; \
	grep -Eq '^\$$_def_case_prop_transl\.vec_case_prop[$$]lower:.*1_n = Corelib\.Init\.Datatypes\.O.*1_n = \(Corelib\.Init\.Datatypes\.S @' case_prop_transl.out || { \
	  echo "general indexed proposition case lower-bound check FAILED"; cat case_prop_transl.out; \
	  rm -f case_prop_transl.vo case_prop_transl.out; exit 1; }; \
	grep -Eq '^\$$_def_case_prop_transl\.vec_case_prop[$$]upper:.*1_n = Corelib\.Init\.Datatypes\.O.*1_n = \(Corelib\.Init\.Datatypes\.S @' case_prop_transl.out || { \
	  echo "general indexed proposition case upper-bound check FAILED"; cat case_prop_transl.out; \
	  rm -f case_prop_transl.vo case_prop_transl.out; exit 1; }; \
	grep -Eq '^\$$_def_case_prop_transl\.compound_eq_case_prop[$$]link:' case_prop_transl.out || { \
	  echo "compound indexed proof case link check FAILED"; cat case_prop_transl.out; \
	  rm -f case_prop_transl.vo case_prop_transl.out; exit 1; }; \
	grep -Eq '^\$$_def_case_prop_transl\.nested_eq_case_prop[$$]link:' case_prop_transl.out || { \
	  echo "nested compound proof case link check FAILED"; cat case_prop_transl.out; \
	  rm -f case_prop_transl.vo case_prop_transl.out; exit 1; }; \
	grep -Eq '^\$$_def_case_prop_transl\.compound_false_case_prop[$$]link:' case_prop_transl.out || { \
	  echo "compound erased-proof case link check FAILED"; cat case_prop_transl.out; \
	  rm -f case_prop_transl.vo case_prop_transl.out; exit 1; }; \
	if grep -Eq '^\$$_def_case_prop_transl\.compound_false_case_prop[$$]link:.*\(\$$_case_Corelib\.Init\.Logic\.False[$$][0-9]+ @' case_prop_transl.out; then \
	  echo "compound erased-proof case retained an application argument"; cat case_prop_transl.out; \
	  rm -f case_prop_transl.vo case_prop_transl.out; exit 1; \
	fi; \
	if grep -Eq '\$$_generic_case_' case_prop_transl.out; then \
	  echo "proposition-valued case emitted a generic fallback"; cat case_prop_transl.out; \
	  rm -f case_prop_transl.vo case_prop_transl.out; exit 1; \
	fi; \
	if grep -Eq 'Corelib\.Init\.Logic\.(and|or|not|iff|eq|ex|all)([[:space:]]|\))' case_prop_transl.out; then \
	  echo "proposition-valued case leaked raw logical parameters"; cat case_prop_transl.out; \
	  rm -f case_prop_transl.vo case_prop_transl.out; exit 1; \
	fi; \
	grep -Fq "'\$$_inversion_case_prop_transl.delivery_box'" "$$tmp/case-structural-delivery.p" || { \
	  echo "case structural inversion delivery check FAILED"; cat "$$tmp/case-structural-delivery.p"; \
	  rm -f case_prop_transl.vo case_prop_transl.out; exit 1; }; \
	grep -Fq "'\$$_inj_case_prop_transl.delivery_left'" "$$tmp/case-structural-delivery.p" || { \
	  echo "case structural injectivity delivery check FAILED"; cat "$$tmp/case-structural-delivery.p"; \
	  rm -f case_prop_transl.vo case_prop_transl.out; exit 1; }; \
	grep -Fq "'\$$_discrim_case_prop_transl.delivery_left\$$case_prop_transl.delivery_right'" "$$tmp/case-structural-delivery.p" || { \
	  echo "case structural discrimination delivery check FAILED"; cat "$$tmp/case-structural-delivery.p"; \
	  rm -f case_prop_transl.vo case_prop_transl.out; exit 1; }; \
	grep -Fq "'\$$_inversion_case_prop_transl.delivery_box'" "$$tmp/case-structural-cache-hit.p" || { \
	  echo "cached case structural dependency replay check FAILED"; cat "$$tmp/case-structural-cache-hit.p"; \
	  rm -f case_prop_transl.vo case_prop_transl.out; exit 1; }; \
	grep -Fq "'\$$_discrim_case_prop_transl.delivery_left\$$case_prop_transl.delivery_right'" "$$tmp/case-structural-cache-hit.p" || { \
	  echo "cached case structural discrimination replay check FAILED"; cat "$$tmp/case-structural-cache-hit.p"; \
	  rm -f case_prop_transl.vo case_prop_transl.out; exit 1; }; \
	warm_case_id=$$(grep -E '^\$$_def_case_prop_transl\.delivery_cache_warm:' case_prop_transl.out | \
	  grep -Eo '\$$_case_case_prop_transl\.delivery_box[$$][0-9]+' | head -n 1 | grep -Eo '[0-9]+'); \
	hit_case_id=$$(grep -F "fof('\$$_def_case_prop_transl.delivery_cache_hit'" "$$tmp/case-structural-cache-hit.p" | \
	  grep -Eo 'delivery__box_24[0-9]+' | head -n 1 | sed 's/.*_24//'); \
	if [ -z "$$warm_case_id" ] || [ "$$warm_case_id" != "$$hit_case_id" ]; then \
	  echo "case structural replay did not exercise a cache hit"; cat case_prop_transl.out; \
	  cat "$$tmp/case-structural-cache-hit.p"; rm -f case_prop_transl.vo case_prop_transl.out; exit 1; \
	fi; \
	grep -Fq "'\$$_inversion_case_prop_transl.prop_case_box'" "$$tmp/prop-case-structural.p" || { \
	  echo "proposition-valued case structural inversion delivery check FAILED"; \
	  cat "$$tmp/prop-case-structural.p"; rm -f case_prop_transl.vo case_prop_transl.out; exit 1; }; \
	grep -Fq "'\$$_discrim_case_prop_transl.prop_case_left\$$case_prop_transl.prop_case_right'" "$$tmp/prop-case-structural.p" || { \
	  echo "proposition-valued case structural discrimination delivery check FAILED"; \
	  cat "$$tmp/prop-case-structural.p"; rm -f case_prop_transl.vo case_prop_transl.out; exit 1; }; \
	rm -f case_prop_transl.out

extraction_transl.vo: extraction_transl.v extraction_matches.vo extraction_deptypes.vo check-extraction-transl.sh
	@set -e; \
	tmp=$$(mktemp -d); \
	trap 'rm -rf "$$tmp"' EXIT; \
	COQHAMMER_DUMP_DIR="$$tmp" $(COQC) extraction_transl.v > extraction_transl.out 2>&1 || { \
	  cat extraction_transl.out; rm -f extraction_transl.vo extraction_transl.out; exit 1; }; \
	if ! ./check-extraction-transl.sh extraction_transl.out; then \
	  cat extraction_transl.out; rm -f extraction_transl.vo extraction_transl.out; exit 1; \
	fi; \
	dump_extractions=$$(grep -Fc 'Extracting features...' extraction_transl.out || true); \
	if [ "$$dump_extractions" -ne 1 ]; then \
	  echo "Hammer_dump ran feature extraction $$dump_extractions times (expected once)"; \
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
