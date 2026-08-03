COQC ?= rocq c

EXTRACTION_VOS := extraction_matches.vo extraction_deptypes.vo case_prop_transl.vo extraction_transl.vo erasure_blacklist.vo
PLUGIN_VOS := transl.vo plugin_test.vo lemma_choice.vo basic.vo bugs.vo prover_selection.vo hashing.vo arith.vo zarith.vo lists.vo misc.vo arrow_transl.vo type_sharing_transl.vo $(EXTRACTION_VOS)

# The tests that pass with no ATP installed, so that CI can run them without
# depending on an external prover.  plugin_test.vo and transl.vo do prove goals,
# but only trivial ones the sauto pretactic phase closes before any ATP is
# consulted; erasure_blacklist.vo, arrow_transl.vo and type_sharing_transl.vo
# assert on the axioms the translation emits and prove nothing -- the last one
# only translates declarations and dumps a problem for an aborted goal.
# Everything else either sets SAutoLimit to 0, which disables that phase and
# hands the goal to the ATPs, or requires a file that does.  prover_selection.vo
# also passes without an ATP, but only vacuously: it checks that `hammer` fails
# when every prover is disabled, which is equally true when no prover exists, so
# running it here would not test detection.
NO_PROVER_VOS := plugin_test.vo transl.vo erasure_blacklist.vo arrow_transl.vo type_sharing_transl.vo

all: $(PLUGIN_VOS)
	COQC="$(COQC)" ./check-consistency.sh

test-no-provers: $(NO_PROVER_VOS)

test-extraction: $(EXTRACTION_VOS)
	COQC="$(COQC)" ./check-consistency.sh

test-consistency: extraction_deptypes.vo
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

erasure_blacklist.vo: erasure_blacklist.v
	@set -e; \
	$(COQC) erasure_blacklist.v > erasure_blacklist.out 2>&1 || { \
	  cat erasure_blacklist.out; rm -f erasure_blacklist.vo erasure_blacklist.out; exit 1; }; \
	grep -Eq '^\$$_def_erasure_blacklist\.blkt_id:' erasure_blacklist.out || { \
	  echo "blacklisted constructor: definition axiom check FAILED"; cat erasure_blacklist.out; \
	  rm -f erasure_blacklist.vo erasure_blacklist.out; exit 1; }; \
	grep -Eq '^\$$_typeof_erasure_blacklist\.blkt_id:' erasure_blacklist.out || { \
	  echo "blacklisted constructor: typing axiom check FAILED"; cat erasure_blacklist.out; \
	  rm -f erasure_blacklist.vo erasure_blacklist.out; exit 1; }; \
	if grep -Eq '\$$_inj_|\$$_discrim_|\$$_inversion_' erasure_blacklist.out; then \
	  echo "blacklisted constructor: constructor-derived axioms must be skipped, but some were emitted"; \
	  cat erasure_blacklist.out; \
	  rm -f erasure_blacklist.vo erasure_blacklist.out; exit 1; \
	fi; \
	rm -f erasure_blacklist.out

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
	two_false_line=$$(grep -E '^\$$_def_case_prop_transl\.two_false_case_props:' case_prop_transl.out || true); \
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
	  grep -Eo '\$$_case_case_prop_transl\.delivery_box[$$][0-9]+' | head -n 1 | grep -Eo '[0-9]+' || true); \
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

arrow_transl.vo: arrow_transl.v
	@set -e; \
	tmp=$$(mktemp -d); \
	trap 'rm -rf "$$tmp"' EXIT; \
	COQHAMMER_DUMP_DIR="$$tmp" timeout 600 $(COQC) arrow_transl.v > arrow_transl.out 2>&1 || { \
	  echo "arrow_transl.v failed or timed out; a deep arrow telescope must not"; \
	  echo "translate in time exponential in its depth"; \
	  cat arrow_transl.out; rm -f arrow_transl.vo arrow_transl.out; exit 1; }; \
	grep -Eq '^\$$_typeof_arrow_transl\.f: \(\(\$$HasType @ arrow_transl\.f\) @ \(\(\$$_arrow @ arrow_transl\.A\) @ arrow_transl\.B\)\)$$' arrow_transl.out || { \
	  echo "instance-position arrow former check FAILED"; cat arrow_transl.out; \
	  rm -f arrow_transl.vo arrow_transl.out; exit 1; }; \
	grep -Eq '^arrow_transl\.map_len:.*\(\(\$$HasType @ 2_g\) @ \(\(\$$_arrow @ 0_X\) @ 1_Y\)\)' arrow_transl.out || { \
	  echo "quantified premise arrow former check FAILED"; cat arrow_transl.out; \
	  rm -f arrow_transl.vo arrow_transl.out; exit 1; }; \
	grep -Eq '^\$$_typeof_arrow_transl\.dep: \(\(\$$HasType @ arrow_transl\.dep\) @ \$$_type_[0-9]+\)$$' arrow_transl.out || { \
	  echo "dependent product lifting check FAILED"; cat arrow_transl.out; \
	  rm -f arrow_transl.vo arrow_transl.out; exit 1; }; \
	grep -Eq '^\$$_typeof_arrow_transl\.propdom: \(\(\$$HasType @ arrow_transl\.propdom\) @ \$$_type_[0-9]+\)$$' arrow_transl.out || { \
	  echo "proposition-domain product lifting check FAILED"; cat arrow_transl.out; \
	  rm -f arrow_transl.vo arrow_transl.out; exit 1; }; \
	grep -Eq '^\$$_typeof_arrow_transl\.nested: \(\(\$$HasType @ arrow_transl\.nested\) @ \(\(\$$_arrow @ arrow_transl\.A\) @ \(\(\$$_arrow @ arrow_transl\.B\) @ arrow_transl\.A\)\)\)$$' arrow_transl.out || { \
	  echo "nested arrow canonicalization check FAILED"; cat arrow_transl.out; \
	  rm -f arrow_transl.vo arrow_transl.out; exit 1; }; \
	arrow_axioms=$$(grep -Ec '^\$$_arrow_[0-9]+:' arrow_transl.out || true); \
	if [ "$$arrow_axioms" -lt 1 ]; then \
	  echo "no arrow unfolding axiom was emitted, so the equivalence guard is vacuous"; \
	  cat arrow_transl.out; rm -f arrow_transl.vo arrow_transl.out; exit 1; \
	fi; \
	if grep -E '^\$$_arrow_[0-9]+:' arrow_transl.out | grep -q '<=>'; then \
	  echo "arrow unfolding axiom is an equivalence, which is unsound over empty domains"; \
	  cat arrow_transl.out; rm -f arrow_transl.vo arrow_transl.out; exit 1; \
	fi; \
	grep -Fq "fof('\$$_typeof_h', axiom, c_24__arrow___24t(cX,cY,ch))." "$$tmp/arrow_transl.p" || { \
	  echo "dumped instance-position arrow guard check FAILED"; \
	  grep -F "'\$$_typeof_h'" "$$tmp/arrow_transl.p" || true; \
	  rm -f arrow_transl.vo arrow_transl.out; exit 1; }; \
	grep -E 'c_24__arrow___24t\(V[A-Za-z0-9_]+,V[A-Za-z0-9_]+,V[A-Za-z0-9_]+\)' "$$tmp/arrow_transl.p" | \
	  grep -qv '^fof(.\$$' || { \
	  echo "dumped quantified premise arrow guard check FAILED"; \
	  rm -f arrow_transl.vo arrow_transl.out; exit 1; }; \
	tdef_arrows=$$(grep -Fc "fof('\$$tdef_\$$_arrow'," "$$tmp/arrow_transl.p" || true); \
	if [ "$$tdef_arrows" -ne 1 ]; then \
	  echo "expected exactly one \$$tdef_\$$_arrow axiom, found $$tdef_arrows"; \
	  grep -F "tdef_\$$_arrow" "$$tmp/arrow_transl.p" || true; \
	  rm -f arrow_transl.vo arrow_transl.out; exit 1; \
	fi; \
	grep -Fq "fof('\$$tdef_\$$_arrow', axiom, ![V_24X1,V_24X2,V_24Y]:(c_24__arrow___24t(V_24X1,V_24X2,V_24Y) <=> t(V_24Y, c_24__arrow___24a2(V_24X1,V_24X2))))." "$$tmp/arrow_transl.p" || { \
	  echo "arrow former arity check FAILED"; \
	  grep -F "tdef_\$$_arrow" "$$tmp/arrow_transl.p" || true; \
	  rm -f arrow_transl.vo arrow_transl.out; exit 1; }; \
	dumped_arrow_axioms=$$(grep -Ec '^fof\(.\$$_arrow_[0-9]+.' "$$tmp/arrow_transl.p" || true); \
	if [ "$$dumped_arrow_axioms" -lt 1 ]; then \
	  echo "the dumped problem has no arrow unfolding axiom, so its equivalence guard is vacuous"; \
	  rm -f arrow_transl.vo arrow_transl.out; exit 1; \
	fi; \
	if grep -E '^fof\(.\$$_arrow_[0-9]+.' "$$tmp/arrow_transl.p" | grep -q '<=>'; then \
	  echo "dumped arrow unfolding axiom is an equivalence, which is unsound over empty domains"; \
	  grep -E '^fof\(.\$$_arrow_[0-9]+.' "$$tmp/arrow_transl.p" | grep '<=>' || true; \
	  rm -f arrow_transl.vo arrow_transl.out; exit 1; \
	fi; \
	rm -f arrow_transl.out

type_sharing_transl.vo: type_sharing_transl.v
	@set -e; \
	tmp=$$(mktemp -d); \
	trap 'rm -rf "$$tmp"' EXIT; \
	fail() { \
	  echo "$$1"; cat type_sharing_transl.out; \
	  rm -f type_sharing_transl.vo type_sharing_transl.out; exit 1; \
	}; \
	COQHAMMER_DUMP_DIR="$$tmp" $(COQC) type_sharing_transl.v > type_sharing_transl.out 2>&1 || \
	  fail "type_sharing_transl.v failed to compile"; \
	dep_link=$$(grep -E '^\$$_link_[0-9]+: \(\$$_type_[0-9]+ = \(\(\$$_type_[0-9]+ @ type_sharing_transl\.X\) @ type_sharing_transl\.Pi\)\)$$' type_sharing_transl.out || true); \
	[ -n "$$dep_link" ] || fail "dependent product link equation check FAILED"; \
	dep_lhs=$$(printf '%s\n' "$$dep_link" | grep -Eo '\$$_type_[0-9]+' | head -n 1); \
	dep_rhs=$$(printf '%s\n' "$$dep_link" | grep -Eo '\$$_type_[0-9]+' | sed -n 2p); \
	dep_sym=$$(grep -E '^\$$_typeof_type_sharing_transl\.dep_inst:' type_sharing_transl.out | \
	  grep -Eo '\$$_type_[0-9]+' | head -n 1); \
	[ "$$dep_lhs" = "$$dep_sym" ] || \
	  fail "the dependent link does not relate the instance's own lifted symbol"; \
	[ "$$dep_lhs" != "$$dep_rhs" ] || \
	  fail "the dependent link relates a lifted symbol to itself, so it says nothing"; \
	grep -Eq '^\$$_link_[0-9]+: !\[v_CANONICAL_0 : \$$Any\]: \(\(\(\$$_type_[0-9]+ @ v_CANONICAL_0\) = \(\(\$$_type_[0-9]+ @ v_CANONICAL_0\) @ \(type_sharing_transl\.Fam @ v_CANONICAL_0\)\)\)\)$$' type_sharing_transl.out || \
	  fail "open dependent instance link equation check FAILED"; \
	prop_link=$$(grep -E '^\$$_link_[0-9]+: \(\$$_type_[0-9]+ = \(\$$_type_[0-9]+ @ type_sharing_transl\.A\)\)$$' type_sharing_transl.out || true); \
	[ -n "$$prop_link" ] || fail "proposition-domain product link equation check FAILED"; \
	prop_lhs=$$(printf '%s\n' "$$prop_link" | grep -Eo '\$$_type_[0-9]+' | head -n 1); \
	prop_sym=$$(grep -E '^\$$_typeof_type_sharing_transl\.prop_inst:' type_sharing_transl.out | \
	  grep -Eo '\$$_type_[0-9]+' | head -n 1); \
	[ "$$prop_lhs" = "$$prop_sym" ] || \
	  fail "the Prop-domain link does not relate the instance's own lifted symbol"; \
	lam_link=$$(grep -E '^\$$_link_[0-9]+: \(\$$_lam_[0-9]+ = \(\(\$$_lam_[0-9]+ @ type_sharing_transl\.X\) @ type_sharing_transl\.gg\)\)$$' type_sharing_transl.out || true); \
	[ -n "$$lam_link" ] || fail "lambda link equation check FAILED"; \
	lam_lhs=$$(printf '%s\n' "$$lam_link" | grep -Eo '\$$_lam_[0-9]+' | head -n 1); \
	lam_rhs=$$(printf '%s\n' "$$lam_link" | grep -Eo '\$$_lam_[0-9]+' | sed -n 2p); \
	lam_inst_sym=$$(grep -E '^\$$_def_type_sharing_transl\.lam_inst:' type_sharing_transl.out | \
	  grep -Eo '\$$_lam_[0-9]+' | head -n 1); \
	lam_schema_sym=$$(grep -E '^\$$_def_type_sharing_transl\.lam_schema:' type_sharing_transl.out | \
	  grep -Eo '\$$_lam_[0-9]+' | head -n 1); \
	[ "$$lam_lhs" = "$$lam_inst_sym" ] || \
	  fail "the lambda link does not relate the instance's own lifted lambda"; \
	[ "$$lam_rhs" = "$$lam_schema_sym" ] || \
	  fail "the lambda link does not relate the schema's own lifted lambda"; \
	[ "$$lam_lhs" != "$$lam_rhs" ] || \
	  fail "the lambda link relates a lifted lambda to itself, so it says nothing"; \
	arrow_axioms=$$(grep -Ec '^\$$_arrow_[0-9]+:' type_sharing_transl.out || true); \
	type_axioms=$$(grep -Ec '^\$$_type_[0-9]+:' type_sharing_transl.out || true); \
	if [ "$$arrow_axioms" -lt 1 ] || [ "$$type_axioms" -lt 1 ]; then \
	  fail "no arrow or type unfolding axiom was emitted, so the equivalence guard is vacuous"; \
	fi; \
	if grep -E '^\$$_(arrow|type|link)_[0-9]+:' type_sharing_transl.out | grep -q '<=>'; then \
	  fail "a lifted-type axiom is an equivalence, which is unsound over empty domains"; \
	fi; \
	grep -Eq "^fof\(.\\\$$_link_[0-9]+., axiom, \(c_24__type__[0-9]+ = c_24__type__[0-9]+___24a2\(ctype__sharing__transl_2eX,cQs\)\)\)\.$$" "$$tmp/type_sharing_transl.p" || { \
	  echo "dumped link equation check FAILED"; \
	  grep -E "^fof\(.\\\$$_link_" "$$tmp/type_sharing_transl.p" || true; \
	  rm -f type_sharing_transl.vo type_sharing_transl.out; exit 1; }; \
	grep -Eq '^fof\(.\$$_link_[0-9]+., axiom, \(c_24__lam__[0-9]+ = c_24__lam__[0-9]+___24a2\(ctype__sharing__transl_2eX,ctype__sharing__transl_2egg\)\)\)\.$$' "$$tmp/type_sharing_transl.p" || { \
	  echo "dumped lambda link equation check FAILED"; \
	  grep -E "^fof\(.\\\$$_link_" "$$tmp/type_sharing_transl.p" || true; \
	  rm -f type_sharing_transl.vo type_sharing_transl.out; exit 1; }; \
	if grep -E '^fof\(.\$$_(arrow|type|link)_[0-9]+.' "$$tmp/type_sharing_transl.p" | grep -q '<=>'; then \
	  echo "a dumped lifted-type axiom is an equivalence, which is unsound over empty domains"; \
	  grep -E '^fof\(.\$$_(arrow|type|link)_[0-9]+.' "$$tmp/type_sharing_transl.p" | grep '<=>' || true; \
	  rm -f type_sharing_transl.vo type_sharing_transl.out; exit 1; \
	fi; \
	rm -f type_sharing_transl.out

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

.PHONY: all test-no-provers test-extraction test-consistency clean
