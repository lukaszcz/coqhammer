COQC ?= rocq c

EXTRACTION_VOS := extraction_matches.vo extraction_deptypes.vo case_prop_transl.vo extraction_transl.vo erasure_blacklist.vo
PLUGIN_VOS := transl.vo plugin_test.vo lemma_choice.vo basic.vo bugs.vo def_premises.vo prover_selection.vo hashing.vo arith.vo zarith.vo lists.vo misc.vo arrow_transl.vo type_sharing_transl.vo membership_transl.vo link_erasure_transl.vo defterm_transl.vo lambda_reuse_transl.vo premise_isolation.vo $(EXTRACTION_VOS)

# The tests that pass with no ATP installed, so that CI can run them without
# depending on an external prover.  plugin_test.vo and transl.vo do prove goals,
# but only trivial ones the sauto pretactic phase closes before any ATP is
# consulted; erasure_blacklist.vo, arrow_transl.vo, type_sharing_transl.vo,
# membership_transl.vo, link_erasure_transl.vo and defterm_transl.vo assert on
# the axioms the translation emits and prove nothing -- arrow_transl.vo,
# type_sharing_transl.vo, lambda_reuse_transl.vo and premise_isolation.vo also
# dump problems for aborted goals, the rest only translate declarations.
# Everything else either sets SAutoLimit to 0, which disables that phase and
# hands the goal to the ATPs, or requires a file that does.  prover_selection.vo
# also passes without an ATP, but only vacuously: it checks that `hammer` fails
# when every prover is disabled, which is equally true when no prover exists, so
# running it here would not test detection.
NO_PROVER_VOS := plugin_test.vo transl.vo erasure_blacklist.vo arrow_transl.vo type_sharing_transl.vo membership_transl.vo link_erasure_transl.vo defterm_transl.vo lambda_reuse_transl.vo premise_isolation.vo

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

def_premises.vo: def_premises.v
	@set -e; \
	$(COQC) def_premises.v > def_premises.out 2>&1 || { \
	  cat def_premises.out; rm -f def_premises.vo def_premises.out; exit 1; \
	}; \
	premises=$$(grep -Fxc 'Current value of Hammer DefinitionPremises is 32' def_premises.out || true); \
	features=$$(grep -Fxc 'Current value of Hammer DefinitionFeatures is 16' def_premises.out || true); \
	if [ "$$premises" -ne 2 ] || [ "$$features" -ne 2 ]; then \
	  echo "definition option default/reset check FAILED"; cat def_premises.out; \
	  rm -f def_premises.vo def_premises.out; exit 1; \
	fi; \
	rm -f def_premises.out

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
	  echo "cross-owner cached case structural discrimination replay check FAILED"; cat "$$tmp/case-structural-cache-hit.p"; \
	  rm -f case_prop_transl.vo case_prop_transl.out; exit 1; }; \
	warm_case=$$(grep -E '^\$$_def_case_prop_transl\.delivery_cache_warm:' case_prop_transl.out | \
	  grep -Eo '\$$_case_case_prop_transl\.delivery_box[$$][0-9]+' | head -n 1); \
	hit_cases=$$(grep -E '^\$$_def_case_prop_transl\.delivery_cache_hit:' case_prop_transl.out | \
	  grep -Eo '\$$_case_case_prop_transl\.delivery_box[$$][0-9]+' || true); \
	[ -n "$$warm_case" ] && \
	[ $$(printf '%s\n' "$$hit_cases" | grep -c .) -eq 2 ] && \
	[ $$(printf '%s\n' "$$hit_cases" | sort -u | grep -c .) -eq 1 ] && \
	[ "$$(printf '%s\n' "$$hit_cases" | head -n 1)" = "$$warm_case" ] || { \
	  echo "cross-owner case cache hit was not exercised"; \
	  grep -E '^\$$_def_case_prop_transl\.delivery_cache_(warm|hit):' case_prop_transl.out || true; \
	  rm -f case_prop_transl.vo case_prop_transl.out; exit 1; }; \
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
	grep -Eq '^fof\(.[^$$][^,]*, axiom, !\[[^]]*\]:.*c_24__arrow___24t\(V[A-Za-z0-9_]+,V[A-Za-z0-9_]+,V[A-Za-z0-9_]+\)' \
	  "$$tmp/arrow_transl.p" || { \
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
	if grep -E '^\$$_(arrow|type|link)_[0-9]+:' type_sharing_transl.out | \
	   awk '{ i = index($$0, "(=> @"); j = index($$0, "(<=> @"); \
	          if (j > 0 && (i == 0 || j < i)) print }' | grep -q .; then \
	  fail "a lifted-type axiom is an equivalence, which is unsound over empty domains"; \
	fi; \
	equivalences=$$(grep -E '^fof\(.\$$_(arrow|type|link)_[0-9]+.' "$$tmp/type_sharing_transl.p" | \
	  awk '{ i = index($$0, " => "); j = index($$0, " <=> "); \
	         if (j > 0 && (i == 0 || j < i)) print }'); \
	if [ -n "$$equivalences" ]; then \
	  echo "a dumped lifted-type axiom is an equivalence, which is unsound over empty domains"; \
	  printf '%s\n' "$$equivalences"; \
	  rm -f type_sharing_transl.vo type_sharing_transl.out; exit 1; \
	fi; \
	rm -f type_sharing_transl.out

membership_transl.vo: membership_transl.v
	@set -e; \
	fail() { \
	  echo "$$1"; cat membership_transl.out; \
	  rm -f membership_transl.vo membership_transl.out; exit 1; \
	}; \
	$(COQC) membership_transl.v > membership_transl.out 2>&1 || \
	  fail "membership_transl.v failed to compile"; \
	grep -Eq '^\$$_typeof_membership_transl\.f: \(\(& @ \(\(\$$HasType @ membership_transl\.f\) @ \(\(\$$_arrow @ membership_transl\.elt\) @ Corelib\.Init\.Datatypes\.bool\)\)\) @ .*Corelib\.Init\.Datatypes\.true' membership_transl.out || \
	  fail "enum codomain: the typing axiom lost its membership conjunct, so no premise quantifying over a function can be instantiated at it"; \
	grep -Eq '^\$$_typeof_membership_transl\.r: \(\(& @ \(\(\$$HasType @ membership_transl\.r\) @ \(\(\$$_arrow @ membership_transl\.elt\) @ \(\(Corelib\.Init\.Specif\.sig @ Corelib\.Init\.Datatypes\.nat\) @ \$$_lam_[0-9]+\)\)\)\) @ .*Corelib\.Init\.Datatypes\.O' membership_transl.out || \
	  fail "subset codomain: the typing axiom lost its membership conjunct"; \
	grep -Eq '^\$$_typeof_membership_transl\.g: \(\(\$$HasType @ membership_transl\.g\) @ \(\(\$$_arrow @ membership_transl\.elt\) @ membership_transl\.A\)\)$$' membership_transl.out || \
	  fail "no erasable content: the typing axiom must be the bare membership, with nothing conjoined to it"; \
	grep -Eq '^\$$_def_membership_transl\.elt: !\[var_[0-9]+ : \$$Any\]: \(\(\(<=> @ \(\(\$$HasType @ var_[0-9]+\) @ membership_transl\.elt\)\) @ \(\(\$$HasType @ var_[0-9]+\) @ membership_transl\.A\)\)\)$$' membership_transl.out || \
	  fail "transparent leaf definition: the two memberships are convertible, so the definition axiom must be an equivalence"; \
	endo_def=$$(grep -E '^\$$_def_membership_transl\.endo:' membership_transl.out || true); \
	[ -n "$$endo_def" ] || \
	  fail "no definition axiom for the transparent product, so the implication check below is vacuous"; \
	printf '%s\n' "$$endo_def" | \
	  grep -Eq '\(=> @ \(\(\$$HasType @ var_[0-9]+\) @ membership_transl\.endo\)\)' || \
	  fail "transparent product definition: the unfolding must be stated as an implication"; \
	if printf '%s\n' "$$endo_def" | \
	   awk '{ i = index($$0, "(=> @"); j = index($$0, "(<=> @"); \
	          if (j > 0 && (i == 0 || j < i)) print }' | grep -q .; then \
	  fail "transparent product definition is an equivalence, which is unsound over empty domains"; \
	fi; \
	product_axioms=$$(grep -Ec '^\$$_(arrow|type)_[0-9]+:' membership_transl.out || true); \
	if [ "$$product_axioms" -lt 1 ]; then \
	  fail "no product unfolding axiom was emitted, so the equivalence guard is vacuous"; \
	fi; \
	if grep -E '^\$$_(arrow|type)_[0-9]+:' membership_transl.out | \
	   awk '{ i = index($$0, "(=> @"); j = index($$0, "(<=> @"); \
	          if (j > 0 && (i == 0 || j < i)) print }' | grep -q .; then \
	  fail "a product unfolding axiom is an equivalence, which is unsound over empty domains"; \
	fi; \
	grep -Eq '^membership_transl\.q_all: !\[[0-9]+_k : \$$Any\]: \(\(\(=> @ \(\(\$$HasType @ [0-9]+_k\) @ \(\(\$$_arrow @ membership_transl\.elt\) @ Corelib\.Init\.Datatypes\.bool\)\)\) @ \(membership_transl\.Q @ [0-9]+_k\)\)\)$$' membership_transl.out || \
	  fail "the premise is no longer guarded by the membership the typing axiom supplies, so the conjunct check above proves nothing"; \
	rm -f membership_transl.out

link_erasure_transl.vo: link_erasure_transl.v
	@set -e; \
	fail() { \
	  echo "$$1"; cat link_erasure_transl.out; \
	  rm -f link_erasure_transl.vo link_erasure_transl.out; exit 1; \
	}; \
	$(COQC) link_erasure_transl.v > link_erasure_transl.out 2>&1 || \
	  fail "link_erasure_transl.v failed to compile"; \
	sch_lam=$$(grep -Ec '^\$$_lam_[0-9]+: !\[v_CANONICAL_0 : \$$Any\]: \(!\[v_CANONICAL_1 : \$$Any\]: \(!\[v_CANONICAL_2 : \$$Any\]' link_erasure_transl.out || true); \
	[ "$$sch_lam" -ge 1 ] || \
	  fail "the schema lambda was not lifted at three arguments, so the arity mismatch this file pins is not being exercised"; \
	inst_lam=$$(grep -Ec '^\$$_lam_[0-9]+: !\[v_CANONICAL_0 : \$$Any\]: \(\(\(\$$_lam_[0-9]+ @ v_CANONICAL_0\) = v_CANONICAL_0\)\)$$' link_erasure_transl.out || true); \
	[ "$$inst_lam" -ge 1 ] || \
	  fail "the instance lambda's proof binder no longer erases, so the two lifts no longer differ in arity and this file proves nothing"; \
	if grep -q '\$$_link_' link_erasure_transl.out; then \
	  fail "a link equation was emitted between lifts whose binder erasure differs; it equates a value with a function and collapses application to a projection"; \
	fi; \
	rm -f link_erasure_transl.out

defterm_transl.vo: defterm_transl.v
	@set -e; \
	fail() { \
	  echo "$$1"; cat defterm_transl.out; \
	  rm -f defterm_transl.vo defterm_transl.out; exit 1; \
	}; \
	$(COQC) defterm_transl.v > defterm_transl.out 2>&1 || \
	  fail "defterm_transl.v failed to compile"; \
	grep -Fq '$$_def_defterm_transl.ltx: ![0_n : $$Any]: (![1_m : $$Any]: (((<=> @ ((defterm_transl.ltx @ 0_n) @ 1_m)) @ ((Corelib.Init.Peano.le @ (Corelib.Init.Datatypes.S @ 0_n)) @ 1_m))))' defterm_transl.out || \
	  fail "atomic Prop body: the propositional equivalence is gone; the term equation is emitted alongside it, never in place of it"; \
	grep -Fq '$$_def_defterm_transl.ltx$$term: ![0_n : $$Any]: (![1_m : $$Any]: ((((defterm_transl.ltx @ 0_n) @ 1_m) = ((Corelib.Init.Peano.le @ (Corelib.Init.Datatypes.S @ 0_n)) @ 1_m))))' defterm_transl.out || \
	  fail "atomic Prop body: no term-level definitional equation, so the two spellings of this proposition stay distinct wherever it occurs as a term"; \
	grep -Fq '$$_def_defterm_transl.conj2: ![0_P : $$Any]: (![1_Q : $$Any]: (((<=> @ ((defterm_transl.conj2 @ 0_P) @ 1_Q)) @ ((& @ 0_P) @ 1_Q))))' defterm_transl.out || \
	  fail "the connective-headed body no longer translates to a conjunction, so the check that it gets no term equation is vacuous"; \
	grep -Fq '$$_def_defterm_transl.allpos: ![0_P : $$Any]: (((<=> @ (defterm_transl.allpos @ 0_P)) @ ![1_n : $$Any]: (((=> @ (($$HasType @ 1_n) @ Corelib.Init.Datatypes.nat)) @ (0_P @ 1_n)))))' defterm_transl.out || \
	  fail "the quantified body no longer translates to a quantified formula, so the check that it gets no term equation is vacuous"; \
	grep -Fq '$$_def_defterm_transl.wfle: ![0_n : $$Any]: (![1_m : $$Any]: (((<=> @ ((defterm_transl.wfle @ 0_n) @ 1_m)) @ ((Corelib.Init.Peano.le @ 0_n) @ 1_m))))' defterm_transl.out || \
	  fail "the well-founded definition no longer unfolds to an atomic body, so its equation is excluded for some reason other than being a Fix_eq theorem"; \
	if grep -Eq '^\$$_def_defterm_transl\.(conj2|allpos|wfle)\$$term:' defterm_transl.out; then \
	  fail "a term-level definitional equation was emitted for a definition whose equation is not a conversion between terms"; \
	fi; \
	rm -f defterm_transl.out

lambda_reuse_transl.vo: lambda_reuse_transl.v
	@set -e; \
	tmp=$$(mktemp -d); \
	trap 'rm -rf "$$tmp"' EXIT; \
	fail() { \
	  echo "$$1"; cat lambda_reuse_transl.out; \
	  rm -f lambda_reuse_transl.vo lambda_reuse_transl.out; exit 1; \
	}; \
	COQHAMMER_DUMP_DIR="$$tmp" timeout 120 $(COQC) lambda_reuse_transl.v > lambda_reuse_transl.out 2>&1 || \
	  fail "lambda_reuse_transl.v failed or timed out"; \
	definition_lams() { \
	  grep -F "_def_lambda_reuse_transl.$$1:" lambda_reuse_transl.out | \
	    grep -Eo '[$$]_lam_[0-9]+' || true; \
	}; \
	reuse_lams=$$(definition_lams reuse_ok); \
	[ $$(printf '%s\n' "$$reuse_lams" | grep -c .) -eq 2 ] && \
	[ $$(printf '%s\n' "$$reuse_lams" | sort -u | grep -c .) -eq 1 ] || \
	  fail "same-declaration schema instance did not reuse the schema lambda"; \
	binder_lams=$$(definition_lams reject_binder_erasure); \
	[ $$(printf '%s\n' "$$binder_lams" | sort -u | grep -c .) -eq 2 ] || \
	  fail "lambda reuse crossed a binder-erasure mismatch"; \
	context_lams=$$(definition_lams reject_context_arity); \
	[ $$(printf '%s\n' "$$context_lams" | sort -u | grep -c .) -ge 2 ] || \
	  fail "lambda reuse accepted a schema application whose translated context spine is short"; \
	grep -Eq 'rejected_schema_candidates_with_effects=[1-9][0-9]* discarded_effects=[1-9][0-9]*' \
	  lambda_reuse_transl.out || \
	  fail "the rejected schema candidate did not exercise behavioral effect rollback"; \
	seed_lam=$$(definition_lams owner_seed | head -n 1); \
	isolated_lam=$$(definition_lams owner_isolated | head -n 1); \
	[ -n "$$seed_lam" ] && [ -n "$$isolated_lam" ] && [ "$$seed_lam" != "$$isolated_lam" ] || \
	  fail "a schema registry entry was reused without availability in the current owner"; \
	seed_dump_lam=$$(grep -F "_def_lambda_reuse_transl.owner_seed'" "$$tmp/lambda-reuse-owners.p" | \
	  grep -Eo 'c_24__lam__[0-9]+' | head -n 1); \
	replay_dump_lams=$$(grep -F "_def_lambda_reuse_transl.owner_replay'" "$$tmp/lambda-reuse-owners.p" | \
	  grep -Eo 'c_24__lam__[0-9]+' || true); \
	[ -n "$$seed_dump_lam" ] && \
	[ $$(printf '%s\n' "$$replay_dump_lams" | grep -c .) -eq 2 ] && \
	[ $$(printf '%s\n' "$$replay_dump_lams" | sort -u | grep -c .) -eq 1 ] && \
	[ "$$(printf '%s\n' "$$replay_dump_lams" | head -n 1)" = "$$seed_dump_lam" ] || \
	  fail "an exact cache hit did not replay and expose the full schema bundle to its current owner"; \
	grep -Fq "_inversion_lambda_reuse_transl.replay_box'" "$$tmp/lambda-reuse-structural.p" || \
	  fail "the cross-owner lambda cache hit lost its replay_box dependency"; \
	if grep -Fq '_def_lambda_reuse_transl.owner_seed' "$$tmp/lambda-reuse-structural.p"; then \
	  fail "the structural replay check is masked by the seed owner in the final theory"; \
	fi; \
	rm -f lambda_reuse_transl.out

premise_isolation.vo: premise_isolation.v
	@set -e; \
	tmp=$$(mktemp -d); \
	trap 'rm -rf "$$tmp"' EXIT; \
	COQHAMMER_DUMP_DIR="$$tmp" timeout 180 $(COQC) premise_isolation.v > premise_isolation.out 2>&1 || { \
	  echo "premise_isolation.v failed or timed out"; cat premise_isolation.out; \
	  rm -f premise_isolation.vo premise_isolation.out; exit 1; }; \
	cmp "$$tmp/premise_seq128.p" "$$tmp/premise_fresh128.p" || { \
	  echo "sequential and fresh bounded 128-premise POPLMark problems differ"; \
	  rm -f premise_isolation.vo premise_isolation.out; exit 1; }; \
	n32=$$(grep -c '^fof(' "$$tmp/premise_seq32.p"); \
	n64=$$(grep -c '^fof(' "$$tmp/premise_seq64.p"); \
	n128=$$(grep -c '^fof(' "$$tmp/premise_seq128.p"); \
	[ "$$n32" -lt "$$n64" ] && [ "$$n64" -lt "$$n128" ] || { \
	  echo "bounded POPLMark premise growth did not preserve increasing translated content: $$n32, $$n64, $$n128"; \
	  rm -f premise_isolation.vo premise_isolation.out; exit 1; }; \
	rm -f premise_isolation.out

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
