#!/usr/bin/env bash
set -euo pipefail

out=${1:-extraction_transl.out}

fail() {
  echo "extraction_transl assertion FAILED: $*" >&2
  exit 1
}

require_line() {
  local label=$1
  local pattern=$2
  grep -Eq -- "$pattern" "$out" || fail "$label (missing pattern: $pattern)"
}

forbid_line() {
  local label=$1
  local pattern=$2
  if grep -Eq -- "$pattern" "$out"; then
    fail "$label (forbidden pattern present: $pattern)"
  fi
}

require_count_at_least() {
  local label=$1
  local pattern=$2
  local min=$3
  local count
  count=$(grep -Ec -- "$pattern" "$out" || true)
  if [ "$count" -lt "$min" ]; then
    fail "$label (expected >= $min matches for: $pattern; found $count)"
  fi
}

# -----------------------------------------------------------------------------
# Global sanity checks enforced now.
# -----------------------------------------------------------------------------

forbid_line "Hammer_transl lookup failures" '^Error: Not found:'

# Same intent as transl.v's Init.Logic sanity check, but restricted to logical
# connective constants: this corpus intentionally still exposes proof constants
# such as eq_refl/False_rect before the extraction phases remove those shapes.
forbid_line "untranslated Init.Logic connectives" 'Init\.Logic\.(and|or|not|iff|ex|all)\b'

# Generic-case symbols may still appear only on fallback paths guarded below;
# covered E1 singleton definitions must not contain them.

# Phase 1 shallowness gates for definitional output: split equations should not
# reintroduce type guards, existential packages, or disjunctive case bodies on
# definition lines.
forbid_line "definition axioms are HasType-free" '^\$_def_.*\$HasType'
forbid_line "definition axioms are existential-free" '^\$_def_.*\?\['
forbid_line "definition axioms are disjunction-free" '^\$_def_.*[|]'

# -----------------------------------------------------------------------------
# Corpus constants: baseline structural assertions that hold today.
# -----------------------------------------------------------------------------

# SProp hypotheses are proof-like: the argument becomes a formula premise and is
# pruned from the term-level definition equation.
require_line "SProp argument is translated as a premise" '^\$_typeof_extraction_transl\.sprop_arg_term: \(\(=> @ extraction_transl\.sflag\) @ \(\(\$HasType @ extraction_transl\.sprop_arg_term\) @ Corelib\.Init\.Datatypes\.nat\)\)'
require_line "SProp proof argument is pruned from the definition" '^\$_def_extraction_transl\.sprop_arg_term: \(extraction_transl\.sprop_arg_term = extraction_transl\.sprop_consumer\)'
forbid_line "SProp proof argument must not be applied as a term" '^\$_def_extraction_transl\.sprop_arg_term:.*sprop_consumer @'

# Spec-extraction S4: a Prop premise must leave the extracted term unapplied
# across the implication (proof argument pruned from arity).
require_line "spec_pruned type axiom keeps pruned arity" '^\$_typeof_extraction_transl\.spec_pruned:.*\(=> @ \(var_0_n_[0-9]+ = var_0_n_[0-9]+\)\) @ \(\(& @ \(\(\$HasType @ \(extraction_transl\.spec_pruned @ var_0_n_[0-9]+\)\) @ Corelib\.Init\.Datatypes\.nat\)\) @ \(var_0_n_[0-9]+ = \(extraction_transl\.spec_pruned @ var_0_n_[0-9]+\)\)\)'
forbid_line "spec_pruned proof premise must not be applied as a term" '^\$_typeof_extraction_transl\.spec_pruned:.*extraction_transl\.spec_pruned @ .*\$Proof'

# Phase 1a split equations: variable-scrutinee definitions are emitted as one
# guard-free unit equation per constructor.
require_line "myadd zero split equation" '^\$_def_extraction_matches\.myadd[$]O:.*extraction_matches\.myadd @ Corelib\.Init\.Datatypes\.O'
require_line "myadd successor split equation" '^\$_def_extraction_matches\.myadd[$]S:.*extraction_matches\.myadd @ \(Corelib\.Init\.Datatypes\.S @'
forbid_line "myadd split equations are guard/existential/disjunction free" '^\$_def_extraction_matches\.myadd[$].*(\$HasType|\?\[|[|])'

require_line "g zero split equation" '^\$_def_extraction_matches\.g[$]O:'
require_line "g one split equation" '^\$_def_extraction_matches\.g[$]S[$]O:'
require_line "g deep split equation" '^\$_def_extraction_matches\.g[$]S[$]S:.*Corelib\.Init\.Datatypes\.S @ \(Corelib\.Init\.Datatypes\.S @'
forbid_line "g split equations are existential-free" '^\$_def_extraction_matches\.g[$].*\?\['

# k: compound scrutinee compilation emits one linking equation to a shared
# bool case symbol plus one unit equation per constructor for that symbol.
require_line "k has a linking definition axiom" '^\$_def_extraction_matches\.k[$]link:.*\$_case_Corelib\.Init\.Datatypes\.bool[$][0-9]+ @ \(Corelib\.Init\.Datatypes\.negb @'
require_line "k aux case true equation" '^\$_case_Corelib\.Init\.Datatypes\.bool[$][0-9]+[$]true:'
require_line "k aux case false equation" '^\$_case_Corelib\.Init\.Datatypes\.bool[$][0-9]+[$]false:'
forbid_line "k aux case equations are unit/guard-free" '^\$_case_Corelib\.Init\.Datatypes\.bool[$][0-9]+[$].*(\$HasType|\?\[|[|])'

# Mutual fixpoints: translating either body emits two equations for the result
# name and two equations for the sibling under the $_fix_<id>_ prefix.
require_line "even zero equation" '^\$_def_extraction_matches\.even[$]O:'
require_line "even successor equation" '^\$_def_extraction_matches\.even[$]S:'
require_line "even translation emits odd sibling zero equation" '^\$_fix_[0-9]+_[0-9]+_odd[$]O:'
require_line "even translation emits odd sibling successor equation" '^\$_fix_[0-9]+_[0-9]+_odd[$]S:'
require_line "odd zero equation" '^\$_def_extraction_matches\.odd[$]O:'
require_line "odd successor equation" '^\$_def_extraction_matches\.odd[$]S:'
require_line "odd translation emits even sibling zero equation" '^\$_fix_[0-9]+_[0-9]+_even[$]O:'
require_line "odd translation emits even sibling successor equation" '^\$_fix_[0-9]+_[0-9]+_even[$]S:'

# Phase 3a E3 refinement unboxing: the conjunction match in h collapses as in
# Phase 2 and the subset constructor occurrence now erases to its carrier z.
require_line "h has a specification-extracted type axiom" '^\$_typeof_extraction_deptypes\.h:.*var_0_x_[0-9]+ = \(\(\(extraction_deptypes\.h @ var_0_x_[0-9]+\) @ var_1_y_[0-9]+\) @ var_2_z_[0-9]+\)'
require_line "h has a refinement-unboxed definition" '^\$_def_extraction_deptypes\.h:.*= 2_z\)'
forbid_line "h type axiom must not keep a sig HasType atom" '^\$_typeof_extraction_deptypes\.h:.*Corelib\.Init\.Specif\.sig'
forbid_line "h output must not mention erased sig/exist/proj1_sig" '^.*extraction_deptypes\.h.*Corelib\.Init\.Specif\.(sig|exist|proj1_sig)'
forbid_line "h singleton collapse must not leave generic case" '^.*extraction_deptypes\.h.*\$_generic_case'

# safe_pred: the dependent match still splits on nat and now keeps a definition
# for both branches while proof payloads in the live successor branch are erased.
require_count_at_least "safe_pred has split definition axioms" '^\$_def_extraction_deptypes\.safe_pred[$]' 2
require_line "safe_pred zero branch remains dead-code fallback" '^\$_def_extraction_deptypes\.safe_pred[$]O:.*Corelib\.Init\.Logic\.False_rect'
require_line "safe_pred successor branch unboxes the subset result" '^\$_def_extraction_deptypes\.safe_pred[$]S:.*= var_0_[$]Anonymous_[0-9]+\)'
require_line "safe_pred type axiom expands the subset payload" '^\$_typeof_extraction_deptypes\.safe_pred:.*var_0_n_[0-9]+ = \(Corelib\.Init\.Datatypes\.S @ \(extraction_deptypes\.safe_pred @ var_0_n_[0-9]+\)\)'
forbid_line "safe_pred type axiom must not keep a sig HasType atom" '^\$_typeof_extraction_deptypes\.safe_pred:.*Corelib\.Init\.Specif\.sig'
forbid_line "safe_pred successor branch must not keep eq_refl" '^\$_def_extraction_deptypes\.safe_pred[$]S:.*Corelib\.Init\.Logic\.eq_refl'
forbid_line "safe_pred successor branch must not keep exist" '^\$_def_extraction_deptypes\.safe_pred[$]S:.*Corelib\.Init\.Specif\.exist'

# Transport erasure: eq_rect/eq_rec/eq_ind-style casts are identities in the
# proof-irrelevant erasure model (guarded by opt_erasure_guards when enabled).
require_line "tr has an identity definition" '^\$_def_extraction_deptypes\.tr:.*= 4_x'

# proj1_sig's own subset match collapses to the identity equation; no
# per-occurrence delta unfolding is needed for users because this is a perfect
# demodulator.
require_line "proj1_sig has an identity definition" '^\$_def_Corelib\.Init\.Specif\.proj1_sig:.*= 2_e\)'

# pval: non-primitive projection over a proof-carrying record is the identity
# after E3 subset-match collapse; its argument guard expands the record payload.
require_line "pval has an identity definition" '^\$_def_extraction_deptypes\.pval:.*= 0_p\)'
require_line "pval type axiom expands the posnat payload" '^\$_typeof_extraction_deptypes\.pval:.*\(=> @ \(\(& @ \(\(\$HasType @ var_0_p_[0-9]+\) @ Corelib\.Init\.Datatypes\.nat\)\) @ \(\(Corelib\.Init\.Peano\.lt @ Corelib\.Init\.Datatypes\.O\) @ var_0_p_[0-9]+\)\)\)'
forbid_line "pval definition must not mention mkpos" '^\$_def_extraction_deptypes\.pval:.*extraction_deptypes\.mkpos'
forbid_line "pval type axiom must not keep a posnat HasType atom" '^\$_typeof_extraction_deptypes\.pval:.*\$HasType @ var_0_p_[0-9]+\) @ extraction_deptypes\.posnat'

# beq: sumbool-driven definition links through an auxiliary case symbol for
# the compound Nat.eq_dec scrutinee; enum guards expand to constructor tags plus
# payload formulas.
require_count_at_least "beq has a linking definition axiom" '^\$_def_extraction_deptypes\.beq[$]link:' 1
require_line "beq link mentions Nat.eq_dec" '^\$_def_extraction_deptypes\.beq[$]link:.*Nat\.eq_dec'
require_line "beq aux case mentions sumbool constructors" '^\$_case_Corelib\.Init\.Specif\.sumbool[$][0-9]+[$].*Corelib\.Init\.Specif\.(left|right)'
require_line "beq type axiom expands bool enum result" '^\$_typeof_extraction_deptypes\.beq:.*extraction_deptypes\.beq @ var_0_n_[0-9]+.*Corelib\.Init\.Datatypes\.true.*Corelib\.Init\.Datatypes\.false'
require_line "Nat.eq_dec type axiom expands sumbool payloads" '^\$_typeof_Stdlib\.Arith\.PeanoNat\.Nat\.eq_dec:.*var_0_n_[0-9]+ = var_1_m_[0-9]+.*~ @ \(var_0_n_[0-9]+ = var_1_m_[0-9]+\)'
forbid_line "Nat.eq_dec type axiom must not keep a sumbool HasType atom" '^\$_typeof_Stdlib\.Arith\.PeanoNat\.Nat\.eq_dec:.*Corelib\.Init\.Specif\.sumbool'

# tag: prod-with-Prop is a per-instance subset; pair erases to the informative
# first component and the result guard carries the equality payload.
require_line "tag has an unboxed definition axiom" '^\$_def_extraction_deptypes\.tag:.*= 0_n\)'
require_line "tag type axiom expands the prod payload" '^\$_typeof_extraction_deptypes\.tag:.*\(& @ \(\(\$HasType @ \(extraction_deptypes\.tag @ var_0_n_[0-9]+\)\) @ Corelib\.Init\.Datatypes\.nat\)\) @ \(var_0_n_[0-9]+ = var_0_n_[0-9]+\)'
forbid_line "tag definition must not mention pair" '^\$_def_extraction_deptypes\.tag:.*Corelib\.Init\.Datatypes\.pair'
forbid_line "tag proof payload is erased" '^\$_def_extraction_deptypes\.tag:.*Corelib\.Init\.Logic\.eq_refl'
forbid_line "tag type axiom must not keep a prod HasType atom" '^\$_typeof_extraction_deptypes\.tag:.*Corelib\.Init\.Datatypes\.prod'

# WF guardrail: until Phase 4, the Acc/Fix_F packagings must not expose an
# unconditional unfolding equation.  These assertions are part of make tests.
require_count_at_least "idiv has a top-level linking definition" '^\$_def_extraction_deptypes\.idiv:' 1
require_line "idiv baseline links to idiv_func" '^\$_def_extraction_deptypes\.idiv:.*extraction_deptypes\.idiv_func'
forbid_line "idiv must not expose an unconditional le_lt_dec unfolding" '^\$_def_extraction_deptypes\.idiv:.*le_lt_dec'
forbid_line "idiv must not expose an unconditional recursive sub-call unfolding" '^\$_def_extraction_deptypes\.idiv:.*Corelib\.Init\.Nat\.sub'
require_count_at_least "idiv2 has only the safe Fix link" '^\$_def_extraction_deptypes\.idiv2:' 1
forbid_line "idiv2 must not expose an unconditional le_lt_dec unfolding" '^\$_def_extraction_deptypes\.idiv2:.*le_lt_dec'
forbid_line "idiv2 must not expose an unconditional recursive sub-call unfolding" '^\$_def_extraction_deptypes\.idiv2:.*Corelib\.Init\.Nat\.sub'
require_count_at_least "idiv3 has only the safe Fix_F link" '^\$_def_extraction_deptypes\.idiv3:' 1
forbid_line "idiv3 must not expose an unconditional le_lt_dec unfolding" '^\$_def_extraction_deptypes\.idiv3:.*le_lt_dec'
forbid_line "idiv3 must not expose an unconditional recursive sub-call unfolding" '^\$_def_extraction_deptypes\.idiv3:.*Corelib\.Init\.Nat\.sub'
forbid_line "Acc_rect must not get an unconditional definition equation" '^\$_def_Corelib\.Init\.Wf\.Acc_rect:'

# -----------------------------------------------------------------------------
# Stdlib regression constants: structural snapshots enforced now.
# -----------------------------------------------------------------------------

require_line "Nat.add zero split equation" '^\$_def_Corelib\.Init\.Nat\.add[$]O:'
require_line "Nat.add successor split equation" '^\$_def_Corelib\.Init\.Nat\.add[$]S:'
forbid_line "Nat.add split equations are guard/existential/disjunction free" '^\$_def_Corelib\.Init\.Nat\.add[$].*(\$HasType|\?\[|[|])'

require_count_at_least "List.app has split definition axioms" '^\$_def_Corelib\.Init\.Datatypes\.app[$]' 2
require_line "List.app split mentions nil" '^\$_def_Corelib\.Init\.Datatypes\.app[$]nil:.*Corelib\.Init\.Datatypes\.nil'
require_line "List.app split mentions cons" '^\$_def_Corelib\.Init\.Datatypes\.app[$]cons:.*Corelib\.Init\.Datatypes\.cons'

require_line "List.Forall has an inversion axiom" '^\$_inversion_Corelib\.Lists\.ListDef\.Forall:'
require_line "eq_ind_r has a translated formula" '^Corelib\.Init\.Logic\.eq_ind_r:'
require_line "eq_ind_r has a transport-erased definition" '^\$_def_Corelib\.Init\.Logic\.eq_ind_r:.*\$Proof = \$Proof'
require_line "proj1 has a translated formula" '^Corelib\.Init\.Logic\.proj1:'
require_line "Acc_rect has a type axiom" '^\$_typeof_Corelib\.Init\.Wf\.Acc_rect:'
require_count_at_least "Nat.eq_dec has a definition axiom" '^\$_def_Stdlib\.Arith\.PeanoNat\.Nat\.eq_dec:' 1
require_line "sumbool has an inversion axiom" '^\$_inversion_Corelib\.Init\.Specif\.sumbool:'
require_line "sig has an inversion axiom" '^\$_inversion_Corelib\.Init\.Specif\.sig:'
require_line "prod has an inversion axiom" '^\$_inversion_Corelib\.Init\.Datatypes\.prod:'
require_count_at_least "Vector.hd has a definition axiom" '^\$_def_Stdlib\.Vectors\.VectorDef\.hd:' 1
require_count_at_least "Streams.hd has a split definition axiom" '^\$_def_Stdlib\.Streams\.Streams\.hd[$]' 1
require_line "typeclass method projection is translated" '^Corelib\.Classes\.RelationClasses\.Equivalence_Reflexive:'

# -----------------------------------------------------------------------------
# Disabled staged assertions. These are intentionally comments until the named
# phase task changes the translator and updates the regexes to the final §6.3
# naming scheme. Phase 1 split-case assertions are enforced above.
# -----------------------------------------------------------------------------

: <<'PHASE_2_SINGLETONS'
# TASK_12 / Phase 2: Prop-singleton elimination.
# - h: $_def_extraction_deptypes.h appears and no $_generic_case/fallback marker
#   remains for the and-match; before Phase 3 its RHS may still mention exist.
# - safe_pred: dead False_rect branch is no longer exposed in the def equation.
# - WF/Acc-recursive definitions (idiv/idiv2/idiv3/Acc_rect users) still do not
#   expose unconditional unfolding equations.
PHASE_2_SINGLETONS

: <<'PHASE_4_WF_RECURSION'
# TASK_17 / Phase 4: premised WF-recursion equations.
# - idiv/idiv2/idiv3 unfolding equations are present only with the converted
#   b <> 0 premise; no unconditional WF unfolding equation is printed.
# - Acc_rect/WF regression outputs stay in the marked/premised class and do not
#   silently revert to an unsafe unconditional definition axiom.
PHASE_4_WF_RECURSION

printf 'extraction_transl assertions passed\n'
