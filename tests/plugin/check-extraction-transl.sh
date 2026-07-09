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
require_line "SProp argument is translated as a premise" '^\$_type_[0-9]+: .*\(\(=> @ extraction_transl\.sflag\) @ \(\(\$HasType @ var_[0-9]+\) @ Corelib\.Init\.Datatypes\.nat\)\)'
require_line "SProp function uses the premise type" '^\$_typeof_extraction_transl\.sprop_arg_term: \(\(\$HasType @ extraction_transl\.sprop_arg_term\) @ \$_type_[0-9]+\)'
require_line "SProp proof argument is pruned from the definition" '^\$_def_extraction_transl\.sprop_arg_term: \(extraction_transl\.sprop_arg_term = extraction_transl\.sprop_consumer\)'
forbid_line "SProp proof argument must not be applied as a term" '^\$_def_extraction_transl\.sprop_arg_term:.*sprop_consumer @'

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

# Phase 2 E1 singleton erasure: the match on the conjunction proof in h
# collapses to its unique branch.  Phase 3 will unbox exist; for this phase the
# proof argument is already erased, so the definition is exist(..., z).
require_line "h has a type axiom" '^\$_typeof_extraction_deptypes\.h:'
require_line "h has a collapsed singleton definition" '^\$_def_extraction_deptypes\.h:.*= \(\(\(Corelib\.Init\.Specif\.exist @ Corelib\.Init\.Datatypes\.nat\) @ .*\) @ 2_z\)'
forbid_line "h singleton collapse must not leave generic case" '^\$_def_extraction_deptypes\.h:.*\$_generic_case'

# safe_pred: the dependent match still splits on nat and now keeps a definition
# for both branches while proof payloads in the live successor branch are erased.
require_count_at_least "safe_pred has split definition axioms" '^\$_def_extraction_deptypes\.safe_pred[$]' 2
require_line "safe_pred zero branch remains dead-code fallback" '^\$_def_extraction_deptypes\.safe_pred[$]O:.*Corelib\.Init\.Logic\.False_rect'
require_line "safe_pred successor branch erases eq_refl proof payload" '^\$_def_extraction_deptypes\.safe_pred[$]S:.*Corelib\.Init\.Specif\.exist'
forbid_line "safe_pred successor branch must not keep eq_refl" '^\$_def_extraction_deptypes\.safe_pred[$]S:.*Corelib\.Init\.Logic\.eq_refl'

# Transport erasure: eq_rect/eq_rec/eq_ind-style casts are identities in the
# proof-irrelevant erasure model (guarded by opt_erasure_guards when enabled).
require_line "tr has an identity definition" '^\$_def_extraction_deptypes\.tr:.*= 4_x'

# pval: non-primitive projection record fixture currently has an inversion-style
# definition axiom.
require_count_at_least "pval has a split definition axiom" '^\$_def_extraction_deptypes\.pval[$]' 1
require_line "pval split mentions mkpos" '^\$_def_extraction_deptypes\.pval[$].*extraction_deptypes\.mkpos'

# beq: sumbool-driven definition links through an auxiliary case symbol for
# the compound Nat.eq_dec scrutinee.
require_count_at_least "beq has a linking definition axiom" '^\$_def_extraction_deptypes\.beq[$]link:' 1
require_line "beq link mentions Nat.eq_dec" '^\$_def_extraction_deptypes\.beq[$]link:.*Nat\.eq_dec'
require_line "beq aux case mentions sumbool constructors" '^\$_case_Corelib\.Init\.Specif\.sumbool[$][0-9]+[$].*Corelib\.Init\.Specif\.(left|right)'

# tag: prod-with-Prop fixture still contains the pair constructor in Phase 2,
# but the propositional eq_refl payload is erased.
require_count_at_least "tag has a definition axiom" '^\$_def_extraction_deptypes\.tag:' 1
require_line "tag baseline mentions pair" '^\$_def_extraction_deptypes\.tag:.*Corelib\.Init\.Datatypes\.pair'
forbid_line "tag proof payload is erased" '^\$_def_extraction_deptypes\.tag:.*Corelib\.Init\.Logic\.eq_refl'

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

: <<'PHASE_3_REFINEMENTS'
# TASK_15 / Phase 3: refinement unboxing and specification extraction.
# - h: $_def_extraction_deptypes.h RHS is the bare z variable; $_typeof_h contains
#   the payload x = h x y z and no $HasType(..., sig ...).
# - h/safe_pred/pval/tag/beq output contains no Corelib.Init.Specif.sig,
#   Corelib.Init.Specif.exist, or proj1_sig where the classified refinement/enum
#   translation applies.
# - beq/Nat.eq_dec sumbool guards are expanded shallowly.
PHASE_3_REFINEMENTS

: <<'PHASE_4_WF_RECURSION'
# TASK_17 / Phase 4: premised WF-recursion equations.
# - idiv/idiv2/idiv3 unfolding equations are present only with the converted
#   b <> 0 premise; no unconditional WF unfolding equation is printed.
# - Acc_rect/WF regression outputs stay in the marked/premised class and do not
#   silently revert to an unsafe unconditional definition axiom.
PHASE_4_WF_RECURSION

printf 'extraction_transl assertions passed\n'
