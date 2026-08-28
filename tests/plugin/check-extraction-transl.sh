#!/usr/bin/env bash
set -euo pipefail

out=${1:-extraction_transl.out}
assert_context=extraction_transl
# shellcheck source=tests/plugin/transl-assert-lib.sh
. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)/transl-assert-lib.sh"

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

require_count_exact() {
  local label=$1
  local pattern=$2
  local expected=$3
  local count
  count=$(grep -Ec -- "$pattern" "$out" || true)
  if [ "$count" -ne "$expected" ]; then
    fail "$label (expected $expected matches for: $pattern; found $count)"
  fi
}




extract_unique_symbol() {
  local label=$1
  local text=$2
  local context_pattern=$3
  local symbol_pattern=$4
  local symbols
  mapfile -t symbols < <(
    printf '%s\n' "$text" |
      grep -Eo -- "$context_pattern" |
      grep -Eo -- "$symbol_pattern" |
      sort -u || true
  )
  if [ "${#symbols[@]}" -ne 1 ]; then
    fail "$label (expected one generated symbol; found ${#symbols[@]})"
  fi
  printf '%s\n' "${symbols[0]}"
}


# Proposition helpers are generated with fresh IDs.  Parse their binders and
# compare the complete defining equivalence instead of baking those IDs into a
# regular expression.
assert_binary_prop_is_equality() {
  local label=$1
  local symbol=$2
  local line
  local binders
  local lhs rhs expected
  line=$(get_unique_line "$label helper definition" "$symbol:")
  parse_binders "$label helper definition" "$line" universal 2 binders
  lhs=${binders[0]}
  rhs=${binders[1]}
  expected="$symbol: ![$lhs : \$Any]: (![$rhs : \$Any]: (((<=> @ (($symbol @ $lhs) @ $rhs)) @ ($lhs = $rhs))))"
  if [ "$line" != "$expected" ]; then
    fail "$label helper $symbol does not define its exact proposition as equality"
  fi
}

assert_nat_eqb_truth_table() {
  local symbol=$1
  local line expected
  local binders
  local x y
  local o='Corelib.Init.Datatypes.O'
  local s='Corelib.Init.Datatypes.S'
  local true='Corelib.Init.Datatypes.true'
  local false='Corelib.Init.Datatypes.false'

  line=$(get_unique_line "Nat.eqb O/O helper equation" "$symbol\$O\$O:")
  expected="$symbol\$O\$O: ((($symbol @ $o) @ $o) = $true)"
  [ "$line" = "$expected" ] || fail "Nat.eqb helper has the wrong O/O equation"

  line=$(get_unique_line "Nat.eqb O/S helper equation" "$symbol\$O\$S:")
  parse_binders "Nat.eqb O/S helper equation" "$line" universal 1 binders
  x=${binders[0]}
  expected="$symbol\$O\$S: ![$x : \$Any]: (((($symbol @ $o) @ ($s @ $x)) = $false))"
  [ "$line" = "$expected" ] || fail "Nat.eqb helper has the wrong O/S equation"

  line=$(get_unique_line "Nat.eqb S/O helper equation" "$symbol\$S\$O:")
  parse_binders "Nat.eqb S/O helper equation" "$line" universal 1 binders
  x=${binders[0]}
  expected="$symbol\$S\$O: ![$x : \$Any]: (((($symbol @ ($s @ $x)) @ $o) = $false))"
  [ "$line" = "$expected" ] || fail "Nat.eqb helper has the wrong S/O equation"

  line=$(get_unique_line "Nat.eqb S/S helper equation" "$symbol\$S\$S:")
  parse_binders "Nat.eqb S/S helper equation" "$line" universal 2 binders
  x=${binders[0]}
  y=${binders[1]}
  expected="$symbol\$S\$S: ![$x : \$Any]: (![$y : \$Any]: (((($symbol @ ($s @ $x)) @ ($s @ $y)) = (($symbol @ $x) @ $y))))"
  [ "$line" = "$expected" ] || fail "Nat.eqb helper has the wrong S/S recursion equation"
}

# -----------------------------------------------------------------------------
# Global sanity checks enforced now.
# -----------------------------------------------------------------------------

forbid_line "Hammer_transl lookup failures" '^Error: Not found:'

# Same intent as transl.v's Init.Logic sanity check, but restricted to logical
# connective constants: this corpus intentionally still exposes proof constants
# such as eq_refl/False_rect on fallback paths.
forbid_line "untranslated Init.Logic connectives" 'Init\.Logic\.(and|or|not|iff|ex|all)\b'


# Proof arguments are proof-irrelevant: generated structural and definitional
# axioms must not leave tautological $Proof = $Proof equalities behind.
forbid_line "injectivity axioms omit proof-only equalities" '^\$_inj_.*\$Proof = \$Proof'
forbid_line "definition axioms omit proof-only equalities" '^\$_def_.*\$Proof = \$Proof'

# Shallowness gates for definitional output: split equations should not
# reintroduce type guards, existential packages, or disjunctive case bodies on
# definition lines.
forbid_line "definition axioms are HasType-free" '^\$_def_.*\$HasType'
forbid_line "definition axioms are existential-free" '^\$_def_.*\?\['
forbid_line "definition axioms are disjunction-free" '^\$_def_.*[|]'

# -----------------------------------------------------------------------------
# Corpus constants: baseline structural assertions that hold today.
# -----------------------------------------------------------------------------

# SProp hypotheses are proof-like: the argument becomes a formula premise and is
# pruned from the term-level definition equation.  The unfolding is conjoined
# with the membership that states the constant inhabits its own type, as
# membership_transl.v pins for every product with erasable content.  The type is
# a lifted name rather than an [$_arrow] application because an SProp domain is
# proof-like, and remove_type canonicalizes only informative domains.
require_line "SProp argument is translated as a premise" '^\$_typeof_extraction_transl\.sprop_arg_term: \(\(& @ \(\(\$HasType @ extraction_transl\.sprop_arg_term\) @ \$_type_[0-9]+\)\) @ \(\(=> @ extraction_transl\.sflag\) @ \(\(\$HasType @ extraction_transl\.sprop_arg_term\) @ Corelib\.Init\.Datatypes\.nat\)\)\)'
require_line "SProp proof argument is pruned from the definition" '^\$_def_extraction_transl\.sprop_arg_term: \(extraction_transl\.sprop_arg_term = extraction_transl\.sprop_consumer\)'
forbid_line "SProp proof argument must not be applied as a term" '^\$_def_extraction_transl\.sprop_arg_term:.*sprop_consumer @'

# A Prop premise must leave the extracted term unapplied across the implication
# (proof argument pruned from arity).
require_line "spec_pruned type axiom keeps pruned arity" '^\$_typeof_extraction_transl\.spec_pruned:.*\(=> @ \(var_0_n_[0-9]+ = var_0_n_[0-9]+\)\) @ \(\(& @ \(\(\$HasType @ \(extraction_transl\.spec_pruned @ var_0_n_[0-9]+\)\) @ Corelib\.Init\.Datatypes\.nat\)\) @ \(var_0_n_[0-9]+ = \(extraction_transl\.spec_pruned @ var_0_n_[0-9]+\)\)\)'
forbid_line "spec_pruned proof premise must not be applied as a term" '^\$_typeof_extraction_transl\.spec_pruned:.*extraction_transl\.spec_pruned @ .*\$Proof'

# User constants with proof/transport basenames must remain ordinary constants.
require_line "shadow eq_rect definition is not a fake transport definition" '^\$_def_extraction_transl\.ShadowTransport\.eq_rect:.*= 4_e\)'
require_line "shadow eq_rect applications are not transport-erased" '^\$_def_extraction_transl\.shadow_eq_rect_user:.*extraction_transl\.ShadowTransport\.eq_rect'
require_line "shadow False_rect type argument is not proof-erased" '^\$_def_extraction_transl\.shadow_false_rect_user:.*Corelib\.Init\.Specif\.sig'
require_line "shadow eq_refl application remains a term" '^\$_def_extraction_transl\.shadow_eq_refl_user:.*extraction_transl\.ShadowProofNames\.eq_refl'
require_line "shadow eq_trans application remains a term" '^\$_def_extraction_transl\.shadow_eq_trans_user:.*extraction_transl\.ShadowProofNames\.eq_trans'
require_line "shadow eq_sym application remains a term" '^\$_def_extraction_transl\.shadow_eq_sym_user:.*extraction_transl\.ShadowProofNames\.eq_sym'
require_line "shadow JMeq_refl application remains a term" '^\$_def_extraction_transl\.shadow_jmeq_refl_user:.*extraction_transl\.ShadowProofNames\.JMeq_refl'
for shadow_name in shadow_false_rect_user shadow_eq_refl_user shadow_eq_trans_user shadow_eq_sym_user shadow_jmeq_refl_user; do
  forbid_line "shadow proof-name constants must not become proof terms ($shadow_name)" '^\$_def_extraction_transl\.'"$shadow_name"':.*\$Proof'
done

# Split-case constructor binders are refreshed when they collide with function
# binders, so the function argument and constructor payload remain distinct.
require_line "box_arg_collision split keeps outer and constructor a distinct" '^\$_def_extraction_transl\.box_arg_collision[$]onebox_intro:.*\(\(\(extraction_transl\.box_arg_collision @ 0_A\) @ 1_a\) @ \(\(extraction_transl\.onebox_intro @ 0_A\) @ var_[0-9]+_a_[0-9]+\)\) = var_[0-9]+_a_[0-9]+'

# A user inductive whose field has type [F x] is instance-dependent: for
# [F : nat -> Prop], the field is proof-only even though the declaration-level
# formal [F : A -> Type] is not.  The definition unboxes the carrier and the
# occurrence guard expands to the carrier guard plus the predicate payload.
require_line "depbox_project unboxes an instance-dependent user subset" '^\$_def_extraction_transl\.depbox_project:.*= 1_b\)'
require_line "depbox_project type axiom expands the dependent package guard" '^\$_typeof_extraction_transl\.depbox_project:.*\(& @ \(\(\$HasType @ var_1_b_[0-9]+\) @ Corelib\.Init\.Datatypes\.nat\)\) @ \(var_0_P_[0-9]+ @ var_1_b_[0-9]+\)'

# A mutually recursive pair of apparent refinement carriers is not collapsible.
# Translation must terminate and retain its ordinary nominal guard.  The guard
# lives in the unfolding axiom of the canonical arrow former, since
# [mutual_ref_a -> mutual_ref_a] is a non-dependent product.
require_line "mutual refinement carrier cycle translation terminates" '^\$_def_extraction_transl\.mutual_ref_identity:'
require_line "mutual refinement carrier cycle falls back to a nominal guard" '^\$_arrow_[0-9]+:.*\$HasType.*extraction_transl\.mutual_ref_a.*\$HasType.*extraction_transl\.mutual_ref_a'

# [poly_ref A] changes classification when [A] is instantiated by a Prop, so
# formal-instance subset classification must not suppress declaration structure.
require_line "parameter-dependent refinement keeps constructor injectivity" '^\$_inj_extraction_transl\.poly_ref_intro:'
forbid_line "erased constructor injectivity does not infer parameter equality" '^\$_inj_extraction_transl\.poly_ref_intro:.*var_0_A_[0-9]+ = var_0_A_[0-9]+'
require_line "parameter-dependent refinement keeps inversion" '^\$_inversion_extraction_transl\.poly_ref:'

# Split equations: variable-scrutinee definitions are emitted as one guard-free
# unit equation per constructor.
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

# A subset constructor with a proof binder before the carrier must still erase
# the constructor occurrence in the type axiom guard.
require_line "proof-first subset type axiom expands the payload on the erased carrier" '^\$_typeof_extraction_transl\.proof_first_make:.*\(\(\$HasType @ \(extraction_transl\.proof_first_make @ var_0_n_[0-9]+\)\) @ Corelib\.Init\.Datatypes\.nat\).*var_0_n_[0-9]+ = \(extraction_transl\.proof_first_make @ var_0_n_[0-9]+\)'
forbid_line "proof-first subset type axiom must not keep the constructor application" '^\$_typeof_extraction_transl\.proof_first_make:.*extraction_transl\.proof_first_intro'
forbid_line "proof-first subset definition must erase proof payloads" '^\$_def_extraction_transl\.proof_first_make:.*(Corelib\.Init\.Logic\.(I|eq_refl)|extraction_transl\.proof_first_intro)'

# The h example has exactly two axioms: a carrier-only program equation and a
# specification axiom with nat guards plus the expanded equality payload.
require_count_exact "h emits exactly its definition and type axioms" '^\$_(def|typeof)_extraction_deptypes\.h:' 2
require_line "h has the carrier-only definition equation" '^\$_def_extraction_deptypes\.h: !\[0_x : \$Any\]: \(!\[1_y : \$Any\]: \(!\[2_z : \$Any\]: .*\(\(\(extraction_deptypes\.h @ 0_x\) @ 1_y\) @ 2_z\) = 2_z'
require_line "h has the specification-extracted axiom shape" '^\$_typeof_extraction_deptypes\.h:.*\$HasType @ var_0_x_[0-9]+\) @ Corelib\.Init\.Datatypes\.nat.*\$HasType @ var_1_y_[0-9]+\) @ Corelib\.Init\.Datatypes\.nat.*\$HasType @ var_2_z_[0-9]+\) @ Corelib\.Init\.Datatypes\.nat.*=> @ \(\(& @ \(var_0_x_[0-9]+ = var_1_y_[0-9]+\)\) @ \(var_1_y_[0-9]+ = var_2_z_[0-9]+\)\).*& @ \(\(\$HasType @ \(\(\(extraction_deptypes\.h @ var_0_x_[0-9]+\) @ var_1_y_[0-9]+\) @ var_2_z_[0-9]+\)\) @ Corelib\.Init\.Datatypes\.nat\)\) @ \(var_0_x_[0-9]+ = \(\(\(extraction_deptypes\.h @ var_0_x_[0-9]+\) @ var_1_y_[0-9]+\) @ var_2_z_[0-9]+\)\)'
forbid_line "h type axiom must not keep a sig HasType atom" '^\$_typeof_extraction_deptypes\.h:.*Corelib\.Init\.Specif\.sig'
forbid_line "h output must not mention erased sig/exist/proj1_sig" '^.*extraction_deptypes\.h.*Corelib\.Init\.Specif\.(sig|exist|proj1_sig)'
forbid_line "h singleton collapse must not leave generic case" '^.*extraction_deptypes\.h.*\$_generic_case'
forbid_line "default extraction output contains no opaque generic case symbol" '\$_generic_case_'

# safe_pred: the dependent match still splits on nat and now keeps a definition
# for both branches while proof payloads in the live successor branch are erased.
require_count_at_least "safe_pred has split definition axioms" '^\$_def_extraction_deptypes\.safe_pred[$]' 2
require_line "safe_pred zero branch remains dead-code fallback" '^\$_def_extraction_deptypes\.safe_pred[$]O:.*Corelib\.Init\.Logic\.False_rect'
forbid_line "safe_pred zero branch must not leak the erased sig package" '^\$_def_extraction_deptypes\.safe_pred[$]O:.*Corelib\.Init\.Specif\.sig'
require_line "safe_pred successor branch unboxes the subset result" '^\$_def_extraction_deptypes\.safe_pred[$]S:.*= var_0_[$]Anonymous_[0-9]+\)'
require_line "safe_pred type axiom expands the subset payload" '^\$_typeof_extraction_deptypes\.safe_pred:.*var_0_n_[0-9]+ = \(Corelib\.Init\.Datatypes\.S @ \(extraction_deptypes\.safe_pred @ var_0_n_[0-9]+\)\)'
forbid_line "safe_pred type axiom must not keep a sig HasType atom" '^\$_typeof_extraction_deptypes\.safe_pred:.*Corelib\.Init\.Specif\.sig'
forbid_line "safe_pred successor branch must not keep eq_refl" '^\$_def_extraction_deptypes\.safe_pred[$]S:.*Corelib\.Init\.Logic\.eq_refl'
forbid_line "safe_pred successor branch must not keep exist" '^\$_def_extraction_deptypes\.safe_pred[$]S:.*Corelib\.Init\.Specif\.exist'

# Transport erasure: eq_rect/eq_rec/eq_ind-style casts are identities in the
# proof-irrelevant erasure model.
require_line "tr has an identity definition" '^\$_def_extraction_deptypes\.tr:.*= 4_x'

# proj1_sig's own subset match collapses to the identity equation; no
# per-occurrence delta unfolding is needed for users because this is a perfect
# demodulator.
require_line "proj1_sig has an identity definition" '^\$_def_Corelib\.Init\.Specif\.proj1_sig:.*= 2_e\)'

# pval: non-primitive projection over a proof-carrying record is the identity
# after subset-match collapse; its argument guard expands to the carrier and
# positivity payload.
require_line "pval has an identity definition" '^\$_def_extraction_deptypes\.pval:.*= 0_p\)'
require_line "pval type axiom expands the posnat guard" '^\$_typeof_extraction_deptypes\.pval:.*\(& @ \(\(\$HasType @ var_0_p_[0-9]+\) @ Corelib\.Init\.Datatypes\.nat\)\) @ \(\(Corelib\.Init\.Peano\.lt @ Corelib\.Init\.Datatypes\.O\) @ var_0_p_[0-9]+\)'
forbid_line "pval definition must not mention mkpos" '^\$_def_extraction_deptypes\.pval:.*extraction_deptypes\.mkpos'

# beq: sumbool-driven definition links through an auxiliary case symbol for
# the compound Nat.eq_dec scrutinee; enum guards expand to constructor tags plus
# payload formulas.
require_count_at_least "beq has a linking definition axiom" '^\$_def_extraction_deptypes\.beq[$]link:' 1
require_line "beq link mentions Nat.eq_dec" '^\$_def_extraction_deptypes\.beq[$]link:.*Nat\.eq_dec'
require_line "beq aux case mentions sumbool constructors" '^\$_case_Corelib\.Init\.Specif\.sumbool[$][0-9]+[$].*Corelib\.Init\.Specif\.(left|right)'
require_line "beq type axiom expands bool enum result" '^\$_typeof_extraction_deptypes\.beq:.*extraction_deptypes\.beq @ var_0_n_[0-9]+.*Corelib\.Init\.Datatypes\.true.*Corelib\.Init\.Datatypes\.false'
require_line "Nat.eq_dec type axiom expands sumbool payloads" '^\$_typeof_Stdlib\.Arith\.PeanoNat\.Nat\.eq_dec:.*var_0_n_[0-9]+ = var_1_m_[0-9]+.*~ @ \(var_0_n_[0-9]+ = var_1_m_[0-9]+\)'
forbid_line "Nat.eq_dec type axiom must not keep a sumbool HasType atom" '^\$_typeof_Stdlib\.Arith\.PeanoNat\.Nat\.eq_dec:.*Corelib\.Init\.Specif\.sumbool'

# between: sig2 is declaration-level subset-like and erases to its carrier while
# both payload propositions are expanded in the type axiom.
require_line "between has an unboxed definition axiom" '^\$_def_extraction_deptypes\.between:.*= 0_n\)'
require_line "between type axiom expands both sig2 payloads" '^\$_typeof_extraction_deptypes\.between:.*Corelib\.Init\.Peano\.le @ var_0_n_[0-9]+\) @ \(extraction_deptypes\.between @ var_0_n_[0-9]+\).*Corelib\.Init\.Peano\.le @ \(extraction_deptypes\.between @ var_0_n_[0-9]+\)\) @ \(Corelib\.Init\.Datatypes\.S @ var_0_n_[0-9]+\)'
forbid_line "between definition must not mention exist2" '^\$_def_extraction_deptypes\.between:.*Corelib\.Init\.Specif\.exist2'
forbid_line "between type axiom must not keep a sig2 HasType atom" '^\$_typeof_extraction_deptypes\.between:.*Corelib\.Init\.Specif\.sig2'

# tag: prod-with-Prop is a per-instance subset; pair erases to the informative
# first component and the result guard carries the equality payload.
require_line "tag has an unboxed definition axiom" '^\$_def_extraction_deptypes\.tag:.*= 0_n\)'
require_line "tag type axiom expands the prod payload" '^\$_typeof_extraction_deptypes\.tag:.*\(& @ \(\(\$HasType @ \(extraction_deptypes\.tag @ var_0_n_[0-9]+\)\) @ Corelib\.Init\.Datatypes\.nat\)\) @ \(var_0_n_[0-9]+ = var_0_n_[0-9]+\)'
forbid_line "tag definition must not mention pair" '^\$_def_extraction_deptypes\.tag:.*Corelib\.Init\.Datatypes\.pair'
forbid_line "tag proof payload is erased" '^\$_def_extraction_deptypes\.tag:.*Corelib\.Init\.Logic\.eq_refl'
forbid_line "tag type axiom must not keep a prod HasType atom" '^\$_typeof_extraction_deptypes\.tag:.*Corelib\.Init\.Datatypes\.prod'

# Indexed-family match: vhead is a normal split-pattern equation over Vector.t;
# it must not introduce existential case bodies in definition axioms.
require_line "vhead has a cons split equation" '^\$_def_extraction_deptypes\.vhead[$]cons:.*= var_1_h_[0-9]+\)'
forbid_line "vhead split equations are existential-free" '^\$_def_extraction_deptypes\.vhead[$].*\?\['

# Forded split equations do not depend on index premises recovered from a
# scrutinee's declared type.  dsize and dheight therefore emit both equations
# unconditionally even though their declared types are type-level functions.
dsize_leaf_line=$(get_unique_line "dsize leaf equation" '$_def_extraction_deptypes.dsize$dleaf:')
parse_binders "dsize leaf equation" "$dsize_leaf_line" universal 1 dsize_leaf_binders
dsize_outer=${dsize_leaf_binders[0]}
require_text_count_exact "dsize has an unconditional leaf equation" "$dsize_leaf_line" "(((extraction_deptypes.dsize @ $dsize_outer) @ extraction_deptypes.dleaf) = Corelib.Init.Datatypes.O)" 1

dsize_node_line=$(get_unique_line "dsize node equation" '$_def_extraction_deptypes.dsize$dnode:')
parse_binders "dsize node equation" "$dsize_node_line" universal 4 dsize_node_binders
dsize_outer=${dsize_node_binders[0]}
dsize_n=${dsize_node_binders[1]}
dsize_left=${dsize_node_binders[2]}
dsize_right=${dsize_node_binders[3]}
require_text_count_exact "dsize correlates its node binders with the result" "$dsize_node_line" "((extraction_deptypes.dsize @ $dsize_outer) @ (((extraction_deptypes.dnode @ $dsize_n) @ $dsize_left) @ $dsize_right)) = (Corelib.Init.Datatypes.S @ $dsize_n)" 1
forbid_line "dsize split equations have no legacy index premise" '^\$_def_extraction_deptypes\.dsize[$].*=> @'
forbid_line "dsize split equations do not expose the declared type-level function" '^\$_def_extraction_deptypes\.dsize[$].*extraction_deptypes\.(dres|dred|dblack|dpair)'

dheight_zero_line=$(get_unique_line "dheight zero equation" '$_def_extraction_deptypes.dheight$dbox_zero:')
parse_binders "dheight zero equation" "$dheight_zero_line" universal 1 dheight_zero_binders
dheight_outer=${dheight_zero_binders[0]}
require_text_count_exact "dheight has an unconditional zero equation" "$dheight_zero_line" "((extraction_deptypes.dheight @ $dheight_outer) @ (extraction_deptypes.dbox_zero @ extraction_deptypes.dred)) = Corelib.Init.Datatypes.O" 1

dheight_succ_line=$(get_unique_line "dheight successor equation" '$_def_extraction_deptypes.dheight$dbox_succ:')
parse_binders "dheight successor equation" "$dheight_succ_line" universal 3 dheight_succ_binders
dheight_outer=${dheight_succ_binders[0]}
dheight_n=${dheight_succ_binders[1]}
dheight_payload=${dheight_succ_binders[2]}
require_text_count_exact "dheight correlates its successor binders with the result" "$dheight_succ_line" "((extraction_deptypes.dheight @ $dheight_outer) @ (((extraction_deptypes.dbox_succ @ extraction_deptypes.dred) @ $dheight_n) @ $dheight_payload)) = (Corelib.Init.Datatypes.S @ $dheight_n)" 1
forbid_line "dheight split equations have no legacy index premise" '^\$_def_extraction_deptypes\.dheight[$].*=> @'
forbid_line "dheight split equations do not expose the declared type-level function" '^\$_def_extraction_deptypes\.dheight[$].*extraction_deptypes\.dswap'

# The same rule makes a match through a type-level fixpoint translatable without
# unfolding that fixpoint merely to manufacture an index guard.
dstack_leaf_line=$(get_unique_line "dstack_size leaf equation" '$_def_extraction_deptypes.dstack_size$dleaf:')
parse_binders "dstack_size leaf equation" "$dstack_leaf_line" universal 1 dstack_leaf_binders
dstack_outer=${dstack_leaf_binders[0]}
require_text_count_exact "dstack_size has an unconditional leaf equation" "$dstack_leaf_line" "(((extraction_deptypes.dstack_size @ $dstack_outer) @ extraction_deptypes.dleaf) = Corelib.Init.Datatypes.O)" 1

dstack_node_line=$(get_unique_line "dstack_size node equation" '$_def_extraction_deptypes.dstack_size$dnode:')
parse_binders "dstack_size node equation" "$dstack_node_line" universal 4 dstack_node_binders
dstack_outer=${dstack_node_binders[0]}
dstack_n=${dstack_node_binders[1]}
dstack_left=${dstack_node_binders[2]}
dstack_right=${dstack_node_binders[3]}
require_text_count_exact "dstack_size correlates its node binders with the result" "$dstack_node_line" "((extraction_deptypes.dstack_size @ $dstack_outer) @ (((extraction_deptypes.dnode @ $dstack_n) @ $dstack_left) @ $dstack_right)) = (Corelib.Init.Datatypes.S @ $dstack_n)" 1
forbid_line "dstack_size split equations have no legacy index premise" '^\$_def_extraction_deptypes\.dstack_size[$].*=> @'
require_line "dstack_size retains its typing axiom" '^\$_typeof_extraction_deptypes\.dstack_size:'

# The nested outer match is known to inspect [dtree 0].  Rigid-clash pruning
# retains its leaf equation and removes the impossible successor-indexed node
# equation.  The link also pins that the outer auxiliary receives exactly the
# result of the inner option case, not a surplus type-level-function argument.
require_line "the inner case supplies the outer scrutinee its unapplied type" '^\$_def_extraction_deptypes\.dnested[$]link:.*= \(\$_case_extraction_deptypes\.dtree[$][0-9]+ @ \(\$_case_Corelib\.Init\.Datatypes\.option[$][0-9]+ @ 0_o\)\)\)'
require_line "the outer case auxiliary keeps its leaf equation" '^\$_case_extraction_deptypes\.dtree[$][0-9]+[$]dleaf:'
forbid_line "rigid clash prunes the outer node equation" '^\$_case_extraction_deptypes\.dtree[$][0-9]+[$]dnode:'

# Indexed-family fixtures: solved constructor arguments and erased proof fields
# make the split equations unconditional, while occurrence guards retain the
# informative payload and residual index equations.  Generated binder suffixes
# are unstable, so parse each inversion line once and use fixed-text fragments
# that correlate the exact binders across guards, constructors, and equations.
breflect_line=$(get_unique_line "breflect inversion" '$_inversion_extraction_indexed.breflect:')
parse_binders "breflect inversion" "$breflect_line" universal 3 breflect_binders
breflect_p=${breflect_binders[0]}
breflect_index=${breflect_binders[1]}
breflect_value=${breflect_binders[2]}
require_text "breflect inversion types its proposition binder" "$breflect_line" "\$HasType @ $breflect_p) @ Prop"
require_text "breflect inversion admits exactly the boolean result indices" "$breflect_line" "((| @ ((& @ ($breflect_index = Corelib.Init.Datatypes.true)) @ \$True)) @ ((& @ ($breflect_index = Corelib.Init.Datatypes.false)) @ \$True))"
require_text_count_exact "breflect ReflectT forward branch correlates constructor, payload, and index" "$breflect_line" "((& @ ($breflect_value = (extraction_indexed.BReflectT @ $breflect_p))) @ ((& @ $breflect_p) @ ($breflect_index = Corelib.Init.Datatypes.true)))" 1
require_text_count_exact "breflect ReflectT reverse branch correlates constructor, payload, and index" "$breflect_line" "((& @ $breflect_p) @ ((& @ ($breflect_index = Corelib.Init.Datatypes.true)) @ ($breflect_value = (extraction_indexed.BReflectT @ $breflect_p))))" 1
require_text_count_exact "breflect ReflectF forward branch correlates constructor, payload, and index" "$breflect_line" "((& @ ($breflect_value = (extraction_indexed.BReflectF @ $breflect_p))) @ ((& @ (~ @ $breflect_p)) @ ($breflect_index = Corelib.Init.Datatypes.false)))" 1
require_text_count_exact "breflect ReflectF reverse branch correlates constructor, payload, and index" "$breflect_line" "((& @ (~ @ $breflect_p)) @ ((& @ ($breflect_index = Corelib.Init.Datatypes.false)) @ ($breflect_value = (extraction_indexed.BReflectF @ $breflect_p))))" 1

tagged_line=$(get_unique_line "tagged inversion" '$_inversion_extraction_indexed.tagged:')
parse_binders "tagged inversion outer" "$tagged_line" universal 2 tagged_outer_binders
parse_binders "tagged inversion constructor" "$tagged_line" existential 1 tagged_constructor_binders
tagged_index=${tagged_outer_binders[0]}
tagged_value=${tagged_outer_binders[1]}
tagged_n=${tagged_constructor_binders[0]}
require_text "tagged inversion correlates its outer guard and constructor" "$tagged_line" "((=> @ ((\$HasType @ $tagged_index) @ Corelib.Init.Datatypes.nat)) @ ((=> @ ((& @ ($tagged_value = (extraction_indexed.tg @ $tagged_index))) @ \$True))"
require_text_count_exact "tagged inversion correlates its solved index, RHS, and constructor typing" "$tagged_line" "?[$tagged_n : \$Any]: (((& @ ((\$HasType @ $tagged_n) @ Corelib.Init.Datatypes.nat)) @ ((& @ ($tagged_index = $tagged_n)) @ ($tagged_value = (extraction_indexed.tg @ $tagged_n))))" 1

okp_line=$(get_unique_line "okp inversion" '$_inversion_extraction_indexed.okp:')
parse_binders "okp inversion" "$okp_line" universal 2 okp_binders
okp_n=${okp_binders[0]}
okp_index=${okp_binders[1]}
require_text "okp inversion types its parameter" "$okp_line" "\$HasType @ $okp_n) @ Corelib.Init.Datatypes.nat"
require_text "okp inversion types its result index" "$okp_line" "\$HasType @ $okp_index) @ Corelib.Init.Datatypes.nat"
require_text_count_exact "okp inversion correlates its family parameters and successor index" "$okp_line" "((=> @ ((extraction_indexed.okp @ $okp_n) @ $okp_index)) @ ($okp_index = (Corelib.Init.Datatypes.S @ $okp_n)))" 1

vec_line=$(get_unique_line "vec inversion" '$_inversion_extraction_indexed.vec:')
parse_binders "vec inversion outer" "$vec_line" universal 3 vec_outer_binders
parse_binders "vec inversion vcons" "$vec_line" existential 3 vec_constructor_binders
vec_a=${vec_outer_binders[0]}
vec_index=${vec_outer_binders[1]}
vec_value=${vec_outer_binders[2]}
vec_n=${vec_constructor_binders[0]}
vec_payload=${vec_constructor_binders[1]}
vec_tail=${vec_constructor_binders[2]}
require_text "vec inversion correlates its outer typing guards" "$vec_line" "((=> @ ((\$HasType @ $vec_a) @ Type)) @ ((=> @ ((\$HasType @ $vec_index) @ Corelib.Init.Datatypes.nat)) @ ((=> @ ((\$HasType @ $vec_value) @ ((extraction_indexed.vec @ $vec_a) @ $vec_index)))"
require_text_count_exact "vec inversion correlates its vnil parameter and zero index" "$vec_line" "((& @ ($vec_index = Corelib.Init.Datatypes.O)) @ ($vec_value = (extraction_indexed.vnil @ $vec_a)))" 1
require_text "vec inversion types its vcons index" "$vec_line" "?[$vec_n : \$Any]: (((& @ ((\$HasType @ $vec_n) @ Corelib.Init.Datatypes.nat))"
require_text "vec inversion types its payload at the exact family parameter" "$vec_line" "?[$vec_payload : \$Any]: (((& @ ((\$HasType @ $vec_payload) @ $vec_a))"
require_text "vec inversion types its tail at the exact parameter and constructor index" "$vec_line" "?[$vec_tail : \$Any]: (((& @ ((\$HasType @ $vec_tail) @ ((extraction_indexed.vec @ $vec_a) @ $vec_n)))"
require_text_count_exact "vec inversion correlates its successor index and complete vcons payload" "$vec_line" "((& @ ($vec_index = (Corelib.Init.Datatypes.S @ $vec_n))) @ ($vec_value = ((((extraction_indexed.vcons @ $vec_a) @ $vec_n) @ $vec_payload) @ $vec_tail)))" 1

# The constructor argument a result index fords is not quantified again: it is
# the scrutinee's own index, so the branch equation binds it once.
untag_line=$(get_unique_line "untag constructor equation" '$_def_extraction_indexed.untag$tg:')
parse_binders "untag constructor equation" "$untag_line" universal 1 untag_binders
untag_index=${untag_binders[0]}
require_text_count_exact "untag fords its constructor index to the occurrence index" "$untag_line" "((extraction_indexed.untag @ $untag_index) @ (extraction_indexed.tg @ $untag_index)) = $untag_index)" 1
forbid_line "untag has no legacy index premise" '^\$_def_extraction_indexed\.untag[$]tg:.*=> @'

ibval_line=$(get_unique_line "ibval constructor equation" '$_def_extraction_indexed.ibval$IBounded:')
parse_binders "ibval constructor equation" "$ibval_line" universal 2 ibval_binders
ibval_outer=${ibval_binders[0]}
ibval_carrier=${ibval_binders[1]}
require_text_count_exact "ibval correlates its carrier argument with the result" "$ibval_line" "((extraction_indexed.ibval @ $ibval_outer) @ $ibval_carrier) = $ibval_carrier)" 1
forbid_line "ibval carrier equation is unconditional" '^\$_def_extraction_indexed\.ibval[$]IBounded:.*=> @'
forbid_line "ibval definition omits the erased subset constructor" '^\$_def_extraction_indexed\.ibval[$]IBounded:.*extraction_indexed\.IBounded'

# A body reading the solved index instead of the carrier must equate the result
# with the scrutinee's index.  A fresh binder there would occur only on the
# right-hand side, and the collapse of the constructor to its carrier would
# then make any two indices equal.
ibidx_line=$(get_unique_line "ibidx constructor equation" '$_def_extraction_indexed.ibidx$IBounded:')
parse_binders "ibidx constructor equation" "$ibidx_line" universal 2 ibidx_binders
ibidx_outer=${ibidx_binders[0]}
ibidx_carrier=${ibidx_binders[1]}
require_text_count_exact "ibidx fords its solved index to the scrutinee index" "$ibidx_line" "((extraction_indexed.ibidx @ $ibidx_outer) @ $ibidx_carrier) = $ibidx_outer)" 1
forbid_line "ibidx carrier equation is unconditional" '^\$_def_extraction_indexed\.ibidx[$]IBounded:.*=> @'
forbid_line "ibidx definition omits the erased subset constructor" '^\$_def_extraction_indexed\.ibidx[$]IBounded:.*extraction_indexed\.IBounded'

ibval_typeof_line=$(get_unique_line "ibval typing axiom" '$_typeof_extraction_indexed.ibval:')
parse_binders "ibval typing axiom" "$ibval_typeof_line" universal 2 ibval_typeof_binders
ibval_n=${ibval_typeof_binders[0]}
ibval_b=${ibval_typeof_binders[1]}
require_text "ibval typing axiom types its exact index binder" "$ibval_typeof_line" "((\$HasType @ $ibval_n) @ Corelib.Init.Datatypes.nat)"
require_text_count_exact "ibval typing axiom correlates its carrier and bound" "$ibval_typeof_line" "((& @ ((\$HasType @ $ibval_b) @ Corelib.Init.Datatypes.nat)) @ ((Corelib.Init.Peano.lt @ $ibval_b) @ $ibval_n))" 1
require_text_count_exact "ibval typing axiom correlates its result application" "$ibval_typeof_line" "((\$HasType @ ((extraction_indexed.ibval @ $ibval_n) @ $ibval_b)) @ Corelib.Init.Datatypes.nat)" 1
forbid_line "ibval type axiom has no nominal ibounded leaf" '^\$_typeof_extraction_indexed\.ibval:.*\$HasType.*extraction_indexed\.ibounded'

ibounded_typeof_line=$(get_unique_line "indexed subset typing axiom" '$_typeof_extraction_indexed.ibounded:')
[ "$ibounded_typeof_line" = '$_typeof_extraction_indexed.ibounded: (($HasType @ extraction_indexed.ibounded) @ (($_arrow @ Corelib.Init.Datatypes.nat) @ Type))' ] || fail "indexed subset declaration has the wrong ordinary type axiom"
forbid_line "indexed subset constructor injectivity is skipped by default" '^\$_inj_extraction_indexed\.IBounded:'
forbid_line "indexed subset inversion is skipped by default" '^\$_inversion_extraction_indexed\.ibounded:'

# An under-applied constructor of an indexed subset is eta-expanded and then
# collapsed to its carrier.  The residual fields are typed through the argument
# the result index fords, so their payload must be instantiated at the
# occurrence's own index rather than at the index formal the classification
# substituted for that argument -- a formal that is free in this context.
ibpart_def_line=$(get_unique_line "under-applied indexed subset constructor" '$_def_extraction_indexed.ibpart:')
ibpart_lam=$(extract_unique_symbol "under-applied indexed subset constructor body" "$ibpart_def_line" '\$_lam_[0-9]+' '\$_lam_[0-9]+')
[ "$ibpart_def_line" = "\$_def_extraction_indexed.ibpart: (extraction_indexed.ibpart = $ibpart_lam)" ] ||
  fail "under-applied indexed subset constructor is not lifted to a single lambda"
ibpart_lam_line=$(get_unique_line "under-applied indexed subset constructor lambda" "$ibpart_lam:")
parse_binders "under-applied indexed subset constructor lambda" "$ibpart_lam_line" universal 1 ibpart_lam_binders
ibpart_carrier=${ibpart_lam_binders[0]}
[ "$ibpart_lam_line" = "$ibpart_lam: ![$ibpart_carrier : \$Any]: ((($ibpart_lam @ $ibpart_carrier) = $ibpart_carrier))" ] ||
  fail "under-applied indexed subset constructor does not collapse to its carrier"

ibpart_bound="(Corelib.Init.Datatypes.S @ (Corelib.Init.Datatypes.S @ (Corelib.Init.Datatypes.S @ (Corelib.Init.Datatypes.S @ (Corelib.Init.Datatypes.S @ Corelib.Init.Datatypes.O)))))"
ibpart_typeof_line=$(get_unique_line "under-applied indexed subset constructor typing axiom" '$_typeof_extraction_indexed.ibpart:')
parse_binders "under-applied indexed subset constructor typing axiom" "$ibpart_typeof_line" universal 1 ibpart_typeof_binders
ibpart_k=${ibpart_typeof_binders[0]}
require_text "under-applied indexed subset constructor types its exact residual binder" "$ibpart_typeof_line" "((\$HasType @ $ibpart_k) @ Corelib.Init.Datatypes.nat)"
require_text_count_exact "under-applied indexed subset constructor instantiates its payload at the occurrence index" "$ibpart_typeof_line" "((=> @ ((Corelib.Init.Peano.lt @ $ibpart_k) @ $ibpart_bound)) @ ((& @ ((\$HasType @ (extraction_indexed.ibpart @ $ibpart_k)) @ Corelib.Init.Datatypes.nat)) @ ((Corelib.Init.Peano.lt @ (extraction_indexed.ibpart @ $ibpart_k)) @ $ibpart_bound)))" 1
forbid_line "under-applied indexed subset constructor leaves no index formal free" '^\$_typeof_extraction_indexed\.ibpart:.*[$]Anonymous'

# An indexed subset whose fields depend on a parameter is not a uniform
# declaration-level subset.  It must stay nominal at occurrences while its
# structural axioms remain enabled, or injectivity would recover distinct
# indices from equality of the collapsed carriers.
require_line "parameter-dependent indexed subset keeps constructor injectivity" '^\$_inj_extraction_indexed\.IndexedPolySubset:.*extraction_indexed\.IndexedPolySubset'
require_line "parameter-dependent indexed subset keeps inversion" '^\$_inversion_extraction_indexed\.indexed_poly_subset:'
require_line "parameter-dependent indexed subset projector keeps its constructor" '^\$_def_extraction_indexed\.indexed_poly_value[$]IndexedPolySubset:.*extraction_indexed\.IndexedPolySubset'
indexed_poly_value_line=$(get_unique_line "parameter-dependent indexed subset projector" '$_def_extraction_indexed.indexed_poly_value$IndexedPolySubset:')
parse_binders "parameter-dependent indexed subset projector" "$indexed_poly_value_line" universal 3 indexed_poly_value_binders
indexed_poly_value_a=${indexed_poly_value_binders[0]}
indexed_poly_value_n=${indexed_poly_value_binders[1]}
indexed_poly_value_x=${indexed_poly_value_binders[2]}
require_text_count_exact "parameter-dependent indexed subset projector fords its constructor index" "$indexed_poly_value_line" "(((extraction_indexed.indexed_poly_value @ $indexed_poly_value_a) @ $indexed_poly_value_n) @ (((extraction_indexed.IndexedPolySubset @ $indexed_poly_value_a) @ $indexed_poly_value_n) @ $indexed_poly_value_x)) = $indexed_poly_value_x)" 1

fromok_line=$(get_unique_line "fromok definition" '$_def_extraction_indexed.fromok:')
parse_binders "fromok definition" "$fromok_line" universal 2 fromok_binders
fromok_n=${fromok_binders[0]}
fromok_m=${fromok_binders[1]}
require_text_count_exact "fromok singleton match is unconditional" "$fromok_line" "((extraction_indexed.fromok @ $fromok_n) @ $fromok_m) = (Corelib.Init.Datatypes.S @ $fromok_n)" 1
forbid_line "fromok definition has no index or proof premise" '^\$_def_extraction_indexed\.fromok:.*=> @'

fromok_typeof_line=$(get_unique_line "fromok typing axiom" '$_typeof_extraction_indexed.fromok:')
parse_binders "fromok typing axiom" "$fromok_typeof_line" universal 2 fromok_typeof_binders
fromok_n=${fromok_typeof_binders[0]}
fromok_m=${fromok_typeof_binders[1]}
require_text "fromok typing axiom types its exact parameter" "$fromok_typeof_line" "((\$HasType @ $fromok_n) @ Corelib.Init.Datatypes.nat)"
require_text "fromok typing axiom types its exact index" "$fromok_typeof_line" "((\$HasType @ $fromok_m) @ Corelib.Init.Datatypes.nat)"
require_text_count_exact "fromok typing axiom correlates its Prop premise" "$fromok_typeof_line" "((=> @ ((extraction_indexed.okp @ $fromok_n) @ $fromok_m)) @ ((\$HasType @ ((extraction_indexed.fromok @ $fromok_n) @ $fromok_m)) @ Corelib.Init.Datatypes.nat))" 1

cast_line=$(get_unique_line "cast definition" '$_def_extraction_indexed.cast:')
parse_binders "cast definition" "$cast_line" universal 3 cast_binders
cast_a=${cast_binders[0]}
cast_b=${cast_binders[1]}
cast_x=${cast_binders[2]}
require_text_count_exact "cast erases transport to its exact payload binder" "$cast_line" "(((extraction_indexed.cast @ $cast_a) @ $cast_b) @ $cast_x) = $cast_x)" 1
forbid_line "cast definition has no equality premise" '^\$_def_extraction_indexed\.cast:.*=> @'
cast_typeof_line=$(get_unique_line "cast typing axiom" '$_typeof_extraction_indexed.cast:')
cast_type_symbol=$(extract_unique_symbol "cast typing helper" "$cast_typeof_line" '\$_type_[0-9]+' '\$_type_[0-9]+')
cast_type_line=$(get_unique_line "cast typing helper definition" "$cast_type_symbol:")
parse_binders "cast typing helper" "$cast_type_line" universal 4 cast_type_binders
cast_function=${cast_type_binders[0]}
cast_source=${cast_type_binders[1]}
cast_target=${cast_type_binders[2]}
cast_payload=${cast_type_binders[3]}
require_text_count_exact "cast typing helper self-types its exact outer function binder" "$cast_type_line" "((\$HasType @ $cast_function) @ $cast_type_symbol)" 1
require_text "cast typing helper types its exact source binder" "$cast_type_line" "((\$HasType @ $cast_source) @ Type)"
require_text "cast typing helper types its exact target binder" "$cast_type_line" "((\$HasType @ $cast_target) @ Type)"
require_text_count_exact "cast typing helper correlates its exact source and target binders" "$cast_type_line" "((=> @ ($cast_source = $cast_target)) @ ![$cast_payload : \$Any]" 1
require_text_count_exact "cast typing helper correlates its function, payload, source, and target binders" "$cast_type_line" "((=> @ ((\$HasType @ $cast_payload) @ $cast_source)) @ ((\$HasType @ ((($cast_function @ $cast_source) @ $cast_target) @ $cast_payload)) @ $cast_target))" 1

vhead_line=$(get_unique_line "indexed vhead vcons equation" '$_def_extraction_indexed.vhead$vcons:')
parse_binders "indexed vhead vcons equation" "$vhead_line" universal 5 vhead_binders
vhead_a=${vhead_binders[0]}
vhead_outer_n=${vhead_binders[1]}
vhead_constructor_n=${vhead_binders[2]}
vhead_payload=${vhead_binders[3]}
vhead_tail=${vhead_binders[4]}
require_text_count_exact "indexed vhead correlates its complete vcons pattern and result" "$vhead_line" "(((extraction_indexed.vhead @ $vhead_a) @ $vhead_outer_n) @ ((((extraction_indexed.vcons @ $vhead_a) @ $vhead_constructor_n) @ $vhead_payload) @ $vhead_tail)) = $vhead_payload)" 1
forbid_line "indexed vhead prunes the impossible vnil equation" '^\$_def_extraction_indexed\.vhead[$]vnil:'
forbid_line "indexed vhead equation has no legacy index premise" '^\$_def_extraction_indexed\.vhead[$].*=> @'

dheight2_line=$(get_unique_line "dheight2 successor equation" '$_def_extraction_indexed.dheight2$dbox_succ:')
parse_binders "dheight2 successor equation" "$dheight2_line" universal 3 dheight2_binders
dheight2_outer=${dheight2_binders[0]}
dheight2_n=${dheight2_binders[1]}
dheight2_payload=${dheight2_binders[2]}
require_text_count_exact "dheight2 correlates its successor pattern and result" "$dheight2_line" "((extraction_indexed.dheight2 @ $dheight2_outer) @ (((extraction_deptypes.dbox_succ @ extraction_deptypes.dred) @ $dheight2_n) @ $dheight2_payload)) = (Corelib.Init.Datatypes.S @ $dheight2_n)" 1
forbid_line "dheight2 prunes the clashing zero equation" '^\$_def_extraction_indexed\.dheight2[$]dbox_zero:'
forbid_line "dheight2 successor equation is unconditional" '^\$_def_extraction_indexed\.dheight2[$]dbox_succ:.*=> @'

# Prop singleton matches collapse to their sole branch.  Their inversion axioms
# still pin the index equation used when the propositions occur as assumptions.
isT_line=$(get_unique_line "isT inversion" '$_inversion_extraction_indexed.isT:')
parse_binders "isT inversion" "$isT_line" universal 1 isT_binders
isT_index=${isT_binders[0]}
require_text_count_exact "isT inversion correlates its typing guard, premise, and index" "$isT_line" "((=> @ ((\$HasType @ $isT_index) @ Type)) @ ((=> @ (extraction_indexed.isT @ $isT_index)) @ ($isT_index = Corelib.Init.Datatypes.nat)))" 1

fromisT_line=$(get_unique_line "fromisT definition" '$_def_extraction_indexed.fromisT:')
parse_binders "fromisT definition" "$fromisT_line" universal 1 fromisT_binders
fromisT_t=${fromisT_binders[0]}
require_text_count_exact "fromisT returns zero for its exact source binder" "$fromisT_line" "(extraction_indexed.fromisT @ $fromisT_t) = Corelib.Init.Datatypes.O" 1
forbid_line "fromisT definition has no singleton premise" '^\$_def_extraction_indexed\.fromisT:.*=> @'

fromisT_typeof_line=$(get_unique_line "fromisT typing axiom" '$_typeof_extraction_indexed.fromisT:')
parse_binders "fromisT typing axiom" "$fromisT_typeof_line" universal 1 fromisT_typeof_binders
fromisT_t=${fromisT_typeof_binders[0]}
require_text_count_exact "fromisT typing correlates its type, premise, application, and result" "$fromisT_typeof_line" "((=> @ ((\$HasType @ $fromisT_t) @ Type)) @ ((=> @ (extraction_indexed.isT @ $fromisT_t)) @ ((\$HasType @ (extraction_indexed.fromisT @ $fromisT_t)) @ $fromisT_t)))" 1

istrue_line=$(get_unique_line "istrue inversion" '$_inversion_extraction_indexed.istrue:')
parse_binders "istrue inversion" "$istrue_line" universal 1 istrue_binders
istrue_index=${istrue_binders[0]}
istrue_enum="((| @ ((& @ ($istrue_index = Corelib.Init.Datatypes.true)) @ \$True)) @ ((& @ ($istrue_index = Corelib.Init.Datatypes.false)) @ \$True))"
require_text_count_exact "istrue inversion correlates its enum guard, premise, and index" "$istrue_line" "((=> @ $istrue_enum) @ ((=> @ (extraction_indexed.istrue @ $istrue_index)) @ ($istrue_index = Corelib.Init.Datatypes.true)))" 1

fromtrue_line=$(get_unique_line "fromtrue definition" '$_def_extraction_indexed.fromtrue:')
parse_binders "fromtrue definition" "$fromtrue_line" universal 1 fromtrue_binders
fromtrue_b=${fromtrue_binders[0]}
require_text_count_exact "fromtrue returns true for its exact source binder" "$fromtrue_line" "(extraction_indexed.fromtrue @ $fromtrue_b) = Corelib.Init.Datatypes.true" 1
forbid_line "fromtrue definition has no singleton premise" '^\$_def_extraction_indexed\.fromtrue:.*=> @'

fromtrue_typeof_line=$(get_unique_line "fromtrue typing axiom" '$_typeof_extraction_indexed.fromtrue:')
parse_binders "fromtrue typing axiom" "$fromtrue_typeof_line" universal 1 fromtrue_typeof_binders
fromtrue_b=${fromtrue_typeof_binders[0]}
fromtrue_guard="((| @ ((& @ ($fromtrue_b = Corelib.Init.Datatypes.true)) @ \$True)) @ ((& @ ($fromtrue_b = Corelib.Init.Datatypes.false)) @ \$True))"
fromtrue_result="((| @ ((& @ ((extraction_indexed.fromtrue @ $fromtrue_b) = Corelib.Init.Datatypes.true)) @ \$True)) @ ((& @ ((extraction_indexed.fromtrue @ $fromtrue_b) = Corelib.Init.Datatypes.false)) @ \$True))"
require_text_count_exact "fromtrue typing correlates its enum guard, premise, and result" "$fromtrue_typeof_line" "((=> @ $fromtrue_guard) @ ((=> @ (extraction_indexed.istrue @ $fromtrue_b)) @ $fromtrue_result))" 1

jmeq_line=$(get_unique_line "JMeq singleton definition" '$_def_extraction_indexed.jmeq_match:')
parse_binders "JMeq singleton definition" "$jmeq_line" universal 4 jmeq_binders
jmeq_a=${jmeq_binders[0]}
jmeq_b=${jmeq_binders[1]}
jmeq_x=${jmeq_binders[2]}
jmeq_y=${jmeq_binders[3]}
require_text_count_exact "JMeq singleton match returns its exact source payload" "$jmeq_line" "((((extraction_indexed.jmeq_match @ $jmeq_a) @ $jmeq_b) @ $jmeq_x) @ $jmeq_y) = $jmeq_x)" 1
forbid_line "JMeq match definition has no proof premise" '^\$_def_extraction_indexed\.jmeq_match:.*=> @'

jmeq_typeof_line=$(get_unique_line "JMeq match typing axiom" '$_typeof_extraction_indexed.jmeq_match:')
parse_binders "JMeq match typing axiom" "$jmeq_typeof_line" universal 4 jmeq_typeof_binders
jmeq_a=${jmeq_typeof_binders[0]}
jmeq_b=${jmeq_typeof_binders[1]}
jmeq_x=${jmeq_typeof_binders[2]}
jmeq_y=${jmeq_typeof_binders[3]}
require_text "JMeq typing types its exact source type" "$jmeq_typeof_line" "((\$HasType @ $jmeq_a) @ Type)"
require_text "JMeq typing types its exact target type" "$jmeq_typeof_line" "((\$HasType @ $jmeq_b) @ Type)"
require_text "JMeq typing correlates its source payload and type" "$jmeq_typeof_line" "((\$HasType @ $jmeq_x) @ $jmeq_a)"
require_text "JMeq typing correlates its target payload and type" "$jmeq_typeof_line" "((\$HasType @ $jmeq_y) @ $jmeq_b)"
require_text_count_exact "JMeq typing correlates its premise and result application" "$jmeq_typeof_line" "((=> @ ((((Stdlib.Logic.JMeq.JMeq @ $jmeq_a) @ $jmeq_x) @ $jmeq_b) @ $jmeq_y)) @ ((\$HasType @ ((((extraction_indexed.jmeq_match @ $jmeq_a) @ $jmeq_b) @ $jmeq_x) @ $jmeq_y)) @ $jmeq_a))" 1

# Corpus-wide shallowness gates for the covered constants.  WF-gated idiv
# definitions and explicit stdlib structural snapshots are checked separately.
forbid_line "covered extraction definitions do not mention erased packages" '^\$_def_extraction_deptypes\.(h|safe_pred|pval|beq|between|tag|vhead)[:$].*Corelib\.Init\.Specif\.(sig|sig2|exist|exist2|proj1_sig)'
forbid_line "covered extraction type axioms do not keep classified HasType leaves" '^\$_typeof_extraction_deptypes\.(h|safe_pred|pval|beq|between|tag):.*Corelib\.Init\.(Specif\.(sig|sig2|sumbool)|Datatypes\.prod)'

# WF recursion: Program Fixpoint/Fix_sub idiv and the bare Fix/Fix_F fixtures
# expose only premised unfolding equations.  The erased b <> 0 premise is
# mandatory on the top-level link and on recursive/zero branches.
require_line "idiv link has the b nonzero premise" '^\$_def_extraction_deptypes\.idiv[$]link:.*=> @ \(~ @ \([^)]*_b = Corelib\.Init\.Datatypes\.O\)\).*le_lt_dec'
require_line "idiv recursive branch has the b nonzero premise" '^\$_case_Corelib\.Init\.Specif\.sumbool[$][0-9]+[$]left:.*=> @ \(~ @ \(v_CANONICAL_1 = Corelib\.Init\.Datatypes\.O\)\).*extraction_deptypes\.idiv_func.*Corelib\.Init\.Nat\.sub'
require_line "idiv zero branch keeps the b nonzero premise" '^\$_case_Corelib\.Init\.Specif\.sumbool[$][0-9]+[$]right:.*=> @ \(~ @ \(v_CANONICAL_1 = Corelib\.Init\.Datatypes\.O\)\).*Corelib\.Init\.Datatypes\.O'
require_line "idiv2 link has the b nonzero premise" '^\$_def_extraction_deptypes\.idiv2[$]link:.*=> @ \(~ @ \(0_b = Corelib\.Init\.Datatypes\.O\)\).*le_lt_dec'
require_line "idiv3 link has the b nonzero premise" '^\$_def_extraction_deptypes\.idiv3[$]link:.*=> @ \(~ @ \(0_b = Corelib\.Init\.Datatypes\.O\)\).*le_lt_dec'
require_line "idiv2 recursive branch has the b nonzero premise" '^\$_case_Corelib\.Init\.Specif\.sumbool[$][0-9]+[$]left:.*=> @ \(~ @ \(v_CANONICAL_0 = Corelib\.Init\.Datatypes\.O\)\).*extraction_deptypes\.idiv2 @ v_CANONICAL_0.*Corelib\.Init\.Nat\.sub'
require_line "idiv3 recursive branch has the b nonzero premise" '^\$_case_Corelib\.Init\.Specif\.sumbool[$][0-9]+[$]left:.*=> @ \(~ @ \(v_CANONICAL_0 = Corelib\.Init\.Datatypes\.O\)\).*extraction_deptypes\.idiv3 @ v_CANONICAL_0.*Corelib\.Init\.Nat\.sub'
require_line "idiv2 zero branch keeps the b nonzero premise" '^\$_case_Corelib\.Init\.Specif\.sumbool[$][0-9]+[$]right:.*=> @ \(~ @ \(v_CANONICAL_0 = Corelib\.Init\.Datatypes\.O\)\).*Corelib\.Init\.Datatypes\.O'
require_line "idiv3 zero branch keeps the b nonzero premise" '^\$_case_Corelib\.Init\.Specif\.sumbool[$][0-9]+[$]right:.*=> @ \(~ @ \(v_CANONICAL_0 = Corelib\.Init\.Datatypes\.O\)\).*Corelib\.Init\.Datatypes\.O'
for wf_name in idiv idiv2 idiv3; do
  wf_pattern='^\$_def_extraction_deptypes\.'"$wf_name"'[$][^:]*:.*le_lt_dec'
  if grep -E "$wf_pattern" "$out" | grep -Ev '=> @ \(~ @ \([^)]* = Corelib\.Init\.Datatypes\.O\)\)' >/dev/null; then
    fail "$wf_name must not expose an unpremised le_lt_dec definition"
  fi
done
require_count_exact "Acc_rect emits one definition with an Acc premise" '^\$_def_Corelib\.Init\.Wf\.Acc_rect:.*=> @ \(\(\(Corelib\.Init\.Wf\.Acc @ 0_A\) @ 1_R\) @ 5_x\)' 1
acc_rect_line=$(get_unique_line "Acc_rect definition" '$_def_Corelib.Init.Wf.Acc_rect:')
require_text_count_exact "Acc_rect definition carries exactly one Acc premise" "$acc_rect_line" '=> @ (((Corelib.Init.Wf.Acc' 1

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
eq_rect_line=$(get_unique_line "eq_rect generic definition" '$_def_Corelib.Init.Logic.eq_rect:')
parse_binders "eq_rect generic definition" "$eq_rect_line" universal 5 eq_rect_binders
eq_rect_a=${eq_rect_binders[0]}
eq_rect_x=${eq_rect_binders[1]}
eq_rect_p=${eq_rect_binders[2]}
eq_rect_f=${eq_rect_binders[3]}
eq_rect_y=${eq_rect_binders[4]}
require_text_count_exact "eq_rect generic singleton equation" "$eq_rect_line" "Corelib.Init.Logic.eq_rect @ $eq_rect_a) @ $eq_rect_x) @ $eq_rect_p) @ $eq_rect_f) @ $eq_rect_y) = $eq_rect_f" 1
if [[ "$eq_rect_line" == *'=> @'* ]]; then
  fail "eq_rect generic singleton equation must be unconditional"
fi
require_line "eq_ind has a translated formula" '^Corelib\.Init\.Logic\.eq_ind:'
require_line "eq_ind_r has a translated formula" '^Corelib\.Init\.Logic\.eq_ind_r:'
forbid_line "eq_ind has no synthetic definition" '^\$_def_Corelib\.Init\.Logic\.eq_ind:'
forbid_line "eq_ind_r has no synthetic definition" '^\$_def_Corelib\.Init\.Logic\.eq_ind_r:'
require_line "proj1 has a translated formula" '^Corelib\.Init\.Logic\.proj1:'
require_line "Acc_rect has a type axiom" '^\$_typeof_Corelib\.Init\.Wf\.Acc_rect:'
require_count_at_least "Nat.eq_dec has a definition axiom" '^\$_def_Stdlib\.Arith\.PeanoNat\.Nat\.eq_dec:' 1

# Applied indexed reflect guards expand shallowly.  Generated proposition and
# fixpoint IDs are deliberately parsed from the eqb_spec typing line: each tag
# is tied to the definition of its exact proposition helper, and the exact
# boolean helper in both residual equations is tied to Nat.eqb's truth table.
nat_eqb_spec_line=$(get_unique_line "Nat.eqb_spec typing axiom" '$_typeof_Stdlib.Arith.PeanoNat.Nat.eqb_spec:')
parse_binders "Nat.eqb_spec typing axiom" "$nat_eqb_spec_line" universal 2 nat_eqb_spec_binders
nat_eqb_x=${nat_eqb_spec_binders[0]}
nat_eqb_y=${nat_eqb_spec_binders[1]}
nat_eqb_true_prop=$(extract_unique_symbol "Nat.eqb_spec ReflectT proposition" "$nat_eqb_spec_line" 'ReflectT @ \(\(\$_prop_[0-9]+' '\$_prop_[0-9]+')
nat_eqb_false_prop=$(extract_unique_symbol "Nat.eqb_spec ReflectF proposition" "$nat_eqb_spec_line" 'ReflectF @ \(\(\$_prop_[0-9]+' '\$_prop_[0-9]+')
nat_eqb_bool=$(extract_unique_symbol "Nat.eqb_spec boolean helper" "$nat_eqb_spec_line" '\$_fix_[A-Za-z0-9_$.-]+' '\$_fix_[A-Za-z0-9_$.-]+')
assert_binary_prop_is_equality "Nat.eqb_spec ReflectT proposition" "$nat_eqb_true_prop"
assert_binary_prop_is_equality "Nat.eqb_spec ReflectF proposition" "$nat_eqb_false_prop"
require_text "Nat.eqb_spec types its exact x binder" "$nat_eqb_spec_line" "((\$HasType @ $nat_eqb_x) @ Corelib.Init.Datatypes.nat)"
require_text "Nat.eqb_spec types its exact y binder" "$nat_eqb_spec_line" "((\$HasType @ $nat_eqb_y) @ Corelib.Init.Datatypes.nat)"
require_text_count_exact "Nat.eqb_spec uses one boolean helper in both residual equations" "$nat_eqb_spec_line" "$nat_eqb_bool" 2

nat_eqb_true_branch="((& @ (((Stdlib.Arith.PeanoNat.Nat.eqb_spec @ $nat_eqb_x) @ $nat_eqb_y) = (Corelib.Init.Datatypes.ReflectT @ (($nat_eqb_true_prop @ $nat_eqb_x) @ $nat_eqb_y)))) @ ((& @ ($nat_eqb_x = $nat_eqb_y)) @ ((($nat_eqb_bool @ $nat_eqb_x) @ $nat_eqb_y) = Corelib.Init.Datatypes.true)))"
nat_eqb_false_branch="((& @ (((Stdlib.Arith.PeanoNat.Nat.eqb_spec @ $nat_eqb_x) @ $nat_eqb_y) = (Corelib.Init.Datatypes.ReflectF @ (($nat_eqb_false_prop @ $nat_eqb_x) @ $nat_eqb_y)))) @ ((& @ (~ @ ($nat_eqb_x = $nat_eqb_y))) @ ((($nat_eqb_bool @ $nat_eqb_x) @ $nat_eqb_y) = Corelib.Init.Datatypes.false)))"
require_text_count_exact "Nat.eqb_spec true branch correlates its outer binders, tag proposition, payload, and boolean helper" "$nat_eqb_spec_line" "$nat_eqb_true_branch" 1
require_text_count_exact "Nat.eqb_spec false branch correlates its outer binders, tag proposition, payload, and boolean helper" "$nat_eqb_spec_line" "$nat_eqb_false_branch" 1

assert_nat_eqb_truth_table "$nat_eqb_bool"
forbid_line "Nat.eqb_spec has no nominal reflect guard" '^\$_typeof_Stdlib\.Arith\.PeanoNat\.Nat\.eqb_spec:.*\$HasType.*Corelib\.Init\.Datatypes\.reflect'

require_line "sumbool has an inversion axiom" '^\$_inversion_Corelib\.Init\.Specif\.sumbool:'
introT_line=$(get_unique_line "introT formula" 'Corelib.ssr.ssrbool.introT:')
parse_binders "introT formula" "$introT_line" universal 3 introT_binders
introT_p=${introT_binders[0]}
introT_b=${introT_binders[1]}
introT_value=${introT_binders[2]}
require_text "introT types its exact proposition binder" "$introT_line" "((\$HasType @ $introT_p) @ Prop)"
introT_bool_guard="((| @ ((& @ ($introT_b = Corelib.Init.Datatypes.true)) @ \$True)) @ ((& @ ($introT_b = Corelib.Init.Datatypes.false)) @ \$True))"
require_text_count_exact "introT correlates its exact boolean binder in the enum guard" "$introT_line" "$introT_bool_guard" 1
require_text_count_exact "introT true branch correlates its exact binders, payload, and index" "$introT_line" "((& @ ($introT_value = (Corelib.Init.Datatypes.ReflectT @ $introT_p))) @ ((& @ $introT_p) @ ($introT_b = Corelib.Init.Datatypes.true)))" 1
require_text_count_exact "introT false branch correlates its exact binders, payload, and index" "$introT_line" "((& @ ($introT_value = (Corelib.Init.Datatypes.ReflectF @ $introT_p))) @ ((& @ (~ @ $introT_p)) @ ($introT_b = Corelib.Init.Datatypes.false)))" 1
require_text_count_exact "introT correlates its exact proposition and boolean binders in the result" "$introT_line" "((=> @ $introT_p) @ (Corelib.Init.Datatypes.is_true @ $introT_b))" 1
forbid_line "introT has no nominal reflect guard" '^Corelib\.ssr\.ssrbool\.introT:.*\$HasType.*Corelib\.Init\.Datatypes\.reflect'
require_line "parameter-dependent sig keeps its inversion axiom" '^\$_inversion_Corelib\.Init\.Specif\.sig:'
require_line "parameter-dependent sig keeps constructor injectivity" '^\$_inj_Corelib\.Init\.Specif\.exist:'
require_line "prod has an inversion axiom" '^\$_inversion_Corelib\.Init\.Datatypes\.prod:'
require_count_at_least "Vector.hd has a definition axiom" '^\$_def_Stdlib\.Vectors\.VectorDef\.hd:' 1
require_count_at_least "Streams.hd has a split definition axiom" '^\$_def_Stdlib\.Streams\.Streams\.hd[$]' 1
require_line "typeclass method projection is translated" '^Corelib\.Classes\.RelationClasses\.Equivalence_Reflexive:'

printf 'extraction_transl assertions passed\n'
