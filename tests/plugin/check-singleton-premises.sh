#!/usr/bin/env bash
set -euo pipefail

out=${1:-singleton_premises.out}
assert_context="singleton-premise"
# By default assert that every singleton elimination below is collapsed, which
# is what the test suite checks.  SINGLETON_PREMISES_EXPECT=absent inverts the
# roster instead, asserting that none of those equations is emitted at all --
# what a plugin built with opt_dependent_types=false must produce, and what the
# install validation in eval/rebuild-config.sh runs.  Both halves of that
# iff therefore read the same roster.
expect=${SINGLETON_PREMISES_EXPECT:-present}
case "$expect" in
  present|absent) ;;
  *)
    echo "Unknown SINGLETON_PREMISES_EXPECT value: $expect" >&2
    exit 2
    ;;
esac
# shellcheck source=tests/plugin/transl-assert-lib.sh
. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)/transl-assert-lib.sh"

cast_prefix='$_def_singleton_premises.singleton_cast:'
eq_rect_prefix='$_def_Corelib.Init.Logic.eq_rect:'
singleton_value_prefix='$_def_singleton_premises.singleton_value:'
prop_index_prefix='$_def_singleton_premises.prop_index_value:'
jmeq_prefix='$_def_singleton_premises.singleton_jmeq:'
singleton_definitions=(
  "$cast_prefix"
  "$eq_rect_prefix"
  "$singleton_value_prefix"
  "$prop_index_prefix"
  "$jmeq_prefix"
)

if [ "$expect" = absent ]; then
  # Anchor the absence on a shape the option does not decide, so that an output
  # the probe never reached cannot satisfy it vacuously.
  require_line "the probe translated its own definitions" \
    '$_typeof_singleton_premises.'
  for prefix in "${singleton_definitions[@]}"; do
    forbid_line "singleton elimination is left uncollapsed" "$prefix"
  done
  echo "singleton-premise absence assertions passed"
  exit 0
fi

cast_line=$(get_unique_line "cast definition" "$cast_prefix")
parse_binders "cast definition" "$cast_line" universal 3 cast_binders
cast_a=${cast_binders[0]}
cast_b=${cast_binders[1]}
cast_x=${cast_binders[2]}
cast_equation="(((singleton_premises.singleton_cast @ $cast_a) @ $cast_b) @ $cast_x) = $cast_x"
require_text "cast equation" "$cast_line" "$cast_equation"

eq_rect_line=$(get_unique_line "eq_rect definition" "$eq_rect_prefix")
parse_binders "eq_rect definition" "$eq_rect_line" universal 5 eq_rect_binders
eq_a=${eq_rect_binders[0]}
eq_x=${eq_rect_binders[1]}
eq_p=${eq_rect_binders[2]}
eq_f=${eq_rect_binders[3]}
eq_y=${eq_rect_binders[4]}
eq_rect_equation="Corelib.Init.Logic.eq_rect @ $eq_a) @ $eq_x) @ $eq_p) @ $eq_f) @ $eq_y) = $eq_f"
require_text "eq_rect equation" "$eq_rect_line" "$eq_rect_equation"

singleton_value_line=$(get_unique_line "singleton_value definition" "$singleton_value_prefix")
parse_binders "singleton_value definition" "$singleton_value_line" universal 1 singleton_value_binders
singleton_value_t=${singleton_value_binders[0]}
singleton_value_equation="(singleton_premises.singleton_value @ $singleton_value_t) = Corelib.Init.Datatypes.O"
require_text "singleton_value equation" "$singleton_value_line" "$singleton_value_equation"

prop_index_line=$(get_unique_line "Prop-index definition" "$prop_index_prefix")
parse_binders "Prop-index definition" "$prop_index_line" universal 1 prop_index_binders
prop_index_p=${prop_index_binders[0]}
prop_index_equation="(singleton_premises.prop_index_value @ $prop_index_p) = (Corelib.Init.Datatypes.S @ (Corelib.Init.Datatypes.S @ (Corelib.Init.Datatypes.S @ Corelib.Init.Datatypes.O)))"
require_text "Prop-index equation" "$prop_index_line" "$prop_index_equation"

jmeq_line=$(get_unique_line "JMeq definition" "$jmeq_prefix")
parse_binders "JMeq definition" "$jmeq_line" universal 4 jmeq_binders
jmeq_a=${jmeq_binders[0]}
jmeq_b=${jmeq_binders[1]}
jmeq_x=${jmeq_binders[2]}
jmeq_y=${jmeq_binders[3]}
jmeq_equation="((((singleton_premises.singleton_jmeq @ $jmeq_a) @ $jmeq_b) @ $jmeq_x) @ $jmeq_y) = $jmeq_x"
require_text "JMeq equation" "$jmeq_line" "$jmeq_equation"

forbid_text "cast is unconditional" "$cast_line" '=> @'
forbid_text "eq_rect is unconditional" "$eq_rect_line" '=> @'
forbid_text "singleton_value is unconditional" "$singleton_value_line" '=> @'
forbid_text "Prop-index singleton is unconditional" "$prop_index_line" '=> @'
forbid_text "JMeq is unconditional" "$jmeq_line" '=> @'

acc_line=$(get_unique_line "Acc_rect definition" '$_def_Corelib.Init.Wf.Acc_rect:')
parse_binders "Acc_rect definition" "$acc_line" universal 5 acc_binders
acc_a=${acc_binders[0]}
acc_r=${acc_binders[1]}
acc_x=${acc_binders[4]}
require_text "Acc_rect keeps its independent well-foundedness premise" "$acc_line" \
  "((=> @ (((Corelib.Init.Wf.Acc @ $acc_a) @ $acc_r) @ $acc_x)) @"
require_text_count_exact "Acc_rect has no extra singleton premise" "$acc_line" '=> @' 1

echo "singleton-premise assertions passed"
