#!/usr/bin/env bash
set -euo pipefail

mode=${1:?usage: check-singleton-premises.sh MODE [OUTPUT]}
out=${2:-singleton_premises.out}
assert_context="singleton-premise ($mode)"
# shellcheck source=tests/plugin/transl-assert-lib.sh
. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)/transl-assert-lib.sh"

case "$mode" in
  guards-off|guards-indexed|guards-legacy) ;;
  *) echo "unknown singleton-premise mode: $mode" >&2; exit 2 ;;
esac

cast_line=$(get_unique_line "cast definition" '$_def_singleton_premises.singleton_cast:')
parse_binders "cast definition" "$cast_line" universal 3 cast_binders
cast_a=${cast_binders[0]}
cast_b=${cast_binders[1]}
cast_x=${cast_binders[2]}
cast_equation="(((singleton_premises.singleton_cast @ $cast_a) @ $cast_b) @ $cast_x) = $cast_x"
require_text "cast equation" "$cast_line" "$cast_equation"

eq_rect_line=$(get_unique_line "eq_rect definition" '$_def_Corelib.Init.Logic.eq_rect:')
parse_binders "eq_rect definition" "$eq_rect_line" universal 5 eq_rect_binders
eq_a=${eq_rect_binders[0]}
eq_x=${eq_rect_binders[1]}
eq_p=${eq_rect_binders[2]}
eq_f=${eq_rect_binders[3]}
eq_y=${eq_rect_binders[4]}
eq_rect_equation="Corelib.Init.Logic.eq_rect @ $eq_a) @ $eq_x) @ $eq_p) @ $eq_f) @ $eq_y) = $eq_f"
require_text "eq_rect equation" "$eq_rect_line" "$eq_rect_equation"

singleton_value_line=$(get_unique_line "singleton_value definition" '$_def_singleton_premises.singleton_value:')
parse_binders "singleton_value definition" "$singleton_value_line" universal 1 singleton_value_binders
singleton_value_t=${singleton_value_binders[0]}
singleton_value_equation="(singleton_premises.singleton_value @ $singleton_value_t) = Corelib.Init.Datatypes.O"
require_text "singleton_value equation" "$singleton_value_line" "$singleton_value_equation"

prop_index_line=$(get_unique_line "Prop-index definition" '$_def_singleton_premises.prop_index_value:')
parse_binders "Prop-index definition" "$prop_index_line" universal 1 prop_index_binders
prop_index_p=${prop_index_binders[0]}
prop_index_equation="(singleton_premises.prop_index_value @ $prop_index_p) = (Corelib.Init.Datatypes.S @ (Corelib.Init.Datatypes.S @ (Corelib.Init.Datatypes.S @ Corelib.Init.Datatypes.O)))"
require_text "Prop-index equation" "$prop_index_line" "$prop_index_equation"

jmeq_line=$(get_unique_line "JMeq definition" '$_def_singleton_premises.singleton_jmeq:')
parse_binders "JMeq definition" "$jmeq_line" universal 4 jmeq_binders
jmeq_a=${jmeq_binders[0]}
jmeq_b=${jmeq_binders[1]}
jmeq_x=${jmeq_binders[2]}
jmeq_y=${jmeq_binders[3]}
jmeq_equation="((((singleton_premises.singleton_jmeq @ $jmeq_a) @ $jmeq_b) @ $jmeq_x) @ $jmeq_y) = $jmeq_x"
require_text "JMeq equation" "$jmeq_line" "$jmeq_equation"

case "$mode" in
  guards-off)
    forbid_text "cast is unconditional" "$cast_line" '=> @'
    forbid_text "eq_rect is unconditional" "$eq_rect_line" '=> @'
    forbid_text "singleton_value is unconditional" "$singleton_value_line" '=> @'
    forbid_text "Prop-index singleton is unconditional" "$prop_index_line" '=> @'
    forbid_text "JMeq is unconditional" "$jmeq_line" '=> @'
    ;;
  guards-indexed)
    require_text "cast has its residual equation" "$cast_line" "((=> @ ($cast_b = $cast_a)) @"
    require_text_count_exact "cast has one premise" "$cast_line" '=> @' 1
    require_text "eq_rect has its residual equation" "$eq_rect_line" "((=> @ ($eq_y = $eq_x)) @"
    require_text_count_exact "eq_rect has one premise" "$eq_rect_line" '=> @' 1
    require_text "singleton_value has its residual equation" "$singleton_value_line" "((=> @ ($singleton_value_t = Corelib.Init.Datatypes.nat)) @"
    require_text_count_exact "singleton_value has one premise" "$singleton_value_line" '=> @' 1
    forbid_text "Prop-index singleton has no residual equation" "$prop_index_line" '=> @'
    require_text "JMeq has both residual equations" "$jmeq_line" \
      "((=> @ ((& @ ($jmeq_b = $jmeq_a)) @ ($jmeq_y = $jmeq_x))) @"
    require_text_count_exact "JMeq has one conjunctive premise" "$jmeq_line" '=> @' 1
    ;;
  guards-legacy)
    require_text "cast has its source proposition" "$cast_line" "((=> @ ($cast_a = $cast_b)) @"
    require_text_count_exact "cast has one premise" "$cast_line" '=> @' 1
    require_text "eq_rect has its source proposition" "$eq_rect_line" "((=> @ ($eq_x = $eq_y)) @"
    require_text_count_exact "eq_rect has one premise" "$eq_rect_line" '=> @' 1
    require_text "singleton_value has its source proposition" "$singleton_value_line" "((=> @ (singleton_premises.indexed_singleton @ $singleton_value_t)) @"
    forbid_text "singleton_value has no residual equation" "$singleton_value_line" "$singleton_value_t = Corelib.Init.Datatypes.nat"
    require_text_count_exact "singleton_value has one premise" "$singleton_value_line" '=> @' 1
    require_text "Prop-index singleton has its source proposition" "$prop_index_line" \
      "((=> @ (singleton_premises.prop_index_singleton @ $prop_index_p)) @"
    require_text_count_exact "Prop-index singleton has one premise" "$prop_index_line" '=> @' 1
    require_text "JMeq has its source proposition" "$jmeq_line" \
      "((=> @ ((((Stdlib.Logic.JMeq.JMeq @ $jmeq_a) @ $jmeq_x) @ $jmeq_b) @ $jmeq_y)) @"
    forbid_text "JMeq has no residual type equation" "$jmeq_line" "$jmeq_b = $jmeq_a"
    forbid_text "JMeq has no residual value equation" "$jmeq_line" "$jmeq_y = $jmeq_x"
    require_text_count_exact "JMeq has one premise" "$jmeq_line" '=> @' 1
    ;;
esac

acc_line=$(get_unique_line "Acc_rect definition" '$_def_Corelib.Init.Wf.Acc_rect:')
parse_binders "Acc_rect definition" "$acc_line" universal 5 acc_binders
acc_a=${acc_binders[0]}
acc_r=${acc_binders[1]}
acc_x=${acc_binders[4]}
require_text "Acc_rect keeps its independent well-foundedness premise" "$acc_line" \
  "((=> @ (((Corelib.Init.Wf.Acc @ $acc_a) @ $acc_r) @ $acc_x)) @"
require_text_count_exact "Acc_rect has no extra singleton premise" "$acc_line" '=> @' 1

echo "singleton-premise assertions passed ($mode)"
