#!/usr/bin/env bash
# Declarative execution engine for screening grids. Source this file after
# declaring the GRID_* spec and grid_label_install/grid_label_preamble.
# force is consumed indirectly by checkpoint_done from the sourced helper.
# shellcheck disable=SC2034

_grid_engine_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
# shellcheck source=eval/grid-checkpoint-lib.sh
# shellcheck disable=SC1091
source "$_grid_engine_dir/grid-checkpoint-lib.sh"
# shellcheck source=eval/install-prefix-lib.sh
# shellcheck disable=SC1091
source "$_grid_engine_dir/install-prefix-lib.sh"

_grid_validate_indexed_array() {
  local name="$1" require_nonempty="$2" declaration index expected=0 value
  declaration=$(declare -p "$name" 2>/dev/null) || {
    echo "Grid spec must define the $name indexed array" >&2
    return 1
  }
  [[ "$declaration" == "declare -a "* ]] || {
    echo "Grid spec $name must be an indexed array" >&2
    return 1
  }
  local -n array_ref="$name"
  if [ "$require_nonempty" = true ] && [ "${#array_ref[@]}" -eq 0 ]; then
    echo "Grid spec $name must not be empty" >&2
    return 1
  fi
  for index in "${!array_ref[@]}"; do
    if [ "$index" -ne "$expected" ]; then
      echo "Grid spec $name must use contiguous indices starting at zero" >&2
      return 1
    fi
    value=${array_ref[$index]}
    if [ -z "$value" ]; then
      echo "Grid spec $name contains an empty value" >&2
      return 1
    fi
    expected=$((expected + 1))
  done
}

_grid_validate_unique_array() {
  local name="$1" value
  local -n array_ref="$name"
  local -A seen=()
  for value in "${array_ref[@]}"; do
    if [ -n "${seen[$value]+set}" ]; then
      echo "Grid spec $name contains duplicate value: $value" >&2
      return 1
    fi
    seen[$value]=true
  done
}

_grid_validate_safe_components() {
  local name="$1" value
  local -n array_ref="$name"
  for value in "${array_ref[@]}"; do
    if ! eval_safe_component "$value"; then
      echo "Grid spec $name value must be a safe single path component: $value" >&2
      return 1
    fi
  done
}

_grid_require_spec() {
  local name prover legacy_hash consistency_premise
  for name in GRID_NAME GRID_RESULTS_ROOT GRID_ARTIFACTS_DIR GRID_SUMMARIZER \
      GRID_COMPLETION_MESSAGE; do
    if [ -z "${!name:-}" ]; then
      echo "Grid spec must define $name" >&2
      return 1
    fi
  done
  # shellcheck disable=SC2153
  if ! eval_safe_component "$GRID_NAME"; then
    echo "Grid spec GRID_NAME must be a safe single path component: $GRID_NAME" >&2
    return 1
  fi
  [ -f "$GRID_SUMMARIZER" ] || {
    echo "Grid summarizer not found: $GRID_SUMMARIZER" >&2
    return 1
  }
  for name in GRID_LABELS GRID_PREMISES GRID_PROVERS GRID_CORPORA; do
    _grid_validate_indexed_array "$name" true || return 1
    _grid_validate_unique_array "$name" || return 1
    _grid_validate_safe_components "$name" || return 1
  done
  if declare -p GRID_LEGACY_SCRIPT_SHA256 >/dev/null 2>&1; then
    _grid_validate_indexed_array GRID_LEGACY_SCRIPT_SHA256 false || return 1
    _grid_validate_unique_array GRID_LEGACY_SCRIPT_SHA256 || return 1
    for legacy_hash in "${GRID_LEGACY_SCRIPT_SHA256[@]}"; do
      if [[ ! "$legacy_hash" =~ ^[0-9a-f]{64}$ ]]; then
        echo "Grid spec GRID_LEGACY_SCRIPT_SHA256 contains an invalid SHA-256: $legacy_hash" >&2
        return 1
      fi
    done
  fi
  for prover in "${GRID_PROVERS[@]}"; do
    case "$prover" in
      eprover|vampire) ;;
      *) echo "Grid spec names unsupported prover: $prover" >&2; return 1 ;;
    esac
  done
  consistency_premise=${GRID_CONSISTENCY_PREMISE-${GRID_PREMISES[0]}}
  if ! array_contains "$consistency_premise" "${GRID_PREMISES[@]}"; then
    echo "GRID_CONSISTENCY_PREMISE is not a member of GRID_PREMISES: $consistency_premise" >&2
    return 1
  fi
  if ! declare -F grid_label_install >/dev/null; then
    echo "Grid spec must define grid_label_install" >&2
    return 1
  fi
  if ! declare -F grid_label_preamble >/dev/null; then
    echo "Grid spec must define grid_label_preamble" >&2
    return 1
  fi
  if ! declare -F grid_usage >/dev/null; then
    echo "Grid spec must define grid_usage" >&2
    return 1
  fi
}

_grid_paths_overlap() {
  local first="$1" second="$2"
  [ "$first" = "$second" ] || [[ "$first" == "$second/"* ]] || [[ "$second" == "$first/"* ]]
}

_grid_validate_output_roots() {
  local confirmation_results confirmation_artifacts protected candidate
  confirmation_results=$(realpath -m -- "$eval_dir/results/confirmation")
  confirmation_artifacts=$(realpath -m -- "$eval_dir/artifacts/extraction-confirmation")
  for candidate in "$results_root" "$artifacts_dir"; do
    for protected in "$confirmation_results" "$confirmation_artifacts"; do
      if _grid_paths_overlap "$candidate" "$protected"; then
        echo "Grid output path overlaps protected confirmation data: $candidate" >&2
        return 1
      fi
    done
  done
  if _grid_paths_overlap "$results_root" "$artifacts_dir"; then
    echo "Grid results and artifacts paths must not overlap" >&2
    return 1
  fi
}

_GRID_TEMP_FILES=()
GRID_ATOMIC_TEMP=

_grid_cleanup_temp_files() {
  local temporary
  for temporary in "${_GRID_TEMP_FILES[@]}"; do
    [ -n "$temporary" ] && rm -f -- "$temporary"
  done
  _GRID_TEMP_FILES=()
}

_grid_signal_exit() {
  local status="$1"
  _grid_cleanup_temp_files
  exit "$status"
}

_grid_install_cleanup_traps() {
  trap _grid_cleanup_temp_files EXIT
  trap '_grid_signal_exit 130' INT
  trap '_grid_signal_exit 143' TERM
}

_grid_forget_temp() {
  local completed="$1" temporary
  local remaining=()
  for temporary in "${_GRID_TEMP_FILES[@]}"; do
    [ "$temporary" = "$completed" ] || remaining+=("$temporary")
  done
  _GRID_TEMP_FILES=("${remaining[@]}")
}

_grid_new_atomic_temp() {
  local target="$1" directory base
  directory=$(dirname "$target")
  base=$(basename "$target")
  # A previous process with a reused PID may have left one of our old fixed
  # names or a newer mktemp name. Delete regular files only; never follow a
  # hostile stale symlink.
  find "$directory" -maxdepth 1 -type f \
    \( -name "$base.tmp.$$" -o -name "$base.tmp.$$.*" \) -delete
  GRID_ATOMIC_TEMP=$(mktemp -- "$directory/$base.tmp.$$.XXXXXXXX")
  _GRID_TEMP_FILES+=("$GRID_ATOMIC_TEMP")
}

_grid_hash_sources() {
  local spec_script="$1" summarizer="$2"
  hash_harness_sources \
    spec "$spec_script" \
    engine "${BASH_SOURCE[0]}" \
    checkpoint-helper "$_grid_engine_dir/grid-checkpoint-lib.sh" \
    rebuild "$_grid_engine_dir/rebuild-config.sh" \
    cli-helper "$_grid_engine_dir/cli-lib.sh" \
    prefix-helper "$_grid_engine_dir/install-prefix-lib.sh" \
    eval-makefile "$_grid_engine_dir/Makefile" \
    compile-supervisor "$_grid_engine_dir/tools/rocq-compile-supervisor.sh" \
    summarizer "$summarizer"
}

_grid_require_reviewable_worktree() {
  local worktree="$1" spec_script="$2" summarizer="$3" relative path dirty=
  local -a allowed=(
    eval/grid-engine.sh
    eval/grid-checkpoint-lib.sh
    eval/rebuild-config.sh
    eval/cli-lib.sh
    eval/install-prefix-lib.sh
    eval/Makefile
    eval/tools/rocq-compile-supervisor.sh
  )
  for path in "$spec_script" "$summarizer"; do
    relative=${path#"$worktree"/}
    if [ "$relative" = "$path" ] || [ -z "$relative" ]; then
      echo "Grid harness source is outside the repository: $path" >&2
      return 1
    fi
    allowed+=("$relative")
  done

  # Runtime harness files are allowed to differ from HEAD only because
  # _grid_hash_sources records their exact bytes in every checkpoint's
  # grid_script_sha256 and in final provenance. eval/Makefile is included in
  # that digest because generation invokes it. eval/tests is non-runtime review
  # material. Every other tracked change remains tied exclusively to
  # repository_commit and must therefore block the run.
  local -a pathspec=(.)
  for path in "${allowed[@]}"; do
    pathspec+=(":(top,exclude,literal)$path")
  done
  pathspec+=(':(top,exclude)eval/tests/**')
  if ! git -C "$worktree" diff --quiet HEAD -- "${pathspec[@]}"; then
    echo "Evaluation grids reject dirty tracked build, plugin, or corpus sources." >&2
    return 1
  fi

  # `git diff HEAD` does not see untracked files. Ignore unrelated local files,
  # but reject untracked files in source-bearing paths unless they are one of
  # the explicitly hashed harness files or an eval test.
  while IFS= read -r -d '' relative; do
    for path in "${allowed[@]}"; do
      [ "$relative" != "$path" ] || continue 2
    done
    case "$relative" in
      eval/tests/*) continue ;;
      src/*|theories/*|eval/corpora/*|eval/*.sh|eval/atp/*|eval/tools/*|\
      Makefile|Makefile.*|_CoqProject.*|dune|dune-project|dune-workspace)
        dirty=$relative
        break
        ;;
    esac
  done < <(git -C "$worktree" ls-files --others --exclude-standard -z)
  if [ -n "$dirty" ]; then
    echo "Evaluation grids reject untracked build, plugin, or corpus source: $dirty" >&2
    return 1
  fi
}

_grid_capture_preamble() {
  local label="$1" temporary value status
  if ! temporary=$(mktemp "${TMPDIR:-/tmp}/coqhammer-grid-preamble.XXXXXXXX"); then
    echo "Could not create temporary file for grid_label_preamble" >&2
    return 1
  fi
  _GRID_TEMP_FILES+=("$temporary")

  # The checked subshell turns both `return` and `exit` in a callback into a
  # status we can report without terminating the grid driver. Capture through a
  # file so command substitution cannot discard the callback's trailing
  # newlines; the final sentinel is removed only after the file is read.
  if (grid_label_preamble "$label") > "$temporary"; then
    status=0
  else
    status=$?
  fi
  if ! value=$(cat -- "$temporary" && printf x); then
    rm -f -- "$temporary"
    _grid_forget_temp "$temporary"
    return 1
  fi
  GRID_CAPTURED_PREAMBLE=${value%x}
  rm -f -- "$temporary"
  _grid_forget_temp "$temporary"
  if [ "$status" -ne 0 ]; then
    echo "grid_label_preamble failed for label: $label" >&2
    return "$status"
  fi
}

_grid_canonicalize_external_source() {
  [ -n "$external_source" ] || return 0
  if [ ! -d "$external_source" ]; then
    echo "External source directory not found: $external_source" >&2
    return 1
  fi
  # This runs before the driver changes directory. Keep this one absolute path
  # for both provenance hashing and prepare-corpus.sh.
  external_source=$(cd -- "$external_source" && pwd -P)
}

_grid_missing_operand() {
  echo "Missing value for $1" >&2
  grid_usage >&2
  return 2
}

_grid_parse_args() {
  jobs=
  tim=${GRID_TIM:-5}
  consistency_tim=${GRID_CONSISTENCY_TIM:-2}
  compile_timeout=${GRID_COMPILE_TIMEOUT:-600}
  compile_timeout_grace=${GRID_COMPILE_TIMEOUT_GRACE:-10}
  skip_builds=false
  only_label=
  only_corpus=
  sample_corpora=true
  external_source=
  force=false

  while [ "$#" -gt 0 ]; do
    case "$1" in
      -j|--jobs)
        [ "$#" -ge 2 ] || { _grid_missing_operand "$1"; return 2; }
        jobs="$2"; shift 2 ;;
      --tim)
        [ "$#" -ge 2 ] || { _grid_missing_operand "$1"; return 2; }
        tim="$2"; shift 2 ;;
      --consistency-tim)
        [ "$#" -ge 2 ] || { _grid_missing_operand "$1"; return 2; }
        consistency_tim="$2"; shift 2 ;;
      --compile-timeout)
        [ "$#" -ge 2 ] || { _grid_missing_operand "$1"; return 2; }
        compile_timeout="$2"; shift 2 ;;
      --compile-timeout-grace)
        [ "$#" -ge 2 ] || { _grid_missing_operand "$1"; return 2; }
        compile_timeout_grace="$2"; shift 2 ;;
      --skip-builds) skip_builds=true; shift ;;
      --only-label)
        [ "$#" -ge 2 ] || { _grid_missing_operand "$1"; return 2; }
        only_label="$2"; shift 2 ;;
      --only-corpus)
        [ "$#" -ge 2 ] || { _grid_missing_operand "$1"; return 2; }
        only_corpus="$2"; shift 2 ;;
      --sample-corpus) sample_corpora=true; shift ;;
      --full-corpus) sample_corpora=false; shift ;;
      --external-source)
        [ "$#" -ge 2 ] || { _grid_missing_operand "$1"; return 2; }
        external_source="$2"; shift 2 ;;
      --force) force=true; shift ;;
      -h|--help) grid_usage; return 10 ;;
      *) echo "Unknown argument: $1" >&2; grid_usage >&2; return 2 ;;
    esac
  done
}

_grid_install_is_supported() {
  local install="$1" core="$1"
  [ "$install" = current ] && return 0
  case "$core" in
    dependent-types-off) ;;
    *) return 1 ;;
  esac
}

_grid_resolve_install_prefixes() {
  local eval_base="$1"
  local install label prefix previous
  local -A prefix_install=()
  for install in "${!install_label[@]}"; do
    if [ "${install_count[$install]}" -gt 1 ]; then
      prefix="$eval_base/_installs/$install"
    else
      prefix="$eval_base/_installs/${install_label[$install]}"
    fi
    prefix=$(realpath -m -- "$prefix")
    if [ -n "${prefix_install[$prefix]+set}" ]; then
      previous=${prefix_install[$prefix]}
      if [ "$previous" != "$install" ]; then
        echo "Distinct install identities resolve to the same prefix: $previous and $install -> $prefix" >&2
        return 1
      fi
    fi
    prefix_install[$prefix]=$install
    install_prefix[$install]=$prefix
  done
  for label in "${labels[@]}"; do
    install=${label_config[$label]}
    label_prefix[$label]=${install_prefix[$install]}
  done
}

_grid_validate_config_options() {
  local manifest="$1" config="$2" dependent
  case "$config" in
    dependent-types-off) dependent=false ;;
    *) return 1 ;;
  esac
  expect_manifest_value "$manifest" opt_dependent_types "$dependent"
}

_grid_manifest_matches_install() {
  local install="$1" prefix="$2" manifest
  manifest="$prefix/manifest.env"
  eval_prefix_is_owned "$prefix" || return 1
  [ -f "$manifest" ] && [ ! -L "$manifest" ] || return 1
  expect_manifest_value "$manifest" prefix "$prefix" || return 1
  if [ "$install" = current ]; then
    expect_manifest_value "$manifest" kind current &&
      expect_manifest_value "$manifest" config current &&
      expect_manifest_value "$manifest" commit "$repo_commit"
  else
    expect_manifest_value "$manifest" kind configuration &&
      expect_manifest_value "$manifest" config "$install" &&
      expect_manifest_value "$manifest" commit "$repo_commit" &&
      _grid_validate_config_options "$manifest" "$install"
  fi
}

_grid_prepare_prefix_env() {
  local prefix="$1"
  export PATH="$prefix/bin:$base_path"
  if [ -n "$base_ocamlpath" ]; then
    export OCAMLPATH="$prefix:$base_ocamlpath"
  else
    export OCAMLPATH="$prefix"
  fi
}

_grid_require_cmd() {
  if ! command -v "$1" >/dev/null 2>&1; then
    echo "Required command not found: $1" >&2
    return 1
  fi
}

_grid_require_prover() {
  case "$1" in
    eprover) _grid_require_cmd eprover ;;
    vampire) _grid_require_cmd htimeout && _grid_require_cmd vampire ;;
    *) echo "Unknown prover: $1" >&2; return 1 ;;
  esac
}

_grid_prepare_corpus() {
  local corpus="$1" prefix="$2"
  local args=("$corpus" --coqlib "$prefix/coq")
  # dependent-slice has only a committed sample fixture, even in full mode.
  if [ "$sample_corpora" = true ] || [ "$corpus" = dependent-slice ]; then
    args+=(--sample)
  fi
  if [ "$corpus" = external-equations ] && [ -n "$external_source" ]; then
    args+=(--source "$external_source")
  fi
  ./prepare-corpus.sh "${args[@]}"
}

_grid_set_corpus_inputs() {
  local corpus="$1" prefix="$2" source_dir module lib subtree modules
  local trees='' files='' source=''
  if [ "$corpus" = external-equations ] && [ -n "$external_source" ]; then
    source=$(corpus_source_path "$external_source")
    trees=$external_source
  elif [ "$sample_corpora" = true ] || [ "$corpus" = dependent-slice ]; then
    source_dir="$eval_dir/corpora/$corpus/sample"
    source=$(corpus_source_path "$source_dir")
    trees=$source_dir
  else
    case "$corpus" in
      stdlib-regression|dependent-stdlib)
        if [ "$corpus" = stdlib-regression ]; then
          modules=$stdlib_modules
        else
          modules=$dependent_stdlib_modules
        fi
        source="installed-Stdlib modules=$modules"
        for module in $modules; do
          if ! eval_safe_component "$module"; then
            echo "Invalid installed Stdlib module in corpus selection: $module" >&2
            return 1
          fi
          source_dir="$prefix/coq/user-contrib/Stdlib/$module"
          [ -d "$source_dir" ] || {
            echo "Installed Stdlib module not found: $source_dir" >&2
            return 1
          }
          source_dir=$(realpath -e -- "$source_dir")
          trees+="${trees:+$'\n'}$source_dir"
        done
        ;;
      stdpp|color-vector|external-equations)
        case "$corpus" in
          stdpp) lib=stdpp; subtree= ;;
          color-vector) lib=CoLoR; subtree=/Util/Vector ;;
          external-equations) lib=Equations; subtree= ;;
        esac
        source="installed-$lib$subtree"
        source_dir="$prefix/coq/user-contrib/$lib$subtree"
        [ -d "$source_dir" ] || {
          echo "Installed library not found: $source_dir" >&2
          return 1
        }
        trees=$(realpath -e -- "$source_dir")
        ;;
      equations-examples)
        source_dir="$eval_dir/_external/Coq-Equations/_build/default/examples"
        [ -d "$source_dir" ] || {
          echo "Equations examples not found: $source_dir" >&2
          return 1
        }
        source_dir=$(realpath -e -- "$source_dir")
        source=$(corpus_source_path "$source_dir")
        trees=$source_dir
        ;;
      *)
        echo "No full-corpus provenance mapping for corpus: $corpus" >&2
        return 1
        ;;
    esac
    if [ -f "$eval_dir/corpora/$corpus/excluded.txt" ]; then
      files="$eval_dir/corpora/$corpus/excluded.txt"
    fi
  fi
  if [[ "$source" == *$'\n'* ]]; then
    echo "Corpus provenance source contains an unsupported newline" >&2
    return 1
  fi
  corpus_source[$corpus]=$source
  corpus_input_trees[$corpus]=$trees
  corpus_input_files[$corpus]=$files
  _grid_recompute_corpus_digest "$corpus"
}

_grid_recompute_corpus_digest() {
  local corpus="$1" path inputs=0 digests=
  while IFS= read -r path; do
    [ -n "$path" ] || continue
    digests+=$(hash_file "$path")
    inputs=$((inputs + 1))
  done <<< "${corpus_input_files[$corpus]}"
  while IFS= read -r path; do
    [ -n "$path" ] || continue
    digests+=$(hash_tree "$path")
    inputs=$((inputs + 1))
  done <<< "${corpus_input_trees[$corpus]}"
  [ "$inputs" -gt 0 ] || {
    echo "Corpus provenance has no inputs: $corpus" >&2
    return 1
  }
  corpus_digest[$corpus]=$(hash_text "$digests")
  # The pre-engine grid scripts folded a one-input corpus differently: they
  # recorded that input's own tree digest, with no outer hash over the
  # concatenation. Keep the older rendering available for exactly that case, so
  # a historical marker can still be recognized without giving up the uniform
  # digest the summarizers recompute from the provenance manifest.
  if [ "$inputs" -eq 1 ]; then
    corpus_legacy_digest[$corpus]=$digests
  else
    corpus_legacy_digest[$corpus]=
  fi
}

_grid_require_consistent_corpus_provenance() {
  local corpus="$1"
  if [ -n "${expected_corpus_digest[$corpus]+set}" ]; then
    if [ "${corpus_source[$corpus]}" != "${expected_corpus_source[$corpus]}" ] ||
        [ "${corpus_digest[$corpus]}" != "${expected_corpus_digest[$corpus]}" ]; then
      echo "Corpus provenance differs across active installs: $corpus" >&2
      return 1
    fi
  else
    expected_corpus_source[$corpus]=${corpus_source[$corpus]}
    expected_corpus_digest[$corpus]=${corpus_digest[$corpus]}
  fi
}

_grid_validate_generation() {
  local outdir="$1" premise
  status_has "$outdir/generation.status" generation_failed=0 || return 1
  status_has "$outdir/generation.status" generation_exit=0 || return 1
  [ -s "$outdir/prepared-files.lst" ] || return 1
  for premise in "${premises[@]}"; do
    list_is_nonempty_and_complete "$outdir/generated-$premise.lst" || return 1
  done
}

_grid_validate_prover_run() {
  local outdir="$1" prover="$2" premise="$3"
  status_has_integer "$outdir/prover-$prover-$premise.status" prover_exit &&
    list_is_nonempty_and_complete "$outdir/generated-$premise.lst" &&
    expected_atp_outputs_are_complete \
      "$outdir/generated-$premise.lst" "$outdir/atp-problems/$premise" \
      "$outdir/prover-outputs/$prover-$premise" "$prover" \
      "$outdir/prover-outputs-$prover-$premise.lst" "$outdir/$prover-$premise.log"
}

_grid_validate_consistency_run() {
  local outdir="$1" prover="$2" premise="$3" work
  work="$outdir/consistency/$prover-$premise"
  status_is "$outdir/consistency-$prover-$premise.status" consistency_exit=0 &&
    consistency_outputs_are_complete \
      "$outdir/generated-$premise.lst" "$work/outputs" "$work/raw" "$work/status" \
      "$outdir/consistency-outputs-$prover-$premise.lst"
}

_grid_checkpoint_contents() {
  local stage="$1" label="$2"
  checkpoint_contents "$@"
  compile_checkpoint_fields "$stage"
  printf '%s\n' \
    "hook_preamble_sha256=${label_preamble_digest[$label]}" \
    "hook_preamble_file=hook-preamble.v"
}

_grid_validate_preamble_sidecar() {
  local marker="$1" label="$2" sidecar
  sidecar="$(dirname "$marker")/hook-preamble.v"
  [ -f "$sidecar" ] || return 1
  [ "$(hash_file "$sidecar")" = "${label_preamble_digest[$label]}" ] || return 1
  printf %s "${label_preamble[$label]}" | cmp -s - "$sidecar"
}

# Read one `key=value` provenance field back out of a historical marker. A key
# that is missing or recorded more than once, and a value that does not have the
# expected digest shape, fail the read: a garbled marker must narrow the
# accepted migration rather than widen it.
_grid_marker_field() {
  local marker="$1" key="$2" pattern="$3" matches value
  matches=$(grep -c -e "^$key=" -- "$marker") || return 1
  [ "$matches" -eq 1 ] || return 1
  value=$(sed -n "s/^$key=//p" -- "$marker")
  [[ "$value" =~ $pattern ]] || return 1
  printf %s "$value"
}

_grid_matches_legacy_checkpoint() {
  local marker="$1" stage="$2" corpus="$4"
  local historical_script historical_commit historical_helper
  local commit_pattern='^([0-9a-f]{40}|[0-9a-f]{64})$'
  local digest_pattern='^[0-9a-f]{64}$'
  # Historical generation ran without the now-provenanced compile supervisor.
  # Its output must be regenerated; non-compiling downstream stages remain
  # reusable when their explicit input hashes and all other fields still match.
  [ "$stage" != generation ] || return 1
  shift
  # A genuinely historical marker was necessarily written at an older repository
  # commit and against an older checkpoint helper, so re-rendering it with only
  # the grid script digest replaced could never match. Recover all three
  # harness-provenance values from the marker instead, and gate the migration on
  # its recorded grid script digest being one the spec declares.
  historical_script=$(_grid_marker_field "$marker.done" grid_script_sha256 \
    "$digest_pattern") || return 1
  array_contains "$historical_script" "${legacy_grid_script_digests[@]}" || return 1
  historical_commit=$(_grid_marker_field "$marker.done" repository_commit \
    "$commit_pattern") || return 1
  historical_helper=$(_grid_marker_field "$marker.done" checkpoint_helper_sha256 \
    "$digest_pattern") || return 1
  # Bash locals are dynamically scoped, so checkpoint_contents renders exactly
  # these three recorded historical values while every remaining field -- the
  # checkpoint version, label, config, install identity, corpus provenance and
  # the stage-specific fields -- stays current and must still match byte for
  # byte, including the unfaked install identity and the corpus inputs.
  local repo_commit="$historical_commit"
  local grid_script_digest="$historical_script"
  local grid_helper_digest="$historical_helper"
  # The one exception is how the corpus inputs are folded into a single field:
  # a historical marker records the pre-engine rendering of the very same
  # inputs. Both renderings are recomputed here from the corpus as it stands
  # now, so the corpus contents are still verified either way.
  local candidates=("${corpus_digest[$corpus]}") candidate
  candidate=${corpus_legacy_digest[$corpus]:-}
  if [ -n "$candidate" ] && [ "$candidate" != "${corpus_digest[$corpus]}" ]; then
    candidates+=("$candidate")
  fi
  local -A corpus_digest
  for candidate in "${candidates[@]}"; do
    corpus_digest[$corpus]=$candidate
    if checkpoint_contents "$@" | cmp -s - "$marker.done"; then
      return 0
    fi
  done
  return 1
}

# Override the checkpoint helpers for engine users. New manifests carry the
# preamble digest, sidecar, and compile provenance. A historical manifest
# remains reusable only for a non-generation stage with an empty preamble, only
# when the grid script digest it records is declared in
# GRID_LEGACY_SCRIPT_SHA256, and only when every field other than the three
# harness-provenance fields read back from it -- grid script digest, repository
# commit, checkpoint helper digest -- exactly matches the current run, with the
# corpus digest also accepted in the pre-engine rendering of the same inputs.
checkpoint_matches() {
  local marker="$1" label="$3"
  shift
  [ -f "$marker.done" ] || return 1
  if _grid_checkpoint_contents "$@" | cmp -s - "$marker.done" &&
      _grid_validate_preamble_sidecar "$marker" "$label"; then
    return 0
  fi
  if [ -z "${label_preamble[$label]}" ] &&
      _grid_matches_legacy_checkpoint "$marker" "$@"; then
    return 0
  fi
  echo "[checkpoint] stale provenance in $marker.done; rerunning" >&2
  rm -f "$marker.done"
  return 1
}

mark_checkpoint() {
  local marker="$1" label="$3" temporary sidecar sidecar_temporary
  shift
  sidecar="$(dirname "$marker")/hook-preamble.v"
  _grid_new_atomic_temp "$sidecar"
  sidecar_temporary=$GRID_ATOMIC_TEMP
  printf %s "${label_preamble[$label]}" > "$sidecar_temporary"
  mv -- "$sidecar_temporary" "$sidecar"
  _grid_forget_temp "$sidecar_temporary"
  _grid_new_atomic_temp "$marker.done"
  temporary=$GRID_ATOMIC_TEMP
  _grid_checkpoint_contents "$@" > "$temporary"
  mv -- "$temporary" "$marker.done"
  _grid_forget_temp "$temporary"
}

# rebuild-config.sh refuses to erase an existing prefix that carries no
# ownership marker written for that exact path, so a prefix built before the
# marker existed, or one that was moved or copied, would abort the whole run
# just after the engine announced a rebuild. Engine prefixes are not
# user-supplied: _grid_resolve_install_prefixes derives every one of them as a
# realpath-normalized <eval_dir>/_installs/<component>. Re-establish that
# ownership by construction here, then erase the stale prefix so the rebuild can
# proceed; refuse loudly, and without deleting anything, when it does not hold.
_grid_discard_stale_prefix() {
  local label="$1" prefix="$2" installs_root component repo_path
  installs_root=$(realpath -m -- "$eval_dir/_installs")
  repo_path=$(realpath -m -- "$repo")
  component=${prefix#"$installs_root"/}
  if [ "$component" != "$prefix" ] && eval_safe_component "$component" &&
      [ -d "$prefix" ] && [ ! -L "$prefix" ] && [ "$prefix" != "$repo_path" ] &&
      [ "${repo_path#"$prefix"/}" = "$repo_path" ]; then
    rm -rf -- "$prefix"
    return 0
  fi
  echo "Install prefix for $label is stale but is not an engine-managed directory under $installs_root: $prefix" >&2
  echo "Remove it by hand before rerunning the grid: rm -rf $prefix" >&2
  return 1
}

_grid_build_install() {
  local install="$1" label prefix
  label=${install_label[$install]}
  prefix=${install_prefix[$install]}
  # Any existing prefix directory is a candidate for reuse; one without a
  # manifest cannot be matched, so it is stale by construction and goes through
  # the same discard path rather than being built over.
  if [ -d "$prefix" ]; then
    if [ -f "$prefix/manifest.env" ] &&
        _grid_manifest_matches_install "$install" "$prefix"; then
      echo "[build] $label already installed"
      return 0
    fi
    if [ "$skip_builds" = true ]; then
      echo "Install prefix for $label is stale or mismatched: $prefix" >&2
      exit 1
    fi
    _grid_discard_stale_prefix "$label" "$prefix" || exit 1
    echo "[build] $label install is stale or mismatched; rebuilding"
  fi
  if [ "$skip_builds" = true ]; then
    echo "Missing install prefix for $label: $prefix" >&2
    exit 1
  fi
  echo "[build] installing $label"
  export PATH="$base_path"
  if [ -n "$base_ocamlpath" ]; then
    export OCAMLPATH="$base_ocamlpath"
  else
    unset OCAMLPATH
  fi
  (cd "$eval_dir" && ./rebuild-config.sh "$install" --label "$label" --prefix "$prefix")
}

# A stage that reports a failure must not also abort the driver, and the driver
# must not lose a failure the stage did not report itself. Bash ignores errexit
# for the whole dynamic extent of a command run in a condition or on the left of
# `||` -- every function and subshell it invokes included -- and a `set -e`
# inside cannot bring it back, so a stage invoked that way would silently walk
# past a failing command it does not check. Call stages through this helper
# instead: it is invoked as a plain command, so the caller's errexit is
# undisturbed, and it reports the stage's status in GRID_STAGE_STATUS rather
# than its own exit code. The subshell restores errexit for the stage body and
# keeps an `exit` reached inside one -- from a shared helper, say -- from
# terminating the driver. It also cleans up the temporaries the stage
# registered, which the driver's own EXIT trap can no longer see.
GRID_STAGE_STATUS=0

_grid_run_stage() {
  local -
  set +e
  (
    set -e
    _GRID_TEMP_FILES=()
    trap _grid_cleanup_temp_files EXIT
    "$@"
  )
  GRID_STAGE_STATUS=$?
}

_grid_run_generation() {
  local label="$1" corpus="$2" prefix="$3" coqc_cmd premise
  local outdir="$results_root/$label/$corpus"
  mkdir -p "$outdir"
  local marker="$outdir/generate"
  if checkpoint_done "$marker" generation "$label" "$corpus" "$prefix"; then
    if _grid_validate_generation "$outdir"; then
      echo "[gen] $label/$corpus already done"
      return 0
    fi
    invalidate_checkpoint "$marker" "generation artifacts are incomplete or invalid"
  fi

  rm -f "$outdir/generation.status" "$marker.done"
  # Keep downstream checkpoints until the regenerated problem trees exist.
  # Their input_sha256 fields then safely decide whether their outputs can be
  # reused, rather than discarding expensive results when generation is equal.
  echo "[gen] $label/$corpus"
  _grid_prepare_prefix_env "$prefix"
  export COQHAMMER_HOOK_PREAMBLE="${label_preamble[$label]}"
  cd "$eval_dir" || return
  _grid_prepare_corpus "$corpus" "$prefix" > "$outdir/prepared-files.lst"
  rm -rf logs atp/problems atp/i atp/o out statistics.html check.log gen-atp.log gen-atp.log.bak coqhammer.opt
  mkdir -p atp/o out

  coqc_cmd="rocq c -coqlib $prefix/coq"
  if ! run_compile_make init init "$coqc_cmd" "$outdir/init.log" logs/init; then
    echo "Init failed for $label/$corpus; see $outdir/init.log" >&2
    return 1
  fi
  echo check > coqhammer.opt
  if ! run_compile_make check check "$coqc_cmd" \
      "$outdir/check.full.log" logs/check; then
    echo "Check failed for $label/$corpus; see $outdir/check.full.log" >&2
    return 1
  fi
  grep Error "$outdir/check.full.log" > "$outdir/check.log" || true
  if [ -s "$outdir/check.log" ]; then
    echo "Check errors for $label/$corpus; see $outdir/check.log" >&2
    return 1
  fi

  echo gen-atp > coqhammer.opt
  if ! run_compile_make gen-atp atp "$coqc_cmd" \
      "$outdir/gen-atp.full.log" logs/atp; then
    cleanup_paired_output_temporaries atp/problems
    grep Error "$outdir/gen-atp.full.log" > "$outdir/gen-atp.log" || true
    echo "ATP generation failed for $label/$corpus; see $outdir/gen-atp.full.log" >&2
    return 1
  fi
  cleanup_paired_output_temporaries atp/problems
  grep Error "$outdir/gen-atp.full.log" > "$outdir/gen-atp.log" || true
  if [ -s "$outdir/gen-atp.log" ]; then
    echo "ATP-generation errors for $label/$corpus; see $outdir/gen-atp.log" >&2
    return 1
  fi

  rm -rf "$outdir/atp-problems"
  mkdir -p "$outdir/atp-problems"
  for premise in "${premises[@]}"; do
    if [ ! -d "atp/problems/$premise" ]; then
      echo "No generated ATP directory for $premise in $label/$corpus" >&2
      return 1
    fi
    cp -R "atp/problems/$premise" "$outdir/atp-problems/$premise"
    find "$outdir/atp-problems/$premise" -name '*.p' | sort > "$outdir/generated-$premise.lst"
    if ! list_is_nonempty_and_complete "$outdir/generated-$premise.lst"; then
      echo "No generated ATP problems for $premise in $label/$corpus" >&2
      return 1
    fi
  done
  {
    echo generation_failed=0
    echo generation_exit=0
  } > "$outdir/generation.status"
  mark_checkpoint "$marker" generation "$label" "$corpus" "$prefix"
}

_grid_run_prover() {
  local label="$1" corpus="$2" premise="$3" prover="$4" prefix="$5" prover_status
  local outdir="$results_root/$label/$corpus"
  local marker="$outdir/prover-$prover-$premise" input_digest
  input_digest=$(hash_tree "$outdir/atp-problems/$premise")
  if checkpoint_done "$marker" prover "$label" "$corpus" "$prefix" \
      "premise=$premise" "prover=$prover" "timeout=$tim" "input_sha256=$input_digest"; then
    if _grid_validate_prover_run "$outdir" "$prover" "$premise"; then
      echo "[prover] $label/$corpus/$prover/$premise already done"
      return 0
    fi
    invalidate_checkpoint "$marker" "prover status or outputs are incomplete or invalid"
  fi

  rm -f "$marker.done" "$outdir/prover-$prover-$premise.status"
  if ! list_is_nonempty_and_complete "$outdir/generated-$premise.lst"; then
    echo "Cannot run $prover: no generated problems for $label/$corpus/$premise" >&2
    return 1
  fi
  echo "[prover] $label/$corpus/$prover/$premise"
  _grid_prepare_prefix_env "$prefix"
  _grid_require_prover "$prover"
  cd "$eval_dir" || return
  rm -rf atp/i "atp/o/$prover" "atp/o/$prover-$premise"
  mkdir -p atp/i atp/o
  ln -s "$outdir/atp-problems/$premise" atp/i/f
  if make -C atp -k -j "$jobs" TIM="$tim" "$prover" > "$outdir/$prover-$premise.log" 2>&1; then
    prover_status=0
  else
    prover_status=$?
    echo "[prover] $label/$corpus/$prover/$premise exited with status $prover_status; keeping partial outputs"
  fi
  echo "prover_exit=$prover_status" > "$outdir/prover-$prover-$premise.status"
  rm -rf "$outdir/prover-outputs/$prover-$premise"
  mkdir -p "$outdir/prover-outputs" "atp/o/$prover"
  mv "atp/o/$prover" "$outdir/prover-outputs/$prover-$premise"
  find "$outdir/prover-outputs/$prover-$premise" -type f | sort > "$outdir/prover-outputs-$prover-$premise.lst"
  if ! _grid_validate_prover_run "$outdir" "$prover" "$premise"; then
    echo "Prover run produced incomplete, malformed, or crashed outputs for $label/$corpus/$prover/$premise" >&2
    return 1
  fi
  mark_checkpoint "$marker" prover "$label" "$corpus" "$prefix" \
    "premise=$premise" "prover=$prover" "timeout=$tim" "input_sha256=$input_digest"
}

# The status a consistency scan returns when the premises it was given really
# are inconsistent. Every other non-zero status it returns is a failure of the
# scan itself, which the driver reports; a hit is a measurement, which it does
# not. Both are recorded as consistency_exit=1 for the summarizer.
_GRID_CONSISTENCY_HIT_STATUS=3

_grid_run_consistency() {
  local label="$1" corpus="$2" premise="$3" prover="$4" prefix="$5"
  local outdir="$results_root/$label/$corpus"
  local marker="$outdir/consistency-$prover-$premise" input_digest
  local output_list="$outdir/consistency-outputs-$prover-$premise.lst"
  # A failed hash proves nothing about the recorded outputs: keep the
  # checkpoint, whose input_sha256 decides on the next run whether it is still
  # valid, rather than discarding an expensive per-problem scan.
  if ! input_digest=$(hash_tree "$outdir/atp-problems/$premise"); then
    return 1
  fi
  if checkpoint_done "$marker" consistency "$label" "$corpus" "$prefix" \
      "premise=$premise" "prover=$prover" "timeout=$consistency_tim" \
      "input_sha256=$input_digest"; then
    if _grid_validate_consistency_run "$outdir" "$prover" "$premise"; then
      echo "[consistency] $label/$corpus/$prover/$premise already done"
      return 0
    fi
    invalidate_checkpoint "$marker" "consistency status or outputs are incomplete or invalid"
  fi

  rm -f "$marker.done" "$outdir/consistency-$prover-$premise.status" \
    "$output_list"
  if ! list_is_nonempty_and_complete "$outdir/generated-$premise.lst"; then
    echo "Cannot run consistency check: no problems for $label/$corpus/$premise" >&2
    return 1
  fi
  echo "[consistency] $label/$corpus/$prover/$premise"
  _grid_prepare_prefix_env "$prefix"
  _grid_require_prover "$prover"
  local work="$outdir/consistency/$prover-$premise"
  rm -rf "$work"
  mkdir -p "$work/problems" "$work/outputs" "$work/raw" "$work/status"

  python3 - "$outdir/atp-problems/$premise" "$work/problems" <<'PY'
import pathlib
import re
import sys
src = pathlib.Path(sys.argv[1])
dst = pathlib.Path(sys.argv[2])
files = sorted(src.glob('*.p'))
for path in files:
    text = path.read_text()
    text, n = re.subn(r"fof\(([^,]+),\s*conjecture,\s*.*?\)\.\s*$",
                      r"fof(\1, conjecture, $false).",
                      text, count=1, flags=re.M)
    if n != 1:
        raise SystemExit(f"did not rewrite exactly one conjecture in {path}")
    (dst / path.name).write_text(text)
PY

  local problems=("$work/problems"/*.p)
  if [ ! -e "${problems[0]}" ]; then
    echo "Consistency check generated no false-conjecture problems for $label/$corpus/$premise" >&2
    return 1
  fi
  for problem in "${problems[@]}"; do
    local name command_status
    name=$(basename "$problem")
    if [ "$prover" = eprover ]; then
      if eprover -s --cpu-limit="$consistency_tim" --auto-schedule -R --print-statistics -p --tstp-format "$problem" \
          > "$work/raw/$name" 2>&1; then
        command_status=0
      else
        command_status=$?
      fi
      grep "file[(]'\|# SZS\|SZS status" "$work/raw/$name" > "$work/outputs/$name" || true
    else
      if htimeout "$((consistency_tim + 5))" vampire --mode casc -t "$consistency_tim" --proof tptp \
          --output_axiom_names on "$problem" > "$work/raw/$name" 2>&1; then
        command_status=0
      else
        command_status=$?
      fi
      grep "file[(]'\|% SZS\|SZS status" "$work/raw/$name" > "$work/outputs/$name" || true
    fi
    echo "command_exit=$command_status" > "$work/status/$name.status"
    if log_has_crash_or_error_ignoring_strategy_aborts "$work/raw/$name" ||
        ! szs_terminal_status "$work/outputs/$name"; then
      echo consistency_exit=1 > "$outdir/consistency-$prover-$premise.status"
      echo "Consistency prover crashed or produced no terminal status for $label/$corpus/$prover/$premise/$name" >&2
      return 1
    fi
  done
  # Validate and publish every output before interpreting any one of them as a
  # hit.  A genuine inconsistency is a measured result, not an incomplete run,
  # and the summarizer needs the complete per-problem output list to count it.
  local candidate_list="$work/consistency-outputs.lst"
  find "$work/outputs" -type f | sort > "$candidate_list"
  if ! consistency_outputs_are_complete \
      "$outdir/generated-$premise.lst" "$work/outputs" "$work/raw" "$work/status" \
      "$candidate_list"; then
    rm -f "$output_list"
    echo consistency_exit=1 > "$outdir/consistency-$prover-$premise.status"
    echo "Consistency check produced incomplete outputs for $label/$corpus/$prover/$premise" >&2
    return 1
  fi
  mv -- "$candidate_list" "$output_list"
  if grep -RE "SZS status (Theorem|Unsatisfiable|ContradictoryAxioms)|^unsat$" "$work/outputs" >/dev/null 2>&1; then
    echo consistency_exit=1 > "$outdir/consistency-$prover-$premise.status"
    echo "Inconsistency hit for $label/$corpus/$prover/$premise; see $work/outputs" >&2
    return "$_GRID_CONSISTENCY_HIT_STATUS"
  fi
  echo consistency_exit=0 > "$outdir/consistency-$prover-$premise.status"
  if ! _grid_validate_consistency_run "$outdir" "$prover" "$premise"; then
    rm -f "$output_list"
    echo "Consistency check produced incomplete outputs for $label/$corpus/$prover/$premise" >&2
    return 1
  fi
  mark_checkpoint "$marker" consistency "$label" "$corpus" "$prefix" \
    "premise=$premise" "prover=$prover" "timeout=$consistency_tim" \
    "input_sha256=$input_digest"
}

# Summarizer API: labels remain positional for compatibility with the existing
# extraction summarizer. Active axes, mode, consistency premise, and all values
# needed to validate current checkpoint provenance are exposed in the
# environment. Summarizers that predate this API may safely ignore them.
_grid_expected_provenance_json() {
  local label corpus prefix
  local args=(
    "$repo_commit" "$grid_script_digest" "$grid_helper_digest"
    "$compile_supervisor_digest" "$compile_timeout" "$compile_timeout_grace"
    "$tim" "$consistency_tim" "${#labels[@]}"
  )
  for label in "${labels[@]}"; do
    prefix=${label_prefix[$label]}
    args+=("$label" "${label_config[$label]}"
      "$(manifest_value "$prefix/manifest.env" commit)"
      "$(manifest_value "$prefix/manifest.env" kind)"
      "$(hash_file "$prefix/manifest.env")")
  done
  args+=("${#corpora[@]}")
  for corpus in "${corpora[@]}"; do
    args+=("$corpus" "$corpus_mode" "${corpus_source[$corpus]}"
      "${corpus_digest[$corpus]}" "${corpus_input_trees[$corpus]}"
      "${corpus_input_files[$corpus]}")
  done
  python3 - "${args[@]}" <<'PY'
import json
import sys

values = iter(sys.argv[1:])
result = {
    "repository_commit": next(values),
    "grid_script_sha256": next(values),
    "checkpoint_helper_sha256": next(values),
    "compile_supervisor_sha256": next(values),
    "compile_timeout": next(values),
    "compile_timeout_grace": next(values),
    "prover_timeout": next(values),
    "consistency_timeout": next(values),
    "labels": {},
    "corpora": {},
}
for _ in range(int(next(values))):
    label = next(values)
    result["labels"][label] = dict(zip(
        ("config", "install_commit", "install_kind", "install_manifest_sha256"),
        (next(values), next(values), next(values), next(values)),
    ))
for _ in range(int(next(values))):
    corpus = next(values)
    mode, source, digest, trees, files = (next(values) for _ in range(5))
    result["corpora"][corpus] = {
        "mode": mode,
        "source": source,
        "sha256": digest,
        "trees": trees.splitlines(),
        "files": files.splitlines(),
    }
try:
    next(values)
except StopIteration:
    pass
else:
    raise SystemExit("internal error: unused provenance arguments")
print(json.dumps(result, sort_keys=True, separators=(",", ":")))
PY
}

_grid_run_summarizer() {
  local summarizer="$1" root="$2" summary="$3" analysis="$4"
  local premise_axis prover_axis corpus_axis expected_provenance
  premise_axis=$(printf '%s\n' "${premises[@]}")
  prover_axis=$(printf '%s\n' "${provers[@]}")
  corpus_axis=$(printf '%s\n' "${corpora[@]}")
  expected_provenance=$(_grid_expected_provenance_json)
  COQHAMMER_GRID_PREMISES="$premise_axis" \
  COQHAMMER_GRID_PROVERS="$prover_axis" \
  COQHAMMER_GRID_CORPORA="$corpus_axis" \
  COQHAMMER_GRID_CORPUS_MODE="$corpus_mode" \
  COQHAMMER_GRID_CONSISTENCY_PREMISE="$consistency_premise" \
  COQHAMMER_GRID_EXPECTED_PROVENANCE="$expected_provenance" \
    python3 "$summarizer" "$root" "$summary" "$analysis" "${labels[@]}"
}

# Same fields and order as the historical helper, but install prefixes come
# from the declarative install mapping so labels can share one build.
# shellcheck disable=SC2153
_grid_write_provenance() {
  local output="$1" summarizer="$2" summary="$3" analysis="$4"
  local temporary label corpus prefix
  _grid_new_atomic_temp "$output"
  temporary=$GRID_ATOMIC_TEMP
  {
    printf '%s\n' \
      provenance_version=1 \
      "grid=$GRID_NAME" \
      "repository_commit=$repo_commit" \
      "grid_script_sha256=$grid_script_digest" \
      "checkpoint_helper_sha256=$grid_helper_digest" \
      "summarizer_sha256=$(hash_file "$summarizer")" \
      "compile_supervisor_sha256=$compile_supervisor_digest" \
      "compile_timeout=$compile_timeout" \
      "compile_timeout_grace=$compile_timeout_grace" \
      "prover_timeout=$tim" \
      "consistency_timeout=$consistency_tim" \
      "checkpoint_markers_sha256=$(hash_checkpoint_markers "$results_root")" \
      "summary_sha256=$(hash_file "$summary")" \
      "analysis_sha256=$(hash_file "$analysis")"
    for label in "${labels[@]}"; do
      prefix=${label_prefix[$label]}
      printf '%s\n' \
        "label.$label.config=${label_config[$label]}" \
        "label.$label.install_commit=$(manifest_value "$prefix/manifest.env" commit)" \
        "label.$label.install_kind=$(manifest_value "$prefix/manifest.env" kind)" \
        "label.$label.install_manifest_sha256=$(hash_file "$prefix/manifest.env")"
    done
    for corpus in "${corpora[@]}"; do
      printf '%s\n' \
        "corpus.$corpus.mode=$corpus_mode" \
        "corpus.$corpus.source=${corpus_source[$corpus]}" \
        "corpus.$corpus.sha256=${corpus_digest[$corpus]}"
    done
  } > "$temporary"
  mv -- "$temporary" "$output"
  _grid_forget_temp "$temporary"
}

# Run the complete driver in a subshell. Its cleanup traps therefore cannot
# replace traps installed by a script that sourced this engine.
grid_run() (
  _grid_install_cleanup_traps
  _grid_require_spec || return 2
  local parse_status=0
  _grid_parse_args "$@" || parse_status=$?
  [ "$parse_status" -eq 0 ] || {
    [ "$parse_status" -eq 10 ] && return 0
    return "$parse_status"
  }

  local value label corpus install prefix consistency_premise
  local run_status=0
  for value in "$tim" "$consistency_tim" "$compile_timeout" "$compile_timeout_grace"; do
    if [[ ! "$value" =~ ^[1-9][0-9]*$ ]]; then
      echo "Timeouts must be positive integers: $value" >&2
      return 2
    fi
  done

  repo=$(git rev-parse --show-toplevel)
  local spec_script
  spec_script=$(realpath "${BASH_SOURCE[1]}")
  _grid_require_reviewable_worktree "$repo" "$spec_script" "$GRID_SUMMARIZER" || return 1
  eval_dir="$repo/eval"
  repo_commit=$(git rev-parse HEAD)
  # This aggregate covers every under-review runtime source accepted by the
  # guard. Clean build/corpus machinery is represented by repository_commit.
  grid_script_digest=$(_grid_hash_sources "$spec_script" "$GRID_SUMMARIZER")
  grid_helper_digest=$(hash_file "$eval_dir/grid-checkpoint-lib.sh")
  compile_supervisor="$eval_dir/tools/rocq-compile-supervisor.sh"
  compile_supervisor_digest=$(hash_file "$compile_supervisor")
  results_root=$(realpath -m -- "$GRID_RESULTS_ROOT")
  artifacts_dir=$(realpath -m -- "$GRID_ARTIFACTS_DIR")
  _grid_validate_output_roots || return 2
  _grid_canonicalize_external_source || return 1
  for value in "$results_root" "$artifacts_dir"; do
    if [ -e "$value" ] && [ ! -d "$value" ]; then
      echo "Grid output root exists but is not a directory: $value" >&2
      return 2
    fi
  done

  labels=("${GRID_LABELS[@]}")
  premises=("${GRID_PREMISES[@]}")
  provers=("${GRID_PROVERS[@]}")
  corpora=("${GRID_CORPORA[@]}")
  declare -ga legacy_grid_script_digests
  legacy_grid_script_digests=()
  if declare -p GRID_LEGACY_SCRIPT_SHA256 >/dev/null 2>&1; then
    legacy_grid_script_digests=("${GRID_LEGACY_SCRIPT_SHA256[@]}")
  fi
  consistency_premise=${GRID_CONSISTENCY_PREMISE-${premises[0]}}
  declare -gA label_config label_preamble label_preamble_digest
  declare -gA install_label install_count install_prefix label_prefix
  label_config=()
  label_preamble=()
  label_preamble_digest=()
  install_label=()
  install_count=()
  install_prefix=()
  label_prefix=()
  for label in "${labels[@]}"; do
    if ! install=$(grid_label_install "$label"); then
      echo "grid_label_install failed for label: $label" >&2
      return 2
    fi
    if ! eval_safe_component "$install"; then
      echo "grid_label_install must return a safe single path component for $label: $install" >&2
      return 2
    fi
    if ! _grid_install_is_supported "$install"; then
      echo "grid_label_install returned an unsupported install for $label: $install" >&2
      return 2
    fi
    label_config[$label]=$install
    if [ -z "${install_label[$install]+set}" ]; then
      install_label[$install]=$label
      install_count[$install]=0
    fi
    install_count[$install]=$((install_count[$install] + 1))
  done
  # Resolve and compare all install destinations before capturing preambles,
  # creating output roots, or invoking a build. A unique install uses its label
  # as before, while shared installs use the install identity.
  _grid_resolve_install_prefixes "$eval_dir" || return 2
  for label in "${labels[@]}"; do
    _grid_capture_preamble "$label" || return 2
    label_preamble[$label]=$GRID_CAPTURED_PREAMBLE
    label_preamble_digest[$label]=$(hash_text "${label_preamble[$label]}")
  done

  if [ -n "$only_label" ] && ! array_contains "$only_label" "${labels[@]}"; then
    echo "Unknown grid label: $only_label" >&2
    return 2
  fi
  if [ -n "$only_corpus" ] && ! array_contains "$only_corpus" "${corpora[@]}"; then
    echo "Unknown corpus: $only_corpus" >&2
    return 2
  fi

  if [ "$sample_corpora" = true ]; then
    corpus_mode=sample
  else
    corpus_mode=full
  fi
  echo "[corpus mode] $corpus_mode"
  stdlib_modules=${STDLIB_CORPUS_MODULES:-"Arith Bool Vectors Lists NArith"}
  dependent_stdlib_modules=${DEPENDENT_STDLIB_MODULES:-"Logic Wellfounded MSets Structures Sorting Program"}
  declare -gA corpus_source corpus_digest corpus_legacy_digest
  declare -gA corpus_input_trees corpus_input_files
  corpus_source=()
  corpus_digest=()
  corpus_legacy_digest=()
  corpus_input_trees=()
  corpus_input_files=()

  if [ -z "$jobs" ]; then
    jobs=$(detect_jobs) || return 2
    echo "[jobs] using $jobs parallel jobs"
  fi
  if [[ ! "$jobs" =~ ^[1-9][0-9]*$ ]]; then
    echo "Jobs must be a positive integer: $jobs" >&2
    return 2
  fi
  base_path=$PATH
  base_ocamlpath=${OCAMLPATH:-}

  # All spec callbacks, axes, and output paths are validated before this first
  # write. Full-corpus source trees are validated after their installs exist.
  mkdir -p "$results_root" "$artifacts_dir"

  declare -A prepared_installs=()
  for label in "${labels[@]}"; do
    if [ -n "$only_label" ] && [ "$label" != "$only_label" ]; then
      continue
    fi
    install=${label_config[$label]}
    if [ -z "${prepared_installs[$install]+set}" ]; then
      _grid_build_install "$install"
      prepared_installs[$install]=true
    fi
  done

  # Full corpora come from the active installation, so calculate provenance
  # only after every selected prefix exists. Distinct installs must expose the
  # same corpus inputs: summaries have one corpus provenance, not one per label.
  declare -A provenance_checked_install=()
  declare -A expected_corpus_source=() expected_corpus_digest=()
  for label in "${labels[@]}"; do
    if [ -n "$only_label" ] && [ "$label" != "$only_label" ]; then
      continue
    fi
    install=${label_config[$label]}
    [ -z "${provenance_checked_install[$install]+set}" ] || continue
    prefix=${label_prefix[$label]}
    for corpus in "${corpora[@]}"; do
      if [ -n "$only_corpus" ] && [ "$corpus" != "$only_corpus" ]; then
        continue
      fi
      _grid_set_corpus_inputs "$corpus" "$prefix" || return 1
      _grid_require_consistent_corpus_provenance "$corpus" || return 1
    done
    provenance_checked_install[$install]=true
  done

  for label in "${labels[@]}"; do
    if [ -n "$only_label" ] && [ "$label" != "$only_label" ]; then
      continue
    fi
    prefix=${label_prefix[$label]}
    for corpus in "${corpora[@]}"; do
      if [ -n "$only_corpus" ] && [ "$corpus" != "$only_corpus" ]; then
        continue
      fi
      # A failed stage leaves the rest of the grid worth running, so remember
      # the failure and carry on. Everything downstream of generation depends
      # on its problem trees, so that one failure skips the rest of the corpus.
      _grid_run_stage _grid_run_generation "$label" "$corpus" "$prefix"
      if [ "$GRID_STAGE_STATUS" -ne 0 ]; then
        run_status=1
        continue
      fi
      for premise in "${premises[@]}"; do
        for prover in "${provers[@]}"; do
          _grid_run_stage _grid_run_prover "$label" "$corpus" "$premise" \
            "$prover" "$prefix"
          [ "$GRID_STAGE_STATUS" -eq 0 ] || run_status=1
        done
      done
      # The consistency canary is measurement, not a gate: a genuine
      # inconsistency hit is a result the summarizer reads from consistency_exit=
      # in its status file, not a reason to fail the grid. A scan that could not
      # be run or crashed is an ordinary infrastructure failure, and a partial
      # run has no summarizer to notice it, so only the hit stays out of
      # run_status.
      for prover in "${provers[@]}"; do
        _grid_run_stage _grid_run_consistency "$label" "$corpus" \
          "$consistency_premise" "$prover" "$prefix"
        if [ "$GRID_STAGE_STATUS" -ne 0 ] &&
            [ "$GRID_STAGE_STATUS" -ne "$_GRID_CONSISTENCY_HIT_STATUS" ]; then
          run_status=1
        fi
      done
    done
  done

  if [ "$run_status" -ne 0 ]; then
    echo "One or more grid stages failed; see the messages above" >&2
  fi
  echo "$GRID_COMPLETION_MESSAGE"
  echo "  raw checkpoints: $results_root"
  if [ -n "$only_label" ] || [ -n "$only_corpus" ]; then
    echo "  summary:         not updated by a partial run"
  elif [ "$run_status" -ne 0 ]; then
    echo "  summary:         not updated because one or more grid stages failed"
  else
    _grid_run_summarizer "$GRID_SUMMARIZER" "$results_root" \
      "$artifacts_dir/summary.tsv" "$artifacts_dir/analysis.md"
    _grid_write_provenance "$artifacts_dir/provenance.env" \
      "$GRID_SUMMARIZER" "$artifacts_dir/summary.tsv" "$artifacts_dir/analysis.md"
    echo "  summary:         $artifacts_dir/summary.tsv"
    echo "  analysis:        $artifacts_dir/analysis.md"
    echo "  provenance:      $artifacts_dir/provenance.env"
  fi
  return "$run_status"
)
