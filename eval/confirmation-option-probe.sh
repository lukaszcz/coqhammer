#!/usr/bin/env bash
# Probe premise-selection option values from a confirmation-grid install.

confirmation_parse_option_value() {
  local output="$1" option="$2"
  awk -v option="$option" '
    BEGIN {
      current = "Current value of Hammer " option
      plain = "Hammer " option
    }
    {
      line = $0
      sub(/\r$/, "", line)
      gsub(/[[:space:]]+/, " ", line)
      sub(/^ /, "", line)
      sub(/ $/, "", line)
      if (index(line, current) == 1)
        rest = substr(line, length(current) + 1)
      else if (index(line, plain) == 1)
        rest = substr(line, length(plain) + 1)
      else
        next
      if (rest ~ /^ is /)
        value = substr(rest, 5)
      else if (rest ~ /^ [:=] /)
        value = substr(rest, 4)
      else
        next
      sub(/[.]$/, "", value)
      if (value !~ /^[0-9]+$/)
        next
      found++
      result = value
    }
    END {
      if (found != 1)
        exit 1
      print result
    }
  ' "$output"
}

confirmation_set_publication_mode() {
  local temporary="$1" reference="$2" mask mode
  if [ -e "$reference" ]; then
    chmod --reference="$reference" "$temporary"
  else
    mask=$(umask)
    printf -v mode '%03o' "$((8#666 & ~(8#$mask)))"
    chmod "$mode" "$temporary"
  fi
}

confirmation_record_hammer_options() (
  local manifest="$1" probe_digest="$2" premises="$3" features="$4" temporary=
  trap 'rm -f -- "$temporary"' EXIT
  trap 'exit 129' HUP
  trap 'exit 130' INT
  trap 'exit 143' TERM

  temporary=$(mktemp "$manifest.tmp.XXXXXX") || return 1
  if ! {
      awk -F= '
        $1 != "option_probe_sha256" &&
        $1 != "definition_premises" &&
        $1 != "definition_features"
      ' "$manifest" &&
      printf '%s\n' \
        "option_probe_sha256=$probe_digest" \
        "definition_premises=$premises" \
        "definition_features=$features"
    } > "$temporary"; then
    return 1
  fi
  confirmation_set_publication_mode "$temporary" "$manifest" || return 1
  mv -- "$temporary" "$manifest" || return 1
  temporary=
  trap - EXIT HUP INT TERM
)

_confirmation_probe_hammer_options() (
  local prefix="$1" temporary='' output premises features
  trap 'rm -rf -- "$temporary"' EXIT
  trap 'exit 129' HUP
  trap 'exit 130' INT
  trap 'exit 143' TERM

  temporary=$(mktemp -d "${TMPDIR:-/tmp}/coqhammer-option-probe.XXXXXX") || return 1
  output="$temporary/output"
  printf '%s\n' \
    'Test Hammer DefinitionPremises.' \
    'Test Hammer DefinitionFeatures.' > "$temporary/options.v" || return 1

  if ! LC_ALL=C PATH="$prefix/bin:$PATH" \
      OCAMLPATH="$prefix${OCAMLPATH:+:$OCAMLPATH}" \
      rocq c -q -coqlib "$prefix/coq" -require Hammer.Plugin.Hammer \
      "$temporary/options.v" > "$output" 2>&1; then
    echo "Could not probe Hammer premise-selection options in $prefix:" >&2
    cat "$output" >&2
    return 1
  fi
  if ! premises=$(confirmation_parse_option_value "$output" DefinitionPremises) ||
      ! features=$(confirmation_parse_option_value "$output" DefinitionFeatures); then
    echo "Could not parse Hammer premise-selection options in $prefix:" >&2
    cat "$output" >&2
    return 1
  fi
  printf '%s\n' "$premises" "$features"
)

confirmation_probe_hammer_options() {
  local prefix="$1" values
  values=$(_confirmation_probe_hammer_options "$prefix") || return 1
  mapfile -t values <<< "$values"
  [ "${#values[@]}" -eq 2 ] || return 1

  # Read by run-confirmation-grid.sh after this function returns.
  # shellcheck disable=SC2034
  CONFIRMATION_DEFINITION_PREMISES=${values[0]}
  # shellcheck disable=SC2034
  CONFIRMATION_DEFINITION_FEATURES=${values[1]}
}

# The checkpoint option fields are centralized so every stage uses the same
# ordering and no stage can accidentally omit one half of this provenance.
# shellcheck disable=SC2154
confirmation_checkpoint_done() {
  local marker="$1" stage="$2" label="$3" corpus="$4" prefix="$5"
  shift 5
  checkpoint_done "$marker" "$stage" "$label" "$corpus" "$prefix" \
    "option_probe_sha256=$option_probe_digest" \
    "definition_premises=${label_definition_premises[$label]}" \
    "definition_features=${label_definition_features[$label]}" "$@"
}

# shellcheck disable=SC2154
confirmation_mark_checkpoint() {
  local marker="$1" stage="$2" label="$3" corpus="$4" prefix="$5"
  shift 5
  mark_checkpoint "$marker" "$stage" "$label" "$corpus" "$prefix" \
    "option_probe_sha256=$option_probe_digest" \
    "definition_premises=${label_definition_premises[$label]}" \
    "definition_features=${label_definition_features[$label]}" "$@"
}

# Atomically add confirmation-only fields to the shared grid provenance. The
# subshell keeps cleanup traps private to callers and also catches the shared
# writer's intermediate file if it fails before publishing its output.
# shellcheck disable=SC2154
confirmation_publish_final_provenance() (
  local output="$1" grid_name="$2" summarizer="$3" summary="$4" analysis="$5"
  local probe_digest="$6" temporary='' nested_temporary='' label
  trap 'rm -f -- "$temporary" "$nested_temporary"' EXIT
  trap 'exit 129' HUP
  trap 'exit 130' INT
  trap 'exit 143' TERM

  temporary=$(mktemp "$output.tmp.XXXXXX") || return 1
  nested_temporary="$temporary.tmp.$$"
  write_grid_provenance "$temporary" "$grid_name" \
    "$summarizer" "$summary" "$analysis" || return 1
  printf '%s\n' "option_probe_sha256=$probe_digest" >> "$temporary" || return 1
  for label in "${labels[@]}"; do
    printf '%s\n' \
      "label.$label.definition_premises=${label_definition_premises[$label]}" \
      "label.$label.definition_features=${label_definition_features[$label]}" \
      >> "$temporary" || return 1
  done
  confirmation_set_publication_mode "$temporary" "$output" || return 1
  mv -- "$temporary" "$output" || return 1
  temporary=
  trap - EXIT HUP INT TERM
)
