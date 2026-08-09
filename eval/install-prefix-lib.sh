#!/usr/bin/env bash
# Shared ownership checks for disposable evaluation install prefixes.

EVAL_PREFIX_MARKER=.coqhammer-eval-prefix
EVAL_PREFIX_MARKER_MAGIC=coqhammer-eval-prefix-v1

eval_safe_component() {
  [[ "$1" =~ ^[A-Za-z0-9][A-Za-z0-9._-]*$ ]]
}

eval_prefix_write_marker() {
  local prefix="$1"
  printf '%s\nprefix=%s\n' "$EVAL_PREFIX_MARKER_MAGIC" "$prefix" > \
    "$prefix/$EVAL_PREFIX_MARKER"
}

eval_prefix_is_owned() {
  local prefix="$1" marker="$1/$EVAL_PREFIX_MARKER"
  [ -f "$marker" ] && [ ! -L "$marker" ] || return 1
  [ "$(wc -l < "$marker")" -eq 2 ] || return 1
  [ "$(sed -n '1p' "$marker")" = "$EVAL_PREFIX_MARKER_MAGIC" ] || return 1
  [ "$(sed -n '2p' "$marker")" = "prefix=$prefix" ]
}
