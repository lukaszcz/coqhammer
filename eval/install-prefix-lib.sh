#!/usr/bin/env bash
# Shared ownership checks for disposable evaluation install prefixes.

EVAL_PREFIX_MARKER=.coqhammer-eval-prefix
EVAL_PREFIX_MARKER_MAGIC=coqhammer-eval-prefix-v1

eval_safe_component() {
  [[ "$1" =~ ^[A-Za-z0-9][A-Za-z0-9._-]*$ ]]
}

# The marker records the path it was written for on a line of its own, so a
# prefix spelled with a newline cannot be read back: its marker would carry an
# extra line and eval_prefix_is_owned would disown the very directory that
# wrote it, leaving every later run unable to erase a prefix it created.  Such
# a path is not usable here; callers reject it before erasing anything.
eval_prefix_path_is_markable() {
  case "$1" in
    *$'\n'*) return 1 ;;
  esac
}

eval_prefix_write_marker() {
  local prefix="$1"
  eval_prefix_path_is_markable "$prefix" || return 1
  printf '%s\nprefix=%s\n' "$EVAL_PREFIX_MARKER_MAGIC" "$prefix" > \
    "$prefix/$EVAL_PREFIX_MARKER"
}

eval_prefix_is_owned() {
  local prefix="$1" marker="$1/$EVAL_PREFIX_MARKER"
  eval_prefix_path_is_markable "$prefix" || return 1
  [ -f "$marker" ] && [ ! -L "$marker" ] || return 1
  [ "$(wc -l < "$marker")" -eq 2 ] || return 1
  [ "$(sed -n '1p' "$marker")" = "$EVAL_PREFIX_MARKER_MAGIC" ] || return 1
  [ "$(sed -n '2p' "$marker")" = "prefix=$prefix" ]
}
