#!/usr/bin/env bash
# Shared command-line parsing helpers for the eval driver scripts.
#
# Kept out of grid-checkpoint-lib.sh on purpose: that file's hash is recorded in
# every grid checkpoint as provenance, so editing it invalidates stored results.

# Every long option in these scripts takes a value.  Without this guard a
# trailing "--label" would bind the empty string and the following "shift 2"
# would fail with an opaque error instead of the usage message.  The caller
# defines usage() before parsing.
need_value() {
  if [ "$#" -lt 2 ]; then
    echo "Missing value for $1" >&2
    usage >&2
    exit 2
  fi
}
