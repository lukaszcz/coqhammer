#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: ./evaluate.sh MODE [options]

Evaluate the CoqHammer checkout containing this eval/ directory.

Modes:
  sample       run a small current-version smoke evaluation
  library      evaluate the prepared library in problems/
  screening    compare current extraction configurations on the sample corpora
  confirmation run the full current-version extraction evaluation

sample options:
  --corpus NAME          corpus to use (required)
  --prover NAME          prover (default: eprover)
  --premise NAME         premise directory (default: knn-32)
  -j, --jobs N           parallel jobs (default: 1)

library options:
  N [MAIL]               parallel jobs and optional progress email

screening and confirmation accept the options shown by:
  ./run-screening-grid.sh --help
  ./run-confirmation-grid.sh --help

All modes build or use the current checkout. No other repository revision is
required.
USAGE
}

if [ "$#" -eq 0 ] || [ "$1" = -h ] || [ "$1" = --help ]; then
  usage
  exit 0
fi

mode="$1"
shift
repo=$(git rev-parse --show-toplevel)
eval_dir="$repo/eval"

build_current() {
  (cd "$eval_dir" && ./rebuild-config.sh current --label current)
}

case "$mode" in
  sample)
    corpus=
    prover=eprover
    premise=knn-32
    jobs=1
    while [ "$#" -gt 0 ]; do
      case "$1" in
        --corpus) corpus="$2"; shift 2 ;;
        --prover) prover="$2"; shift 2 ;;
        --premise) premise="$2"; shift 2 ;;
        -j|--jobs) jobs="$2"; shift 2 ;;
        -h|--help) usage; exit 0 ;;
        *) echo "Unknown sample option: $1" >&2; usage >&2; exit 2 ;;
      esac
    done
    if [ -z "$corpus" ]; then
      echo "sample requires --corpus" >&2
      exit 2
    fi
    build_current
    exec "$eval_dir/run-dry-sample.sh" --label current --corpus "$corpus" \
      --prover "$prover" --premise "$premise" --jobs "$jobs"
    ;;
  library)
    if [ "$#" -lt 1 ] || [ "$#" -gt 2 ]; then
      echo "library requires N and accepts an optional email address" >&2
      exit 2
    fi
    build_current
    prefix="$eval_dir/_installs/current"
    cd "$eval_dir"
    PATH="$prefix/bin:$PATH" \
    OCAMLPATH="$prefix${OCAMLPATH:+:$OCAMLPATH}" \
    COQFLAGS="-coqlib $prefix/coq${COQFLAGS:+ $COQFLAGS}" \
      exec ./run-eval.sh "$@"
    ;;
  screening)
    exec "$eval_dir/run-screening-grid.sh" "$@"
    ;;
  confirmation)
    exec "$eval_dir/run-confirmation-grid.sh" "$@"
    ;;
  *)
    echo "Unknown mode: $mode" >&2
    usage >&2
    exit 2
    ;;
esac
