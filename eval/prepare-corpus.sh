#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: ./prepare-corpus.sh CORPUS [--sample] [--source DIR]

Populate eval/problems for one corpus.

Corpora:
  stdlib-regression       committed stdlib smoke wrappers; full stdlib problem
                          sets can also be dropped into eval/problems manually
  dependent-slice         Vector/Fin, FMapAVL/MSetAVL, Eqdep_dec, Program/WF
                          and extraction_deptypes-style fixtures
  external-equations      adapter for a local Coq-Equations checkout; without
                          --source it installs the committed Program/Equations
                          smoke sample used for harness dry-runs
USAGE
}

if [ "$#" -lt 1 ]; then
  usage >&2
  exit 2
fi

corpus="$1"
shift
sample=false
source_dir=
while [ "$#" -gt 0 ]; do
  case "$1" in
    --sample) sample=true; shift ;;
    --source) source_dir="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "Unknown argument: $1" >&2; usage >&2; exit 2 ;;
  esac
done

repo=$(git rev-parse --show-toplevel)
eval_dir="$repo/eval"
cd "$eval_dir"
rm -rf problems
mkdir -p problems

copy_committed() {
  local name="$1"
  local src="corpora/$name"
  if [ "$sample" = true ]; then
    src="$src/sample"
  fi
  if [ ! -d "$src" ]; then
    echo "Missing corpus directory: eval/$src" >&2
    exit 1
  fi
  cp -R "$src"/. problems/
}

case "$corpus" in
  stdlib-regression)
    copy_committed stdlib-regression
    ;;
  dependent-slice)
    copy_committed dependent-slice
    ;;
  external-equations)
    if [ -n "$source_dir" ]; then
      if [ ! -d "$source_dir" ]; then
        echo "External source directory not found: $source_dir" >&2
        exit 1
      fi
      mkdir -p problems/external-equations
      find "$source_dir" \( -path '*/_build' -o -path '*/.git' \) -prune -o -name '*.v' -print | while IFS= read -r file; do
        rel=${file#"$source_dir"/}
        mkdir -p "problems/external-equations/$(dirname "$rel")"
        cp "$file" "problems/external-equations/$rel"
      done
      if [ -f "$source_dir/_CoqProject" ]; then
        sed -n '/^-Q /p; /^-R /p; /^-I /p' "$source_dir/_CoqProject" > problems/external-equations.conf || true
      fi
    else
      copy_committed external-equations
    fi
    ;;
  *) echo "Unknown corpus: $corpus" >&2; usage >&2; exit 2 ;;
esac

find problems -name '*.v' -print | sort
