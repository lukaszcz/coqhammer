#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: ./prepare-corpus.sh CORPUS [--sample] [--source DIR] [--coqlib DIR]
                           [--modules "Mod1 Mod2 ..."]

Populate eval/problems for one corpus.

Options:
  --sample                use the small committed smoke sample instead of
                          building the full corpus
  --coqlib DIR            Rocq library directory (default: rocq c -where)
  --modules "A B"         Stdlib modules for stdlib-regression
                          (default: Arith Bool Vectors Lists NArith)

Corpora:
  stdlib-regression       hammer_hook corpus built from the installed Rocq
                          standard library; --sample selects the committed
                          smoke wrappers instead
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
coqlib=
# Default stdlib slice: broad enough for per-prover and per-premise rates to
# mean something, and biased towards the inductive and dependent material the
# translation work targets.  Override with --modules or STDLIB_CORPUS_MODULES.
stdlib_modules=${STDLIB_CORPUS_MODULES:-"Arith Bool Vectors Lists NArith"}
while [ "$#" -gt 0 ]; do
  case "$1" in
    --sample) sample=true; shift ;;
    --source) source_dir="$2"; shift 2 ;;
    --coqlib) coqlib="$2"; shift 2 ;;
    --modules) stdlib_modules="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "Unknown argument: $1" >&2; usage >&2; exit 2 ;;
  esac
done

if [ -z "$coqlib" ]; then
  coqlib=$(rocq c -where 2>/dev/null || true)
fi

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

# Build a corpus from the installed Rocq standard library.  The installed
# library ships each .glob beside its .v, which is all coqnames needs to place
# the hammer_hook calls, so this needs no stdlib rebuild.  Generating from the
# installed library also keeps the corpus in step with the Rocq the evaluation
# actually runs against, instead of committing a snapshot that silently drifts.
build_stdlib_corpus() {
  local stdlib_dir="$coqlib/user-contrib/Stdlib"
  local module count
  if [ ! -d "$stdlib_dir" ]; then
    echo "Installed Stdlib not found: $stdlib_dir" >&2
    echo "Pass --coqlib DIR pointing at the Rocq library directory." >&2
    exit 1
  fi
  for module in $stdlib_modules; do
    if [ ! -d "$stdlib_dir/$module" ]; then
      echo "Stdlib module directory not found: $stdlib_dir/$module" >&2
      exit 1
    fi
    mkdir -p "problems/$module"
    find -L "$stdlib_dir/$module" -name '*.v' -print | while IFS= read -r file; do
      local rel base glob
      rel=${file#"$stdlib_dir"/}
      base=${file%.v}
      glob="$base.glob"
      # Without the .glob there are no theorem names to hook, so the file would
      # contribute nothing but compile time.
      [ -f "$glob" ] || continue
      mkdir -p "problems/$(dirname "$rel")"
      cp "$file" "problems/$rel"
      cp "$glob" "problems/${rel%.v}.glob"
    done
  done
  count=$(find problems -name '*.v' | wc -l)
  if [ "$count" -eq 0 ]; then
    echo "No stdlib sources with .glob files found under $stdlib_dir" >&2
    exit 1
  fi
  insert_hooks
}

# Same trick as the stdlib corpus: the installed Equations library ships its
# .glob files, so its own sources can be hooked without rebuilding it.
build_equations_corpus() {
  local lib_dir="$coqlib/user-contrib/Equations"
  if [ ! -d "$lib_dir" ]; then
    echo "Installed Equations library not found: $lib_dir" >&2
    echo "Install rocq-equations into the switch, or pass --source DIR." >&2
    exit 1
  fi
  mkdir -p problems/Equations
  # -L because the installed library is reached through a symlink in the
  # evaluation prefix, and find does not descend into a symlinked directory
  # named as its own starting point.
  find -L "$lib_dir" -name '*.v' -print | while IFS= read -r file; do
    local rel base glob
    rel=${file#"$lib_dir"/}
    base=${file%.v}
    glob="$base.glob"
    [ -f "$glob" ] || continue
    # Files with no theorems contribute no goals, only compile time -- and the
    # library's interface modules are exactly the ones that Register their own
    # fully qualified names (Equations.Signature.Signature and friends), which
    # cannot resolve here because the corpus is compiled with no logical path
    # mapping.  Skipping them drops nothing measurable.
    grep -q '^prf ' "$glob" || continue
    mkdir -p "problems/Equations/$(dirname "$rel")"
    cp "$file" "problems/Equations/$rel"
    cp "$glob" "problems/Equations/${rel%.v}.glob"
  done
  if [ -z "$(find problems -name '*.v' -print -quit)" ]; then
    echo "No Equations sources with .glob files found under $lib_dir" >&2
    exit 1
  fi
  insert_hooks
}

insert_hooks() {
  (cd problems && "$eval_dir/tools/mkhooks.sh" > /dev/null 2>&1)
  # rmcomments leaves a .bak beside every rewritten file; they are not sources.
  find problems -name '*.v.bak' -delete
}

case "$corpus" in
  stdlib-regression)
    if [ "$sample" = true ]; then
      copy_committed stdlib-regression
    else
      build_stdlib_corpus
    fi
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
        awk '
          function relocated(path) {
            if (path ~ /^\//) return path
            return "problems/external-equations/" path
          }
          $1 == "-Q" && NF >= 3 { print $1, relocated($2), $3; next }
          $1 == "-R" && NF >= 3 { print $1, relocated($2), $3; next }
          $1 == "-I" && NF >= 2 { print $1, relocated($2); next }
        ' "$source_dir/_CoqProject" > problems/external-equations.conf || true
      fi
    elif [ "$sample" = true ]; then
      copy_committed external-equations
    else
      build_equations_corpus
    fi
    ;;
  *) echo "Unknown corpus: $corpus" >&2; usage >&2; exit 2 ;;
esac

find problems -name '*.v' -print | sort
