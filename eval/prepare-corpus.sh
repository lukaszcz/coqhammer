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
  dependent-stdlib        the dependently typed stdlib modules (Logic,
                          Wellfounded, MSets, Structures, Sorting, Program);
                          override with --modules or DEPENDENT_STDLIB_MODULES
  stdpp                   installed rocq-stdpp: fin/vec and the Decision and
                          Countable typeclass hierarchies
  color-vector            CoLoR/Util/Vector, length-indexed Vector.t lemmas
  dependent-slice         Vector/Fin, FMapAVL/MSetAVL, Eqdep_dec, Program/WF
                          and extraction_deptypes-style fixtures
  equations-examples      the Equations examples/, which rocq-equations does not
                          install; defaults to the built checkout under
                          eval/_external, override with --source
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
# --modules names the slice of whichever stdlib corpus was asked for, so it
# overrides the defaults of both rather than only the regression one.
modules_override=
# Default stdlib slice: broad enough for per-prover and per-premise rates to
# mean something, and biased towards the inductive and dependent material the
# translation work targets.  Override with --modules or STDLIB_CORPUS_MODULES.
stdlib_modules=${STDLIB_CORPUS_MODULES:-"Arith Bool Vectors Lists NArith"}
# The stdlib modules that lean hardest on dependent types: equality on indexed
# families, well-founded recursion, the module-functor container hierarchies and
# Program's subset types.  Kept apart from the regression slice above so that
# "does the translation still work broadly" and "does it work on dependent
# material" stay separately answerable rather than averaged together.
dependent_stdlib_modules=${DEPENDENT_STDLIB_MODULES:-"Logic Wellfounded MSets Structures Sorting Program"}
while [ "$#" -gt 0 ]; do
  case "$1" in
    --sample) sample=true; shift ;;
    --source) source_dir="$2"; shift 2 ;;
    --coqlib) coqlib="$2"; shift 2 ;;
    --modules) modules_override="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "Unknown argument: $1" >&2; usage >&2; exit 2 ;;
  esac
done

stdlib_modules=${modules_override:-$stdlib_modules}
dependent_stdlib_modules=${modules_override:-$dependent_stdlib_modules}

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

# Build a corpus from a library already installed in the switch.  An installed
# library ships each .glob beside its .v, which is all coqnames needs to place
# the hammer_hook calls, so none of these need the library rebuilt.  Generating
# from the installed copy also keeps a corpus in step with the libraries the
# evaluation actually runs against, instead of committing a snapshot that
# silently drifts.
#
# $lib is the library directory under user-contrib, $dest the subtree of
# problems to fill, and $require_proofs is passed through to
# copy_hookable_sources.  The remaining arguments name subtrees of the library
# to take; passing none takes the whole library.
build_installed_corpus() {
  local lib="$1" dest="$2" require_proofs="$3"
  shift 3
  local lib_dir="$coqlib/user-contrib/$lib" subtree
  if [ ! -d "$lib_dir" ]; then
    echo "Installed library not found: $lib_dir" >&2
    echo "Install it into the switch, or pass --coqlib DIR pointing at the" >&2
    echo "Rocq library directory." >&2
    exit 1
  fi
  mkdir -p "$dest"
  if [ "$#" -eq 0 ]; then
    copy_hookable_sources "$lib_dir" "$lib_dir" "$dest" "$require_proofs"
  else
    for subtree in "$@"; do
      if [ ! -d "$lib_dir/$subtree" ]; then
        echo "Library subtree not found: $lib_dir/$subtree" >&2
        exit 1
      fi
      copy_hookable_sources "$lib_dir" "$lib_dir/$subtree" "$dest" "$require_proofs"
    done
  fi
  apply_exclusions "$corpus" "$dest"
  require_hookable_sources "$lib_dir"
  insert_hooks
}

insert_hooks() {
  (cd problems && "$eval_dir/tools/mkhooks.sh" > /dev/null 2>&1)
  # rmcomments leaves a .bak beside every rewritten file; they are not sources.
  find problems -name '*.v.bak' -delete
}

# Copy the sources that can actually be hooked.  coqnames reads the module
# prefix and the theorem names out of the .glob beside each .v, so a source
# without one contributes compile time and no goals.  Paths under $dest keep
# their layout relative to $root, while $start selects the subtree to walk, so
# a corpus can take part of a library without flattening it.  With
# $require_proofs, a .glob must also declare a proof: that skips the interface
# modules which only Register their own fully qualified names, which cannot
# resolve in a corpus compiled with no logical path mapping.
copy_hookable_sources() {
  local root="$1" start="$2" dest="$3" require_proofs="${4:-false}"
  # -L because an installed library is reached through a symlink in the
  # evaluation prefix, and find does not descend into a symlinked directory
  # named as its own starting point.
  find -L "$start" \( -name '_build' -o -name '.git' \) -prune -o -name '*.v' -print |
    while IFS= read -r file; do
      local rel glob
      rel=${file#"$root"/}
      glob="${file%.v}.glob"
      [ -f "$glob" ] || continue
      if [ "$require_proofs" = true ]; then
        grep -q '^prf ' "$glob" || continue
      fi
      mkdir -p "$dest/$(dirname "$rel")"
      cp "$file" "$dest/$rel"
      cp "$glob" "$dest/${rel%.v}.glob"
      # A corpus is rewritten in place by mkhooks and then compiled in place,
      # which overwrites the .glob.  cp preserves the source mode, and a dune
      # build tree marks its artifacts read-only, so the copy has to be made
      # writable or the compilation fails on its own .glob.
      chmod u+w "$dest/$rel" "$dest/${rel%.v}.glob"
    done
}

# Drop the sources that import a sibling of the same corpus.  The evaluation
# Makefile compiles the problem files independently and in random order, with no
# coqdep pass, so a file is only ever compiled against the installed libraries:
# one that needs a sibling's .vo cannot be ordered after it and would fail
# whatever logical path it were given.  A library taken from user-contrib never
# trips this, because its own Requires resolve to the installed copy; a corpus
# taken from a build tree, which is not installed anywhere, does.
drop_intra_corpus_dependents() {
  local dir="$1" file modules=
  for file in "$dir"/*.v; do
    [ -e "$file" ] || continue
    modules="$modules $(basename "$file" .v)"
  done
  local module
  for file in "$dir"/*.v; do
    [ -e "$file" ] || continue
    for module in $modules; do
      [ "$(basename "$file" .v)" = "$module" ] && continue
      if grep -qE "(^|[[:space:]])(Require|Import|Export)([[:space:]]+[A-Za-z_.]+)*[[:space:]]+[A-Za-z_.]*\\b$module\\b" "$file"; then
        rm -f "$file" "${file%.v}.glob"
        break
      fi
    done
  done
}

# Drop the sources listed in the corpus's excluded.txt.  A corpus file is
# compiled on its own against the installed libraries, which for a library taken
# from user-contrib means it is compiled alongside the installed copy of itself:
# its definitions and instances are then present twice, and a proof whose
# tactics depend on the exact shape of a goal can break.  Such a file fails
# before the hammer runs at all, so it measures nothing and would only be noise
# in the grid.  Excluding it is a statement about the corpus, so it is recorded
# in the tree and reported here rather than being dropped quietly.
apply_exclusions() {
  local corpus="$1" dest="$2" list="corpora/$corpus/excluded.txt" rel dropped=0
  [ -f "$list" ] || return 0
  while IFS= read -r rel; do
    case "$rel" in ''|'#'*) continue ;; esac
    if [ -f "$dest/$rel" ]; then
      rm -f "$dest/$rel" "$dest/${rel%.v}.glob"
      dropped=$((dropped + 1))
    else
      echo "Stale entry in $list: $rel" >&2
      exit 1
    fi
  done < "$list"
  echo "Excluded $dropped source(s) listed in $list" >&2
}

# A corpus with no hookable source is a corpus with no goals, and the usual
# cause is a checkout that was never built: .glob files appear only after
# compilation.  Say so rather than letting the run proceed to an empty grid.
require_hookable_sources() {
  local where="$1"
  if [ -z "$(find problems -name '*.v' -print -quit)" ]; then
    echo "No sources with .glob files found under $where" >&2
    echo "A .glob is produced by compiling a file, so build the library or" >&2
    echo "checkout first; without one there are no theorem names to hook." >&2
    exit 1
  fi
}

# stdlib-regression, dependent-slice and external-equations are the only
# corpora with a committed eval/corpora/<name>/sample fixture; the rest are
# always built from an installed library or an external checkout, so a
# --sample request for them would otherwise be silently ignored and the full
# corpus built instead, contradicting what --sample promises.  Fail loudly
# rather than let that mismatch pass unnoticed.
case "$corpus" in
  dependent-stdlib|stdpp|color-vector|equations-examples)
    if [ "$sample" = true ]; then
      echo "No committed sample for corpus '$corpus': it is always built from" >&2
      echo "an installed library or checkout, not eval/corpora/$corpus/sample." >&2
      exit 1
    fi
    ;;
esac

case "$corpus" in
  stdlib-regression)
    if [ "$sample" = true ]; then
      copy_committed stdlib-regression
    else
      build_installed_corpus Stdlib problems false $stdlib_modules
    fi
    ;;
  dependent-stdlib)
    build_installed_corpus Stdlib problems false $dependent_stdlib_modules
    ;;
  stdpp)
    build_installed_corpus stdpp problems/stdpp true
    ;;
  color-vector)
    build_installed_corpus CoLoR problems/CoLoR true Util/Vector
    ;;
  dependent-slice)
    copy_committed dependent-slice
    ;;
  equations-examples)
    if [ -z "$source_dir" ]; then
      source_dir="$eval_dir/_external/Coq-Equations/_build/default/examples"
    fi
    if [ ! -d "$source_dir" ]; then
      echo "Equations examples not found: $source_dir" >&2
      echo "The examples are not installed by rocq-equations; build the" >&2
      echo "checkout (dune build) so its .glob files exist, or pass --source." >&2
      exit 1
    fi
    mkdir -p problems/equations-examples
    copy_hookable_sources "$source_dir" "$source_dir" problems/equations-examples true
    apply_exclusions "$corpus" problems/equations-examples
    require_hookable_sources "$source_dir"
    drop_intra_corpus_dependents problems/equations-examples
    insert_hooks
    ;;
  external-equations)
    if [ -n "$source_dir" ]; then
      if [ ! -d "$source_dir" ]; then
        echo "External source directory not found: $source_dir" >&2
        exit 1
      fi
      mkdir -p problems/external-equations
      copy_hookable_sources "$source_dir" "$source_dir" problems/external-equations true
      require_hookable_sources "$source_dir"
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
      insert_hooks
    elif [ "$sample" = true ]; then
      copy_committed external-equations
    else
      build_installed_corpus Equations problems/Equations true
    fi
    ;;
  *) echo "Unknown corpus: $corpus" >&2; usage >&2; exit 2 ;;
esac

find problems -name '*.v' -print | sort
