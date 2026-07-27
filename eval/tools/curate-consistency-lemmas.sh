#!/usr/bin/env bash
# Curate a consistency lemma list from a corpus's generated ATP problems.
#
# The false-conjecture check expects the axioms of a goal to be satisfiable.
# The goal's own hypotheses are among those axioms, so a vacuously true lemma
# is refutable however faithful the translation is.  Rather than guess which
# lemmas those are, replace each conjecture with $false, run the prover, and
# keep only the lemmas that survive.
#
# Curation deliberately uses a longer timeout than the check itself: a lemma
# whose refutation needs more time than the check allows would pass here and
# fire later, so the margin is what makes the resulting list stable.
#
# Usage: curate-consistency-lemmas.sh PROBLEM_DIR OUT_FILE [CURATE_TIM] [LIMIT]
set -euo pipefail

problem_dir=${1:?problem dir}
out_file=${2:?output file}
curate_tim=${3:-10}
limit=${4:-0}

work=$(mktemp -d "${TMPDIR:-/tmp}/curate-lemmas.XXXXXX")
trap 'rm -rf "$work"' EXIT HUP INT TERM

mkdir -p "$work/problems"
python3 - "$problem_dir" "$work/problems" <<'PY'
import pathlib, re, sys
src = pathlib.Path(sys.argv[1]); dst = pathlib.Path(sys.argv[2])
for path in sorted(src.glob('*.p')):
    text = path.read_text()
    text, n = re.subn(r"fof\(([^,]+),\s*conjecture,\s*.*?\)\.\s*$",
                      r"fof(\1, conjecture, $false).", text, count=1, flags=re.M)
    if n == 1:
        (dst / path.name).write_text(text)
PY

jobs=$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 4)
# The check runs both provers, so a lemma has to survive both to be listed:
# one of them refuting is enough to fail a real run.
run_one() {
  local p="$1" name eout vout
  name=$(basename "$p" .p)
  eout=$(eprover -s --cpu-limit="$curate_tim" --auto-schedule -R --print-statistics \
         -p --tstp-format "$p" 2>&1 | grep -E "SZS status" | head -1 || true)
  vout=$(htimeout "$((curate_tim + 5))" vampire --mode casc -t "$curate_tim" --proof tptp \
         --output_axiom_names on "$p" 2>&1 | grep -E "SZS status" | tail -1 || true)
  case "$eout$vout" in
    *ContradictoryAxioms*|*"status Theorem"*|*Unsatisfiable*) echo "VACUOUS $name" ;;
    *) if [ -z "$eout" ] || [ -z "$vout" ]; then echo "NORESULT $name"; else echo "KEEP $name"; fi ;;
  esac
}
export -f run_one
export curate_tim

# NUL-delimit the file list: some lemma names contain a single quote (e.g.
# small_drinkers'_paradox), which the default whitespace/quote-processing xargs
# rejects with "unmatched single quote".  -print0 | xargs -0 passes each path
# verbatim; head -z keeps the optional limit NUL-aware.
{ [ "$limit" -gt 0 ] && find "$work/problems" -name '*.p' -print0 | head -z -n "$limit" \
    || find "$work/problems" -name '*.p' -print0; } |
  xargs -0 -P "$jobs" -I{} bash -c 'run_one "$@"' _ {} > "$work/verdicts.txt"

echo "kept:     $(grep -c '^KEEP ' "$work/verdicts.txt" || true)"
echo "vacuous:  $(grep -c '^VACUOUS ' "$work/verdicts.txt" || true)"
echo "noresult: $(grep -c '^NORESULT ' "$work/verdicts.txt" || true)"

grep '^KEEP ' "$work/verdicts.txt" | awk '{print $2}' | sort > "$out_file.kept"
grep '^VACUOUS ' "$work/verdicts.txt" | awk '{print $2}' | sort > "$out_file.vacuous"
echo "wrote $out_file.kept and $out_file.vacuous"
