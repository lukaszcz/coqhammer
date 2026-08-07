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
  local p="$1" name eout vout e_ok v_ok
  name=$(basename "$p" .p)
  eout=$(eprover -s --cpu-limit="$curate_tim" --auto-schedule -R --print-statistics \
         -p --tstp-format "$p" 2>&1 | grep -E "SZS status" | head -1 || true)
  vout=$(htimeout "$((curate_tim + 5))" vampire --mode casc -t "$curate_tim" --proof tptp \
         --output_axiom_names on "$p" 2>&1 | grep -E "SZS status" | tail -1 || true)
  case "$eout$vout" in
    *ContradictoryAxioms*|*"status Theorem"*|*Unsatisfiable*) echo "VACUOUS $name" ;;
    *)
      # KEEP requires a conclusive satisfiability verdict from both provers;
      # timeouts and other inconclusive statuses (ResourceOut, GaveUp, ...)
      # must not let a possibly-vacuous lemma slip into the consistency list.
      # Matches both Satisfiable and CounterSatisfiable; the outer case
      # already ruled out Unsatisfiable and Theorem for this branch.
      case "$eout" in *Satisfiable*) e_ok=1 ;; *) e_ok=0 ;; esac
      case "$vout" in *Satisfiable*) v_ok=1 ;; *) v_ok=0 ;; esac
      if [ "$e_ok" = 1 ] && [ "$v_ok" = 1 ]; then echo "KEEP $name"; else echo "NORESULT $name"; fi
      ;;
  esac
}
export -f run_one
export curate_tim

# NUL-delimit the file list: some lemma names contain a single quote (e.g.
# small_drinkers'_paradox), which the default whitespace/quote-processing xargs
# rejects with "unmatched single quote".  -print0 | xargs -0 passes each path
# verbatim; head -z keeps the optional limit NUL-aware.
#
# In the limited case "head -z -n limit" exits as soon as it has read enough,
# and "find" then dies of SIGPIPE on its next write; under pipefail that failure
# would propagate and abort the whole bounded run.  Draining the rest of find's
# output with "cat" after head returns keeps the producer's pipe open, so find
# finishes normally and the pipeline succeeds.
if [ "$limit" -gt 0 ]; then
  find "$work/problems" -name '*.p' -print0 | { head -z -n "$limit"; cat >/dev/null; }
else
  find "$work/problems" -name '*.p' -print0
fi |
  xargs -0 -P "$jobs" -I{} bash -c 'run_one "$@"' _ {} > "$work/verdicts.txt"

echo "kept:     $(grep -c '^KEEP ' "$work/verdicts.txt" || true)"
echo "vacuous:  $(grep -c '^VACUOUS ' "$work/verdicts.txt" || true)"
echo "noresult: $(grep -c '^NORESULT ' "$work/verdicts.txt" || true)"

grep '^KEEP ' "$work/verdicts.txt" | awk '{print $2}' | sort > "$out_file"
grep '^VACUOUS ' "$work/verdicts.txt" | awk '{print $2}' | sort > "$out_file.vacuous"
echo "wrote $out_file and $out_file.vacuous"
