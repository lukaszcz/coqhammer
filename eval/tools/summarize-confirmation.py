#!/usr/bin/env python3
"""Summarize extraction confirmation checkpoints."""

from __future__ import annotations

import csv
import re
import statistics
import sys
from collections import defaultdict
from pathlib import Path

PREMISES = (
    "knn-32",
    "knn-64",
    "knn-128",
    "knn-256",
    "knn-1024",
    "nbayes-32",
    "nbayes-64",
    "nbayes-128",
    "nbayes-256",
    "nbayes-1024",
)
PROVERS = ("eprover", "vampire", "z3", "cvc4")
CONSISTENCY_PROVERS = ("eprover", "vampire")
CORPORA = ("stdlib-regression", "dependent-slice", "external-equations")
BASELINE = "baseline-merge-base"
WINNER = "selected-config"


def read_list(path: Path) -> list[Path]:
    if not path.exists():
        return []
    return [Path(line.strip()) for line in path.read_text().splitlines() if line.strip()]


def has_atp_theorem(path: Path) -> bool:
    try:
        text = path.read_text(errors="replace")
    except FileNotFoundError:
        return False
    return "SZS status Theorem" in text


def status_theorem_count(files: list[Path]) -> int:
    return sum(1 for path in files if has_atp_theorem(path))


def reconstr_success_count(files: list[Path]) -> int:
    count = 0
    for path in files:
        try:
            text = path.read_text(errors="replace")
        except FileNotFoundError:
            continue
        if text.startswith("Success "):
            count += 1
    return count


def def_base(name: str) -> str | None:
    if not name.startswith("$_def_"):
        return None
    rest = name[len("$_def_") :]
    if rest.startswith("$"):
        return None
    return rest.split("$", 1)[0]


def problem_metrics(files: list[Path]) -> tuple[set[str], int, float, int, float, int]:
    defs: set[str] = set()
    total_bytes = 0
    total_lines = 0
    max_bytes = 0
    max_lines = 0
    axiom_re = re.compile(r"^fof\('([^']+)'\s*,\s*axiom,", re.M)
    for path in files:
        try:
            text = path.read_text(errors="replace")
        except FileNotFoundError:
            continue
        size = len(text.encode())
        lines = text.count("\n") + (0 if text.endswith("\n") else 1)
        total_bytes += size
        total_lines += lines
        max_bytes = max(max_bytes, size)
        max_lines = max(max_lines, lines)
        for match in axiom_re.finditer(text):
            base = def_base(match.group(1))
            if base:
                defs.add(base)
    n = max(len(files), 1)
    return defs, total_bytes, total_bytes / n, max_bytes, total_lines / n, max_lines


def reconstr_files(corpus_dir: Path, prover: str, premise: str, generated: list[Path]) -> list[Path]:
    odir = corpus_dir / "reconstr-outputs" / f"{prover}-{premise}"
    return [odir / Path(path).name.replace(".p", ".out") for path in generated]


def load_rows(root: Path) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for label_dir in sorted(p for p in root.iterdir() if p.is_dir()):
        label = label_dir.name
        config = "baseline" if label == BASELINE else "loo-erasure-guards-decl-skips"
        for corpus in CORPORA:
            corpus_dir = label_dir / corpus
            if not corpus_dir.exists():
                continue
            for premise in PREMISES:
                generated = read_list(corpus_dir / f"generated-{premise}.lst")
                defs, total_bytes, avg_bytes, max_bytes, avg_lines, max_lines = problem_metrics(generated)
                for prover in PROVERS:
                    prover_outputs = read_list(corpus_dir / f"prover-outputs-{prover}-{premise}.lst")
                    theorems = status_theorem_count(prover_outputs)
                    rfiles = reconstr_files(corpus_dir, prover, premise, generated)
                    recon_successes = reconstr_success_count(rfiles)
                    if prover in CONSISTENCY_PROVERS:
                        consistency_outputs = read_list(corpus_dir / f"consistency-outputs-{prover}-{premise}.lst")
                    else:
                        consistency_outputs = []
                    consistency_hits = status_theorem_count(consistency_outputs)
                    generated_n = len(generated)
                    rows.append(
                        {
                            "label": label,
                            "config": config,
                            "corpus": corpus,
                            "premise": premise,
                            "prover": prover,
                            "generated": generated_n,
                            "theorems": theorems,
                            "success_rate": (theorems / generated_n) if generated_n else 0.0,
                            "recon_successes": recon_successes,
                            "recon_rate_on_atp": (recon_successes / theorems) if theorems else 0.0,
                            "def_constants": len(defs),
                            "def_constant_names": defs,
                            "total_bytes": total_bytes,
                            "avg_bytes": avg_bytes,
                            "max_bytes": max_bytes,
                            "avg_lines": avg_lines,
                            "max_lines": max_lines,
                            "consistency_outputs": len(consistency_outputs),
                            "consistency_hits": consistency_hits,
                        }
                    )
    return rows


def write_tsv(rows: list[dict[str, object]], out: Path) -> None:
    out.parent.mkdir(parents=True, exist_ok=True)
    fieldnames = [
        "label",
        "config",
        "corpus",
        "premise",
        "prover",
        "generated",
        "theorems",
        "success_rate",
        "recon_successes",
        "recon_rate_on_atp",
        "def_constants",
        "total_bytes",
        "avg_bytes",
        "max_bytes",
        "avg_lines",
        "max_lines",
        "consistency_outputs",
        "consistency_hits",
    ]
    with out.open("w", newline="") as f:
        writer = csv.DictWriter(f, delimiter="\t", fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            formatted = {k: row[k] for k in fieldnames}
            formatted["success_rate"] = f"{row['success_rate']:.6f}"
            formatted["recon_rate_on_atp"] = f"{row['recon_rate_on_atp']:.6f}"
            formatted["avg_bytes"] = f"{row['avg_bytes']:.1f}"
            formatted["avg_lines"] = f"{row['avg_lines']:.1f}"
            writer.writerow(formatted)


def aggregate(rows: list[dict[str, object]], *keys: str) -> list[dict[str, object]]:
    groups: dict[tuple[object, ...], list[dict[str, object]]] = defaultdict(list)
    for row in rows:
        groups[tuple(row[k] for k in keys)].append(row)
    out = []
    for key, rs in sorted(groups.items()):
        generated = sum(int(r["generated"] or 0) for r in rs)
        theorems = sum(int(r["theorems"] or 0) for r in rs)
        recon_successes = sum(int(r["recon_successes"] or 0) for r in rs)
        defs: set[str] = set()
        for r in rs:
            defs.update(r["def_constant_names"])  # type: ignore[arg-type]
        out.append(
            {
                **dict(zip(keys, key)),
                "generated": generated,
                "theorems": theorems,
                "success_rate": (theorems / generated) if generated else 0.0,
                "recon_successes": recon_successes,
                "recon_rate_on_atp": (recon_successes / theorems) if theorems else 0.0,
                "def_constants": len(defs),
                "def_constants_mean": statistics.mean(float(r["def_constants"]) for r in rs),
                "avg_bytes_mean": statistics.mean(float(r["avg_bytes"]) for r in rs),
                "max_bytes": max(int(r["max_bytes"]) for r in rs),
                "avg_lines_mean": statistics.mean(float(r["avg_lines"]) for r in rs),
                "max_lines": max(int(r["max_lines"]) for r in rs),
                "consistency_outputs": sum(int(r["consistency_outputs"]) for r in rs),
                "consistency_hits": sum(int(r["consistency_hits"]) for r in rs),
            }
        )
    return out


def md_table(rows: list[dict[str, object]], columns: list[str], limit: int | None = None) -> str:
    if limit is not None:
        rows = rows[:limit]
    lines = ["| " + " | ".join(columns) + " |", "| " + " | ".join("---" for _ in columns) + " |"]
    for row in rows:
        vals = []
        for col in columns:
            val = row[col]
            if isinstance(val, float):
                if "rate" in col:
                    vals.append(f"{100*val:.1f}%")
                else:
                    vals.append(f"{val:.1f}")
            else:
                vals.append(str(val))
        lines.append("| " + " | ".join(vals) + " |")
    return "\n".join(lines)


def attempt_maps(root: Path, label: str) -> tuple[set[tuple[str, str, str, str]], set[tuple[str, str, str, str]]]:
    atp: set[tuple[str, str, str, str]] = set()
    recon: set[tuple[str, str, str, str]] = set()
    for corpus in CORPORA:
        corpus_dir = root / label / corpus
        if not corpus_dir.exists():
            continue
        for premise in PREMISES:
            generated = read_list(corpus_dir / f"generated-{premise}.lst")
            names = [Path(p).name for p in generated]
            for prover in PROVERS:
                pdir = corpus_dir / "prover-outputs" / f"{prover}-{premise}"
                for name in names:
                    key = (corpus, premise, prover, name)
                    if has_atp_theorem(pdir / name):
                        atp.add(key)
                        rpath = corpus_dir / "reconstr-outputs" / f"{prover}-{premise}" / name.replace(".p", ".out")
                        try:
                            if rpath.read_text(errors="replace").startswith("Success "):
                                recon.add(key)
                        except FileNotFoundError:
                            pass
    return atp, recon


def defs_by_label(rows: list[dict[str, object]]) -> dict[str, set[str]]:
    out: dict[str, set[str]] = defaultdict(set)
    for row in rows:
        out[str(row["label"])].update(row["def_constant_names"])  # type: ignore[arg-type]
    return out


def special_problem_summary(root: Path, label: str, problem_stem: str) -> dict[str, object]:
    atp, recon = attempt_maps(root, label)
    atp_problem = {k for k in atp if k[3] == f"{problem_stem}.p"}
    recon_problem = {k for k in recon if k[3] == f"{problem_stem}.p"}
    return {
        "label": label,
        "problem": problem_stem,
        "atp_successes": len(atp_problem),
        "recon_successes": len(recon_problem),
        "recon_rate_on_atp": (len(recon_problem) / len(atp_problem)) if atp_problem else 0.0,
    }


def write_analysis(rows: list[dict[str, object]], root: Path, out: Path) -> None:
    by_label = aggregate(rows, "label", "config")
    by_corpus = aggregate(rows, "label", "corpus")
    by_prover = aggregate(rows, "label", "prover")
    by_premise = aggregate(rows, "label", "premise")

    baseline = next((r for r in by_label if r["label"] == BASELINE), None)
    winner = next((r for r in by_label if r["label"] == WINNER), None)

    baseline_atp, baseline_recon = attempt_maps(root, BASELINE)
    winner_atp, winner_recon = attempt_maps(root, WINNER)
    newly_found = winner_atp - baseline_atp
    newly_reconstructed = newly_found & winner_recon

    defs = defs_by_label(rows)
    gained_defs = defs.get(WINNER, set()) - defs.get(BASELINE, set())
    lost_defs = defs.get(BASELINE, set()) - defs.get(WINNER, set())

    eq_rect_rows = [special_problem_summary(root, label, "dep_eq_rect_refl") for label in (BASELINE, WINNER)]
    idiv_rows = [special_problem_summary(root, label, "dep_idiv_zero") for label in (BASELINE, WINNER)]

    consistency_hits = sum(int(r["consistency_hits"]) for r in rows)

    lines = [
        "# Extraction confirmation analysis",
        "",
        f"Rows summarized: {len(rows)}.",
        "Grid: {knn,nbayes} x {32,64,128,256,1024} x {E prover,Vampire,Z3,CVC4} over the three committed extraction corpora.",
        f"Consistency hits: {consistency_hits}.",
        "Consistency scope: exhaustive scan of every generated confirmation problem in the committed corpora with E prover and Vampire after rewriting the conjecture to `$false`.",
        "",
        "## Overall rates",
        "",
        md_table(by_label, ["label", "config", "generated", "theorems", "success_rate", "recon_successes", "recon_rate_on_atp", "def_constants", "avg_bytes_mean", "max_bytes", "consistency_outputs", "consistency_hits"]),
        "",
        "## Per-prover ATP and reconstruction rates",
        "",
        md_table(by_prover, ["label", "prover", "generated", "theorems", "success_rate", "recon_successes", "recon_rate_on_atp", "consistency_hits"]),
        "",
        "## Per-corpus rates",
        "",
        md_table(by_corpus, ["label", "corpus", "generated", "theorems", "success_rate", "recon_successes", "recon_rate_on_atp", "def_constants", "avg_bytes_mean", "consistency_hits"]),
        "",
        "## Per-premise-selector/count rates",
        "",
        md_table(by_premise, ["label", "premise", "generated", "theorems", "success_rate", "recon_successes", "recon_rate_on_atp"]),
        "",
        "## Eq_rect / WF watch points",
        "",
        md_table(eq_rect_rows + idiv_rows, ["label", "problem", "atp_successes", "recon_successes", "recon_rate_on_atp"]),
        "",
        "## Newly found winner proofs",
        "",
        f"Winner ATP successes absent from baseline: {len(newly_found)}.",
        f"Reconstructed among those: {len(newly_reconstructed)} ({(100*len(newly_reconstructed)/len(newly_found)) if newly_found else 0.0:.1f}%).",
        "",
        "## Definitional-equation footprint",
        "",
        f"Unique `$_def_*` constants in baseline problems: {len(defs.get(BASELINE, set()))}.",
        f"Unique `$_def_*` constants in winner problems: {len(defs.get(WINNER, set()))}.",
        f"Winner-only constants gaining `$_def_*` equations: {len(gained_defs)}.",
        "Sample winner-only constants: " + (", ".join(sorted(gained_defs)[:25]) if gained_defs else "none") + ".",
        f"Baseline-only constants absent from winner generated problems: {len(lost_defs)}.",
        "",
        "## Verdict inputs",
        "",
    ]

    if baseline and winner:
        delta = winner["success_rate"] - baseline["success_rate"]
        lines.append(f"Overall ATP delta (winner - baseline): {100*delta:+.1f} percentage points.")
        lines.append(f"Overall reconstruction-on-ATP delta: {100*(winner['recon_rate_on_atp'] - baseline['recon_rate_on_atp']):+.1f} percentage points.")
    dep_rows = {r["label"]: r for r in by_corpus if r["corpus"] == "dependent-slice"}
    if BASELINE in dep_rows and WINNER in dep_rows:
        dep_delta = dep_rows[WINNER]["success_rate"] - dep_rows[BASELINE]["success_rate"]
        lines.append(f"Dependent-slice ATP delta: {100*dep_delta:+.1f} percentage points.")
    std_rows = {r["label"]: r for r in by_corpus if r["corpus"] == "stdlib-regression"}
    if BASELINE in std_rows and WINNER in std_rows:
        std_delta = std_rows[WINNER]["success_rate"] - std_rows[BASELINE]["success_rate"]
        lines.append(f"Stdlib-regression ATP delta: {100*std_delta:+.1f} percentage points.")
    ext_rows = {r["label"]: r for r in by_corpus if r["corpus"] == "external-equations"}
    if BASELINE in ext_rows and WINNER in ext_rows:
        ext_delta = ext_rows[WINNER]["success_rate"] - ext_rows[BASELINE]["success_rate"]
        lines.append(f"External Program/WF ATP delta: {100*ext_delta:+.1f} percentage points.")
    lines.append("")

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text("\n".join(lines))


def main() -> int:
    if len(sys.argv) != 4:
        print("usage: summarize-confirmation.py RESULTS_ROOT SUMMARY_TSV ANALYSIS_MD", file=sys.stderr)
        return 2
    root = Path(sys.argv[1])
    rows = load_rows(root)
    if not rows:
        print(f"no rows found under {root}", file=sys.stderr)
        return 1
    write_tsv(rows, Path(sys.argv[2]))
    write_analysis(rows, root, Path(sys.argv[3]))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
