#!/usr/bin/env python3
"""Summarize extraction screening checkpoints.

The input tree is produced by eval/run-screening-grid.sh.  The script is kept
separate so partially completed runs can be re-summarized without rerunning ATPs.
"""

from __future__ import annotations

import csv
import re
import statistics
import sys
from collections import defaultdict
from pathlib import Path

PREMISES = ("knn-64", "knn-256", "knn-1024")
PROVERS = ("eprover", "vampire")
CORPORA = ("stdlib-regression", "dependent-slice", "external-equations")
BASELINE = "baseline-merge-base"
ATP_SUCCESS_RE = re.compile(r"\bSZS status (?:Theorem|Unsatisfiable)\b")
CONSISTENCY_HIT_RE = re.compile(r"\bSZS status (?:Theorem|Unsatisfiable|ContradictoryAxioms)\b|^unsat$", re.M)


def read_list(path: Path) -> list[Path]:
    if not path.exists():
        return []
    return [Path(line.strip()) for line in path.read_text().splitlines() if line.strip()]


def generation_status(corpus_dir: Path) -> tuple[bool, dict[str, int]]:
    path = corpus_dir / "generation.status"
    if not path.exists():
        return False, {}
    failed = False
    counts: dict[str, int] = {}
    for line in path.read_text(errors="replace").splitlines():
        if line == "generation_failed=1":
            failed = True
            continue
        parts = line.split()
        if len(parts) == 3 and parts[0] == "generated_count":
            try:
                counts[parts[1]] = int(parts[2])
            except ValueError:
                pass
    return failed, counts


def baseline_generated_count(root: Path, corpus: str, premise: str) -> int:
    return len(read_list(root / BASELINE / corpus / f"generated-{premise}.lst"))


def status_count(files: list[Path], status_re: re.Pattern[str]) -> int:
    count = 0
    for path in files:
        try:
            text = path.read_text(errors="replace")
        except FileNotFoundError:
            continue
        if status_re.search(text):
            count += 1
    return count


def status_theorem_count(files: list[Path]) -> int:
    return status_count(files, ATP_SUCCESS_RE)


def consistency_hit_count(files: list[Path]) -> int:
    return status_count(files, CONSISTENCY_HIT_RE)


def def_base(name: str) -> str | None:
    if not name.startswith("$_def_"):
        return None
    rest = name[len("$_def_") :]
    if rest.startswith("$"):
        return None
    return rest.split("$", 1)[0]


def problem_metrics(files: list[Path]) -> tuple[int, int, float, int, float, int]:
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
    return len(defs), total_bytes, total_bytes / n, max_bytes, total_lines / n, max_lines


def load_rows(root: Path) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for label_dir in sorted(p for p in root.iterdir() if p.is_dir()):
        label = label_dir.name
        config = "baseline" if label == BASELINE else label.removeprefix("screening-")
        decl_skips = config.endswith("-decl-skips")
        if decl_skips:
            config_core = config.removesuffix("-decl-skips")
        else:
            config_core = config
        for corpus in CORPORA:
            corpus_dir = label_dir / corpus
            if not corpus_dir.exists():
                continue
            generation_failed, generated_counts = generation_status(corpus_dir)
            for premise in PREMISES:
                generated = read_list(corpus_dir / f"generated-{premise}.lst")
                def_count, total_bytes, avg_bytes, max_bytes, avg_lines, max_lines = problem_metrics(generated)
                for prover in PROVERS:
                    prover_outputs = read_list(corpus_dir / f"prover-outputs-{prover}-{premise}.lst")
                    theorems = status_theorem_count(prover_outputs)
                    if premise == "knn-64":
                        consistency_outputs = read_list(corpus_dir / f"consistency-outputs-{prover}-knn-64.lst")
                    else:
                        consistency_outputs = []
                    consistency_hits = consistency_hit_count(consistency_outputs)
                    generated_n = len(generated)
                    if generation_failed and generated_n == 0:
                        generated_n = generated_counts.get(
                            premise, baseline_generated_count(root, corpus, premise)
                        )
                    rows.append(
                        {
                            "label": label,
                            "config": config_core,
                            "decl_skips": str(decl_skips).lower(),
                            "corpus": corpus,
                            "premise": premise.removeprefix("knn-"),
                            "prover": prover,
                            "generated": generated_n,
                            "theorems": theorems,
                            "success_rate": (theorems / generated_n) if generated_n else 0.0,
                            "def_constants": def_count,
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
        "decl_skips",
        "corpus",
        "premise",
        "prover",
        "generated",
        "theorems",
        "success_rate",
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
            formatted = dict(row)
            formatted["success_rate"] = f"{row['success_rate']:.6f}"
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
        out.append(
            {
                **dict(zip(keys, key)),
                "generated": generated,
                "theorems": theorems,
                "success_rate": (theorems / generated) if generated else 0.0,
                "def_constants_mean": statistics.mean(float(r["def_constants"]) for r in rs),
                "avg_bytes_mean": statistics.mean(float(r["avg_bytes"]) for r in rs),
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


def find_generation_failures(root: Path) -> list[str]:
    failures: list[str] = []
    for status in sorted(root.glob("*/*/generation.status")):
        text = status.read_text(errors="replace")
        if "generation_failed=1" in text:
            failures.append(f"{status.parents[1].name}/{status.parent.name}")
    return failures


def write_analysis(rows: list[dict[str, object]], root: Path, out: Path) -> None:
    by_label = aggregate(rows, "label", "config", "decl_skips")
    by_label_sorted = sorted(by_label, key=lambda r: (-float(r["success_rate"]), str(r["label"])))
    by_corpus = aggregate(rows, "label", "config", "decl_skips", "corpus")
    by_prover = aggregate(rows, "label", "config", "decl_skips", "prover")

    baseline_rate = next((r["success_rate"] for r in by_label if r["label"] == BASELINE), 0.0)
    non_baseline = [r for r in by_label_sorted if r["label"] != BASELINE]
    winner = non_baseline[0] if non_baseline else None
    all_on = next((r for r in by_label if r["label"] == "screening-all-on"), None)

    flagged: list[str] = []
    if all_on is not None:
        for r in by_label:
            if str(r["label"]).startswith("screening-loo-") and not str(r["label"]).endswith("decl-skips"):
                if r["success_rate"] > all_on["success_rate"]:
                    flagged.append(f"{r['config']} improved over all-on ({100*r['success_rate']:.1f}% vs {100*all_on['success_rate']:.1f}%)")

    dep_rows = [r for r in by_corpus if r["corpus"] == "dependent-slice"]
    dep_baseline = next((r for r in dep_rows if r["label"] == BASELINE), None)
    dep_winner = next((r for r in dep_rows if winner and r["label"] == winner["label"]), None)
    dep_delta = None
    if dep_baseline and dep_winner:
        dep_delta = dep_winner["success_rate"] - dep_baseline["success_rate"]

    generation_failures = find_generation_failures(root)
    lines = [
        "# Extraction screening analysis",
        "",
        f"Rows summarized: {len(rows)}.",
        f"Baseline sanity success rate: {100*baseline_rate:.1f}% overall.",
        f"Consistency hits: {sum(int(r['consistency_hits']) for r in rows)}.",
        "Generation failures recorded as screened regressions: " + (", ".join(generation_failures) if generation_failures else "none") + ".",
        "",
        "## Overall configuration ranking",
        "",
        md_table(by_label_sorted, ["label", "config", "decl_skips", "generated", "theorems", "success_rate", "def_constants_mean", "avg_bytes_mean", "consistency_hits"]),
        "",
        "## Per-corpus rates",
        "",
        md_table(by_corpus, ["label", "corpus", "generated", "theorems", "success_rate", "def_constants_mean", "avg_bytes_mean", "consistency_hits"]),
        "",
        "## Per-prover rates",
        "",
        md_table(by_prover, ["label", "prover", "generated", "theorems", "success_rate", "consistency_hits"]),
        "",
    ]
    if winner:
        lines.extend([
            "## Decision inputs",
            "",
            f"Winner by screening ATP success rate: `{winner['label']}` ({100*winner['success_rate']:.1f}%).",
        ])
    if dep_delta is not None:
        lines.append(f"Dependent-slice delta for winner vs baseline: {100*dep_delta:+.1f} percentage points.")
    if flagged:
        lines.append("Flagged options: " + "; ".join(flagged) + ".")
    else:
        lines.append("Flagged options: none by leave-one-out ATP success rate.")
    lines.append("")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text("\n".join(lines))


def main() -> int:
    if len(sys.argv) != 4:
        print("usage: summarize-screening.py RESULTS_ROOT SUMMARY_TSV ANALYSIS_MD", file=sys.stderr)
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
