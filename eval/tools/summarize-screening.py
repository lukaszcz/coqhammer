#!/usr/bin/env python3
"""Summarize extraction screening checkpoints.

The input tree is produced by eval/run-screening-grid.sh.  The script is kept
separate so partially completed runs can be re-summarized without rerunning ATPs.
Callers supply the active labels so obsolete checkpoint directories are ignored.
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
ATP_SUCCESS_RE = re.compile(r"\bSZS status (?:Theorem|Unsatisfiable)\b")
CONSISTENCY_HIT_RE = re.compile(r"\bSZS status (?:Theorem|Unsatisfiable|ContradictoryAxioms)\b|^unsat$", re.M)


def read_list(path: Path) -> list[Path]:
    if not path.is_file():
        raise ValueError(f"required checkpoint list is missing: {path}")
    files = [Path(line.strip()) for line in path.read_text().splitlines() if line.strip()]
    missing = [item for item in files if not item.is_file()]
    if missing:
        raise ValueError(f"checkpoint list {path} names missing output: {missing[0]}")
    return files


def generation_status(corpus_dir: Path) -> None:
    path = corpus_dir / "generation.status"
    if not path.is_file() or path.read_text(errors="replace").splitlines() != [
        "generation_failed=0",
        "generation_exit=0",
    ]:
        raise ValueError(f"incomplete generation status: {path}")


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


def load_rows(root: Path, labels: list[str]) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for label in labels:
        label_dir = root / label
        if not label_dir.is_dir():
            raise ValueError(f"required label checkpoints are missing: {label_dir}")
        config = "current" if label == "current" else label.removeprefix("screening-")
        decl_skips = config.endswith("-decl-skips")
        if decl_skips:
            config_core = config.removesuffix("-decl-skips")
        else:
            config_core = config
        for corpus in CORPORA:
            corpus_dir = label_dir / corpus
            if not corpus_dir.is_dir():
                raise ValueError(f"required corpus checkpoints are missing: {corpus_dir}")
            generation_status(corpus_dir)
            for premise in PREMISES:
                generated = read_list(corpus_dir / f"generated-{premise}.lst")
                def_count, total_bytes, avg_bytes, max_bytes, avg_lines, max_lines = problem_metrics(generated)
                for prover in PROVERS:
                    prover_outputs = read_list(
                        corpus_dir / f"prover-outputs-{prover}-{premise}.lst"
                    )
                    if premise == "knn-64":
                        consistency_outputs = read_list(
                            corpus_dir / f"consistency-outputs-{prover}-knn-64.lst"
                        )
                    else:
                        consistency_outputs = []
                    theorems = status_theorem_count(prover_outputs)
                    consistency_hits = consistency_hit_count(consistency_outputs)
                    generated_n = len(generated)
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
        writer = csv.DictWriter(f, delimiter="\t", fieldnames=fieldnames, lineterminator="\n")
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


def write_analysis(rows: list[dict[str, object]], out: Path) -> None:
    by_label = aggregate(rows, "label", "config", "decl_skips")
    by_label_sorted = sorted(by_label, key=lambda r: (-float(r["success_rate"]), str(r["label"])))
    by_corpus = aggregate(rows, "label", "config", "decl_skips", "corpus")
    by_prover = aggregate(rows, "label", "config", "decl_skips", "prover")
    current = next((r for r in by_label if r["label"] == "current"), None)
    all_on = next((r for r in by_label if r["label"] == "screening-all-on"), None)

    flagged: list[str] = []
    if all_on is not None:
        for row in by_label:
            if str(row["label"]).startswith("screening-loo-") and not str(row["label"]).endswith("decl-skips"):
                if row["success_rate"] > all_on["success_rate"]:
                    flagged.append(
                        f"{row['config']} exceeds all-on ({100*row['success_rate']:.1f}% vs "
                        f"{100*all_on['success_rate']:.1f}%)"
                    )

    lines = [
        "# Extraction screening analysis",
        "",
        f"Rows summarized: {len(rows)}.",
        f"Consistency hits: {sum(int(r['consistency_hits']) for r in rows)}.",
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
        "## Current configuration",
        "",
    ]
    if current:
        lines.append(f"Current ATP success rate: {100*current['success_rate']:.1f}% overall.")
    else:
        lines.append("The current configuration was not included in this partial run.")
    if flagged:
        lines.append("Leave-one-out configurations exceeding all-on: " + "; ".join(flagged) + ".")
    else:
        lines.append("No leave-one-out configuration exceeded all-on.")
    lines.append("")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text("\n".join(lines))


def main() -> int:
    if len(sys.argv) < 5:
        print(
            "usage: summarize-screening.py RESULTS_ROOT SUMMARY_TSV ANALYSIS_MD LABEL...",
            file=sys.stderr,
        )
        return 2
    root = Path(sys.argv[1])
    labels = sys.argv[4:]
    try:
        rows = load_rows(root, labels)
    except ValueError as error:
        print(error, file=sys.stderr)
        return 1
    expected_rows = len(labels) * len(CORPORA) * len(PREMISES) * len(PROVERS)
    if len(rows) != expected_rows:
        print(f"incomplete checkpoint grid: expected {expected_rows} rows, found {len(rows)}", file=sys.stderr)
        return 1
    write_tsv(rows, Path(sys.argv[2]))
    write_analysis(rows, Path(sys.argv[3]))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
