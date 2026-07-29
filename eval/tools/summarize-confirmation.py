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
CORPORA = (
    "stdlib-regression",
    "dependent-stdlib",
    "stdpp",
    "color-vector",
    "dependent-slice",
    "equations-examples",
    "external-equations",
)
CURRENT = "current"
ATP_SUCCESS_RE = re.compile(r"\bSZS status (?:Theorem|Unsatisfiable)\b")


def read_list(path: Path) -> list[Path]:
    if not path.is_file():
        raise ValueError(f"required checkpoint list is missing: {path}")
    files = [Path(line.strip()) for line in path.read_text().splitlines() if line.strip()]
    missing = [item for item in files if not item.is_file()]
    if missing:
        raise ValueError(f"checkpoint list {path} names missing output: {missing[0]}")
    return files


def has_atp_theorem(path: Path) -> bool:
    try:
        text = path.read_text(errors="replace")
    except FileNotFoundError:
        return False
    return ATP_SUCCESS_RE.search(text) is not None


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


def reconstr_files(corpus_dir: Path, prover: str, premise: str, prover_outputs: list[Path]) -> list[Path]:
    # Reconstruction runs on what the ATP proved, not on every problem: a goal
    # the prover gave up on leaves no premise list to replay, so it has no
    # output here and its absence is not a gap.  This matches the metric the
    # rows report, which divides reconstruction successes by theorems.
    odir = corpus_dir / "reconstr-outputs" / f"{prover}-{premise}"
    return [
        odir / Path(path).with_suffix(".out").name
        for path in prover_outputs
        if has_atp_theorem(path)
    ]


def load_rows(root: Path, labels: list[str]) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for label in labels:
        label_dir = root / label
        if not label_dir.is_dir():
            raise ValueError(f"required label checkpoints are missing: {label_dir}")
        config = "current" if label == CURRENT else label.removeprefix("confirmation-")
        for corpus in CORPORA:
            corpus_dir = label_dir / corpus
            if not corpus_dir.is_dir():
                raise ValueError(f"required corpus checkpoints are missing: {corpus_dir}")
            for premise in PREMISES:
                generated = read_list(corpus_dir / f"generated-{premise}.lst")
                defs, total_bytes, avg_bytes, max_bytes, avg_lines, max_lines = problem_metrics(generated)
                for prover in PROVERS:
                    prover_outputs = read_list(corpus_dir / f"prover-outputs-{prover}-{premise}.lst")
                    theorems = status_theorem_count(prover_outputs)
                    rfiles = reconstr_files(corpus_dir, prover, premise, prover_outputs)
                    missing_reconstructions = [path for path in rfiles if not path.is_file()]
                    if missing_reconstructions:
                        raise ValueError(
                            f"required reconstruction output is missing: {missing_reconstructions[0]}"
                        )
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
    eq_rect_rows = [special_problem_summary(root, str(row["label"]), "dep_eq_rect_refl") for row in by_label]
    idiv_rows = [special_problem_summary(root, str(row["label"]), "dep_idiv_zero") for row in by_label]
    consistency_hits = sum(int(row["consistency_hits"]) for row in rows)
    corpus_names = sorted({str(row["corpus"]) for row in rows})

    lines = [
        "# Extraction confirmation analysis",
        "",
        f"Rows summarized: {len(rows)}.",
        f"Grid: {{knn,nbayes}} x {{32,64,128,256,1024}} x {{E prover,Vampire,Z3,CVC4}} over {len(corpus_names)} extraction corpora ({', '.join(corpus_names)}).",
        f"Consistency hits: {consistency_hits}.",
        "Consistency scope: the lemmas listed in each corpus's consistency-lemmas.txt, run with E prover and Vampire after rewriting the conjecture to `$false`. The list is curated rather than exhaustive because a vacuously true lemma is refutable however faithful the translation is: the rewritten problem keeps the goal's own hypotheses as axioms, so only lemmas with satisfiable hypotheses can distinguish a sound translation from an unsound one.",
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
    ]
    current = next((row for row in by_label if row["label"] == CURRENT), None)
    if current:
        lines.extend([
            "## Current configuration",
            "",
            f"ATP success rate: {100*current['success_rate']:.1f}%.",
            f"Reconstruction-on-ATP rate: {100*current['recon_rate_on_atp']:.1f}%.",
            "",
        ])
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text("\n".join(lines))


def main() -> int:
    if len(sys.argv) < 4:
        print(
            "usage: summarize-confirmation.py RESULTS_ROOT SUMMARY_TSV ANALYSIS_MD [LABEL ...]",
            file=sys.stderr,
        )
        return 2
    root = Path(sys.argv[1])
    labels = sys.argv[4:] or [CURRENT]
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
    write_analysis(rows, root, Path(sys.argv[3]))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
