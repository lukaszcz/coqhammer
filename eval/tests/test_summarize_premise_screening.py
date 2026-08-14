#!/usr/bin/env python3
"""Validation and GoalKey-level tests for premise-screening summaries."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

SCRIPT = Path(__file__).resolve().parents[1] / "tools" / "summarize-premise-screening.py"
SPEC = importlib.util.spec_from_file_location("summarize_premise_screening", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
summarizer = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = summarizer
SPEC.loader.exec_module(summarizer)

LABELS = ["ds0-df0", "ds8-df4"]
AXES = summarizer.Axes(
    premises=("knn-32", "nbayes-32", "knn-1024"),
    provers=("eprover", "vampire"),
    corpora=("tiny-a", "tiny-b"),
    corpus_mode="sample",
)


def fixture_hash_tree(path: Path) -> str:
    """Independent reproduction of the shell engine's documented tree hash."""
    root = path.resolve()
    digest = hashlib.sha256()
    for item in sorted(entry for entry in root.rglob("*") if entry.is_file()):
        relative = item.relative_to(root)
        if ".git" in relative.parts or "_build" in relative.parts:
            continue
        name = relative.as_posix().encode()
        digest.update(len(name).to_bytes(8, "big"))
        digest.update(name)
        digest.update(item.read_bytes())
    return digest.hexdigest()


def fixture_corpus_hash(fields: dict[str, object]) -> str:
    digests = "".join(
        hashlib.sha256(Path(filename).read_bytes()).hexdigest()
        for filename in fields["files"]
    )
    digests += "".join(fixture_hash_tree(Path(directory)) for directory in fields["trees"])
    return hashlib.sha256(digests.encode()).hexdigest()


def fixture_label_options(label: str) -> tuple[int, int]:
    match = re.fullmatch(r"ds([0-9]+)-df([0-9]+)", label)
    assert match is not None
    return int(match.group(1)), int(match.group(2))


def fixture_premise_count(premise: str) -> int:
    match = re.fullmatch(r"[^/]+-([1-9][0-9]*)", premise)
    assert match is not None
    return int(match.group(1))


def fixture_preamble(label: str) -> bytes:
    slots, features = fixture_label_options(label)
    return (
        f"Set Hammer DefinitionPremises {slots}.\n"
        f"Set Hammer DefinitionFeatures {features}.\n"
    ).encode()


def fixture_checkpoint(
    stage: str, label: str, corpus: str, provenance: summarizer.Provenance,
    premise: str | None = None, prover: str | None = None,
    input_sha256: str | None = None,
) -> dict[str, str]:
    """Literal engine schema, deliberately independent of the checker helper."""
    label_fields = provenance.labels[label]
    corpus_fields = provenance.corpora[corpus]
    fields = {
        "checkpoint_version": "3",
        "stage": stage,
        "repository_commit": provenance.repository_commit,
        "grid_script_sha256": provenance.grid_script_sha256,
        "checkpoint_helper_sha256": provenance.checkpoint_helper_sha256,
        "label": label,
        "config": label_fields["config"],
        "install_commit": label_fields["install_commit"],
        "install_kind": label_fields["install_kind"],
        "install_manifest_sha256": label_fields["install_manifest_sha256"],
        "corpus": corpus,
        "corpus_mode": corpus_fields["mode"],
        "corpus_source": corpus_fields["source"],
        "corpus_sha256": corpus_fields["sha256"],
        "hook_preamble_sha256": hashlib.sha256(fixture_preamble(label)).hexdigest(),
        "hook_preamble_file": "hook-preamble.v",
    }
    if stage == "generation":
        fields.update({
            "compile_supervisor_sha256": provenance.compile_supervisor_sha256,
            "compile_timeout": provenance.compile_timeout,
            "compile_timeout_grace": provenance.compile_timeout_grace,
        })
    if stage in ("prover", "consistency"):
        assert premise is not None and prover is not None and input_sha256 is not None
        fields.update({
            "premise": premise,
            "prover": prover,
            "timeout": (provenance.prover_timeout if stage == "prover"
                        else provenance.consistency_timeout),
            "input_sha256": input_sha256,
        })
    return fields


class Fixture:
    intrinsic = {
        "tiny-a": (8, "1", "2"),
        "tiny-b": (0, "none", "none"),
    }

    def __init__(
        self, root: Path, axes: summarizer.Axes = AXES, labels: list[str] = LABELS
    ) -> None:
        self.root = root
        self.axes = axes
        self.metadata_paths: dict[tuple[str, str, str], Path] = {}
        self.outputs: dict[tuple[str, str, str, str], Path] = {}
        self.markers: dict[tuple[str, str, str, str], Path] = {}
        self.statuses: dict[tuple[str, str, str, str], Path] = {}
        self.logs: dict[tuple[str, str, str, str], Path] = {}
        self.consistency_markers: dict[tuple[str, str, str], Path] = {}
        corpus_fields: dict[str, dict[str, object]] = {}
        for corpus in axes.corpora:
            source = root / "corpus-inputs" / corpus
            source.mkdir(parents=True)
            (source / "source.v").write_text(f"(* {corpus} *)\n")
            fields: dict[str, object] = {
                "mode": axes.corpus_mode,
                "source": f"fixture-{corpus}",
                "sha256": "",
                "trees": [str(source)],
                "files": [],
            }
            fields["sha256"] = fixture_corpus_hash(fields)
            corpus_fields[corpus] = fields
        label_fields = {
            label: {
                "config": "current",
                "install_commit": "1" * 40,
                "install_kind": "current",
                "install_manifest_sha256": "2" * 64,
            }
            for label in labels
        }
        self.provenance = summarizer.Provenance(
            repository_commit="3" * 40,
            grid_script_sha256="4" * 64,
            checkpoint_helper_sha256="5" * 64,
            compile_supervisor_sha256="6" * 64,
            compile_timeout="600",
            compile_timeout_grace="10",
            prover_timeout="5",
            consistency_timeout="2",
            consistency_premise=axes.premises[0],
            labels=label_fields,
            corpora=corpus_fields,
        )
        for label in labels:
            slots, _ = fixture_label_options(label)
            for corpus in axes.corpora:
                corpus_dir = root / label / corpus
                corpus_dir.mkdir(parents=True)
                (corpus_dir / "hook-preamble.v").write_bytes(fixture_preamble(label))
                self.write_marker(
                    corpus_dir / "generate.done",
                    fixture_checkpoint("generation", label, corpus, self.provenance),
                )
                (corpus_dir / "generation.status").write_text(
                    "generation_failed=0\ngeneration_exit=0\n"
                )
                d_size, minimum, median = self.intrinsic.get(
                    corpus, (8, "3", "4")
                )
                premise_inputs: dict[str, tuple[dict[str, Path], str]] = {}
                for premise in axes.premises:
                    count = fixture_premise_count(premise)
                    problem_dir = corpus_dir / "atp-problems" / premise
                    problem_dir.mkdir(parents=True)
                    # Reusing this relative name proves corpus is part of GoalKey.
                    problem = problem_dir / "shared.p"
                    problem.write_text("% fixture\n")
                    k = min(d_size, slots, (count + 7) // 8)
                    metadata = problem.with_suffix(".meta")
                    metadata.write_text(
                        f"d_size={d_size} min_occ={minimum} median_occ={median} k={k}\n"
                    )
                    self.metadata_paths[label, corpus, premise] = metadata
                    (corpus_dir / f"generated-{premise}.lst").write_text(f"{problem}\n")
                    input_hash = fixture_hash_tree(problem_dir)
                    premise_inputs[premise] = ({problem.name: problem}, input_hash)
                    for prover in axes.provers:
                        key = (label, corpus, premise, prover)
                        stem = f"{prover}-{premise}"
                        output_dir = corpus_dir / "prover-outputs" / stem
                        output_dir.mkdir(parents=True)
                        output = output_dir / problem.name
                        output.write_text(self.output_text(*key))
                        (corpus_dir / f"prover-outputs-{stem}.lst").write_text(
                            f"{output}\n"
                        )
                        marker = corpus_dir / f"prover-{stem}.done"
                        self.write_marker(
                            marker,
                            fixture_checkpoint(
                                "prover", label, corpus, self.provenance,
                                premise, prover, input_hash,
                            ),
                        )
                        status = corpus_dir / f"prover-{stem}.status"
                        status.write_text("prover_exit=0\n")
                        log = corpus_dir / f"{stem}.log"
                        log.write_text("ordinary prover log\n")
                        self.outputs[key] = output
                        self.markers[key] = marker
                        self.statuses[key] = status
                        self.logs[key] = log
                premise = self.provenance.consistency_premise
                generated, input_hash = premise_inputs[premise]
                for prover in axes.provers:
                    stem = f"{prover}-{premise}"
                    marker = corpus_dir / f"consistency-{stem}.done"
                    self.write_marker(
                        marker,
                        fixture_checkpoint(
                            "consistency", label, corpus, self.provenance,
                            premise, prover, input_hash,
                        ),
                    )
                    (corpus_dir / f"consistency-{stem}.status").write_text(
                        "consistency_exit=0\n"
                    )
                    work = corpus_dir / "consistency" / stem
                    for subdir in ("outputs", "raw", "status"):
                        (work / subdir).mkdir(parents=True)
                    listed = []
                    for name in generated:
                        output = work / "outputs" / name
                        output.write_text("% SZS status GaveUp\n")
                        (work / "raw" / name).write_text("ordinary consistency log\n")
                        (work / "status" / f"{name}.status").write_text(
                            "command_exit=0\n"
                        )
                        listed.append(str(output))
                    (corpus_dir / f"consistency-outputs-{stem}.lst").write_text(
                        "\n".join(listed) + "\n"
                    )
                    self.consistency_markers[label, corpus, prover] = marker

    @staticmethod
    def write_marker(path: Path, fields: dict[str, str]) -> None:
        path.write_text("".join(f"{key}={value}\n" for key, value in fields.items()))

    def environment_json(self) -> str:
        return json.dumps({
            "repository_commit": self.provenance.repository_commit,
            "grid_script_sha256": self.provenance.grid_script_sha256,
            "checkpoint_helper_sha256": self.provenance.checkpoint_helper_sha256,
            "compile_supervisor_sha256": self.provenance.compile_supervisor_sha256,
            "compile_timeout": self.provenance.compile_timeout,
            "compile_timeout_grace": self.provenance.compile_timeout_grace,
            "prover_timeout": self.provenance.prover_timeout,
            "consistency_timeout": self.provenance.consistency_timeout,
            "labels": self.provenance.labels,
            "corpora": self.provenance.corpora,
        })

    @staticmethod
    def output_text(label: str, corpus: str, premise: str, prover: str) -> str:
        # tiny-a remains N=32-solved after losing one exact attempt. tiny-b loses
        # its only N=32 solution but remains solved overall through N=1024.
        baseline_successes = {
            ("tiny-a", "knn-32", "eprover"),
            ("tiny-a", "nbayes-32", "vampire"),
            ("tiny-b", "knn-32", "eprover"),
            ("tiny-b", "knn-1024", "vampire"),
        }
        candidate_successes = {
            ("tiny-a", "nbayes-32", "vampire"),
            ("tiny-b", "knn-1024", "vampire"),
        }
        successes = baseline_successes if label == summarizer.BASELINE else candidate_successes
        status = "Theorem" if (corpus, premise, prover) in successes else "GaveUp"
        return f"% SZS status {status}\n"


class SummarizerTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.fixture = Fixture(self.root)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def load(self) -> summarizer.LoadedGrid:
        return summarizer.load_grid(self.root, LABELS, AXES, self.fixture.provenance)

    def test_goalkey_decisions_attempt_diagnostics_and_mode(self) -> None:
        grid = self.load()
        rows = summarizer.make_summary_rows(grid, LABELS)
        aggregate = next(
            row for row in rows
            if row["label"] == "ds8-df4" and row["scope"] == "aggregate"
        )
        # Both GoalKeys are still solved, although two exact N=32 attempts were lost.
        self.assertEqual(aggregate["solved_goals"], 2)
        self.assertEqual(aggregate["baseline_solved_goals"], 2)
        self.assertEqual(aggregate["goal_net"], 0)
        self.assertEqual(aggregate["goal_losses"], 0)
        self.assertEqual(aggregate["solved_attempts"], 2)
        self.assertEqual(aggregate["baseline_solved_attempts"], 4)
        self.assertEqual(aggregate["attempt_losses"], 2)
        # The guard is a GoalKey-level N=32 loss: tiny-a is retained, tiny-b is lost.
        self.assertEqual(aggregate["n32_goal_losses"], 1)
        self.assertEqual(aggregate["n32_regression_flag"], "REGRESSION")

        n32 = next(
            row for row in rows
            if row["label"] == "ds8-df4" and row["scope"] == "n32"
        )
        self.assertEqual(n32["solved_goals"], 1)
        self.assertEqual(n32["baseline_solved_goals"], 2)
        self.assertEqual(n32["goal_losses"], 1)
        self.assertEqual(n32["attempt_losses"], 2)

        self.assertEqual(
            {row["corpus"] for row in rows if row["scope"] == "corpus"},
            set(AXES.corpora),
        )
        exact_rows = [row for row in rows if row["scope"] == "exact_attempt"]
        self.assertEqual({row["premise"] for row in exact_rows}, set(AXES.premises))
        self.assertTrue(all(row["solved_goals"] == "" for row in exact_rows))
        self.assertTrue(all(row["n32_regression_flag"] == "diagnostic" for row in exact_rows))
        self.assertTrue(all(row["corpus_mode"] == "sample" for row in rows))

        summary = self.root / "summary.tsv"
        analysis = self.root / "analysis.md"
        summarizer.write_tsv(rows, summary)
        summarizer.write_analysis(grid, LABELS, analysis)
        text = analysis.read_text()
        self.assertIn("## Corpus mode: `SAMPLE`", text)
        self.assertIn("SMOKE DATA ONLY", text)
        self.assertIn("Aggregate solved goals", text)
        self.assertIn("Per-corpus solved goals", text)
        self.assertIn("Per-bucket solved goals", text)
        self.assertIn("Goal-level N=32 regression guard", text)
        self.assertIn("Exact-attempt diagnostics (not decision metrics)", text)

    def test_standalone_one_label_one_corpus_strict_summary(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            axes = summarizer.Axes(
                premises=("knn-32",),
                provers=("eprover",),
                corpora=("tiny-a",),
                corpus_mode="sample",
            )
            fixture = Fixture(root / "results", axes, [summarizer.BASELINE])
            summary = root / "summary.tsv"
            analysis = root / "analysis.md"
            environment = os.environ.copy()
            environment.update({
                "COQHAMMER_GRID_PREMISES": "knn-32",
                "COQHAMMER_GRID_PROVERS": "eprover",
                "COQHAMMER_GRID_CORPORA": "tiny-a",
                "COQHAMMER_GRID_CORPUS_MODE": "sample",
                "COQHAMMER_GRID_CONSISTENCY_PREMISE": "knn-32",
                "COQHAMMER_GRID_EXPECTED_PROVENANCE": fixture.environment_json(),
            })
            result = subprocess.run(
                [sys.executable, str(SCRIPT), str(root / "results"), str(summary),
                 str(analysis), summarizer.BASELINE],
                env=environment, capture_output=True, text=True,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("scope", summary.read_text().splitlines()[0])
            self.assertIn("SMOKE DATA ONLY", analysis.read_text())

    def test_dynamic_axes_are_read_from_engine_environment(self) -> None:
        environment = {
            "COQHAMMER_GRID_PREMISES": "knn-32\nnbayes-77",
            "COQHAMMER_GRID_PROVERS": "vampire",
            "COQHAMMER_GRID_CORPORA": "custom-one\ncustom-two",
            "COQHAMMER_GRID_CORPUS_MODE": "full",
        }
        with mock.patch.dict(os.environ, environment, clear=True):
            axes = summarizer.axes_from_environment()
        self.assertEqual(axes.premises, ("knn-32", "nbayes-77"))
        self.assertEqual(axes.provers, ("vampire",))
        self.assertEqual(axes.corpora, ("custom-one", "custom-two"))
        self.assertEqual(axes.corpus_mode, "full")

    def test_provenance_json_rejects_root_and_nested_type_errors(self) -> None:
        base = json.loads(self.fixture.environment_json())
        malformed = []
        for value in (None, [], "labels"):
            envelope = dict(base)
            envelope["labels"] = value
            malformed.append(json.dumps(envelope))
        for value in (None, [], "corpora"):
            envelope = dict(base)
            envelope["corpora"] = value
            malformed.append(json.dumps(envelope))
        envelope = json.loads(self.fixture.environment_json())
        envelope["labels"][LABELS[0]] = []
        malformed.append(json.dumps(envelope))
        envelope = json.loads(self.fixture.environment_json())
        envelope["corpora"][AXES.corpora[0]] = None
        malformed.append(json.dumps(envelope))
        malformed.extend(("null", "[]", '"string"', "1"))

        for raw in malformed:
            with self.subTest(raw=raw[:80]), mock.patch.dict(os.environ, {
                "COQHAMMER_GRID_EXPECTED_PROVENANCE": raw,
                "COQHAMMER_GRID_CONSISTENCY_PREMISE": "knn-32",
            }, clear=True):
                with self.assertRaises(ValueError):
                    summarizer.provenance_from_environment(LABELS, AXES)

    def test_provenance_json_rejects_duplicate_keys_at_every_level(self) -> None:
        duplicates = (
            '{"labels":{},"labels":{}}',
            '{"labels":{"ds0-df0":{},"ds0-df0":{}}}',
            '{"corpora":{"tiny-a":{"mode":"sample","mode":"full"}}}',
        )
        for raw in duplicates:
            with self.subTest(raw=raw), mock.patch.dict(os.environ, {
                "COQHAMMER_GRID_EXPECTED_PROVENANCE": raw,
                "COQHAMMER_GRID_CONSISTENCY_PREMISE": "knn-32",
            }, clear=True):
                with self.assertRaisesRegex(ValueError, "duplicate JSON object key"):
                    summarizer.provenance_from_environment(LABELS, AXES)

    def test_malformed_envelope_cli_error_is_concise(self) -> None:
        environment = os.environ.copy()
        environment.update({
            "COQHAMMER_GRID_PREMISES": "knn-32",
            "COQHAMMER_GRID_PROVERS": "eprover",
            "COQHAMMER_GRID_CORPORA": "tiny-a",
            "COQHAMMER_GRID_CORPUS_MODE": "sample",
            "COQHAMMER_GRID_CONSISTENCY_PREMISE": "knn-32",
            "COQHAMMER_GRID_EXPECTED_PROVENANCE": '{"labels":null,"labels":{}}',
        })
        result = subprocess.run(
            [sys.executable, str(SCRIPT), str(self.root), str(self.root / "out.tsv"),
             str(self.root / "out.md"), summarizer.BASELINE],
            env=environment, capture_output=True, text=True,
        )
        self.assertEqual(result.returncode, 1)
        self.assertIn("duplicate JSON object key", result.stderr)
        self.assertNotIn("Traceback", result.stderr)
        self.assertLessEqual(len(result.stderr.splitlines()), 1)

    def test_incomplete_and_inconsistent_checkpoints_are_rejected(self) -> None:
        key = ("ds0-df0", "tiny-a", "knn-32", "eprover")
        self.fixture.markers[key].unlink()
        with self.assertRaisesRegex(ValueError, "checkpoint is missing"):
            self.load()

    def test_checkpoint_identity_and_mode_are_rejected(self) -> None:
        key = ("ds0-df0", "tiny-a", "knn-32", "eprover")
        marker = self.fixture.markers[key]
        marker.write_text(marker.read_text().replace("stage=prover", "stage=generation"))
        with self.assertRaisesRegex(ValueError, "wrong stage"):
            self.load()

        marker.write_text(marker.read_text().replace("stage=generation", "stage=prover")
                          .replace("corpus_mode=sample", "corpus_mode=full"))
        with self.assertRaisesRegex(ValueError, "wrong corpus_mode"):
            self.load()

    def test_stale_commit_and_tampered_input_hash_are_rejected(self) -> None:
        key = ("ds0-df0", "tiny-a", "knn-32", "eprover")
        marker = self.fixture.markers[key]
        marker.write_text(marker.read_text().replace(
            f"repository_commit={self.fixture.provenance.repository_commit}",
            "repository_commit=stale",
        ))
        with self.assertRaisesRegex(ValueError, "wrong repository_commit"):
            self.load()

        # Restore the full realistic marker, then alter the actual generated tree.
        self.fixture.write_marker(
            marker,
            fixture_checkpoint(
                "prover", *key[:2], self.fixture.provenance,
                key[2], key[3], fixture_hash_tree(marker.parent / "atp-problems" / key[2]),
            ),
        )
        self.fixture.metadata_paths[key[:3]].with_suffix(".p").write_text("% tampered\n")
        with self.assertRaisesRegex(ValueError, "wrong input_sha256"):
            self.load()

    def test_tampered_corpus_source_and_preamble_are_rejected(self) -> None:
        source = Path(self.fixture.provenance.corpora["tiny-a"]["trees"][0])
        (source / "source.v").write_text("(* changed installed source *)\n")
        with self.assertRaisesRegex(ValueError, "current corpus input hash differs"):
            self.load()

        # A separate realistic fixture keeps the preamble failure focused.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fixture = Fixture(root)
            (root / "ds0-df0" / "tiny-a" / "hook-preamble.v").write_text(
                "Set Hammer DefinitionPremises 99.\n"
            )
            with self.assertRaisesRegex(ValueError, "hook preamble"):
                summarizer.load_grid(root, LABELS, AXES, fixture.provenance)

    def test_generation_marker_and_status_are_required(self) -> None:
        corpus_dir = self.root / "ds0-df0" / "tiny-a"
        (corpus_dir / "generate.done").unlink()
        with self.assertRaisesRegex(ValueError, "checkpoint is missing"):
            self.load()

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fixture = Fixture(root)
            (root / "ds0-df0" / "tiny-a" / "generation.status").write_text(
                "generation_exit=0\n"
            )
            with self.assertRaisesRegex(ValueError, "incomplete generation status"):
                summarizer.load_grid(root, LABELS, AXES, fixture.provenance)

    def test_consistency_checkpoint_and_result_are_required(self) -> None:
        marker = self.fixture.consistency_markers["ds0-df0", "tiny-a", "eprover"]
        marker.write_text(marker.read_text().replace("timeout=2", "extra=2"))
        with self.assertRaisesRegex(ValueError, "wrong schema"):
            self.load()

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fixture = Fixture(root)
            output = (root / "ds0-df0" / "tiny-a" / "consistency" /
                      "eprover-knn-32" / "outputs" / "shared.p")
            output.write_text("% SZS status Theorem\n")
            with self.assertRaisesRegex(ValueError, "inconsistent premises"):
                summarizer.load_grid(root, LABELS, AXES, fixture.provenance)

    def test_noninteger_status_and_incomplete_output_mapping_are_rejected(self) -> None:
        key = ("ds0-df0", "tiny-a", "knn-32", "eprover")
        self.fixture.statuses[key].write_text("prover_exit=signal\n")
        with self.assertRaisesRegex(ValueError, "single integer"):
            self.load()

        self.fixture.statuses[key].write_text("prover_exit=0\n")
        corpus_dir = self.root / "ds0-df0" / "tiny-a"
        (corpus_dir / "prover-outputs-eprover-knn-32.lst").write_text("")
        with self.assertRaisesRegex(ValueError, "checkpoint list is empty"):
            self.load()

    def test_crashes_and_malformed_terminal_statuses_are_rejected(self) -> None:
        key = ("ds0-df0", "tiny-a", "knn-32", "eprover")
        self.fixture.logs[key].write_text("Segmentation fault (core dumped)\n")
        with self.assertRaisesRegex(ValueError, "crash or infrastructure error"):
            self.load()

        self.fixture.logs[key].write_text("ordinary prover log\n")
        self.fixture.outputs[key].write_text(
            "% SZS status Theorem\n% SZS status GaveUp\n"
        )
        with self.assertRaisesRegex(ValueError, "exactly one allowed"):
            self.load()

    def test_vampire_empty_backstop_and_documented_log_exceptions(self) -> None:
        key = ("ds0-df0", "tiny-a", "knn-32", "vampire")
        self.fixture.outputs[key].write_text("")
        self.fixture.logs[key].write_text(
            "Killed\n"
            "make[1]: *** [Makefile:9: target] Error 137\n"
            "% Aborted by signal SIGSEGV on child.p\n"
            "use '--traceback on' to invoke a debugger and get a human-readable stack trace\n"
        )
        self.load()  # Empty Vampire output is only the documented backstop result.

    def test_empty_e_output_is_rejected(self) -> None:
        key = ("ds0-df0", "tiny-a", "knn-32", "eprover")
        self.fixture.outputs[key].write_text("")
        with self.assertRaisesRegex(ValueError, "empty E prover output"):
            self.load()

    def test_metadata_impossible_combinations_are_rejected(self) -> None:
        path = self.fixture.metadata_paths["ds0-df0", "tiny-a", "knn-32"]
        path.write_text("d_size=0 min_occ=1 median_occ=2 k=0\n")
        with self.assertRaisesRegex(ValueError, "d_size=0 iff"):
            self.load()

        path.write_text("d_size=8 min_occ=none median_occ=none k=0\n")
        with self.assertRaisesRegex(ValueError, "d_size=0 iff"):
            self.load()

    def test_missing_malformed_conflicting_metadata_and_k_are_rejected(self) -> None:
        path = self.fixture.metadata_paths["ds0-df0", "tiny-a", "knn-32"]
        path.unlink()
        with self.assertRaisesRegex(ValueError, "metadata is missing"):
            self.load()

        # Independent fixtures keep each failure focused.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fixture = Fixture(root)
            fixture.metadata_paths["ds0-df0", "tiny-a", "knn-32"].write_text(
                "d_size=8 min_occ=1 k=0\n"
            )
            with self.assertRaisesRegex(ValueError, "malformed selection metadata"):
                summarizer.load_grid(root, LABELS, AXES, fixture.provenance)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fixture = Fixture(root)
            fixture.metadata_paths["ds8-df4", "tiny-a", "nbayes-32"].write_text(
                "d_size=9 min_occ=1 median_occ=2 k=4\n"
            )
            with self.assertRaisesRegex(ValueError, "conflicting metadata for goal"):
                summarizer.load_grid(root, LABELS, AXES, fixture.provenance)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fixture = Fixture(root)
            fixture.metadata_paths["ds8-df4", "tiny-a", "knn-32"].write_text(
                "d_size=8 min_occ=1 median_occ=2 k=3\n"
            )
            with self.assertRaisesRegex(ValueError, "metadata k conflicts"):
                summarizer.load_grid(root, LABELS, AXES, fixture.provenance)


if __name__ == "__main__":
    unittest.main()
