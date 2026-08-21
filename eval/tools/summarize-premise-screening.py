#!/usr/bin/env python3
"""Validate and summarize a premise-selection screening grid.

Decision metrics compare sets of solved GoalKeys, where a GoalKey is the pair
(corpus, relative problem path). Exact prover/premise attempts are retained only
as diagnostics. The grid engine supplies active axes through the documented
COQHAMMER_GRID_* environment variables; this file does not duplicate them.
"""

from __future__ import annotations

import csv
import hashlib
import json
import os
import re
import sys
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Callable, Iterable

BASELINE = "ds0-df0"
BUCKETS = ("<=1", "<=4", "rest")
# Premise count guarded by the goal-level regression guard. The emitted TSV
# columns, the summary scope and the analysis heading all spell this count out
# ("n32_*", "N=32") because eval/artifacts/premise-screening/summary.tsv is
# already published with those names; deriving every one of them from this
# constant keeps the names and the guarded count from drifting apart silently.
# validate_guarded_premise_axis() refuses an axis in which no premise selector
# has this count, so the guard can never report "clear" without measuring.
GUARD_PREMISE_COUNT = 32
GUARD_SCOPE = f"n{GUARD_PREMISE_COUNT}"
GUARD_PREMISE_FIELD = f"N={GUARD_PREMISE_COUNT}"
GUARD_GAINS_COLUMN = f"{GUARD_SCOPE}_goal_gains"
GUARD_LOSSES_COLUMN = f"{GUARD_SCOPE}_goal_losses"
GUARD_NET_COLUMN = f"{GUARD_SCOPE}_goal_net"
GUARD_FLAG_COLUMN = f"{GUARD_SCOPE}_regression_flag"
# git rev-parse prints 40 hex characters in a SHA-1 repository and 64 in a
# SHA-256 one; the grid engine accepts either (commit_pattern in
# grid-engine.sh), so this checker must not narrow that to SHA-1 alone.
COMMIT_RE = re.compile(r"[0-9a-f]{40}|[0-9a-f]{64}")
LABEL_RE = re.compile(r"ds(0|[1-9][0-9]*)-df(0|[1-9][0-9]*)")
META_RE = re.compile(
    r"d_size=(0|[1-9][0-9]*) "
    r"min_occ=(none|0|[1-9][0-9]*) "
    r"median_occ=(none|0|[1-9][0-9]*) "
    r"k=(0|[1-9][0-9]*)\n?"
)
STATUS_RE = re.compile(r"prover_exit=(0|[1-9][0-9]*)\n")
SZS_RE = re.compile(r"\bSZS status ([A-Za-z]+)\b")
ATP_SUCCESS = frozenset(("Theorem", "Unsatisfiable"))
TERMINAL_SZS = frozenset(
    (
        "Theorem", "CounterTheorem", "Unsatisfiable", "Satisfiable",
        "CounterSatisfiable", "ContradictoryAxioms", "GaveUp", "Timeout",
        "ResourceOut", "MemoryOut", "Unknown", "Incomplete",
    )
)
CRASH_RE = re.compile(
    r"(segmentation fault|segfault|core dumped|bus error|floating point exception|"
    r"aborted|anomaly|assertion[^\r\n]*failed|uncaught exception|traceback|"
    r"command not found|no such file or directory|no rule to make target|"
    r"permission denied|cannot execute|exec[^\r\n]*failed|"
    r"(^|[^A-Za-z])killed([^A-Za-z]|$)|out of memory|cannot allocate memory|"
    r"no space left on device|input/output error|stack overflow|broken pipe|"
    r"(^|[^A-Za-z])(fatal|internal|system)[\s_-]+(error|exception)([\s:]|$))",
    re.IGNORECASE | re.MULTILINE,
)
PARSE_ERROR_RE = re.compile(
    r"(^|[^A-Za-z])(parse|input)?[\s_-]*error([:\s]|$)",
    re.IGNORECASE | re.MULTILINE,
)
ROUTINE_MAKE_ERROR_RE = re.compile(
    # "make -C" implies "-w", so the directory notices always carry the quoted
    # path: "make: Entering directory '/.../eval/atp'". Anchoring right after
    # the phrase would never match one.
    r"^make(?:\[[0-9]+\])?: (?:\*\*\* .* Error [0-9]+|"
    r"Target .* not remade because of errors\.|"
    r"(?:Entering|Leaving) directory .*)$",
    re.IGNORECASE,
)
BACKSTOP_LINE_RE = re.compile(
    r"^(?:Killed|make(?:\[[0-9]+\])?: \*\*\* \[[^]]*\] Error 137)$"
)
STRATEGY_ABORT_RE = re.compile(r"% Aborted by signal [A-Z]+ on \S*")
STRATEGY_HINT = "use '--traceback on' to invoke a debugger and get a human-readable stack trace"

GoalKey = tuple[str, str]
AttemptKey = tuple[str, str, str, str]


@dataclass(frozen=True)
class Axes:
    premises: tuple[str, ...]
    provers: tuple[str, ...]
    corpora: tuple[str, ...]
    corpus_mode: str


@dataclass(frozen=True)
class Provenance:
    repository_commit: str
    grid_script_sha256: str
    checkpoint_helper_sha256: str
    compile_supervisor_sha256: str
    compile_timeout: str
    compile_timeout_grace: str
    prover_timeout: str
    consistency_timeout: str
    consistency_premise: str
    labels: dict[str, dict[str, str]]
    corpora: dict[str, dict[str, object]]


@dataclass(frozen=True)
class Metadata:
    d_size: int
    min_occ: int | None
    median_occ: int | None
    k: int

    @property
    def intrinsic(self) -> tuple[int, int | None, int | None]:
        return self.d_size, self.min_occ, self.median_occ

    @property
    def bucket(self) -> str:
        if self.min_occ is not None and self.min_occ <= 1:
            return "<=1"
        if self.min_occ is not None and self.min_occ <= 4:
            return "<=4"
        return "rest"


@dataclass(frozen=True)
class Attempt:
    success: bool
    bucket: str


@dataclass(frozen=True)
class Stats:
    attempts: int
    solved_attempts: int
    baseline_solved_attempts: int
    attempt_gains: int
    attempt_losses: int
    goals: int
    solved_goals: int
    baseline_solved_goals: int
    goal_gains: int
    goal_losses: int
    guard_goal_gains: int
    guard_goal_losses: int

    @property
    def attempt_net(self) -> int:
        return self.solved_attempts - self.baseline_solved_attempts

    @property
    def goal_net(self) -> int:
        return self.solved_goals - self.baseline_solved_goals

    @property
    def guard_goal_net(self) -> int:
        return self.guard_goal_gains - self.guard_goal_losses


@dataclass(frozen=True)
class LoadedGrid:
    attempts: dict[str, dict[AttemptKey, Attempt]]
    label_options: dict[str, tuple[int, int]]
    axes: Axes


def parse_label(label: str) -> tuple[int, int]:
    match = LABEL_RE.fullmatch(label)
    if match is None:
        raise ValueError(f"malformed premise-grid label: {label}")
    return int(match.group(1)), int(match.group(2))


def _axis_from_environment(name: str) -> tuple[str, ...]:
    variable = f"COQHAMMER_GRID_{name}"
    raw = os.environ.get(variable)
    if raw is None:
        raise ValueError(f"grid engine did not supply {variable}")
    values = tuple(raw.splitlines())
    if not values or any(not value for value in values):
        raise ValueError(f"{variable} must contain a nonempty newline-separated axis")
    if len(values) != len(set(values)):
        raise ValueError(f"{variable} contains a duplicate value")
    return values


def axes_from_environment() -> Axes:
    mode = os.environ.get("COQHAMMER_GRID_CORPUS_MODE")
    if mode not in ("sample", "full"):
        raise ValueError("COQHAMMER_GRID_CORPUS_MODE must be 'sample' or 'full'")
    axes = Axes(
        premises=_axis_from_environment("PREMISES"),
        provers=_axis_from_environment("PROVERS"),
        corpora=_axis_from_environment("CORPORA"),
        corpus_mode=mode,
    )
    unsupported = set(axes.provers) - {"eprover", "vampire"}
    if unsupported:
        raise ValueError(f"unsupported premise-screening prover: {sorted(unsupported)[0]}")
    for premise in axes.premises:
        premise_count(premise)
    validate_guarded_premise_axis(axes.premises)
    return axes


def _unique_json_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON object key: {key}")
        result[key] = value
    return result


def provenance_from_environment(labels: list[str], axes: Axes) -> Provenance:
    raw = os.environ.get("COQHAMMER_GRID_EXPECTED_PROVENANCE")
    if raw is None:
        raise ValueError("grid engine did not supply COQHAMMER_GRID_EXPECTED_PROVENANCE")
    try:
        data = json.loads(raw, object_pairs_hook=_unique_json_object)
    except json.JSONDecodeError as error:
        raise ValueError("COQHAMMER_GRID_EXPECTED_PROVENANCE is not valid JSON") from error
    top_keys = {
        "repository_commit", "grid_script_sha256", "checkpoint_helper_sha256",
        "compile_supervisor_sha256", "compile_timeout", "compile_timeout_grace",
        "prover_timeout", "consistency_timeout", "labels", "corpora",
    }
    if not isinstance(data, dict) or set(data) != top_keys:
        raise ValueError("expected provenance has the wrong top-level schema")
    scalar_keys = top_keys - {"labels", "corpora"}
    if any(not isinstance(data[key], str) or not data[key] for key in scalar_keys):
        raise ValueError("expected provenance scalar fields must be nonempty strings")
    label_data = data["labels"]
    corpus_data = data["corpora"]
    if not isinstance(label_data, dict) or not isinstance(corpus_data, dict):
        raise ValueError("expected provenance labels and corpora must be JSON objects")
    if COMMIT_RE.fullmatch(data["repository_commit"]) is None:
        raise ValueError("expected provenance has an invalid repository commit")
    for key in ("grid_script_sha256", "checkpoint_helper_sha256",
                "compile_supervisor_sha256"):
        if re.fullmatch(r"[0-9a-f]{64}", data[key]) is None:
            raise ValueError(f"expected provenance has an invalid hash: {key}")
    for key in ("compile_timeout", "compile_timeout_grace",
                "prover_timeout", "consistency_timeout"):
        if re.fullmatch(r"[1-9][0-9]*", data[key]) is None:
            raise ValueError(f"expected provenance has an invalid timeout: {key}")
    if set(label_data) != set(labels) or set(corpus_data) != set(axes.corpora):
        raise ValueError("expected provenance labels/corpora conflict with active axes")
    label_keys = {"config", "install_commit", "install_kind", "install_manifest_sha256"}
    for label, fields in label_data.items():
        if not isinstance(fields, dict) or set(fields) != label_keys or any(
            not isinstance(value, str) or not value for value in fields.values()
        ):
            raise ValueError(f"expected provenance has malformed label fields: {label}")
        if COMMIT_RE.fullmatch(fields["install_commit"]) is None or \
                re.fullmatch(r"[0-9a-f]{64}", fields["install_manifest_sha256"]) is None:
            raise ValueError(f"expected provenance has invalid install hashes: {label}")
        if fields["install_kind"] not in ("current", "configuration"):
            raise ValueError(f"expected provenance has invalid install kind: {label}")
    corpus_keys = {"mode", "source", "sha256", "trees", "files"}
    for corpus, fields in corpus_data.items():
        if not isinstance(fields, dict) or set(fields) != corpus_keys:
            raise ValueError(f"expected provenance has malformed corpus fields: {corpus}")
        if not isinstance(fields["mode"], str) or not isinstance(fields["source"], str) or \
                fields["mode"] != axes.corpus_mode:
            raise ValueError(f"expected provenance has conflicting corpus fields: {corpus}")
        if not isinstance(fields["sha256"], str) or re.fullmatch(r"[0-9a-f]{64}", fields["sha256"]) is None:
            raise ValueError(f"expected provenance has invalid corpus hash: {corpus}")
        if any(not isinstance(fields[key], list) or
               any(not isinstance(item, str) or not item for item in fields[key])
               for key in ("trees", "files")):
            raise ValueError(f"expected provenance has malformed corpus inputs: {corpus}")
        if not fields["trees"] and not fields["files"]:
            raise ValueError(f"expected provenance has no corpus inputs: {corpus}")
    consistency_premise = os.environ.get("COQHAMMER_GRID_CONSISTENCY_PREMISE")
    if consistency_premise not in axes.premises:
        raise ValueError("COQHAMMER_GRID_CONSISTENCY_PREMISE is not an active premise")
    return Provenance(
        repository_commit=data["repository_commit"],
        grid_script_sha256=data["grid_script_sha256"],
        checkpoint_helper_sha256=data["checkpoint_helper_sha256"],
        compile_supervisor_sha256=data["compile_supervisor_sha256"],
        compile_timeout=data["compile_timeout"],
        compile_timeout_grace=data["compile_timeout_grace"],
        prover_timeout=data["prover_timeout"],
        consistency_timeout=data["consistency_timeout"],
        consistency_premise=consistency_premise,
        labels=data["labels"],
        corpora=data["corpora"],
    )


def hash_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def hash_tree(path: Path) -> str:
    root = path.resolve()
    if not root.is_dir():
        raise ValueError(f"provenance input directory not found: {path}")
    digest = hashlib.sha256()
    files = sorted(item for item in root.rglob("*") if item.is_file())
    for item in files:
        relative = item.relative_to(root)
        if ".git" in relative.parts or "_build" in relative.parts:
            continue
        encoded = relative.as_posix().encode()
        digest.update(len(encoded).to_bytes(8, "big"))
        digest.update(encoded)
        with item.open("rb") as source:
            for chunk in iter(lambda: source.read(1024 * 1024), b""):
                digest.update(chunk)
    return digest.hexdigest()


def corpus_input_hash(fields: dict[str, object]) -> str:
    digests = ""
    for filename in fields["files"]:
        path = Path(filename)
        if not path.is_file():
            raise ValueError(f"provenance input file not found: {path}")
        digests += hash_file(path)
    for directory in fields["trees"]:
        digests += hash_tree(Path(directory))
    return hashlib.sha256(digests.encode()).hexdigest()


def expected_preamble(label: str) -> bytes:
    slots, features = parse_label(label)
    return (
        f"Set Hammer DefinitionPremises {slots}.\n"
        f"Set Hammer DefinitionFeatures {features}.\n"
    ).encode()


def parse_metadata(path: Path) -> Metadata:
    if not path.is_file():
        raise ValueError(f"required selection metadata is missing: {path}")
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        raise ValueError(f"could not read selection metadata {path}: {error}") from error
    match = META_RE.fullmatch(text)
    if match is None:
        raise ValueError(f"malformed selection metadata: {path}")
    d_size = int(match.group(1))
    min_text, median_text = match.group(2), match.group(3)
    occurrences_none = min_text == "none" and median_text == "none"
    if (min_text == "none") != (median_text == "none"):
        raise ValueError(f"conflicting none occurrence fields in metadata: {path}")
    if (d_size == 0) != occurrences_none:
        raise ValueError(f"d_size=0 iff occurrence statistics are none: {path}")
    min_occ = None if occurrences_none else int(min_text)
    median_occ = None if occurrences_none else int(median_text)
    if min_occ is not None and median_occ is not None and median_occ < min_occ:
        raise ValueError(f"median_occ is smaller than min_occ in metadata: {path}")
    k = int(match.group(4))
    if k > d_size:
        raise ValueError(f"metadata k exceeds d_size: {path}")
    return Metadata(d_size, min_occ, median_occ, k)


def generation_status(corpus_dir: Path) -> None:
    path = corpus_dir / "generation.status"
    expected = ["generation_failed=0", "generation_exit=0"]
    if not path.is_file() or path.read_bytes() != ("\n".join(expected) + "\n").encode():
        raise ValueError(f"incomplete generation status: {path}")


def listed_files(path: Path, expected_root: Path, suffix: str) -> dict[str, Path]:
    if not path.is_file():
        raise ValueError(f"required checkpoint list is missing: {path}")
    root = expected_root.resolve()
    result: dict[str, Path] = {}
    for line_number, line in enumerate(path.read_text(errors="replace").splitlines(), 1):
        if not line.strip():
            continue
        item = Path(line.strip())
        if not item.is_file():
            raise ValueError(f"checkpoint list {path} names missing output: {item}")
        try:
            relative = item.resolve().relative_to(root).as_posix()
        except ValueError as error:
            raise ValueError(
                f"checkpoint list {path}:{line_number} names a file outside {expected_root}: {item}"
            ) from error
        if PurePosixPath(relative).suffix != suffix:
            raise ValueError(f"checkpoint list {path}:{line_number} has wrong suffix: {item}")
        if relative in result:
            raise ValueError(f"checkpoint list {path} repeats goal identity: {relative}")
        result[relative] = item
    if not result:
        raise ValueError(f"checkpoint list is empty: {path}")
    actual = {
        item.resolve().relative_to(root).as_posix()
        for item in expected_root.rglob(f"*{suffix}") if item.is_file()
    }
    if actual != set(result):
        # The directory is the ground truth here: every listed entry was already
        # is_file()-verified above, so the only real failure is an output the
        # list omits. Passing the list as "expected" would report exactly that
        # omission as an "unexpected" file.
        difference = describe_set_difference(actual, set(result))
        raise ValueError(f"checkpoint list does not exactly cover {expected_root}: {difference}")
    return result


def parse_checkpoint(path: Path) -> dict[str, str]:
    if not path.is_file():
        raise ValueError(f"completed checkpoint is missing: {path}")
    fields: dict[str, str] = {}
    for number, line in enumerate(path.read_text(errors="replace").splitlines(), 1):
        if "=" not in line:
            raise ValueError(f"malformed completed prover checkpoint {path}:{number}")
        key, value = line.split("=", 1)
        if not key or key in fields:
            raise ValueError(f"duplicate or empty checkpoint field in {path}:{number}")
        fields[key] = value
    return fields


def checkpoint_expected(
    stage: str, label: str, corpus: str, provenance: Provenance,
    premise: str | None = None, prover: str | None = None,
    input_sha256: str | None = None,
) -> dict[str, str]:
    label_fields = provenance.labels[label]
    corpus_fields = provenance.corpora[corpus]
    expected = {
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
        "hook_preamble_sha256": hashlib.sha256(expected_preamble(label)).hexdigest(),
        "hook_preamble_file": "hook-preamble.v",
    }
    if stage == "generation":
        expected.update({
            "compile_supervisor_sha256": provenance.compile_supervisor_sha256,
            "compile_timeout": provenance.compile_timeout,
            "compile_timeout_grace": provenance.compile_timeout_grace,
        })
    if stage in ("prover", "consistency"):
        assert premise is not None and prover is not None and input_sha256 is not None
        expected.update({
            "premise": premise,
            "prover": prover,
            "timeout": (provenance.prover_timeout if stage == "prover"
                        else provenance.consistency_timeout),
            "input_sha256": input_sha256,
        })
    return expected


def validate_checkpoint(path: Path, expected: dict[str, str]) -> None:
    fields = parse_checkpoint(path)
    if set(fields) != set(expected):
        missing = sorted(set(expected) - set(fields))
        extra = sorted(set(fields) - set(expected))
        detail = f"missing={missing}, extra={extra}"
        raise ValueError(f"completed checkpoint has wrong schema in {path}: {detail}")
    for key, value in expected.items():
        if fields[key] != value:
            raise ValueError(
                f"completed checkpoint has wrong {key} in {path}: "
                f"expected {value}, found {fields[key]!r}"
            )


def validate_preamble(corpus_dir: Path, label: str) -> None:
    path = corpus_dir / "hook-preamble.v"
    if not path.is_file():
        raise ValueError(f"hook preamble is missing: {path}")
    preamble = expected_preamble(label)
    expected_hash = hashlib.sha256(preamble).hexdigest()
    if hash_file(path) != expected_hash:
        raise ValueError(f"hook preamble hash does not match label {label}: {path}")
    if path.read_bytes() != preamble:
        raise ValueError(f"hook preamble does not exactly match label {label}: {path}")


def validate_status(path: Path) -> None:
    if not path.is_file() or STATUS_RE.fullmatch(path.read_text(errors="replace")) is None:
        raise ValueError(f"prover status is missing or not a single integer field: {path}")


def _filtered_log(text: str, ignore_backstop_kills: bool) -> str:
    if ignore_backstop_kills:
        lines = [
            line for line in text.splitlines() if BACKSTOP_LINE_RE.fullmatch(line) is None
        ]
        text = "\n".join(lines)
    # A portfolio prover reports a child strategy that died while the run itself
    # carried on to a terminal SZS status; every tier drops those notices, as
    # strip_portfolio_strategy_aborts does in grid-checkpoint-lib.sh.
    text = STRATEGY_ABORT_RE.sub("", text).replace(STRATEGY_HINT, "")
    return text


def log_has_crash_or_error(text: str, *, ignore_backstop_kills: bool) -> bool:
    """Scan a raw log the way the grid engine's shell helpers do.

    ``ignore_backstop_kills=True`` mirrors
    ``log_has_crash_or_error_ignoring_backstop_kills``: it drops the "Killed" and
    "Error 137" lines that htimeout's SIGKILL backstop leaves behind. ``False``
    mirrors ``log_has_crash_or_error_ignoring_strategy_aborts``, which keeps
    them, and is the tier the engine applies to the consistency stage
    (eval/grid-engine.sh). Picking the wrong tier would let this checker accept
    a run the engine itself failed.
    """
    filtered = _filtered_log(text, ignore_backstop_kills)
    if CRASH_RE.search(filtered) is not None:
        return True
    nonroutine = "\n".join(
        line for line in filtered.splitlines() if ROUTINE_MAKE_ERROR_RE.fullmatch(line) is None
    )
    return PARSE_ERROR_RE.search(nonroutine) is not None


def validate_log(path: Path) -> None:
    if not path.is_file():
        raise ValueError(f"required prover log is missing: {path}")
    # The prover stage runs each ATP under htimeout, so the engine accepts the
    # backstop's kill reports here (expected_atp_outputs_are_complete).
    if log_has_crash_or_error(path.read_text(errors="replace"), ignore_backstop_kills=True):
        raise ValueError(f"prover log records a crash or infrastructure error: {path}")


def terminal_status(path: Path, allow_empty_vampire: bool = False, prover: str = "") -> str | None:
    text = path.read_text(errors="replace")
    if not text:
        if allow_empty_vampire and prover == "vampire":
            return None
        if prover == "eprover":
            raise ValueError(f"empty E prover output is not a completed result: {path}")
        raise ValueError(f"empty consistency output is not a completed result: {path}")
    statuses = SZS_RE.findall(text)
    if len(statuses) != 1 or statuses[0] not in TERMINAL_SZS:
        raise ValueError(f"prover output must contain exactly one allowed terminal SZS status: {path}")
    return statuses[0]


def output_success(path: Path, prover: str) -> bool:
    return terminal_status(path, allow_empty_vampire=True, prover=prover) in ATP_SUCCESS


def validate_integer_status(path: Path, key: str) -> None:
    pattern = re.compile(rf"{re.escape(key)}=(0|[1-9][0-9]*)\n")
    if not path.is_file() or pattern.fullmatch(path.read_text(errors="replace")) is None:
        raise ValueError(f"status is missing or not a single integer field: {path}")


def validate_consistency(
    corpus_dir: Path, label: str, corpus: str, prover: str,
    generated: dict[str, Path], provenance: Provenance, input_hash: str,
) -> None:
    premise = provenance.consistency_premise
    stem = f"{prover}-{premise}"
    validate_checkpoint(
        corpus_dir / f"consistency-{stem}.done",
        checkpoint_expected("consistency", label, corpus, provenance,
                            premise, prover, input_hash),
    )
    status_path = corpus_dir / f"consistency-{stem}.status"
    if not status_path.is_file() or status_path.read_text(errors="replace") != "consistency_exit=0\n":
        raise ValueError(f"incomplete consistency status: {status_path}")
    work = corpus_dir / "consistency" / stem
    outputs = listed_files(
        corpus_dir / f"consistency-outputs-{stem}.lst", work / "outputs", ".p"
    )
    expected_names: dict[str, str] = {}
    for relative in generated:
        name = PurePosixPath(relative).name
        if name in expected_names:
            raise ValueError(f"consistency inputs have colliding basenames: {relative}")
        expected_names[name] = relative
    if set(outputs) != set(expected_names):
        difference = describe_set_difference(set(expected_names), set(outputs))
        raise ValueError(
            f"consistency outputs do not preserve inputs for {label}/{corpus}/{prover}: "
            f"{difference}"
        )
    inconsistent = {"Theorem", "Unsatisfiable", "ContradictoryAxioms"}
    for name, output in outputs.items():
        raw = work / "raw" / name
        # The consistency stage fails on a backstop kill (grid-engine.sh uses
        # log_has_crash_or_error_ignoring_strategy_aborts there), so this
        # checker must not accept a "Killed" the engine rejects.
        if not raw.is_file() or log_has_crash_or_error(
            raw.read_text(errors="replace"), ignore_backstop_kills=False
        ):
            raise ValueError(f"consistency raw log records a crash or error: {raw}")
        validate_integer_status(work / "status" / f"{name}.status", "command_exit")
        status = terminal_status(output)
        if status in inconsistent:
            raise ValueError(f"consistency result reports inconsistent premises: {output}")


def premise_count(premise: str) -> int:
    match = re.fullmatch(r"[^/]+-([1-9][0-9]*)", premise)
    if match is None:
        raise ValueError(f"premise axis does not end in a positive count: {premise}")
    return int(match.group(1))


def validate_guarded_premise_axis(premises: Iterable[str]) -> None:
    if not any(premise_count(premise) == GUARD_PREMISE_COUNT for premise in premises):
        raise ValueError(
            f"premise axis has no selector with GUARD_PREMISE_COUNT="
            f"{GUARD_PREMISE_COUNT}, so the goal-level regression guard would "
            f"measure nothing; update GUARD_PREMISE_COUNT in "
            f"{Path(__file__).name} together with GRID_PREMISES in "
            f"run-premise-screening-grid.sh"
        )


def describe_set_difference(expected: set[str], actual: set[str]) -> str:
    missing = sorted(expected - actual)
    extra = sorted(actual - expected)
    parts = []
    if missing:
        parts.append(f"missing {missing[0]}")
    if extra:
        parts.append(f"unexpected {extra[0]}")
    return "; ".join(parts)


def load_grid(
    root: Path, labels: list[str], axes: Axes, provenance: Provenance
) -> LoadedGrid:
    if not labels:
        raise ValueError("no premise-grid labels were supplied")
    if len(labels) != len(set(labels)):
        raise ValueError("premise-grid labels contain a duplicate")
    if axes.corpus_mode not in ("sample", "full"):
        raise ValueError(f"invalid expected corpus mode: {axes.corpus_mode}")
    if not axes.premises or not axes.provers or not axes.corpora:
        raise ValueError("premise-grid axes must not be empty")
    validate_guarded_premise_axis(axes.premises)
    label_options = {label: parse_label(label) for label in labels}
    if set(provenance.labels) != set(labels) or set(provenance.corpora) != set(axes.corpora):
        raise ValueError("expected provenance conflicts with requested grid")
    if provenance.consistency_premise not in axes.premises:
        raise ValueError("consistency premise is not active")
    for corpus, fields in provenance.corpora.items():
        actual = corpus_input_hash(fields)
        if actual != fields["sha256"]:
            raise ValueError(
                f"current corpus input hash differs from expected provenance for {corpus}: "
                f"expected {fields['sha256']}, found {actual}"
            )
    if BASELINE not in label_options:
        raise ValueError(f"required baseline label is missing: {BASELINE}")

    attempts: dict[str, dict[AttemptKey, Attempt]] = {}
    # Only a cross-label/premise consistency check: a GoalKey's intrinsic
    # metadata may not depend on which label or premise selector produced it.
    # Buckets travel on Attempt.bucket, so nothing outside this loop reads it.
    goal_metadata: dict[GoalKey, Metadata] = {}
    metadata_sources: dict[GoalKey, Path] = {}
    corpus_goals: dict[str, set[str]] = {}

    for label in labels:
        slots, _features = label_options[label]
        label_dir = root / label
        if not label_dir.is_dir():
            raise ValueError(f"required label checkpoints are missing: {label_dir}")
        label_attempts: dict[AttemptKey, Attempt] = {}
        for corpus in axes.corpora:
            corpus_dir = label_dir / corpus
            if not corpus_dir.is_dir():
                raise ValueError(f"required corpus checkpoints are missing: {corpus_dir}")
            validate_preamble(corpus_dir, label)
            validate_checkpoint(
                corpus_dir / "generate.done",
                checkpoint_expected("generation", label, corpus, provenance),
            )
            generation_status(corpus_dir)
            consistency_generated: dict[str, Path] | None = None
            consistency_input_hash: str | None = None
            for premise in axes.premises:
                problem_root = corpus_dir / "atp-problems" / premise
                generated = listed_files(
                    corpus_dir / f"generated-{premise}.lst", problem_root, ".p"
                )
                identities = set(generated)
                input_hash = hash_tree(problem_root)
                if premise == provenance.consistency_premise:
                    consistency_generated = generated
                    consistency_input_hash = input_hash
                if corpus in corpus_goals and identities != corpus_goals[corpus]:
                    difference = describe_set_difference(corpus_goals[corpus], identities)
                    raise ValueError(
                        f"conflicting goal identities for {label}/{corpus}/{premise}: {difference}"
                    )
                corpus_goals.setdefault(corpus, identities)

                count = premise_count(premise)
                metadata_for_goal: dict[str, Metadata] = {}
                for relative, problem in generated.items():
                    metadata_path = problem.with_suffix(".meta")
                    metadata = parse_metadata(metadata_path)
                    expected_k = min(metadata.d_size, slots, (count + 7) // 8)
                    if metadata.k != expected_k:
                        raise ValueError(
                            f"metadata k conflicts with label/count in {metadata_path}: "
                            f"expected {expected_k}, found {metadata.k}"
                        )
                    goal = (corpus, relative)
                    previous = goal_metadata.get(goal)
                    if previous is not None and metadata.intrinsic != previous.intrinsic:
                        raise ValueError(
                            f"conflicting metadata for goal {corpus}/{relative}: "
                            f"{metadata_sources[goal]} vs {metadata_path}"
                        )
                    if previous is None:
                        goal_metadata[goal] = metadata
                        metadata_sources[goal] = metadata_path
                    metadata_for_goal[relative] = metadata

                for prover in axes.provers:
                    stem = f"{prover}-{premise}"
                    validate_checkpoint(
                        corpus_dir / f"prover-{stem}.done",
                        checkpoint_expected("prover", label, corpus, provenance,
                                            premise, prover, input_hash),
                    )
                    validate_status(corpus_dir / f"prover-{stem}.status")
                    validate_log(corpus_dir / f"{stem}.log")
                    output_root = corpus_dir / "prover-outputs" / stem
                    outputs = listed_files(
                        corpus_dir / f"prover-outputs-{stem}.lst", output_root, ".p"
                    )
                    if set(outputs) != identities:
                        difference = describe_set_difference(identities, set(outputs))
                        raise ValueError(
                            f"prover outputs do not preserve goal identities for "
                            f"{label}/{corpus}/{premise}/{prover}: {difference}"
                        )
                    for relative, output in outputs.items():
                        key = (corpus, premise, prover, relative)
                        label_attempts[key] = Attempt(
                            success=output_success(output, prover),
                            bucket=metadata_for_goal[relative].bucket,
                        )
            assert consistency_generated is not None and consistency_input_hash is not None
            for prover in axes.provers:
                validate_consistency(
                    corpus_dir, label, corpus, prover, consistency_generated,
                    provenance, consistency_input_hash,
                )
        attempts[label] = label_attempts

    baseline_keys = set(attempts[BASELINE])
    for label, label_attempts in attempts.items():
        if set(label_attempts) != baseline_keys:
            raise ValueError(f"attempt identities for {label} conflict with {BASELINE}")
    return LoadedGrid(attempts, label_options, axes)


def goal_of(key: AttemptKey) -> GoalKey:
    return key[0], key[3]


def _solved_goals(keys: set[AttemptKey], attempts: dict[AttemptKey, Attempt]) -> set[GoalKey]:
    return {goal_of(key) for key in keys if attempts[key].success}


def collect_stats(
    attempts: dict[AttemptKey, Attempt],
    baseline: dict[AttemptKey, Attempt],
    predicate: Callable[[AttemptKey, Attempt], bool] = lambda _key, _attempt: True,
) -> Stats:
    keys = {key for key, attempt in attempts.items() if predicate(key, attempt)}
    solved_attempts = {key for key in keys if attempts[key].success}
    baseline_solved_attempts = {key for key in keys if baseline[key].success}
    solved_goals = _solved_goals(keys, attempts)
    baseline_solved_goals = _solved_goals(keys, baseline)
    guard_keys = {key for key in keys if premise_count(key[1]) == GUARD_PREMISE_COUNT}
    guard_solved = _solved_goals(guard_keys, attempts)
    baseline_guard_solved = _solved_goals(guard_keys, baseline)
    return Stats(
        attempts=len(keys),
        solved_attempts=len(solved_attempts),
        baseline_solved_attempts=len(baseline_solved_attempts),
        attempt_gains=len(solved_attempts - baseline_solved_attempts),
        attempt_losses=len(baseline_solved_attempts - solved_attempts),
        goals=len({goal_of(key) for key in keys}),
        solved_goals=len(solved_goals),
        baseline_solved_goals=len(baseline_solved_goals),
        goal_gains=len(solved_goals - baseline_solved_goals),
        goal_losses=len(baseline_solved_goals - solved_goals),
        guard_goal_gains=len(guard_solved - baseline_guard_solved),
        guard_goal_losses=len(baseline_guard_solved - guard_solved),
    )


def regression_flag(label: str, stats: Stats) -> str:
    if label == BASELINE:
        return "baseline"
    return "REGRESSION" if stats.guard_goal_losses else "clear"


def summary_row(
    grid: LoadedGrid,
    label: str,
    scope: str,
    corpus: str,
    premise: str,
    prover: str,
    bucket: str,
    stats: Stats,
) -> dict[str, object]:
    options = grid.label_options[label]
    diagnostic = scope == "exact_attempt"
    return {
        "label": label,
        "definition_premises": options[0],
        "definition_features": options[1],
        "corpus_mode": grid.axes.corpus_mode,
        "scope": scope,
        "corpus": corpus,
        "premise": premise,
        "prover": prover,
        "min_occ_bucket": bucket,
        # Exact-attempt rows deliberately leave every decision field blank: a
        # loss by one prover is not a GoalKey loss if another active attempt
        # still solves that goal.
        "goals": "" if diagnostic else stats.goals,
        "solved_goals": "" if diagnostic else stats.solved_goals,
        "baseline_solved_goals": "" if diagnostic else stats.baseline_solved_goals,
        "goal_net": "" if diagnostic else stats.goal_net,
        "goal_gains": "" if diagnostic else stats.goal_gains,
        "goal_losses": "" if diagnostic else stats.goal_losses,
        GUARD_GAINS_COLUMN: "" if diagnostic else stats.guard_goal_gains,
        GUARD_LOSSES_COLUMN: "" if diagnostic else stats.guard_goal_losses,
        GUARD_NET_COLUMN: "" if diagnostic else stats.guard_goal_net,
        GUARD_FLAG_COLUMN: "diagnostic" if diagnostic else regression_flag(label, stats),
        "attempts": stats.attempts,
        "solved_attempts": stats.solved_attempts,
        "baseline_solved_attempts": stats.baseline_solved_attempts,
        "attempt_net": stats.attempt_net,
        "attempt_gains": stats.attempt_gains,
        "attempt_losses": stats.attempt_losses,
    }


def make_summary_rows(grid: LoadedGrid, labels: list[str]) -> list[dict[str, object]]:
    baseline = grid.attempts[BASELINE]
    rows: list[dict[str, object]] = []
    for label in labels:
        attempts = grid.attempts[label]

        def add(scope: str, corpus: str = "all", premise: str = "all",
                prover: str = "all", bucket: str = "all",
                predicate: Callable[[AttemptKey, Attempt], bool] = lambda _k, _a: True,
                label: str = label,
                attempts: dict[AttemptKey, Attempt] = attempts) -> None:
            rows.append(summary_row(
                grid, label, scope, corpus, premise, prover, bucket,
                collect_stats(attempts, baseline, predicate),
            ))

        add("aggregate")
        for corpus in grid.axes.corpora:
            add("corpus", corpus=corpus,
                predicate=lambda key, _attempt, corpus=corpus: key[0] == corpus)
        for bucket in BUCKETS:
            add("bucket", bucket=bucket,
                predicate=lambda _key, attempt, bucket=bucket: attempt.bucket == bucket)
        add(GUARD_SCOPE, premise=GUARD_PREMISE_FIELD,
            predicate=lambda key, _attempt: premise_count(key[1]) == GUARD_PREMISE_COUNT)
        for corpus in grid.axes.corpora:
            for premise in grid.axes.premises:
                for prover in grid.axes.provers:
                    add(
                        "exact_attempt", corpus=corpus, premise=premise, prover=prover,
                        predicate=lambda key, _attempt, corpus=corpus, premise=premise,
                        prover=prover: key[:3] == (corpus, premise, prover),
                    )
    return rows


FIELDNAMES = (
    "label", "definition_premises", "definition_features", "corpus_mode", "scope",
    "corpus", "premise", "prover", "min_occ_bucket", "goals", "solved_goals",
    "baseline_solved_goals", "goal_net", "goal_gains", "goal_losses",
    GUARD_GAINS_COLUMN, GUARD_LOSSES_COLUMN, GUARD_NET_COLUMN, GUARD_FLAG_COLUMN,
    "attempts", "solved_attempts", "baseline_solved_attempts", "attempt_net",
    "attempt_gains", "attempt_losses",
)


def write_tsv(rows: Iterable[dict[str, object]], out: Path) -> None:
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("w", newline="") as stream:
        writer = csv.DictWriter(
            stream, delimiter="\t", fieldnames=FIELDNAMES, lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(rows)


def md_table(headers: list[str], rows: Iterable[Iterable[object]]) -> str:
    lines = [
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join("---" for _ in headers) + " |",
    ]
    lines.extend("| " + " | ".join(str(value) for value in row) + " |" for row in rows)
    return "\n".join(lines)


def signed(value: int) -> str:
    return f"{value:+d}"


def _decision_row(label: str, stats: Stats) -> tuple[object, ...]:
    return (
        label, stats.solved_goals, stats.baseline_solved_goals,
        signed(stats.goal_net), stats.goal_gains, stats.goal_losses,
    )


def write_analysis(grid: LoadedGrid, labels: list[str], out: Path) -> None:
    baseline = grid.attempts[BASELINE]

    def stats(label: str, predicate: Callable[[AttemptKey, Attempt], bool]) -> Stats:
        return collect_stats(grid.attempts[label], baseline, predicate)

    overall = {label: stats(label, lambda _k, _a: True) for label in labels}
    mode = grid.axes.corpus_mode.upper()
    mode_notice = (
        "**SMOKE DATA ONLY: sample corpora are not full-corpus decision evidence.**"
        if grid.axes.corpus_mode == "sample"
        else "**FULL-CORPUS MODE.**"
    )
    lines = [
        "# Premise-selection screening analysis",
        "",
        f"## Corpus mode: `{mode}`",
        "",
        mode_notice,
        "",
        (
            "Decision metrics use solved `GoalKey = (corpus, relative goal path)` sets. "
            "A goal is solved when any active premise-selector/prover attempt solves it. "
            "Gains and losses are paired set differences against `ds0-df0`; they are not "
            "attempt totals."
        ),
        "",
        f"## Aggregate solved goals vs `{BASELINE}`",
        "",
        md_table(
            ["label", "solved goals", "baseline", "net", "gains", "losses"],
            (_decision_row(label, overall[label]) for label in labels),
        ),
        "",
        "## Per-corpus solved goals",
        "",
        md_table(
            ["label", "corpus", "solved goals", "baseline", "net", "gains", "losses"],
            (
                (label, corpus, *_decision_row(label, stats(
                    label, lambda key, _a, corpus=corpus: key[0] == corpus,
                ))[1:])
                for label in labels for corpus in grid.axes.corpora
            ),
        ),
        "",
        "## Per-bucket solved goals",
        "",
        (
            "Buckets are exclusive: `<=4` means 2--4 after removing `<=1`; `rest` means "
            "greater than 4 or an empty seed (`d_size=0`, occurrence statistics `none`)."
        ),
        "",
        md_table(
            ["label", "bucket", "solved goals", "baseline", "net", "gains", "losses"],
            (
                (label, bucket, *_decision_row(label, stats(
                    label, lambda _key, attempt, bucket=bucket: attempt.bucket == bucket,
                ))[1:])
                for label in labels for bucket in BUCKETS
            ),
        ),
        "",
        f"## Goal-level {GUARD_PREMISE_FIELD} regression guard",
        "",
        (
            f"`REGRESSION` means at least one {GUARD_PREMISE_FIELD} GoalKey solved by the "
            f"baseline is no longer solved by any active {GUARD_PREMISE_FIELD} "
            "selector/prover for that label. Attempt-level losses cannot trigger this "
            "guard, and gains cannot hide a GoalKey loss."
        ),
        "",
        md_table(
            ["label", f"{GUARD_PREMISE_FIELD} solved goals", "baseline", "net",
             "gains", "losses", "flag"],
            (
                (
                    label,
                    guard.solved_goals,
                    guard.baseline_solved_goals,
                    signed(guard.goal_net),
                    guard.goal_gains,
                    guard.goal_losses,
                    regression_flag(label, guard),
                )
                for label in labels
                for guard in [stats(
                    label,
                    lambda key, _a: premise_count(key[1]) == GUARD_PREMISE_COUNT,
                )]
            ),
        ),
        "",
        "## Exact-attempt diagnostics (not decision metrics)",
        "",
        md_table(
            ["label", "solved attempts", "baseline", "net", "gains", "losses"],
            (
                (
                    label, value.solved_attempts, value.baseline_solved_attempts,
                    signed(value.attempt_net), value.attempt_gains, value.attempt_losses,
                )
                for label, value in ((label, overall[label]) for label in labels)
            ),
        ),
        "",
        "Per-corpus/premise/prover attempt diagnostics are available in `summary.tsv` "
        "rows with `scope=exact_attempt`.",
        "",
    ]
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text("\n".join(lines))


def main() -> int:
    if len(sys.argv) < 5:
        print(
            "usage: summarize-premise-screening.py RESULTS_ROOT SUMMARY_TSV "
            "ANALYSIS_MD LABEL...",
            file=sys.stderr,
        )
        return 2
    root = Path(sys.argv[1])
    labels = sys.argv[4:]
    try:
        axes = axes_from_environment()
        provenance = provenance_from_environment(labels, axes)
        grid = load_grid(root, labels, axes, provenance)
        rows = make_summary_rows(grid, labels)
        write_tsv(rows, Path(sys.argv[2]))
        write_analysis(grid, labels, Path(sys.argv[3]))
    except (OSError, ValueError) as error:
        print(error, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
