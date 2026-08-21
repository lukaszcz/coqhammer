#!/usr/bin/env python3

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


EVAL_DIR = Path(__file__).resolve().parents[1]
TOOL = EVAL_DIR / "tools" / "insert-committed-preamble.py"
PREAMBLE = b'Set Warnings "-deprecated".\nSet Default Proof Using "Type".'

# Runs the tool in-process so that a chosen file-system call can be made to
# fail partway through, which no external means can trigger deterministically.
FAILING_DRIVER = """\
import importlib.util
import os
from pathlib import Path
import sys

tool_path, target, successes, root = sys.argv[1:]
successes = int(successes)
spec = importlib.util.spec_from_file_location("tool", tool_path)
tool = importlib.util.module_from_spec(spec)
spec.loader.exec_module(tool)

calls = []


def guard():
    calls.append(None)
    if len(calls) > successes:
        raise OSError("simulated failure")


if target == "replace":
    real_replace = os.replace
    def replace(source, destination, **kwargs):
        guard()
        return real_replace(source, destination, **kwargs)
    os.replace = replace
else:
    real_write_bytes = Path.write_bytes
    def write_bytes(self, data):
        guard()
        return real_write_bytes(self, data)
    Path.write_bytes = write_bytes

sys.argv = [tool_path, root]
tool.main()
"""


class InsertCommittedPreambleTests(unittest.TestCase):
    def setUp(self):
        self.tempdir = tempfile.TemporaryDirectory()
        self.root = Path(self.tempdir.name)

    def tearDown(self):
        self.tempdir.cleanup()

    def run_tool(self, preamble=PREAMBLE):
        env = os.environ.copy()
        if preamble is None:
            env.pop("COQHAMMER_HOOK_PREAMBLE", None)
        else:
            env["COQHAMMER_HOOK_PREAMBLE"] = preamble.decode()
        return subprocess.run(
            ["python3", str(TOOL), str(self.root)],
            env=env,
            capture_output=True,
            text=True,
        )

    def run_tool_failing_at(self, target, successes, preamble=PREAMBLE):
        """Run the tool with everything after `successes` `target` calls failing."""
        env = os.environ.copy()
        env["COQHAMMER_HOOK_PREAMBLE"] = preamble.decode()
        result = subprocess.run(
            [
                "python3",
                "-c",
                FAILING_DRIVER,
                str(TOOL),
                target,
                str(successes),
                str(self.root),
            ],
            env=env,
            capture_output=True,
            text=True,
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("simulated failure", result.stderr)
        return result

    def assert_only_sources_remain(self):
        leftovers = [
            str(path.relative_to(self.root))
            for path in self.root.rglob("*")
            if path.is_file() and path.suffix != ".v"
        ]
        self.assertEqual(leftovers, [])

    def rewrite_of(self, original):
        command_end = original.index(b"\n") + 1
        return original[:command_end] + PREAMBLE + b"\n\n" + original[command_end:]

    def write_corpus(self):
        originals = {}
        for name in ("a.v", "b.v", "c.v"):
            path = self.root / name
            contents = (
                f"From Hammer Require Import Hammer.\nCheck {name[0]}.\n".encode()
            )
            path.write_bytes(contents)
            originals[path] = contents
        return originals

    def test_spacing_leading_whitespace_and_mixed_import_lists(self):
        cases = {
            "hammer.v": (
                b" \tFrom\tHammer  Require\tImport Other Hammer More\t.\nCheck True.\n"
            ),
            "hook.v": (
                b"\tFrom Hammer Require Import Tactics\t HammerHook Hints .  \r\n"
                b"Check True.\r\n"
            ),
            "both.v": (
                b"From Hammer Require Import Hammer Tactics HammerHook .\n"
                b"Check True.\n"
            ),
        }
        for name, contents in cases.items():
            (self.root / name).write_bytes(contents)

        result = self.run_tool()
        self.assertEqual(result.returncode, 0, result.stderr)
        for name, contents in cases.items():
            command_end = contents.index(b"\n") + 1
            expected = (
                contents[:command_end]
                + PREAMBLE
                + b"\n\n"
                + contents[command_end:]
            )
            self.assertEqual((self.root / name).read_bytes(), expected)

    def test_multiline_import_masks_strings_and_nested_comments(self):
        path = self.root / "lexical.v"
        contents = (
            b'Definition fake := "quoted ""From Hammer Require Import '
            b'Fake.HammerHook."" text".\n'
            b"(* outer From Hammer Require Import Hammer.\n"
            b"   (* nested From Hammer Require Import HammerHook. *) *)\n"
            b"From (* separator (* nested *) *) Hammer\n"
            b"  Require\n"
            b"  Import Support Qualified.Provider.HammerHook Other.\n"
            b"Check True.\n"
        )
        path.write_bytes(contents)

        result = self.run_tool()
        self.assertEqual(result.returncode, 0, result.stderr)
        command_end = contents.index(b"Other.") + len(b"Other.")
        command_end = contents.index(b"\n", command_end) + 1
        self.assertEqual(
            path.read_bytes(),
            contents[:command_end] + PREAMBLE + b"\n\n" + contents[command_end:],
        )

    def test_commented_import_does_not_count_as_a_command(self):
        path = self.root / "comment.v"
        contents = (
            b"(* From Hammer Require Import HammerHook. *)\n"
            b"From Hammer Require Import Tactics Hammer. (* hook provider *)\n"
            b"Check True.\n"
        )
        path.write_bytes(contents)

        preamble = b"Set Debug Tactic Unification."
        result = self.run_tool(preamble)
        self.assertEqual(result.returncode, 0, result.stderr)
        command_end = contents.index(b"\n", contents.index(b"\n") + 1) + 1
        self.assertEqual(
            path.read_bytes(),
            contents[:command_end] + preamble + b"\n\n" + contents[command_end:],
        )

    def test_same_line_following_command_is_not_part_of_the_import(self):
        path = self.root / "same-line.v"
        original = (
            b"Set Warnings \"none\". From Hammer Require Import "
            b"Qualified.Plugin.Hammer. Check True.\n"
        )
        path.write_bytes(original)

        result = self.run_tool(b"Set Universe Polymorphism.")
        self.assertEqual(result.returncode, 0, result.stderr)
        following = original.index(b"Check True.")
        self.assertEqual(
            path.read_bytes(),
            original[:following]
            + b"\nSet Universe Polymorphism.\n\n"
            + original[following:],
        )

    def test_trailing_nested_comment_stays_on_the_import_line(self):
        path = self.root / "trailing-comment.v"
        command = (
            b"From Hammer Require Import Qualified.HammerHook. "
            b"(* provider (* nested dot. *) *)\n"
        )
        path.write_bytes(command + b"Check True.\n")

        result = self.run_tool(b"Set Universe Polymorphism.")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(
            path.read_bytes(),
            command + b"Set Universe Polymorphism.\n\nCheck True.\n",
        )

    def test_eof_without_newline_terminates_import_and_adds_one_blank_line(self):
        path = self.root / "eof.v"
        original = b"From Hammer Require Import Tactics Hammer ."
        path.write_bytes(original)

        result = self.run_tool(b"Set Universe Polymorphism.")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(
            path.read_bytes(),
            original + b"\nSet Universe Polymorphism.\n\n",
        )

    def test_preamble_is_verbatim_when_it_already_ends_in_a_newline(self):
        path = self.root / "verbatim.v"
        command = b"From Hammer Require Import Hammer.\n"
        preamble = b"Set Ltac Debug.\n\t(* $HOME and `ticks` stay literal *)\n"
        path.write_bytes(command + b"Check True.\n")

        result = self.run_tool(preamble)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(path.read_bytes(), command + preamble + b"\nCheck True.\n")

    def test_unset_and_empty_preamble_are_successful_byte_identity_noops(self):
        path = self.root / "no-import-needed.v"
        original = b'Definition text := "From Hammer Require Import Hammer.".\r\n'
        path.write_bytes(original)

        for preamble in (None, b""):
            with self.subTest(preamble=preamble):
                result = self.run_tool(preamble)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(path.read_bytes(), original)

    def test_missing_import_fails_without_rewriting_other_files(self):
        valid = self.root / "valid.v"
        missing = self.root / "missing.v"
        valid_contents = b"From Hammer Require Import Hammer.\nCheck True.\n"
        missing_contents = b"From Hammer Require Import Tactics.\nCheck True.\n"
        valid.write_bytes(valid_contents)
        missing.write_bytes(missing_contents)

        result = self.run_tool()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("found 0", result.stderr)
        self.assertEqual(valid.read_bytes(), valid_contents)
        self.assertEqual(missing.read_bytes(), missing_contents)

    def test_duplicate_import_fails_transactionally(self):
        valid = self.root / "a-valid.v"
        duplicate = self.root / "z-duplicate.v"
        valid_contents = b"From Hammer Require Import HammerHook.\nCheck True.\n"
        duplicate_contents = (
            b"From Hammer Require Import Tactics Hammer.\n"
            b"From Hammer Require Import HammerHook Hints.\n"
        )
        valid.write_bytes(valid_contents)
        duplicate.write_bytes(duplicate_contents)

        result = self.run_tool()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("found 2", result.stderr)
        self.assertEqual(valid.read_bytes(), valid_contents)
        self.assertEqual(duplicate.read_bytes(), duplicate_contents)

    def test_duplicate_basenames_are_rewritten_without_collisions(self):
        originals = {}
        for directory, provider in (("one", "Hammer"), ("two", "HammerHook")):
            path = self.root / directory / "sample.v"
            path.parent.mkdir()
            contents = f"From Hammer Require Import {provider}.\nCheck True.\n".encode()
            path.write_bytes(contents)
            originals[path] = contents

        result = self.run_tool()
        self.assertEqual(result.returncode, 0, result.stderr)
        for path, original in originals.items():
            command_end = original.index(b"\n") + 1
            self.assertEqual(
                path.read_bytes(),
                original[:command_end] + PREAMBLE + b"\n\n" + original[command_end:],
            )

    def test_staging_keeps_an_occupied_sibling_and_the_source_permissions(self):
        path = self.root / "sample.v"
        original = b"From Hammer Require Import Hammer.\nCheck True.\n"
        path.write_bytes(original)
        path.chmod(0o640)
        occupied = self.root / "sample.v.preamble-tmp"
        occupied.write_bytes(b"unrelated\n")

        result = self.run_tool()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(path.read_bytes(), self.rewrite_of(original))
        self.assertEqual(path.stat().st_mode & 0o7777, 0o640)
        self.assertEqual(occupied.read_bytes(), b"unrelated\n")

    def test_read_only_source_is_rewritten_with_its_mode_preserved(self):
        path = self.root / "sample.v"
        original = b"From Hammer Require Import Hammer.\nCheck True.\n"
        path.write_bytes(original)
        path.chmod(0o444)

        result = self.run_tool()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(path.read_bytes(), self.rewrite_of(original))
        self.assertEqual(path.stat().st_mode & 0o7777, 0o444)
        self.assert_only_sources_remain()

    def test_committed_samples(self):
        corpora = EVAL_DIR / "corpora"
        samples = sorted(corpora.glob("*/sample/*.v"))
        self.assertTrue(samples)
        originals = {}
        for sample in samples:
            destination = self.root / sample.relative_to(corpora)
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(sample, destination)
            originals[destination] = destination.read_bytes()
        self.assertEqual(len(originals), len(samples))

        preamble = b"Set Universe Polymorphism."
        result = self.run_tool(preamble)
        self.assertEqual(result.returncode, 0, result.stderr)
        command = b"From Hammer Require Import Hammer.\n"
        for path, original in originals.items():
            self.assertEqual(original.count(command), 1)
            self.assertEqual(
                path.read_bytes(),
                original.replace(command, command + preamble + b"\n\n", 1),
            )

    def test_rerunning_does_not_insert_the_preamble_twice(self):
        shapes = {
            "eof.v": b"From Hammer Require Import Tactics Hammer .",
            "same-line.v": (
                b'Set Warnings "none". From Hammer Require Import '
                b"Qualified.Plugin.Hammer. Check True.\n"
            ),
            "crlf.v": (
                b"\tFrom Hammer Require Import Tactics\t HammerHook Hints .  \r\n"
                b"Check True.\r\n"
            ),
            "plain.v": b"From Hammer Require Import Hammer.\nCheck True.\n",
        }
        for name, contents in shapes.items():
            (self.root / name).write_bytes(contents)

        for preamble in (PREAMBLE, PREAMBLE + b"\n"):
            with self.subTest(preamble=preamble):
                first = self.run_tool(preamble)
                self.assertEqual(first.returncode, 0, first.stderr)
                inserted = {
                    name: (self.root / name).read_bytes() for name in shapes
                }
                second = self.run_tool(preamble)
                self.assertEqual(second.returncode, 0, second.stderr)
                for name, contents in inserted.items():
                    self.assertEqual((self.root / name).read_bytes(), contents)
                    self.assertEqual(contents.count(PREAMBLE), 1)
                for name, contents in shapes.items():
                    (self.root / name).write_bytes(contents)
        self.assert_only_sources_remain()

    def test_failed_staging_leaves_every_source_untouched(self):
        originals = self.write_corpus()

        self.run_tool_failing_at("write", 1)
        for path, original in originals.items():
            self.assertEqual(path.read_bytes(), original)
        self.assert_only_sources_remain()

        result = self.run_tool()
        self.assertEqual(result.returncode, 0, result.stderr)
        for path, original in originals.items():
            self.assertEqual(path.read_bytes(), self.rewrite_of(original))

    def test_failed_replace_leaves_a_completable_corpus(self):
        originals = self.write_corpus()

        self.run_tool_failing_at("replace", 1)
        rewritten = 0
        for path, original in originals.items():
            contents = path.read_bytes()
            if contents != original:
                self.assertEqual(contents, self.rewrite_of(original))
                rewritten += 1
        self.assertEqual(rewritten, 1)
        self.assert_only_sources_remain()

        result = self.run_tool()
        self.assertEqual(result.returncode, 0, result.stderr)
        for path, original in originals.items():
            self.assertEqual(path.read_bytes(), self.rewrite_of(original))
        self.assert_only_sources_remain()

    def build_coqnames(self):
        build = self.root / "coqnames-build"
        build.mkdir()
        for source in ("utils.ml", "coqnames.ml"):
            shutil.copyfile(EVAL_DIR / "tools" / source, build / source)
        result = subprocess.run(
            [
                "ocamlfind",
                "ocamlopt",
                "-package",
                "unix,str",
                "-linkpkg",
                "-inline",
                "100",
                "-unsafe",
                "utils.ml",
                "coqnames.ml",
                "-o",
                "coqnames",
            ],
            cwd=build,
            capture_output=True,
            text=True,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        return build / "coqnames"

    def run_coqnames(self, binary, name, preamble):
        directory = self.root / name
        directory.mkdir()
        source = b"Lemma demo : True.\nProof.\n  exact I.\nQed.\n"
        (directory / "fixture.v").write_bytes(source)
        (directory / "fixture.glob").write_bytes(
            b"Ffixture\nprf 0:3 <> demo\n"
        )
        env = os.environ.copy()
        if preamble is None:
            env.pop("COQHAMMER_HOOK_PREAMBLE", None)
        else:
            env["COQHAMMER_HOOK_PREAMBLE"] = preamble.decode()
        result = subprocess.run(
            [str(binary)], cwd=directory, env=env, capture_output=True, text=True
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        return (directory / "fixture.v").read_bytes()

    def test_actual_coqnames_preserves_unset_empty_and_set_preambles(self):
        binary = self.build_coqnames()
        unset = self.run_coqnames(binary, "unset", None)
        empty = self.run_coqnames(binary, "empty", b"")
        injected = self.run_coqnames(binary, "injected", PREAMBLE)

        header = b"From Hammer Require Import HammerHook.\n\n"
        self.assertTrue(unset.startswith(header))
        self.assertEqual(empty, unset)
        self.assertEqual(
            injected,
            unset.replace(
                header,
                b"From Hammer Require Import HammerHook.\n"
                + PREAMBLE
                + b"\n\n",
                1,
            ),
        )

    def test_actual_prepare_corpus_committed_paths(self):
        repo = self.root / "repo"
        eval_copy = repo / "eval"
        (eval_copy / "tools").mkdir(parents=True)
        shutil.copyfile(TOOL, eval_copy / "tools" / TOOL.name)
        bin_dir = repo / "bin"
        bin_dir.mkdir()
        git = bin_dir / "git"
        git.write_text(
            '#!/bin/sh\n'
            'if [ "$1" = rev-parse ] && [ "$2" = --show-toplevel ]; then\n'
            '  printf "%s\\n" "$COQHAMMER_TEST_REPO"\n'
            'else\n'
            '  exit 1\n'
            'fi\n'
        )
        git.chmod(0o755)

        corpora = ("stdlib-regression", "dependent-slice", "external-equations")
        for corpus in corpora:
            shutil.copytree(
                EVAL_DIR / "corpora" / corpus,
                eval_copy / "corpora" / corpus,
            )
        env = os.environ.copy()
        preamble = b"Set Universe Polymorphism."
        env["COQHAMMER_HOOK_PREAMBLE"] = preamble.decode()
        env["COQHAMMER_TEST_REPO"] = str(repo)
        env["PATH"] = str(bin_dir) + os.pathsep + env["PATH"]
        for corpus in corpora:
            with self.subTest(corpus=corpus):
                result = subprocess.run(
                    [
                        "bash",
                        str(EVAL_DIR / "prepare-corpus.sh"),
                        corpus,
                        "--sample",
                        "--coqlib",
                        "/unused",
                    ],
                    cwd=eval_copy,
                    env=env,
                    capture_output=True,
                    text=True,
                )
                self.assertEqual(result.returncode, 0, result.stderr)
                generated = list((eval_copy / "problems").rglob("*.v"))
                self.assertEqual(len(generated), 1)
                original = next(
                    (EVAL_DIR / "corpora" / corpus / "sample").glob("*.v")
                ).read_bytes()
                command = b"From Hammer Require Import Hammer.\n"
                self.assertEqual(
                    generated[0].read_bytes(),
                    original.replace(command, command + preamble + b"\n\n", 1),
                )


if __name__ == "__main__":
    unittest.main()
