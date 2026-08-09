#!/usr/bin/env python3
"""Insert COQHAMMER_HOOK_PREAMBLE into an already-hooked Coq corpus."""

import os
from pathlib import Path
import re
import sys


# Match the grammar of the relevant import rather than its physical line.
# Comments and strings are masked first, so every match offset also indexes the
# original bytes.  In particular, the final dot below cannot be one of the dots
# inside a qualified module name.
SPACE = rb"[ \t\r\n\f\v]"
SEPARATOR = SPACE + rb"+"
IDENTIFIER = rb"[A-Za-z_][A-Za-z0-9_']*"
MODULE_NAME = IDENTIFIER + rb"(?:\." + IDENTIFIER + rb")*"
HAMMER_IMPORT = re.compile(
    rb"(?<![A-Za-z0-9_'])From"
    + SEPARATOR
    + rb"Hammer"
    + SEPARATOR
    + rb"Require"
    + SEPARATOR
    + rb"Import"
    + SEPARATOR
    + rb"(?P<modules>"
    + MODULE_NAME
    + rb"(?:"
    + SEPARATOR
    + MODULE_NAME
    + rb")*)"
    + SPACE
    + rb"*(?P<terminator>\.)"
)
MODULE = re.compile(MODULE_NAME)
HOOK_MODULES = {b"Hammer", b"HammerHook"}


def mask_comments_and_strings(contents):
    """Mask non-code bytes without changing offsets or line boundaries."""
    masked = bytearray(contents)
    i = 0
    comment_depth = 0
    in_string = False
    while i < len(contents):
        pair = contents[i : i + 2]
        if comment_depth:
            if pair == b"(*":
                masked[i : i + 2] = b"  "
                comment_depth += 1
                i += 2
            elif pair == b"*)":
                masked[i : i + 2] = b"  "
                comment_depth -= 1
                i += 2
            else:
                if contents[i] not in b"\r\n":
                    masked[i] = ord(" ")
                i += 1
        elif in_string:
            if pair == b'""':
                masked[i : i + 2] = b"  "
                i += 2
            elif contents[i] == ord('"'):
                masked[i] = ord(" ")
                in_string = False
                i += 1
            else:
                if contents[i] not in b"\r\n":
                    masked[i] = ord(" ")
                i += 1
        elif pair == b"(*":
            masked[i : i + 2] = b"  "
            comment_depth = 1
            i += 2
        elif contents[i] == ord('"'):
            masked[i] = ord(" ")
            in_string = True
            i += 1
        else:
            i += 1
    return bytes(masked)


def hook_import_ends(contents):
    masked = mask_comments_and_strings(contents)
    ends = []
    for match in HAMMER_IMPORT.finditer(masked):
        modules = [
            re.sub(SPACE, b"", module.group()).rsplit(b".", 1)[-1]
            for module in MODULE.finditer(match.group("modules"))
        ]
        if HOOK_MODULES.intersection(modules):
            ends.append(match.end("terminator"))
    return ends


def skip_comment(contents, start):
    """Return the offset after a nested comment, or None if it is unclosed."""
    depth = 1
    i = start + 2
    while i < len(contents):
        pair = contents[i : i + 2]
        if pair == b"(*":
            depth += 1
            i += 2
        elif pair == b"*)":
            depth -= 1
            i += 2
            if depth == 0:
                return i
        else:
            i += 1
    return None


def insertion_offset(contents, command_end):
    """Keep trailing trivia on the import line, without entering a comment."""
    i = command_end
    while i < len(contents):
        if contents.startswith(b"(*", i):
            comment_end = skip_comment(contents, i)
            if comment_end is None:
                return command_end
            i = comment_end
        elif contents.startswith(b"\r\n", i):
            return i + 2
        elif contents[i] in b"\r\n":
            return i + 1
        elif contents[i] in b" \t\f\v":
            i += 1
        else:
            return i
    return i


def rewritten_files(root, preamble):
    """Validate every source before returning any rewritten contents."""
    rewritten = []
    separator = b"\n" if preamble.endswith(b"\n") else b"\n\n"
    for path in sorted(root.rglob("*.v")):
        contents = path.read_bytes()
        ends = hook_import_ends(contents)
        if len(ends) != 1:
            raise ValueError(
                f"Expected one Hammer hook-providing import in {path}, "
                f"found {len(ends)}"
            )
        offset = insertion_offset(contents, ends[0])
        line_break = b"" if contents[:offset].endswith((b"\r", b"\n")) else b"\n"
        rewritten.append(
            (
                path,
                contents[:offset]
                + line_break
                + preamble
                + separator
                + contents[offset:],
            )
        )
    return rewritten


def main():
    if len(sys.argv) != 2:
        raise SystemExit(f"Usage: {Path(sys.argv[0]).name} ROOT")
    preamble = os.environb.get(b"COQHAMMER_HOOK_PREAMBLE", b"")
    if not preamble:
        return
    try:
        rewritten = rewritten_files(Path(sys.argv[1]), preamble)
    except ValueError as error:
        raise SystemExit(str(error)) from error

    for path, contents in rewritten:
        path.write_bytes(contents)


if __name__ == "__main__":
    main()
