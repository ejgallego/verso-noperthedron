#!/usr/bin/env python3
from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys
import tomllib


DOCSTRING_WARNING_RE = re.compile(
    r"^warning:\s+.+?:\d+:\d+:\s+'.*(?:''|') is not documented\.$"
)
DOCSTRING_HINT_LINE = (
    "Set option 'verso.docstring.allowMissing' to 'false' to disallow missing docstrings."
)
REPLAY_WARNING_RE = re.compile(r"^⚠ \[\d+/\d+\] Replayed .+$")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Filter missing-docstring build noise according to verso-harness.toml."
    )
    parser.add_argument(
        "--project-root",
        type=Path,
        default=Path.cwd(),
        help="Host project root. Defaults to the current working directory.",
    )
    parser.add_argument(
        "--docstring-warnings",
        action="store_true",
        help="Force docstring warnings on for this run.",
    )
    parser.add_argument(
        "--no-docstring-warnings",
        action="store_true",
        help="Force docstring warnings off for this run.",
    )
    return parser.parse_args()


def effective_docstring_warnings(args: argparse.Namespace) -> bool:
    if args.docstring_warnings and args.no_docstring_warnings:
        raise SystemExit("choose at most one of --docstring-warnings and --no-docstring-warnings")
    if args.docstring_warnings:
        return True
    if args.no_docstring_warnings:
        return False

    config_path = args.project_root.resolve() / "verso-harness.toml"
    if not config_path.exists():
        return False
    try:
        data = tomllib.loads(config_path.read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError):
        return False
    harness = data.get("harness")
    if not isinstance(harness, dict):
        return False
    value = harness.get("docstring_warnings")
    return value if isinstance(value, bool) else False


def main() -> int:
    args = parse_args()
    if effective_docstring_warnings(args):
        for raw_line in sys.stdin:
            print(raw_line, end="")
        return 0

    skip_next_hint = False
    suppress_blank_run = False

    for raw_line in sys.stdin:
        line = raw_line.rstrip("\n")
        if REPLAY_WARNING_RE.match(line):
            skip_next_hint = False
            suppress_blank_run = False
            continue
        if DOCSTRING_WARNING_RE.match(line):
            skip_next_hint = True
            suppress_blank_run = True
            continue
        if line == DOCSTRING_HINT_LINE:
            skip_next_hint = False
            suppress_blank_run = True
            continue
        if suppress_blank_run and line == "":
            continue
        skip_next_hint = False
        suppress_blank_run = False
        print(line)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
