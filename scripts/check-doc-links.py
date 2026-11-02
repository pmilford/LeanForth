#!/usr/bin/env python3
"""Fail if any documentation link or repository path reference is broken.

Usage: python3 scripts/check-doc-links.py   (run from the repository root)

Checks every tracked or new (not ignored) Markdown file's relative links, and every mention of a
`docs/...` file path in such Markdown, shell, Python, Forth, TOML, YAML
and Makefile sources. Dated review records (reviews/YYYY-MM-DD-*.md under docs)
and prompts/ are historical and keep the paths current when they were
written, so they are not checked; docs/README.md maps old paths to new ones.
Exits 1 and lists each broken reference, or prints a summary and exits 0.
"""
import pathlib
import re
import subprocess
import sys

TEXT = re.compile(r"(\.md|\.toml|\.sh|\.py|\.yml|\.fs|Makefile)$")
HISTORICAL = re.compile(r"^(docs/reviews/\d{4}-\d{2}-\d{2}-|prompts/)")
LINK = re.compile(r"\]\(([^)\s]+)\)")
DOC_PATH = re.compile(r"(?<![A-Za-z0-9_./-])docs/[A-Za-z0-9_./-]*[A-Za-z0-9_]")


def tracked_files():
    # Include new, not yet committed files so problems are caught before commit.
    listing = subprocess.check_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard"], text=True)
    return [p for p in sorted(set(listing.splitlines()))
            if TEXT.search(p) and not HISTORICAL.match(p)
            and pathlib.Path(p).exists()]


def broken_references(path):
    text = pathlib.Path(path).read_text(encoding="utf-8")
    base = pathlib.Path(path).parent
    if path.endswith(".md"):
        for target in LINK.findall(text):
            if re.match(r"^([a-z]+:|#|/)", target):
                continue
            file_part = target.split("#", 1)[0]
            if file_part and not (base / file_part).exists():
                yield f"{path}: broken link ({target})"
    for mention in DOC_PATH.findall(text):
        if not pathlib.Path(mention).exists():
            yield f"{path}: missing path {mention}"


def main():
    files = tracked_files()
    problems = [problem for path in files for problem in broken_references(path)]
    for problem in problems:
        print(problem, file=sys.stderr)
    if problems:
        print(f"{len(problems)} broken documentation reference(s).", file=sys.stderr)
        return 1
    print(f"Documentation references resolve in {len(files)} checked files.")
    return 0


sys.exit(main())
