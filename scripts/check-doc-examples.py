#!/usr/bin/env python3
"""Run the Forth and Lean examples of a Markdown page and compare outputs.

Usage (from the repository root):
  python3 scripts/check-doc-examples.py [--gforth GFORTH] [--lean LEAN] PAGE.md...

On each page the first ```forth block is the prelude. Every later ```forth
block runs in a new Gforth after src/main.fs and the prelude; its output
must equal the ```text block that follows it (trailing spaces ignored).

With --lean, every ```lean block is checked with that Lean and
-DwarningAsError=true. It must fail exactly when the next block is a
```text block starting with "error:"; when a ```text block follows, Lean's
output (file positions removed) must equal it, and otherwise Lean must
print nothing. Without --lean the Lean blocks are counted and skipped.

Exits 1 if any example differs. A development tool: it needs Python 3,
Gforth and, for --lean, the pinned Lean; none of them is a product
dependency.
"""
import argparse
import pathlib
import re
import subprocess
import sys
import tempfile

BLOCK = re.compile(r"^```(\w*)\n(.*?)^```\n", re.S | re.M)


def blocks(text):
    return [(m.group(1), m.group(2)) for m in BLOCK.finditer(text)]


def norm(text):
    return "\n".join(line.rstrip() for line in text.strip("\n").splitlines())


def run_forth(gforth, prelude, body, tmp, index):
    source = tmp / f"example{index}.fs"
    source.write_text(body, encoding="utf-8")
    run = subprocess.run([gforth, "src/main.fs", str(prelude), str(source), "-e", "bye"],
                         stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=120)
    return run.returncode, norm(run.stdout + run.stderr)


def lean_ok(lean, body, following, tmp, index):
    source = tmp / f"example{index}.lean"
    source.write_text(body, encoding="utf-8")
    run = subprocess.run([lean, "-DwarningAsError=true", str(source)],
                         stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=120)
    out = (run.stdout + run.stderr).replace(str(source), "FILE")
    kind, text = following
    expect_error = kind == "text" and text.startswith("error:")
    if (run.returncode != 0) != expect_error:
        return False, out
    if kind == "text":
        return norm(re.sub(r"^FILE:\d+:\d+: ", "", out, flags=re.M)) == norm(text), out
    return not out.strip(), out


def check_page(page, gforth, lean, tmp):
    items = blocks(page.read_text(encoding="utf-8"))
    prelude = None
    failures = forth_runs = lean_runs = lean_skipped = 0
    for index, (lang, body) in enumerate(items):
        following = items[index + 1] if index + 1 < len(items) else (None, "")
        if lang == "forth" and prelude is None:
            prelude = tmp / f"{page.stem}-prelude.fs"
            prelude.write_text(body, encoding="utf-8")
        elif lang == "forth":
            forth_runs += 1
            status, got = run_forth(gforth, prelude, body, tmp, index)
            want = norm(following[1]) if following[0] == "text" else None
            if status != 0 or got != want:
                failures += 1
                print(f"{page}: Forth block {index} differs (exit {status}):\n"
                      f"--- got\n{got}\n--- want\n{want}\n")
        elif lang == "lean" and lean is None:
            lean_skipped += 1
        elif lang == "lean":
            lean_runs += 1
            ok, out = lean_ok(lean, body, following, tmp, index)
            if not ok:
                failures += 1
                print(f"{page}: Lean block {index} unexpected:\n{out}\n")
    skipped = f", {lean_skipped} Lean skipped" if lean_skipped else ""
    print(f"{page}: {forth_runs} Forth and {lean_runs} Lean examples agree{skipped}"
          if not failures else f"{page}: {failures} example(s) differ")
    return failures


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--gforth", default="gforth")
    parser.add_argument("--lean")
    parser.add_argument("pages", nargs="+", type=pathlib.Path)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="doc-examples-") as tmp:
        failures = sum(check_page(page, args.gforth, args.lean, pathlib.Path(tmp))
                       for page in args.pages)
    return 1 if failures else 0


sys.exit(main())
