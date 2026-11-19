#!/usr/bin/env python3
"""Lean's binder kinds on all of Init (plan FE1c-bk; docs/programming/ELABORATION_DATA.md,
"Format 3.2: binder kinds"). Run by tests/front/elab-init.sh (make reference-elab-data),
which makes Init's export and its elaboration data with pinned Lean.

1. tests/front/bk-init.lf, three statements whose lemma's binder kinds the export gives
   otherwise than Lean, elaborated against the export and the data (tests/front/elab-dump.fs):
   their types and values equal pinned Lean's node for node (tests/front/bk-init.golden, the
   output of tests/front/bk-init.lean).
2. The same data with its binder_kinds records taken out (format 3.1 or 3, as the exporter
   wrote before): each of the three stops, so none equals Lean's (what LeanForth did before).
3. tests/front/bk-init-wrong.lf stops at by-exact with Lean's message, as pinned Lean refuses
   tests/front/bk-init-wrong.lean (error 96: Type mismatch ... but is expected to have type).
With --lean, pinned Lean writes the golden again and it must be unchanged, and refuses the
wrong twin with a type mismatch.

Usage: GFORTH=... python3 tests/front/check_bk_init.py INIT.ndjson INIT.elab.ndjson
       LEAN=... python3 tests/front/check_bk_init.py --lean
"""
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile
import functools
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / "scripts"))
import lean_pin  # noqa: E402  $LEAN or the pinned Lean, refused unrun when an elan proxy


@functools.lru_cache(maxsize=None)
def lean_binary():
    """The Lean to run: scripts/lean_pin.py's pinned_lean ($LEAN, else this
    checkout's pinned toolchain), refused before it runs when it is an elan
    proxy or not Lean 4.35.0 (Forth review of reuse-b, finding 4)."""
    return lean_pin.pinned_lean()


ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
GFORTH = os.environ.get("GFORTH", "gforth")
LIMIT = int(os.environ.get("TEST_TIMEOUT", "1800"))
TEXT = ROOT / "tests/front/bk-init.lf"
WRONG = "tests/front/bk-init-wrong.lf"
GOLDEN = ROOT / "tests/front/bk-init.golden"
MISMATCH = ["error 96", "Type mismatch\n  Nat.not_lt_eq a b\nhas type",
            "but is expected to have type\n  ¬a < b = (a ≤ b)"]


def run(args):
    return subprocess.run(args, cwd=ROOT, stdin=subprocess.DEVNULL, capture_output=True,
                          text=True, timeout=LIMIT)


def dump(export, data, path):
    """LeanForth's dump of a text's declarations: (type and value lines, all output)."""
    setup = f'[: s" {export}" ;] is dump-lib [: s" {data}" ;] is dump-data'
    done = run([GFORTH, "tests/front/elab-dump.fs", "-e", f'{setup} s" {path}" elab-dump bye'])
    out = done.stdout + done.stderr
    return [x for x in done.stdout.splitlines() if " type " in x or " value " in x], out


def without_kinds(data, out):
    """DATA with its binder_kinds records taken out, as the exporter wrote it before."""
    head, body = data.read_text(encoding="utf-8").split("\n", 1)
    lines = [x for x in body.split("\n") if not x.startswith('{"binder_kinds"')]
    body = "\n".join(lines)
    header = json.loads(head)["elab_data"]
    del header["records"]["binder_kinds"]
    header.update(format_version="3.1" if '{"inert":' in body else 3,
                  records_sha256=hashlib.sha256(body.encode()).hexdigest())
    out.write_text(json.dumps({"elab_data": header}, sort_keys=True, separators=(",", ":"))
                   + "\n" + body, encoding="utf-8")


def theorems(work):
    """Each theorem of TEXT in a file of its own: (name, path)."""
    found = re.findall(r"(theorem (\w+)\n.*?\nend \2\n)", TEXT.read_text(), re.S)
    paths = []
    for block, name in found:
        path = work / f"{name}.lf"
        path.write_text(block)
        paths.append((name, path))
    return paths


def check(export, data):
    failures = []
    want = GOLDEN.read_text(encoding="utf-8").splitlines()
    got, out = dump(export, data, TEXT)
    if got != want:
        failures.append(f"{TEXT.name}: terms differ from pinned Lean's\n{out[-1500:]}")
    with tempfile.TemporaryDirectory() as work:
        work = pathlib.Path(work)
        before = work / "before.elab.ndjson"
        without_kinds(pathlib.Path(data), before)
        parts = theorems(work)
        if len(parts) != 3:
            failures.append(f"{TEXT.name}: {len(parts)} theorems, not 3")
        with ThreadPoolExecutor(max_workers=2) as pool:
            olds = list(pool.map(lambda p: dump(export, before, p[1]), parts))
        for (name, _), (old, said) in zip(parts, olds):
            if "stopped: error" not in said or any(x in want for x in old):
                failures.append(f"{name}: without the binder kinds it does not stop\n{said[-600:]}")
    _, out = dump(export, data, WRONG)
    if any(m not in out for m in MISMATCH):
        failures.append(f"{WRONG}: not Lean's type mismatch\n{out[-800:]}")
    return failures


def check_lean():
    done = run([lean_binary(), "-DwarningAsError=true", "tests/front/bk-init.lean"])
    failures = [] if done.returncode == 0 and done.stdout.splitlines() == \
        GOLDEN.read_text(encoding="utf-8").splitlines() else [f"bk-init.lean: {done.stdout[-600:]}"]
    if "--write-golden" in sys.argv:
        GOLDEN.write_text(done.stdout, encoding="utf-8")
    done = run([lean_binary(), "-DwarningAsError=true", "tests/front/bk-init-wrong.lean"])
    if done.returncode != 1 or "Type mismatch" not in done.stdout:
        failures.append(f"bk-init-wrong.lean: exit {done.returncode}: {done.stdout[-400:]}")
    return failures


def main(argv):
    failures = check_lean() if "--lean" in argv else check(argv[1], argv[2])
    for f in failures:
        print("FAIL " + f)
    if failures:
        return 1
    print("binder kinds: bk-init.lf's 3 theorems node for node pinned Lean's on all of Init; "
          "each stops without the data's binder kinds; the wrong twin refused as Lean refuses it")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
