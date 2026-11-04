#!/usr/bin/env python3
"""Cases of the importer stage (src/import/stage.fs) that need a changed
export: each is written into a temporary folder from a reference export,
loaded with tests/support/compact-load.fs (compact-try, or
compact-try-unchecked where the file has no manifest), and its report
compared with the expected one:

- an expression naming a constant that no declaration has: read ok, then
  sealing is invalid ("unknown constant", the name given), never ok;
- two declarations of one name and a constant naming it: loaded; both
  declarations are found by the name (the newest, then the one before it
  along the chain) and the constant is resolved to neither (payload 0),
  as ADR 0016 C4 says, so that ADR 0012 E5 decides;
- a file cut cleanly between two lines, and one changed byte, with the
  original's manifest: invalid (the manifest differs), rolled back;
- no manifest beside the file: invalid;
- a reader failure (a reference to a later expression): invalid;
- numbers beyond 32 bits (a numeric name component, a projection's
  index, an inductive type's parameter count): full;
- the pinned Lean version changed: unsupported.

Usage: GFORTH=path/to/gforth python3 tests/core/test_stage.py [-v]
"""
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
GFORTH = os.environ.get("GFORTH") or str(ROOT / ".tools/gforth/bin/gforth")
if not os.path.isabs(GFORTH) and os.sep in GFORTH:
    GFORTH = str(ROOT / GFORTH)
VERBOSE = "-v" in sys.argv[1:]
IDENTITY = ROOT / "tests/reference/identity.ndjson"
FIXTURE = ROOT / "tests/reference/constant-fixture.ndjson"
BLOCK = ROOT / "tests/core/ndjson-block.ndjson"


def report(path, checked=False, manifest=None):
    """compact-try's report on the export at path."""
    use = f's" {manifest}" compact-manifest-use ' if manifest else ""
    word = "compact-try" if checked else "compact-try-unchecked"
    run = subprocess.run(
        [GFORTH, "tests/support/compact-load.fs", "-e", f'{use}s" {path}" {word} bye'],
        cwd=ROOT, stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=120)
    if run.returncode != 0 or run.stderr:
        raise AssertionError(f"gforth failed on {path}: {run.stderr.strip()}")
    return run.stdout


def lines(path):
    return path.read_text(encoding="utf-8").splitlines(keepends=True)


def write(folder, name, text_lines):
    path = folder / name
    path.write_text("".join(text_lines), encoding="utf-8")
    return path


def cases(folder):
    """(name, path, checked, manifest, expected substrings, refused substrings)."""
    identity = lines(IDENTITY)
    fixture = lines(FIXTURE)
    block = lines(BLOCK)
    out = []
    # An unknown constant: P (name 2) has no declaration.
    path = write(folder, "unknown.ndjson",
                 identity + ['{"const":{"name":2,"us":[]},"ie":7}\n'])
    out.append(("unknown constant", path, False, None,
                ["why unknown constant", "outcome=1", "culprit=P"], ["ok decls"]))
    # The theorem twice, then a constant naming it.
    path = write(folder, "twice.ndjson",
                 identity + [identity[-1], '{"const":{"name":1,"us":[]},"ie":7}\n'])
    out.append(("duplicate names", path, False, None,
                ["ok decls=2", "declarations=2 found=2", "by text: found=2",
                 "constants=1 wrong=0"], ["outcome="]))
    # The fixture cut after its 21st line, and with one byte changed, each
    # with the whole fixture's manifest.
    manifest = str(FIXTURE) + ".manifest.json"
    path = write(folder, "cut.ndjson", fixture[:21])
    out.append(("truncated", path, True, manifest,
                ["export differs from its manifest", "outcome=1"], ["ok decls"]))
    changed = fixture[:1] + [fixture[1].replace("fixtureId", "fixtureIc")] + fixture[2:]
    path = write(folder, "changed.ndjson", changed)
    out.append(("one byte changed", path, True, manifest,
                ["field sha256", "outcome=1"], ["ok decls"]))
    path = write(folder, "bare.ndjson", fixture)
    out.append(("no manifest", path, True, None,
                ["manifest missing", "outcome=1"], ["ok decls"]))
    # The reader's own failure: an application of an expression not yet read.
    path = write(folder, "forward.ndjson",
                 identity[:-1] + ['{"app":{"arg":1,"fn":9},"ie":7}\n'] + identity[-1:])
    out.append(("bad reference", path, False, None,
                ["why bad reference", "outcome=1"], ["ok decls"]))
    # Numbers beyond 32 bits.
    path = write(folder, "wide-name.ndjson",
                 identity[:-1] + ['{"in":4,"num":{"i":4294967296,"pre":1}}\n'] + identity[-1:])
    out.append(("numeric name beyond 32 bits", path, False, None,
                ["number beyond 32 bits", "outcome=6"], ["ok decls"]))
    path = write(folder, "wide-proj.ndjson",
                 identity[:-1]
                 + ['{"ie":7,"proj":{"idx":4294967296,"struct":1,"typeName":1}}\n']
                 + identity[-1:])
    out.append(("projection index beyond 32 bits", path, False, None,
                ["number beyond 32 bits", "outcome=6"], ["ok decls"]))
    wide = [line.replace('"numParams":0', '"numParams":4294967296', 1)
            if '"inductive"' in line else line for line in block]
    path = write(folder, "wide-type.ndjson", wide)
    out.append(("parameter count beyond 32 bits", path, False, None,
                ["number beyond 32 bits", "outcome=6"], ["ok decls"]))
    path = write(folder, "lean.ndjson",
                 [identity[0].replace("4.35.0", "4.36.0")] + identity[1:])
    out.append(("another Lean version", path, False, None,
                ["unsupported exporter, format or Lean version", "outcome=5"], ["ok decls"]))
    # The unchanged files load.
    out.append(("identity", IDENTITY, True, None,
                ["ok decls=1", "found=1", "constants=0 wrong=0"], ["outcome="]))
    out.append(("block", BLOCK, False, None,
                ["ok decls=7", "declarations=6 found=6", "constants=2 wrong=0"], ["outcome="]))
    return out


def main():
    failures = 0
    with tempfile.TemporaryDirectory() as tmp:
        folder = pathlib.Path(tmp)
        all_cases = cases(folder)
        for name, path, checked, manifest, expected, refused in all_cases:
            text = report(path, checked, manifest)
            missing = [e for e in expected if e not in text]
            present = [r for r in refused if r in text]
            if missing or present:
                failures += 1
                print(f"FAIL {name}: missing {missing}, unexpected {present}\n{text}")
            elif VERBOSE:
                print(f"ok   {name}\n{text}")
    if failures:
        print(f"{failures} of {len(all_cases)} stage cases failed")
        return 1
    print(f"All {len(all_cases)} changed-export cases of the stage behave as expected.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
