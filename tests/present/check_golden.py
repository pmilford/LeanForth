"""Golden tests of the term printer (make test; Gforth and Python only).

Usage: python3 tests/present/check_golden.py [--write]   (from the repository root)

1. tests/present/print-cases.fs prints every hand-built case in the
   Unicode, ASCII and LaTeX modes; the output must equal print-cases.golden.
2. Each pinned fixture (identity, composition, type-identity, poly-identity,
   constant-fixture) goes through the printer transport
   (present_transport.py) into fixture-reader.fs, which prints every
   declaration as Lean's #print does in the three modes; the output must
   equal fixtures.golden.
The Unicode lines of both files are also Lean's own output:
printer-differential.py checks that against pinned Lean (make check).
--write regenerates both golden files from the current printer; review
the diff before committing it.
"""
import os
import pathlib
import subprocess
import sys

sys.path.insert(0, "tests/present")
from present_transport import encode  # noqa: E402

sys.path.insert(0, "tests/support")
from ndjson_preview import preview  # noqa: E402

GFORTH = os.environ.get("GFORTH", "gforth")
HERE = pathlib.Path("tests/present")
FIXTURES = ("identity", "composition", "type-identity", "poly-identity", "constant-fixture")


def run_forth(path, data=b""):
    result = subprocess.run([GFORTH, str(path)], input=data, capture_output=True, timeout=120)
    if result.returncode != 0 or result.stderr:
        raise RuntimeError(f"{path} failed:\n{result.stdout.decode()}{result.stderr.decode()}")
    return result.stdout.decode("utf-8")


def fixture_output(name):
    with open(f"tests/reference/{name}.ndjson", "rb") as stream:
        data = encode(preview(stream))
    return f"== {name}\n" + run_forth(HERE / "fixture-reader.fs", data)


def outputs():
    cases = run_forth(HERE / "print-cases.fs")
    fixtures = "".join(fixture_output(name) for name in FIXTURES)
    return {HERE / "print-cases.golden": cases, HERE / "fixtures.golden": fixtures}


def main(write):
    failures = 0
    for path, text in outputs().items():
        if write:
            path.write_text(text, encoding="utf-8")
            print(f"wrote {path}")
            continue
        expected = path.read_text(encoding="utf-8")
        if text != expected:
            failures += 1
            got, want = text.splitlines(), expected.splitlines()
            for number, (a, b) in enumerate(zip(got, want), 1):
                if a != b:
                    print(f"{path}:{number}: expected {b!r}\n{' ' * len(str(path))}  printed  {a!r}")
                    break
            else:
                print(f"{path}: {len(got)} lines printed, {len(want)} expected")
        else:
            print(f"{path}: {len(expected.splitlines())} lines as expected")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main("--write" in sys.argv[1:]))
