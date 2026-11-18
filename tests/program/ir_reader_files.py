"""The program reader on files with every kind of line end, and Gforth
loading the same files.

Usage (from the repository root):
  GFORTH=... python3 tests/program/ir_reader_files.py      # make test

The reader (src/program/ir-reader.fs) splits a file into lines at LF
itself, drops one CR just before an LF, refuses any other CR and refuses
a line of 128 characters or more, without reading the rest of a file that
has no LF after it. This test writes files with exactly
such bytes into a temporary directory and runs the reader on each in one
Gforth: the outcome and the last line written must be as expected, and
an accepted file must give the IR its LF-only twin gives. Then a second
Gforth loads every accepted file, and the three fixtures the reader's
golden tests read, each into a word list of its own under CATCH: the
load must not throw, must leave the data stack as it was, and the words
must give the values of their IR. Three refused files are loaded too, to
pin down why they are refused: Gforth ends a line at a lone CR, and
stops loading at a division before CONSTANT (THROW -10 and -11; gforth-fast
reports -10 for both). Finite
tests on the Gforth that GFORTH names, not a proof.
"""
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent.parent
READER = ROOT / "src/program/ir-reader.fs"
FIXTURES = [  # path, Forth run after loading it, its printed values
    ("src/program/clamp.fs", "5 1 9 lf-clamp 0 1 9 lf-clamp 5 9 1 lf-clamp", "5 -1 1 -1 0"),
    ("src/program/examples.fs", "5 lf-factorial 12 18 lf-gcd", "120 -1 6 -1"),
    ("tests/program/ir/all-primitives.fs", "", ""),
]
CHARACTER = "a character outside printable ASCII"
TOO_LONG = "invalid @1:0: file not readable or line too long"
F7 = b": f 7 ;"
LINE_127 = F7 + b" " * 120
LINE_128 = LINE_127 + b" "
# The IR of ": f 7 ;" then ": g f f + ;", without its source line.
TWO_WORDS = ["lf-ir 0.1", "word f @1:1", "  lit 7 @1:5", "end @1:7", "word g @2:1",
             "  call f @2:5", "  call f @2:7", "  prim + @2:9", "end @2:11"]
G14 = b": g f f + ;"


def padded_lines():
    """Twelve words, each on a line of 100 characters, every other one ending
    in CRLF, so that line ends and CRs fall at many places in the reader's
    blocks of 128 characters."""
    out = b""
    for n in range(12):
        line = f": w{n} {n} ;".encode().ljust(100)
        out += line + (b"\r\n" if n % 2 else b"\n")
    return out


# name: (bytes, outcome, expected IR lines or last line written, Forth run, values)
# A refused case with an int instead of a run expects that THROW from Gforth.
CASES = {
    "lf": (F7 + b"\n" + G14 + b"\n", 0, TWO_WORDS, "f g", "7 14"),
    "crlf": (F7 + b"\r\n" + G14 + b"\r\n", 0, TWO_WORDS, "f g", "7 14"),
    "no-final-lf": (F7 + b"\n" + G14, 0, TWO_WORDS, "f g", "7 14"),
    "crlf-no-final-lf": (F7 + b"\r\n" + G14, 0, TWO_WORDS, "f g", "7 14"),
    "blank-lines": (b"\n\r\n" + F7 + b"\n\n", 0, "end @3:7", "f", "7"),
    "empty": (b"", 0, ["lf-ir 0.1"], "", ""),
    "127": (LINE_127 + b"\n: g 8 ;\n", 0, "end @2:7", "f g", "7 8"),
    # The CR is the 128th byte, the last of the reader's first block.
    "127-crlf": (LINE_127 + b"\r\n: g 8 ;\r\n", 0, "end @2:7", "f g", "7 8"),
    "127-last": (b"\n" + LINE_127, 0, "end @2:7", "f", "7"),
    "many-blocks": (padded_lines(), 0, "end @12:10", "w0 w7 w11", "0 7 11"),
    "128": (LINE_128 + b"\n: g 8 ;\n", 1, TOO_LONG, None, None),
    "128-crlf": (LINE_128 + b"\r\n", 1, TOO_LONG, None, None),
    "128-last": (LINE_128, 1, TOO_LONG, None, None),
    # Refused once a block ends with the line too long, before the file ends.
    "long-no-lf": (b"\\ " + b"x" * 1000, 1, TOO_LONG, None, None),
    "lone-cr": (b"\\ x\r" + F7 + b"\n", 5, f"unsupported @1:4: {CHARACTER}", "f", "7"),
    "cr-cr-lf": (F7 + b"\r\r\n: g 8 ;\n", 5, f"unsupported @1:8: {CHARACTER}", None, None),
    "cr-at-end": (F7 + b"\r", 5, f"unsupported @1:8: {CHARACTER}", None, None),
    "cr-inside": (F7 + b" \r: g 8 ;\r\n", 5, f"unsupported @1:9: {CHARACTER}", None, None),
    "divide-by-zero": (b"1 0 / constant junk\n: lf-five 5 ;\n", 5,
                       "unsupported @1:5: a division outside a definition: /", -10, None),
    # The smallest number divided by -1: Gforth's checking engine (1.0 and 0.7.3) throws -11
    # (result out of range), gforth-fast -10 (its division reports every fault so).
    "divide-smallest": (b"-1 1 rshift invert -1 / constant junk\n", 5,
                        "unsupported @1:23: a division outside a definition: /", (-11, -10), None),
}


def gforth(gforth_path, driver_text, directory):
    driver = Path(directory) / "driver.fs"
    driver.write_text(driver_text, encoding="ascii")
    done = subprocess.run([gforth_path, str(driver)], capture_output=True, text=True,
                          timeout=120, stdin=subprocess.DEVNULL, errors="replace")
    if done.returncode != 0:
        raise SystemExit(f"{gforth_path} failed:\n{done.stdout}{done.stderr}")
    return done.stdout.splitlines()


def forth_string(path):
    text = str(path)
    if '"' in text or not text.isascii():
        raise SystemExit(f"path not usable in a Forth string: {text}")
    return f's" {text}"'


def read_all(gforth_path, paths, directory):
    """Each file's output lines, without its source line, and its outcome."""
    driver = [f"require {READER}",
              ": type-line ( c-addr u -- ) type cr ;",
              ": read ( c-addr u -- ) ['] type-line -rot lf-ir-read-file "
              '." outcome " . cr ;']
    driver += [f"{forth_string(p)} read" for p in paths] + ["bye", ""]
    results, current = [], []
    for line in gforth(gforth_path, "\n".join(driver), directory):
        if line.startswith("outcome "):
            results.append((current, int(line.split()[1])))
            current = []
        elif not line.startswith("source "):
            current.append(line.rstrip())
    return results


HOST = r"""[defined] warnings [if] false warnings ! [then]
2variable path
: load-it ( -- ) path 2@ included ;
: scope ( -- ) wordlist dup set-current forth-wordlist swap 2 set-order ;
: host-load ( c-addr u -- )
  path 2! scope ['] load-it depth >r catch depth r> - ." load " swap . . cr ;
: drops ( x1 .. xn n -- ) 0 ?do drop loop ;
: show ( x1 .. xn n -- ) dup 0 ?do dup i - pick . loop drops ;
\ Evaluate c-addr u and print the values it leaves, bottom first.
: run ( c-addr u -- )
  ." values " ['] evaluate depth 3 - >r catch depth r> - 1- swap
  ?dup if ." error " . drops else show then cr ;
"""


def load_all(gforth_path, loads, directory):
    """For each (path, run): the THROW code, cells left, and the values printed."""
    driver = [HOST] + [f"{forth_string(p)} host-load {forth_string(run)} run"
                       for p, run in loads] + ["bye", ""]
    lines = [line for line in gforth(gforth_path, "\n".join(driver), directory)
             if line.startswith(("load ", "values "))]
    if len(lines) != 2 * len(loads):
        raise SystemExit("unexpected host output:\n" + "\n".join(lines))
    results = []
    for load, values in zip(lines[0::2], lines[1::2]):
        _, code, left = load.split()
        results.append((int(code), int(left), " ".join(values.split()[1:])))
    return results


def check_reader(name, result, expected_outcome, expected):
    lines, outcome = result
    problems = []
    if outcome != expected_outcome:
        problems.append(f"{name}: outcome {outcome}, expected {expected_outcome}")
    if isinstance(expected, list) and lines != expected:
        problems.append(f"{name}: IR {lines}, expected {expected}")
    if isinstance(expected, str) and (not lines or lines[-1] != expected):
        problems.append(f"{name}: last line {lines[-1:]}, expected {expected!r}")
    return problems


def main():
    gforth_path = os.environ.get("GFORTH", "gforth")
    problems = []
    with tempfile.TemporaryDirectory() as directory:
        paths = {}
        for name, (data, *_rest) in CASES.items():
            paths[name] = Path(directory) / f"{name}.fs"
            paths[name].write_bytes(data)
        results = read_all(gforth_path, [paths[n] for n in CASES], directory)
        if len(results) != len(CASES):
            raise SystemExit(f"{len(results)} reader results for {len(CASES)} files")
        loads, wanted = [], []
        for (name, (_data, outcome, expected, run, values)), result in zip(CASES.items(),
                                                                           results):
            problems += check_reader(name, result, outcome, expected)
            if isinstance(run, str):
                loads.append((paths[name], run))
                wanted.append((name, (0,), values))
            elif isinstance(run, (int, tuple)):
                loads.append((paths[name], ""))
                wanted.append((name, run if isinstance(run, tuple) else (run,), ""))
        for path, run, values in FIXTURES:
            loads.append((ROOT / path, run))
            wanted.append((path, (0,), values))
        found = load_all(gforth_path, loads, directory)
        if len(found) != len(wanted):
            raise SystemExit(f"{len(found)} host loads for {len(wanted)} files")
        for (name, codes, values), (got_code, left, got_values) in zip(wanted, found):
            if got_code not in codes or (left, got_values) != (0, values):
                problems.append(f"{name}: host load gave throw {got_code}, {left} cells "
                                f"left, values '{got_values}'; expected throw "
                                f"{' or '.join(map(str, codes))}, 0, '{values}'")
    for problem in problems:
        print(problem, file=sys.stderr)
    if problems:
        return 1
    print(f"program reader files: {len(CASES)} files read, {len(wanted)} loaded by the host, "
          "all as expected")
    return 0


if __name__ == "__main__":
    sys.exit(main())
