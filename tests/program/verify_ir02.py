"""IR 0.2 against plain Gforth (ADR 0019 Amendment 1, tests of A1, A2 and A5).

Usage (from the repository root):
  GFORTH=... python3 tests/program/verify_ir02.py [--seed N] [--files N]
  GFORTH=... LEAN=... python3 tests/program/verify_ir02.py --lean

The oracle is plain Gforth, which runs every source file here in run mode.
One Gforth process per batch:

1. Redefinitions (A1, test 1): --files (default 60) generated files from
   --seed, one definition per line, that define a few names again and again
   in any case of letters, as words and as constants, with bodies that call
   earlier versions (also a word's own name, which means the version
   before), output words (A2: dup ., u., emit, cr, space, spaces, .s, ." and
   S" ... TYPE) at random points, every IR 0.2 primitive and Forth-2012's
   number prefixes (A3). Gforth loads each file line by line into a word
   list of its own and keeps each definition's execution token right after
   its line; the program words (the mode shift) write the file's IR, which
   the IR interpreter (src/program/ir-run.fs) loads. Every definition then
   runs on random inputs, in the interpreter by its version's IR name and
   in Gforth by its token: where the interpreter ends normally, Gforth must
   too, with the same stack and the same bytes on standard output (the
   interpreter's out lines rendered as Lean's Event.render says). The IR
   names must also be those the rule predicts (the name folded, then 'k).
2. Output words (A2, test 1): each output word at the edges, `.` and `U.`
   at 0, -1, the smallest and largest cell and 32-bit edges, EMIT of 0 to
   255 and beyond, SPACES of positive, zero and negative counts, `."` with
   leading blanks, S" ... " TYPE, .S of 0, 3 and 12 cells: the bytes Gforth
   prints must be the interpreter's.
3. Literals (A3, test 2): every Forth-2012 form at the edges, as the
   program words read them and as Gforth reads them.

With --lean, Lean's model (tests/reference/program-ir-run.lean) also runs
the cases of the first eight generated files and must give the
interpreter's stacks. Finite tests on the Gforth that GFORTH names, not a
proof.
"""
import argparse
import os
from pathlib import Path
import random
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
EVALUATOR = ROOT / "tests/reference/program-ir-run.lean"
MIN, MAX = -(1 << 63), (1 << 63) - 1
NAMES = ["pa", "pb", "pc", "pd"]
PRIMS = ("dup drop swap over nip tuck rot 2dup 2drop + - * negate abs 1+ 1- = <> < > 0= "
         "0<> 0< 0> and or xor invert rshift max min true false lshift -rot").split()
OUTPUTS = ["dup .", "dup u.", "dup emit", "cr", "space", "3 spaces", "0 spaces", ".s",
           '." hi there"', '."   lead"', 's" typed text" type', '." "']
INPUTS = [0, 1, -1, 2, 7, 31, 32, 63, 255, 2 ** 31, 2 ** 32 - 1, -(2 ** 31), MIN, MAX]
START, MIDDLE, END = "@@IR@@", "@@HOST@@", "@@END@@"


def literal(rng):
    """A number in one of the forms the program words read (A3)."""
    n = rng.choice([0, 1, -1, 3, 16, 255, 2 ** 31 - 1, 2 ** 32 - 1, -(2 ** 31), 65536])
    form = rng.randrange(5)
    if form == 1:
        return f"#{n}"
    if form == 2:
        return ("$-" if n < 0 else "$") + format(abs(n), rng.choice(["x", "X"]))
    if form == 3 and abs(n) < 2 ** 12:
        return ("%-" if n < 0 else "%") + format(abs(n), "b")
    if form == 4:
        return f"'{rng.choice('aZ~!0')}'"
    return str(n)


def spelt(rng, name):
    return "".join(c.upper() if rng.random() < 0.3 else c for c in name)


class File:
    """A generated source file: its lines, the IR name each definition must
    get, and the source name each line defines."""

    def __init__(self, rng):
        self.rng, self.lines, self.ir_names, self.source_names = rng, [], [], []
        self.versions, self.constants = {}, set()
        for _ in range(rng.randint(3, 10)):
            self.define()

    def visible(self):
        return sorted(self.versions)

    def body(self, name):
        r, out = self.rng, []
        for _ in range(r.randint(0, 7)):
            k = r.random()
            if k < 0.4:
                out.append(spelt(r, r.choice(PRIMS)))
            elif k < 0.55:
                out.append(literal(r))
            elif k < 0.65:
                out += [str(r.randrange(64)), r.choice(["lshift", "rshift"])]
            elif k < 0.8 and self.visible():
                # Any name seen so far; its own name only if it has a version before.
                out.append(spelt(r, r.choice(self.visible())))
            elif k < 0.95:
                out.append(r.choice(OUTPUTS))
        return out

    def define(self):
        r = self.rng
        name = r.choice(NAMES)
        version = self.versions.get(name, -1) + 1
        ir_name = name if version == 0 else f"{name}'{version}"
        if r.random() < 0.25:
            known = [n for n in self.constants if n in self.versions]
            first = spelt(r, r.choice(known)) if known and r.random() < 0.4 else literal(r)
            tail = r.choice([[], [literal(r), r.choice(["+", "-", "*", "max", "and", "xor"])],
                             ["negate"], ["invert"]])
            self.lines.append(" ".join([first] + tail + ["constant", spelt(r, name)]))
            self.constants.add(name)
        else:
            line = "x" * 200
            while len(line) > 120:    # lines must be shorter than 128 characters
                line = " ".join([":", spelt(r, name)] + self.body(name) + [";"])
            self.lines.append(line)
            self.constants.discard(name)
        self.versions[name] = version
        self.ir_names.append(ir_name)
        self.source_names.append(name)


def forth_string(text):
    return 's\\" ' + "".join("\\x%02x" % b if b in (34, 92) or not 32 <= b < 127 else chr(b)
                             for b in text.encode("latin-1")) + '"'


DRIVER = f"""require {ROOT}/src/program/verify.fs
require {ROOT}/src/program/ir-run.fs
[defined] warnings [if] false warnings ! [then]
decimal
\\ The program words' IR, shown and loaded into the interpreter.
: ir-show ( c-addr u -- ) ." | " 2dup type cr irx-load-line ;
: verify-ir ( c-addr u -- )
  irx-load-start ['] ir-show lf-verify-to lf-verify-file ." VERIFY " .
  irx-load-finish . cr ;
\\ Plain Gforth: each line evaluated in a word list of the file's own,
\\ the definition's token kept right after its line.
create host-settings /run-settings allot
variable host-words
create tokens 64 cells allot
: host-file ( -- ) wordlist host-words ! ;
: host-scope ( -- )
  host-settings run-settings-save drop forth-wordlist host-words @ 2 set-order
  host-words @ set-current decimal ;
: host-line ( c-addr u c-addr2 u2 k -- )
  >r 2>r host-scope ['] evaluate catch host-settings run-settings-restore throw
  2r> host-words @ search-wordlist 0= abort" not defined" r> cells tokens + ! ;
\\ A case: inputs kept, then run by the interpreter (its output between
\\ markers), and by Gforth when the interpreter ended normally.
create inputs 16 cells allot
variable inputs#
: inputs! ( i*x n -- ) dup inputs# ! 0 ?do inputs inputs# @ 1- i - cells + ! loop ;
: inputs@ ( -- i*x ) inputs# @ 0 ?do inputs i cells + @ loop ;
: irx-inputs ( -- ) irx-clear inputs# @ 0 ?do inputs i cells + @ irx-push drop loop ;
variable token
2variable ir-name
: show-items ( -- ) irx-depth dup . 0 ?do i irx-item drop . loop ;
: show-stack ( i*x -- ) depth dup . 0 ?do depth 1- i - pick . loop ;
: clear-stack ( i*x -- ) begin depth while drop repeat ;
: host-run ( -- )
  ." {MIDDLE}" inputs@ token @ catch ." {END}" ." HOST " . show-stack cr clear-stack ;
: ir-run ( -- ok? )
  ." {START}" ['] type irx-output-to irx-inputs 40 ir-name 2@ irx-run
  ['] irx-discard-output irx-output-to ." {END}" ." IR " irx-result irx-result-text type
  space show-items cr ok? ;
: run-case ( c-addr u k i*x n -- )
  inputs! cells tokens + @ token ! ir-name 2! ." CASE" cr ir-run if host-run then ;
\\ A literal as the program words read it, and as the host does.
: lit-case ( c-addr u -- )
  2dup type space 2dup pv-literal? if ." WORDS " d. else ." WORDS - " then
  depth 2 - >r ['] evaluate catch if 2drop r> drop ." HOST -" cr exit then
  ." HOST " depth r> - 0 ?do . loop cr ;
"""


def driver_text(files, directory, edges, literals):
    lines = [DRIVER]
    for n, f in enumerate(files):
        path = Path(directory) / f"r{n:03d}.fs"
        path.write_text("\n".join(f.lines) + "\n", encoding="latin-1")
        lines.append(f'." FILE {n}" cr s" {path}" verify-ir host-file')
        for k, line in enumerate(f.lines):
            lines.append(f"{forth_string(line)} s\" {f.source_names[k]}\" {k} host-line")
        rng = random.Random(n)
        for k, name in enumerate(f.ir_names):
            for _ in range(3):
                xs = [rng.choice(INPUTS) for _ in range(rng.randint(0, 5))]
                lines.append(f's" {name}" {k} {" ".join(map(str, xs))} {len(xs)} run-case')
    path = Path(directory) / "edges.fs"
    path.write_text("\n".join(EDGE_SOURCE) + "\n", encoding="latin-1")
    lines.append(f'." FILE edges" cr s" {path}" verify-ir host-file')
    for k, line in enumerate(EDGE_SOURCE):
        name = line.split()[1]
        lines.append(f"{forth_string(line)} s\" {name}\" {k} host-line")
    for name, k, xs in edges:
        lines.append(f's" {name}" {k} {" ".join(map(str, xs))} {len(xs)} run-case')
    lines.append('." LITERALS" cr')
    lines += [f"{forth_string(t)} lit-case" for t in literals]
    lines.append("bye")
    driver = Path(directory) / "driver.fs"
    driver.write_text("\n".join(lines) + "\n", encoding="latin-1")
    return driver


# Each output word on its own, for the edge cases of A2's test 1.
EDGE_SOURCE = [": o-dot . ;", ": o-udot u. ;", ": o-emit emit ;", ": o-cr cr ;",
               ": o-space space ;", ": o-spaces spaces ;", ": o-dots .s ;",
               ': o-text ."   lead  and  inner " ;', ': o-typed s" typed  text" TYPE ;',
               ': o-empty ." " ;', ": o-dup-dot dup . ;"]


def edge_cases():
    numbers = [0, -1, 1, MIN, MAX, 2 ** 31 - 1, 2 ** 31, -(2 ** 31), 2 ** 32 - 1, 2 ** 32]
    cases = [("o-dot", 0, [n]) for n in numbers] + [("o-udot", 1, [n]) for n in numbers]
    cases += [("o-emit", 2, [n]) for n in list(range(256)) + [256, 321, 955, -1, MIN, MAX]]
    cases += [("o-cr", 3, []), ("o-space", 4, [])]
    cases += [("o-spaces", 5, [n]) for n in (0, -2, MIN, 1, 5)]
    cases += [("o-dots", 6, list(range(n))) for n in (0, 3, 12)] + [("o-dots", 6, [MIN, MAX])]
    cases += [("o-text", 7, []), ("o-typed", 8, []), ("o-empty", 9, []),
              ("o-dup-dot", 10, [5]), ("o-dot", 0, []), ("o-emit", 2, [])]
    return cases


LITERALS = ["0", "-0", "4294967295", "-2147483648", "4294967296", "-2147483649",
            "#10", "#-10", "#4294967295", "$10", "$ff", "$FF", "$-80000000", "$FFFFFFFF",
            "$100000000", "%101", "%-101", "%11111111111111111111111111111111", "'a'", "'''",
            "'\"'", "'~'", "-$10", "1_000", "0x10", "1.", "-'a'", "'ab'", "$", "#-", "%2",
            "$1g", "0004294967295", "00000000001"]


def parse(stdout):
    """The records the driver printed: files (IR lines, verdict, cases) and
    literals."""
    files, literals, current, case, section = [], [], None, None, None
    data = stdout
    pos = 0
    while pos < len(data):
        end = data.find(b"\n", pos)
        end = len(data) if end < 0 else end
        line = data[pos:end]
        if line.startswith(b"FILE "):
            current = {"name": line[5:].decode(), "ir": [], "verify": None, "cases": []}
            files.append(current)
            section = "file"
        elif line == b"LITERALS":
            section = "literals"
        elif section == "literals" and line:
            literals.append(line.decode("latin-1"))
        elif line.startswith(b"| "):
            current["ir"].append(line[2:].decode("latin-1"))
        elif line.startswith(b"VERIFY "):
            current["verify"] = tuple(int(x) for x in line.split()[1:])
        elif line == b"CASE":
            # The interpreter's part: output between markers, then its result.
            start = data.index(START.encode(), end) + len(START)
            stop = data.index(END.encode(), start)
            result_end = data.index(b"\n", stop)
            ir_result = data[stop + len(END):result_end].decode().split()[1:]
            case = {"ir_out": data[start:stop], "ir": ir_result, "host": None}
            current["cases"].append(case)
            end = result_end
            if data.startswith(MIDDLE.encode(), end + 1):
                start = end + 1 + len(MIDDLE)
                stop = data.index(END.encode(), start)
                result_end = data.index(b"\n", stop)
                case["host_out"] = data[start:stop]
                case["host"] = data[stop + len(END):result_end].decode().split()[1:]
                end = result_end
        pos = end + 1
    return files, literals


def predicted_literal(text):
    """The value of a literal in the forms the program words read (A3)."""
    sys.path.insert(0, str(ROOT / "tests" / "program"))
    import verify_check  # noqa: E402
    return verify_check.literal_value(text)


def check(files, generated, literals):
    problems, counts = [], {"files": 0, "cases": 0, "compared": 0, "bytes": 0, "edges": 0}
    for record, f in zip(files, generated + [None]):
        if record["verify"] != (0, 0):
            problems.append(f"file {record['name']}: program words or interpreter refused it: "
                            f"{record['verify']} {record['ir'][-1:]}")
            continue
        if f is not None:
            names = [line.split()[1] for line in record["ir"]
                     if line.split()[:1] in (["word"], ["constant"])]
            if names != f.ir_names:
                problems.append(f"file {record['name']}: IR names {names}, predicted "
                                f"{f.ir_names}")
            counts["files"] += 1
        for n, case in enumerate(record["cases"]):
            counts["cases"] += 1
            if case["host"] is None:
                continue
            counts["compared"] += 1
            if f is None:
                counts["edges"] += 1
            ir_items, host = case["ir"][1:], case["host"]
            if host[0] != "0" or host[1:] != ir_items:
                problems.append(f"file {record['name']} case {n}: interpreter {case['ir']}, "
                                f"Gforth {host}")
            if case["host_out"] != case["ir_out"]:
                problems.append(f"file {record['name']} case {n}: interpreter printed "
                                f"{case['ir_out']!r}, Gforth {case['host_out']!r}")
            counts["bytes"] += len(case["host_out"])
    for line in literals:
        text, _, rest = line.partition(" WORDS ")
        words, _, host = rest.partition(" HOST ")
        expected = predicted_literal(text)
        if (words.strip() == "-") != (expected is None) or (
                expected is not None and int(words) != expected):
            problems.append(f"literal {text}: program words {words}, expected {expected}")
        if expected is not None and host.strip() != str(expected):
            problems.append(f"literal {text}: the program words read {expected}, Gforth {host}")
    return problems, counts


def lean_problems(lean, files, generated, directory):
    """Lean's model on the cases of the first eight generated files."""
    lines, expected = [], []
    for n, (record, f) in enumerate(zip(files[:8], generated[:8])):
        path = Path(directory) / f"r{n:03d}.ir"
        path.write_text("\n".join(record["ir"]) + "\n", encoding="latin-1")
        rng = random.Random(n)
        k_cases = iter(record["cases"])
        for k, name in enumerate(f.ir_names):
            for _ in range(3):
                xs = [rng.choice(INPUTS) for _ in range(rng.randint(0, 5))]
                case = next(k_cases)
                lines.append(f"{path} {name} 40 {' '.join(map(str, xs))} -> ?".replace("  ", " "))
                result = case["ir"]
                expected.append("ok" + "".join(f" {x}" for x in result[2:]) if result[0] == "next"
                                else f"fail {result[0]}")
    cases = Path(directory) / "lean-cases.txt"
    cases.write_text("\n".join(lines) + "\n", encoding="utf-8")
    done = subprocess.run([lean, "-DwarningAsError=true", "--run", str(EVALUATOR), str(cases)],
                          capture_output=True, text=True, timeout=900, stdin=subprocess.DEVNULL)
    if done.returncode != 0:
        return [f"Lean failed:\n{done.stdout[-2000:]}{done.stderr[-2000:]}"], 0
    got = [line.split(" -> ", 1)[1] for line in done.stdout.splitlines()]
    problems = [f"Lean case {i}: {lines[i]}: model {g}, interpreter {e}"
                for i, (g, e) in enumerate(zip(got, expected)) if g != e]
    if len(got) != len(expected):
        problems.append(f"Lean gave {len(got)} results for {len(expected)} cases")
    return problems, len(expected)


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--seed", type=int, default=20261104)
    parser.add_argument("--files", type=int, default=60)
    parser.add_argument("--lean", action="store_true")
    args = parser.parse_args()
    gforth = os.environ.get("GFORTH", "gforth")
    rng = random.Random(args.seed)
    generated = [File(rng) for _ in range(args.files)]
    with tempfile.TemporaryDirectory() as directory:
        driver = driver_text(generated, directory, edge_cases(), LITERALS)
        done = subprocess.run(["timeout", "-k", "5", "600", gforth, str(driver)],
                              capture_output=True, stdin=subprocess.DEVNULL, cwd=ROOT)
        if done.returncode != 0:
            print(done.stdout[-3000:].decode("latin-1"), done.stderr[-3000:].decode("latin-1"),
                  file=sys.stderr)
            return 1
        files, literals = parse(done.stdout)
        problems, counts = check(files, generated, literals)
        lean_note = ""
        if args.lean:
            more, compared = lean_problems(os.environ.get("LEAN", "lean"), files, generated,
                                           directory)
            problems += more
            lean_note = f"; Lean's model agrees on {compared} cases of 8 files"
    for problem in problems[:40]:
        print(problem, file=sys.stderr)
    print(f"IR 0.2 against Gforth: {counts['files']} generated files (seed {args.seed}) with "
          f"their predicted version names, {counts['cases']} cases, {counts['compared']} "
          f"run by both (the rest end abnormally in the IR: underflow, unmodeled), "
          f"{counts['edges']} of them output words at the edges, {counts['bytes']} bytes "
          f"printed alike; {len(literals)} literals read as Gforth reads them{lean_note}; "
          f"{len(problems)} problems")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
