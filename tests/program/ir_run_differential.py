"""Three-way comparison for the program IR interpreter (task 2.5.4).

Usage (from the repository root):
  GFORTH=... python3 tests/program/ir_run_differential.py                 # make test
  GFORTH=... LEAN=... python3 tests/program/ir_run_differential.py --lean # make check
  options: --seed N (random programs, default 20261102), --programs N (default 300),
           --programs02 N (IR 0.2 programs, seed N + 1, default 150)

Without --lean it needs only Gforth and Python: it checks that the copies
of the model in tests/reference/program-ir-run.lean are verbatim, and runs
tests/program/ir-run-table.fs, where the IR interpreter (on the reader's IR
of src/program/clamp.fs and examples.fs) and the host's own execution of
those words must give the same stack on every case, and where two planted
faults in the interpreter must be caught.

With --lean it also gives every line of that table to Lean's evaluation of
the model (tests/reference/program-ir-run.lean), which must print exactly
the same lines; generates random IR programs and cases (every primitive,
IF, loops also inside loops, calls, EXIT, constants, unknown words,
literals with leading zeros, small fuel), and IR 0.2 programs with LSHIFT,
-ROT, out lines and version names, which the
interpreter (tests/program/ir-run-cases.fs) and Lean must also agree on
exactly (the stacks; what out lines print is compared with the hosts by
tests/program/verify_ir02.py); checks that faults planted in the
interpreter's primitive table make that comparison fail; and checks that
the comparison notices one changed line. Finite tests, not a proof.
"""
import argparse
import collections
import os
from pathlib import Path
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_program_ir import copy_problems  # noqa: E402

EVALUATOR = Path("tests/reference/program-ir-run.lean")
TABLE = Path("tests/program/ir-run-table.fs")
RUNNER = Path("tests/program/ir-run-cases.fs")
COPIED = "tests/reference/program-ir.lean"
MASK = (1 << 64) - 1
MAX = (1 << 63) - 1

PRIMS = ["dup", "drop", "swap", "over", "nip", "tuck", "rot", "2dup", "2drop", ">r", "r>",
         "r@", "+", "-", "*", "/", "mod", "negate", "abs", "1+", "1-", "=", "<>", "<", ">",
         "0=", "0<>", "0<", "0>", "and", "or", "xor", "invert", "rshift", "max", "min",
         "true", "false"]
# IR 0.2 (ADR 0019 Amendment 1): two more primitives and the output words,
# which the second batch of random programs also uses.
PRIMS_02 = PRIMS + ["lshift", "-rot"] * 4
OUTS = [".", "u.", "cr", "emit", "space", "spaces", ".s", '." x y"', '." "']
# Faults planted in the interpreter: (description, Forth phrase run before the cases).
PLANTS = [
    ("xor computed as or", "' or s\" xor\" plant-fault"),
    ("0> computed as 0<", "' 0< s\" 0>\" plant-fault"),
    ("nip computed as drop", "' drop s\" nip\" plant-fault"),
    ("-rot computed as rot", "' rot s\" -rot\" plant-fault"),
    ("lshift computed as rshift", "' rshift s\" lshift\" plant-fault"),
]


class Random:
    """xorshift64, so that the programs do not depend on Python's generator."""

    def __init__(self, seed):
        self.state = (seed & MASK) or 1

    def next(self):
        x = self.state
        x ^= (x << 13) & MASK
        x ^= x >> 7
        x ^= (x << 17) & MASK
        self.state = x
        return x

    def below(self, n):
        return self.next() % n

    def choice(self, items):
        return items[self.below(len(items))]


def value(rng):
    """A literal or input: small numbers, shift counts, cell edges."""
    kind = rng.below(4)
    if kind < 2:
        return rng.below(15) - 4
    if kind == 2:
        return rng.choice([63, 64, 65, 2 ** 31, -(2 ** 31), MAX, -MAX, MAX - 1])
    return (rng.next() & MASK) - (1 << 63) if rng.below(2) else rng.below(1000)


def literal(rng):
    """A literal's text: mostly a value, sometimes one at or beyond the cell's
    edge, which the model and the interpreter must both treat as unmodeled;
    sometimes with leading zeros, which the model's parser (String.toInt?)
    reads as the same number, and so must the interpreter."""
    if rng.below(12) == 0:
        n = rng.choice([-(1 << 63), 1 << 63, -(1 << 63) - 1, 10 ** 20, -(10 ** 20)])
    else:
        n = value(rng)
    zeros = "0" * (1 + rng.below(25)) if rng.below(8) == 0 else ""
    return ("-" if n < 0 else "") + zeros + str(abs(n))


def block(rng, names, depth, pad, ir02=False):
    """Up to five lines at one depth; IF up to three deep, and loops, also
    inside loops, up to two deep; for IR 0.2 also LSHIFT, -ROT and out
    lines."""
    lines = []
    for _ in range(rng.below(6)):
        kind = rng.below(100)
        if ir02 and kind < 12:
            word = rng.choice(OUTS)
            if word == "spaces":    # a small count: the interpreter prints every blank
                lines.append(f"{pad}lit {rng.below(4) - 1}")
            lines.append(f"{pad}out {word}")
        elif kind < 55:
            lines.append(f"{pad}prim {rng.choice(PRIMS_02 if ir02 else PRIMS)}")
        elif kind < 73:
            lines.append(f"{pad}lit {literal(rng)}")
        elif kind < 83:
            lines.append(f"{pad}call {rng.choice(names + ['zz'])}")
        elif kind < 91 and depth < 3:
            lines.append(f"{pad}if")
            lines += block(rng, names, depth + 1, pad + "  ", ir02)
            if rng.below(2):
                lines.append(f"{pad}else")
                lines += block(rng, names, depth + 1, pad + "  ", ir02)
            lines.append(f"{pad}then")
        elif kind < 96 and depth < 2:
            lines.append(f"{pad}begin")
            lines += block(rng, names, depth + 1, pad + "  ", ir02)
            lines.append(f"{pad}while")
            lines += block(rng, names, depth + 1, pad + "  ", ir02)
            lines.append(f"{pad}repeat")
        else:
            lines.append(f"{pad}exit")
    return lines


def program(rng, number, ir02=False):
    """A random program; for IR 0.2 its names are versions (w0'1 ...)."""
    names = [f"w{i}'{i}" if ir02 else f"w{i}" for i in range(1 + rng.below(4))]
    lines = ["lf-ir 0.2" if ir02 else "lf-ir 0.1", f"source random-{number}"]
    for name in names:
        kind = "constant" if rng.below(5) == 0 else "word"
        lines.append(f"{kind} {name}")
        lines += block(rng, names, 0, "  ", ir02 and kind == "word")
        lines.append("end")
    return names, "\n".join(lines) + "\n"


def random_cases(directory, seed, count, ir02=False):
    rng = Random(seed)
    cases = []
    for number in range(count):
        names, text = program(rng, number, ir02)
        path = Path(directory) / f"p{number:04d}{'-02' if ir02 else ''}.ir"
        path.write_text(text, encoding="utf-8")
        for _ in range(4):
            word = rng.choice(names + ["zz"]) if rng.below(20) == 0 else rng.choice(names)
            inputs = [value(rng) for _ in range(rng.below(6))]
            fields = [str(path), word, str(rng.below(7))] + [str(x) for x in inputs]
            cases.append(" ".join(fields) + " -> ?")
    return cases


def run(command):
    done = subprocess.run(command, capture_output=True, text=True, timeout=600, stdin=subprocess.DEVNULL)
    if done.returncode != 0:
        raise SystemExit(f"{' '.join(command)} failed ({done.returncode}):\n{done.stdout}{done.stderr}")
    return done.stdout.splitlines()


def forth_cases(gforth, case_file, plant=None):
    phrase = (plant + " " if plant else "") + f"s\" {case_file}\" run-case-file bye"
    return run([gforth, str(RUNNER), "-e", phrase])


def lean_cases(lean, case_file):
    return run([lean, "-DwarningAsError=true", "--run", str(EVALUATOR), str(case_file)])


def differences(left, right):
    if len(left) != len(right):
        return [f"{len(left)} lines against {len(right)}"]
    return [f"interpreter: {a}\nmodel:       {b}" for a, b in zip(left, right) if a != b]


def outcome_mix(lines):
    mix = collections.Counter()
    for line in lines:
        result = line.split(" -> ", 1)[1]
        mix["ok" if result.startswith("ok") else result.split()[1]] += 1
    return dict(sorted(mix.items()))


def summary_line(summary, prefix):
    found = [line for line in summary if line.startswith(prefix)]
    if len(found) != 1:
        raise SystemExit(f"ir-run-table: no single '{prefix}' line in {summary}")
    return found[0]


def table_counts(line):
    """'# NAME cases N host M mismatches K ...' as a dictionary of numbers."""
    words = line.split()
    return {words[i]: int(words[i + 1]) for i in range(len(words) - 1)
            if words[i] in ("cases", "host", "mismatches", "seed")}


def check_table(gforth):
    """The table's case lines and its summary: totals, clamp alone, planted faults."""
    lines = run([gforth, str(TABLE)])
    summary = [line for line in lines if line.startswith("#")]
    cases = [line for line in lines if not line.startswith("#")]
    totals = table_counts(summary_line(summary, "# cases"))
    clamp = table_counts(summary_line(summary, "# clamp"))
    planted = summary_line(summary, "# planted").split()
    if totals["mismatches"] or clamp["mismatches"] or len(cases) != totals["cases"]:
        raise SystemExit(f"ir-run-table: unexpected summary {summary}")
    if "0" in (planted[-3], planted[-1]):
        raise SystemExit(f"ir-run-table: a planted fault was not caught: {summary}")
    return cases, [summary_line(summary, "# cases"), summary_line(summary, "# planted")]


def write(directory, name, lines):
    path = Path(directory) / name
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return path


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lean", action="store_true")
    parser.add_argument("--seed", type=int, default=20261102)
    parser.add_argument("--programs", type=int, default=300)
    parser.add_argument("--programs02", type=int, default=150)
    args = parser.parse_args()
    gforth = os.environ.get("GFORTH", "gforth")
    problems, copied = copy_problems(EVALUATOR.read_text(encoding="utf-8"))
    if problems or copied != {COPIED}:
        raise SystemExit("program-ir-run.lean copies: " + "; ".join(problems or ["none found"]))
    table, summary = check_table(gforth)
    print(f"ir-run table: {summary[0][2:]}; {summary[1][2:]}; outcomes {outcome_mix(table)}")
    if not args.lean:
        return 0
    lean = os.environ.get("LEAN", "lean")
    with tempfile.TemporaryDirectory() as directory:
        found = differences(table, lean_cases(lean, write(directory, "table.txt", table)))
        if found:
            raise SystemExit("Lean and the interpreter differ on the table:\n" + "\n".join(found[:10]))
        changed = table[:]
        changed[len(changed) // 2] = changed[len(changed) // 2].replace(" -> ok", " -> ok 0", 1)
        if not differences(changed, table):
            raise SystemExit("the comparison did not notice a changed line")
        cases = random_cases(directory, args.seed, args.programs)
        cases02 = random_cases(directory, args.seed + 1, args.programs02, ir02=True)
        case_file = write(directory, "random.txt", cases + cases02)
        forth = forth_cases(gforth, case_file)
        found = differences(forth, lean_cases(lean, case_file))
        if found:
            raise SystemExit("Lean and the interpreter differ on random programs:\n" + "\n".join(found[:10]))
        caught = []
        for description, phrase in PLANTS:
            count = len(differences(forth_cases(gforth, case_file, phrase), forth))
            if count == 0:
                raise SystemExit(f"planted fault not caught: {description}")
            caught.append(f"{description}: {count}")
    print(f"Lean agrees on all {len(table)} table lines and on {len(forth)} cases of "
          f"{args.programs} random IR 0.1 programs (seed {args.seed}) and "
          f"{args.programs02} IR 0.2 programs (seed {args.seed + 1}), outcomes "
          f"{outcome_mix(forth)}; planted faults caught ({'; '.join(caught)}); a changed line "
          f"is noticed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
