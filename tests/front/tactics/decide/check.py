#!/usr/bin/env python3
"""by-decide end to end against pinned Lean (plan row S3, slice S3a; src/front/tactics/decide.fs,
src/front/reduce-nat.fs): the harness and its usage are tests/front/tactics/tactic_check.py's,
against decide's own slice of Init, tests/front/decide-slice.ndjson (its roots
tests/front/decide-slice.roots, cut by scripts/export-slice.py from Init's export, its
elaboration data by scripts/export-elab.sh): the slice holds, besides the statements'
constants, the first instance Lean's search tries for OfNat, HAdd, Add, HMod, Mod, HPow, Pow,
LT, LE and Mul on a goal whose type is a metavariable, and for HMul (Lean.Omega.IntList's,
then Vector's for `HMul Nat ?b ?c`; plan S3a-ops C1), so that numerals elaborate as on all of
Init (a left-out first candidate answers unsupported, error 119).

Plain mode also runs LeanForth's own refusals (EXTRA): a value left over (86), the fuel
(--elab-fuel 50: exhausted, exit 3, never accepted) and two runs of a file giving the same
output, and --jobs 2 the same verdicts.
With --init SNAPSHOT ELAB: the files whose numerals need first candidates a slice cannot hold
(dc-init.lf, dc-ops-init.lf, and the talk's theorems with symbol words, dc-symbols.lf, and in
ASCII spellings, dc-ascii.lf: FilePath's HDiv, String's HSub, Fin's NatPow; plan S3a-ops), and
the slice's files, against Init's snapshot and elaboration data, through the command line's
check with each term dumped (tests/front/elab-dump.fs's cli-dump): each theorem accepted with
no axiom and its type and value node for node pinned Lean's (goal-layer.golden), dc-ascii.lf's
terms equal to dc-symbols.lf's; the wrong twins of those operators refused with Lean's message
(error 250), and decide on `∣` not supported yet (error 93, exit 2).

Usage: GFORTH=... python3 tests/front/tactics/decide/check.py
       LEAN=... python3 tests/front/tactics/decide/check.py --lean
       GFORTH=... python3 tests/front/tactics/decide/check.py --init INIT.lfsnap INIT.elab.ndjson
"""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tests/front/tactics"))
import tactic_check  # noqa: E402

D = "tests/front/tactics/decide/"
ENV = tactic_check.Env("tests/front/decide-slice.ndjson", "tests/front/decide-slice.elab.ndjson",
                       "decide-dump")
FILES = [(D + "dc-arith.lf", ["dc_add", "dc_lt", "dc_le", "dc_mul", "dc_mod", "dc_gcd"]),
         (D + "dc-logic.lf", ["dc_not", "dc_and", "dc_or", "dc_true", "dc_bool", "dc_hyp"]),
         (D + "dc-ops.lf", ["d_mul", "d_pythag", "d_gauss", "d_gt", "d_ge", "d_ne", "d_compare",
                            "d_leap", "d_perfect", "d_mul_big"])]
TALK = ["mul", "pythag", "gauss", "divmod", "gcd", "compare", "leap", "mersenne", "euler",
        "taxicab", "not", "or", "iff", "pow_cmp"]
SYMBOLS = (D + "dc-symbols.lf", ["sy_" + name for name in TALK])
ASCII = (D + "dc-ascii.lf", ["as_" + name for name in TALK])
INIT_FILES = [(D + "dc-init.lf", ["dc_sub", "dc_div", "dc_pow", "dc_word"]),
              (D + "dc-ops-init.lf", ["d_divmod", "d_mersenne", "d_euler", "d_taxicab",
                                      "d_pow_cmp"]), SYMBOLS, ASCII] + FILES
FALSE = "Tactic `decide` proved that the proposition"
FVARS = "Expected type must not contain free variables"
REVERT = "\n\nHint: Use the `+revert` option to automatically clean up and revert free variables"
# Lean's first line and the detail after it. Lean prints Decidable (Nonempty Nat) and
# @decide P I where LeanForth's printer, given no binder kinds by the slice, writes
# @Nonempty Nat and Decidable.decide P I (plan 8.6): those compare their first lines.
WRONG = [(D + "w-dc-add.lf", 250, FALSE, "  2 + 2 = 5\nis false"),
         (D + "w-dc-lt.lf", 250, FALSE, "  ¬10 < 20\nis false"),
         (D + "w-dc-and.lf", 250, FALSE, "  3 ≤ 3 ∧ 2 + 2 = 5\nis false"),
         (D + "w-dc-fvar.lf", 251, FVARS, "  n + 1 = n" + REVERT),
         (D + "w-dc-fvar0.lf", 251, FVARS, "  n + 0 = n" + REVERT),
         (D + "w-dc-nonempty.lf", 122, "failed to synthesize", ""),
         (D + "w-dc-choice.lf", 253, "Tactic `decide` failed to reduce", ""),
         (D + "w-dc-choice-bool.lf", 253, "Tactic `decide` failed to reduce", ""),
         (D + "w-dc-none.lf", 90, "No goals to be solved", ""),
         (D + "w-dc-mul.lf", 250, FALSE, "  6 * 7 = 43\nis false"),
         (D + "w-dc-gt.lf", 250, FALSE, "  10 > 20\nis false"),
         (D + "w-dc-ne.lf", 250, FALSE, "  3 ≠ 3\nis false"),
         (D + "w-dc-ge.lf", 250, FALSE, "  10 ≥ 11\nis false"),
         # Slice S3a-ops C2-C5: symbol words, some in Lean's ASCII spelling.
         (D + "w-sy-lt.lf", 250, FALSE, "  20 < 10\nis false"),
         (D + "w-sy-ne.lf", 250, FALSE, "  3 ≠ 3\nis false"),
         (D + "w-sy-ge.lf", 250, FALSE, "  10 ≥ 11\nis false"),
         (D + "w-sy-or.lf", 250, FALSE, "  1 = 0 ∨ 2 = 3\nis false"),
         (D + "w-sy-iff.lf", 250, FALSE, "  2 = 2 ↔ 2 = 3\nis false"),
         (D + "w-sy-not.lf", 250, FALSE, "  ¬2 = 2\nis false")]
UNSUPPORTED = [(D + "x-dc-native.lf", 254, "`native_decide` is not supported: it trusts Lean's "
                "compiler (`Lean.ofReduceBool`), never accepted (ADR 0021 D7)"),
               (D + "x-dc-pow.lf", 93, "not supported yet: a type inference, reduction")]
# Against Init only (--init): wrong twins whose `/` and `^` need Init's first candidates, and
# decide on `∣` (Nat.decidable_dvd unverified: inferType of a lambda-headed application, FE1c).
INIT_WRONG = [(D + "w-dc-euler.lf", 250, FALSE, "  2 ^ 32 + 1 = 641 * 6700419\nis false"),
              (D + "w-dc-divmod.lf", 250, FALSE, "  17 / 5 = 3 ∧ 17 % 5 = 3\nis false"),
              (D + "w-sy-euler.lf", 250, FALSE, "  2 ^ 32 + 1 = 641 * 6700419\nis false"),
              (D + "w-sy-divmod.lf", 250, FALSE, "  17 / 5 = 3 ∧ 17 % 5 = 3\nis false")]
INIT_UNSUPPORTED = [(D + "x-dc-dvd.lf", 93, "not supported yet: a type inference, reduction"),
                    (D + "x-sy-dvd.lf", 93, "not supported yet: a type inference, reduction")]
# #check of symbol words against Init: pinned Lean's lines for c-sy-check.lean (--lean).
CHECKS = (D + "c-sy-check.lf", D + "c-sy-check.lean",
          ["3 ∣ 12 : Prop", "3 ∣ 12 : Prop", "2 ^ 10 : Nat", "2 ^ 3 ^ 2 : Nat",
           "10 - 3 < 10 ∧ 17 / 5 = 3 : Prop"])


def checks_printed(out):
    return [line for line in out.splitlines() if line.endswith((" : Prop", " : Nat"))]


def lean_checks():
    """Pinned Lean prints CHECKS' lines for c-sy-check.lean."""
    done = next(tactic_check.s2.run_many([[tactic_check.s2.lean_binary(), CHECKS[1]]]))
    if done.returncode != 0 or checks_printed(done.stdout) != CHECKS[2]:
        print(f"decide --lean: {CHECKS[1]}: exit {done.returncode}\n{done.stdout}{done.stderr}",
              file=sys.stderr)
        sys.exit(1)


def outcome(argv):
    return tactic_check.s2.outcome(next(tactic_check.s2.run_many([argv])))


def own(_golden):
    """LeanForth's own refusals and its determinism, against the slice."""
    code, out = outcome(tactic_check.check_argv(ENV, D + "x-dc-value.lf"))
    if code != 4 or "error 86 at " not in out:
        raise tactic_check.Failure(f"x-dc-value.lf: exit {code}, expected 4 and error 86\n{out}")
    code, out = outcome(tactic_check.check_argv(ENV, D + "dc-arith.lf", "--elab-fuel", "50"))
    if code != 3 or "accepted; axioms" in out:
        raise tactic_check.Failure(f"--elab-fuel 50: exit {code}, expected 3 and nothing "
                                   f"accepted\n{out}")
    runs = tactic_check.s2.run_many([tactic_check.check_argv(ENV, D + "dc-logic.lf", "--steps", "-"),
                                     tactic_check.check_argv(ENV, D + "dc-logic.lf", "--steps", "-"),
                                     tactic_check.check_argv(ENV, D + "dc-logic.lf", "--jobs", "2")])
    first, second, jobs = (tactic_check.s2.outcome(done) for done in runs)
    if first != second:
        raise tactic_check.Failure("dc-logic.lf: two runs differ")
    verdicts = [line for line in first[1].splitlines() if ": accepted" in line]
    if jobs[0] != 0 or verdicts != [line for line in jobs[1].splitlines() if ": accepted" in line]:
        raise tactic_check.Failure(f"dc-logic.lf: --jobs 2 gives other verdicts\n{jobs[1]}")
    return "a value left over 86, --elab-fuel 50 exhausted, two runs and --jobs 2 alike"


def fast_engine():
    """bin/leanforth's engine: the gforth-fast beside GFORTH, else GFORTH itself."""
    gforth = pathlib.Path(tactic_check.s2.GFORTH)
    fast = gforth.with_name("gforth-fast")
    return str(fast) if gforth.name == "gforth" and fast.exists() else str(gforth)


def dumped(out):
    """The NAME type/value lines tests/front/elab-dump.fs's cli-dump printed, by key."""
    return {" ".join(line.split(" ", 2)[:2]): line for line in out.splitlines()
            if tactic_check.DUMPED.match(line)}


def same_terms(want, files_dumps):
    """Each theorem's type and value equal to pinned Lean's (the golden) node for node, and
    dc-ascii.lf's to dc-symbols.lf's (as_X to sy_X)."""
    for path, names, lines in files_dumps:
        for name in names:
            for part in ("type", "value"):
                key = f"{name} {part}"
                if key not in lines or want.get(key) != lines[key]:
                    return (f"{path}: {key} differs from pinned Lean's:\n  LeanForth: "
                            f"{lines.get(key)}\n  Lean:      {want.get(key)}")
    by_path = {path: lines for path, _, lines in files_dumps}
    for key, line in by_path[SYMBOLS[0]].items():
        twin = by_path[ASCII[0]].get(key.replace("sy_", "as_", 1), "")
        if twin.split(" ", 2)[2:] != line.split(" ", 2)[2:]:
            return f"dc-ascii.lf's {key.replace('sy_', 'as_', 1)} differs from dc-symbols.lf's"
    return None


def init_mode(snapshot, data):
    """INIT_FILES against Init's snapshot, through the command line's check with each term
    dumped (tests/front/elab-dump.fs's cli-dump): each theorem accepted with no axiom, its
    terms node for node pinned Lean's, the ASCII file's the symbol file's; INIT_WRONG refused
    with Lean's message and INIT_UNSUPPORTED answered not supported (exit 2), never accepted."""
    opts = ["check", "--snapshot", snapshot, "--elab-data", data]
    dump = [fast_engine(), "src/main.fs", "tests/front/elab-dump.fs", "-e", "cli-dump (bye)"]
    argvs = [dump + opts + ["--steps", "-", path] for path, _ in INIT_FILES]
    refusals = INIT_WRONG + INIT_UNSUPPORTED
    base = ["bin/leanforth"] + opts
    finished = tactic_check.s2.run_many(argvs + [base + [path] for path, *_ in refusals]
                                        + [base + [CHECKS[0]]])
    files_dumps = []
    for (path, names), done in zip(INIT_FILES, finished):
        code, out = tactic_check.s2.outcome(done)
        missing = [n for n in names if f"\n{n}: accepted (checked in this run" not in "\n" + out
                   or "axioms: none" not in out]
        if code != 0 or missing:
            print(f"decide --init: {path}: exit {code}, not accepted: {missing}\n{out}",
                  file=sys.stderr)
            sys.exit(1)
        files_dumps.append((path, names, dumped(out)))
    differ = same_terms(tactic_check.golden(), files_dumps)
    if differ:
        print(f"decide --init: {differ}", file=sys.stderr)
        sys.exit(1)
    for (path, number, *text), done in zip(refusals, finished):
        code, out = tactic_check.s2.outcome(done)
        want, shown = (4, "\n".join(text)) if len(text) == 2 else (2, text[0])
        if code != want or f"error {number} at " not in out or shown not in out:
            print(f"decide --init: {path}: exit {code}, expected {want}, error {number} and "
                  f"{shown!r}\n{out}", file=sys.stderr)
            sys.exit(1)
    code, out = tactic_check.s2.outcome(next(finished))
    if code != 0 or checks_printed(out) != CHECKS[2] or "nothing checked by the kernel" not in out:
        print(f"decide --init: {CHECKS[0]}: exit {code}, not Lean's #check lines\n{out}",
              file=sys.stderr)
        sys.exit(1)
    print(f"decide --init: {sum(len(n) for _, n in INIT_FILES)} theorems of {len(INIT_FILES)} "
          f"files accepted against Init's snapshot, axioms none, their terms node for node "
          f"pinned Lean's (dc-ascii.lf's dc-symbols.lf's); {len(INIT_WRONG)} wrong twins "
          f"refused with Lean's messages; {len(INIT_UNSUPPORTED)} not supported yet (exit 2); "
          f"{len(CHECKS[2])} #check lines as pinned Lean's")


if __name__ == "__main__":
    if "--init" in sys.argv:
        at = sys.argv.index("--init")
        init_mode(sys.argv[at + 1], sys.argv[at + 2])
    else:
        # --lean checks every wrong twin's message, the Init ones too, and the #check lines.
        if "--lean" in sys.argv:
            lean_checks()
        wrong = WRONG + INIT_WRONG if "--lean" in sys.argv else WRONG
        tactic_check.main("decide", FILES, wrong, UNSUPPORTED, own, ENV)
