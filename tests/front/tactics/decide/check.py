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
(dc-init.lf and dc-ops-init.lf: FilePath's HDiv, Grind's Sub and NatPow), and the slice's files,
against Init's snapshot and elaboration data, as the done checker runs them: each theorem
accepted with no axiom (their terms are compared node for node only on the slice); the wrong
twins of those operators refused with Lean's message (error 250), and decide on `∣` not
supported yet (error 93, exit 2).

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
INIT_FILES = [(D + "dc-init.lf", ["dc_sub", "dc_div", "dc_pow", "dc_word"]),
              (D + "dc-ops-init.lf", ["d_divmod", "d_mersenne", "d_euler", "d_taxicab",
                                      "d_pow_cmp"])] + FILES
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
         (D + "w-dc-ge.lf", 250, FALSE, "  10 ≥ 11\nis false")]
UNSUPPORTED = [(D + "x-dc-native.lf", 254, "`native_decide` is not supported: it trusts Lean's "
                "compiler (`Lean.ofReduceBool`), never accepted (ADR 0021 D7)"),
               (D + "x-dc-pow.lf", 93, "not supported yet: a type inference, reduction")]
# Against Init only (--init): wrong twins whose `/` and `^` need Init's first candidates, and
# decide on `∣` (Nat.decidable_dvd unverified: inferType of a lambda-headed application, FE1c).
INIT_WRONG = [(D + "w-dc-euler.lf", 250, FALSE, "  2 ^ 32 + 1 = 641 * 6700419\nis false"),
              (D + "w-dc-divmod.lf", 250, FALSE, "  17 / 5 = 3 ∧ 17 % 5 = 3\nis false")]
INIT_UNSUPPORTED = [(D + "x-dc-dvd.lf", 93, "not supported yet: a type inference, reduction")]


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


def init_mode(snapshot, data):
    """INIT_FILES against Init's snapshot: each theorem accepted with no axiom; INIT_WRONG refused
    with Lean's message and INIT_UNSUPPORTED answered not supported (exit 2), never accepted."""
    base = ["bin/leanforth", "check", "--snapshot", snapshot, "--elab-data", data]
    argvs = [base + ["--steps", "-", path] for path, _ in INIT_FILES]
    refusals = INIT_WRONG + INIT_UNSUPPORTED
    finished = tactic_check.s2.run_many(argvs + [base + [path] for path, *_ in refusals])
    for (path, names), done in zip(INIT_FILES, finished):
        code, out = tactic_check.s2.outcome(done)
        missing = [n for n in names if f"\n{n}: accepted (checked in this run" not in "\n" + out
                   or "axioms: none" not in out]
        if code != 0 or missing:
            print(f"decide --init: {path}: exit {code}, not accepted: {missing}\n{out}",
                  file=sys.stderr)
            sys.exit(1)
    for (path, number, *text), done in zip(refusals, finished):
        code, out = tactic_check.s2.outcome(done)
        want, shown = (4, "\n".join(text)) if len(text) == 2 else (2, text[0])
        if code != want or f"error {number} at " not in out or shown not in out:
            print(f"decide --init: {path}: exit {code}, expected {want}, error {number} and "
                  f"{shown!r}\n{out}", file=sys.stderr)
            sys.exit(1)
    print(f"decide --init: {sum(len(n) for _, n in INIT_FILES)} theorems of {len(INIT_FILES)} "
          f"files accepted against Init's snapshot, axioms none; {len(INIT_WRONG)} wrong twins "
          f"refused with Lean's messages; {len(INIT_UNSUPPORTED)} not supported yet (exit 2)")


if __name__ == "__main__":
    if "--init" in sys.argv:
        at = sys.argv.index("--init")
        init_mode(sys.argv[at + 1], sys.argv[at + 2])
    else:
        # --lean checks every wrong twin's message, the Init ones too.
        wrong = WRONG + INIT_WRONG if "--lean" in sys.argv else WRONG
        tactic_check.main("decide", FILES, wrong, UNSUPPORTED, own, ENV)
