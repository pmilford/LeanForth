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

Plain mode's files (FILES) include the talk's theorems that the slice elaborates, with symbol
words (dc-symbols.lf) and in ASCII spellings (dc-ascii.lf), and every symbol word on variables
(sy-vars.lf, proved from a hypothesis False; review of ops-symbols B3, 2026-11-20), each term
node for node pinned Lean's. Plain mode also runs LeanForth's own refusals (EXTRA): a value
left over (86), the fuel (--elab-fuel 50: exhausted, exit 3, never accepted) and two runs of a
file giving the same output, and --jobs 2 the same verdicts.
With --init SNAPSHOT ELAB (make reference-decide-init, part of make daily): the files whose
numerals need first candidates a slice cannot hold (dc-init.lf, dc-ops-init.lf, the talk's
other theorems with symbol words, dc-symbols-init.lf, and in ASCII spellings,
dc-ascii-init.lf: FilePath's HDiv, String's HSub, Fin's NatPow; plan S3a-ops; and the symbol
words on Int variables, numeral powers and `∣`, sy-vars-init.lf), and the slice's files,
against Init's snapshot and elaboration data, through the command line's check with each term
dumped (tests/front/elab-dump.fs's cli-dump): each theorem accepted with no axiom and its type
and value node for node pinned Lean's (goal-layer.golden), each ASCII file's terms equal to its
symbol file's; the wrong twins of those operators refused with Lean's message (error 250), and
decide on `∣` not supported yet (error 93, exit 2). Without the snapshot or the data a user's
run prints "SKIPPED, NOT RUN" and exits 0, and a recorded run (REQUIRE_INIT_SNAPSHOT=1, set by
scripts/tested-tree.py) fails; a snapshot not of this build's verdict version fails and says so.

Usage: GFORTH=... python3 tests/front/tactics/decide/check.py
       LEAN=... python3 tests/front/tactics/decide/check.py --lean [--write-golden]
       GFORTH=... python3 tests/front/tactics/decide/check.py --init INIT.lfsnap INIT.elab.ndjson
"""
import os
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tests/front/tactics"))
import tactic_check  # noqa: E402

D = "tests/front/tactics/decide/"
ENV = tactic_check.Env("tests/front/decide-slice.ndjson", "tests/front/decide-slice.elab.ndjson",
                       "decide-dump")
# The talk's theorems (plan S3a-ops C2-C5): those whose numerals elaborate on the slice, and the
# ones whose - / ^ need Init's first candidates, each with symbol words and in ASCII spellings.
TALK = ["mul", "pythag", "gauss", "gcd", "compare", "leap", "not", "or", "iff"]
TALK_INIT = ["divmod", "mersenne", "euler", "taxicab", "pow_cmp"]
# Each pair: the file with symbol words (sy_X) and its ASCII twin (as_X), terms equal node for node.
PAIRS = [((D + "dc-symbols.lf", ["sy_" + name for name in TALK]),
          (D + "dc-ascii.lf", ["as_" + name for name in TALK])),
         ((D + "dc-symbols-init.lf", ["sy_" + name for name in TALK_INIT]),
          (D + "dc-ascii-init.lf", ["as_" + name for name in TALK_INIT]))]
# The reviewer's probes of every symbol word on variables (review of ops-symbols B3, 2026-11-20),
# proved from a hypothesis False: sv_ID on the slice, si_ID (Int variables, numeral powers, ∣)
# on Init only.
VARS = (D + "sy-vars.lf", ["sv_" + i for i in
                           "p01 p02 p03 p04 p05 p06 p07 p08 p09 p11 p12 p13 p14 p19 p31 p36 p37 "
                           "p38 p39 p40 p48 p50".split()])
VARS_INIT = (D + "sy-vars-init.lf", ["si_" + i for i in
                                     "p10 p15 p16 p17 p18 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 "
                                     "p30 p32 p34 p35 p41 p42 p43 p44 p45 p46 p47 p49 r1 r2 r3 r4 "
                                     "r5 r6 r7 r8".split()])
FILES = [(D + "dc-arith.lf", ["dc_add", "dc_lt", "dc_le", "dc_mul", "dc_mod", "dc_gcd"]),
         (D + "dc-logic.lf", ["dc_not", "dc_and", "dc_or", "dc_true", "dc_bool", "dc_hyp"]),
         (D + "dc-ops.lf", ["d_mul", "d_pythag", "d_gauss", "d_gt", "d_ge", "d_ne", "d_compare",
                            "d_leap", "d_perfect", "d_mul_big"]), *PAIRS[0], VARS]
INIT_FILES = [(D + "dc-init.lf", ["dc_sub", "dc_div", "dc_pow", "dc_word"]),
              (D + "dc-ops-init.lf", ["d_divmod", "d_mersenne", "d_euler", "d_taxicab",
                                      "d_pow_cmp"]), *PAIRS[1], VARS_INIT] + FILES
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
    each ASCII file's to its symbol file's (PAIRS: as_X to sy_X)."""
    for path, names, lines in files_dumps:
        for name in names:
            for part in ("type", "value"):
                key = f"{name} {part}"
                if key not in lines or want.get(key) != lines[key]:
                    return (f"{path}: {key} differs from pinned Lean's:\n  LeanForth: "
                            f"{lines.get(key)}\n  Lean:      {want.get(key)}")
    by_path = {path: lines for path, _, lines in files_dumps}
    for (symbols, _), (ascii_, _) in PAIRS:
        for key, line in by_path[symbols].items():
            twin = by_path[ascii_].get(key.replace("sy_", "as_", 1), "")
            if twin.split(" ", 2)[2:] != line.split(" ", 2)[2:]:
                return f"{ascii_}'s {key.replace('sy_', 'as_', 1)} differs from {symbols}'s"
    return None


# What bin/leanforth prints for a snapshot that is not this build's: one of an older verdict
# version, loaded ("verdict version 8 (this build: 9)" in its snapshot line, a carry line) or
# refused, or a damaged one (COMMAND_LINE.md, "Older snapshots").
STALE = ("(this build: ", "carry: a snapshot of verdict version",
         "this build reads snapshots of verdict versions", "newer than this build's",
         "the snapshot was refused")


def missing_input(snapshot, data):
    """Why the Init run cannot start (a missing snapshot or elaboration data), else None."""
    for what, name, path in (("Init snapshot", "INIT_SNAPSHOT", snapshot),
                             ("Init elaboration data", "INIT_ELAB", data)):
        if not pathlib.Path(path).is_file():
            return f"no {what} ({name}={path})"
    return None


def stale_line(out):
    """The line of a run's report saying its snapshot is not this build's, else None."""
    return next((line for line in out.splitlines() if any(mark in line for mark in STALE)), None)


def skip_or_fail(why):
    """Without Init's inputs: a user's run says so and passes unrun (exit 0); a recorded run
    (scripts/tested-tree.py sets REQUIRE_INIT_SNAPSHOT=1: a tier, a push, make daily) fails."""
    if os.environ.get("REQUIRE_INIT_SNAPSHOT") == "1":
        print(f"check decide --init: FAILED, NOT RUN: {why}; a recorded run requires it "
              f"(REQUIRE_INIT_SNAPSHOT=1; make parallel-init writes the snapshot)", file=sys.stderr)
        sys.exit(1)
    print(f"check decide --init: SKIPPED, NOT RUN: {why}. Nothing was compared against Init; "
          f"make daily requires it (REQUIRE_INIT_SNAPSHOT=1).")
    sys.exit(0)


def init_mode(snapshot, data):
    """INIT_FILES against Init's snapshot, through the command line's check with each term
    dumped (tests/front/elab-dump.fs's cli-dump): each theorem accepted with no axiom, its
    terms node for node pinned Lean's, the ASCII file's the symbol file's; INIT_WRONG refused
    with Lean's message and INIT_UNSUPPORTED answered not supported (exit 2), never accepted.
    Without the snapshot or the data, skip_or_fail; a snapshot not of this build's verdict
    version fails and says so."""
    why = missing_input(snapshot, data)
    if why:
        skip_or_fail(why)
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
        stale = stale_line(out)
        if stale:
            print(f"decide --init: STALE SNAPSHOT, NOT A PASS: {snapshot} was not read as this "
                  f"build's snapshot ({stale.strip()}); write it again (make parallel-init) or "
                  f"give a current one (INIT_SNAPSHOT=...)", file=sys.stderr)
            sys.exit(1)
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
          f"pinned Lean's (each ASCII file's its symbol file's); {len(INIT_WRONG)} wrong twins "
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
