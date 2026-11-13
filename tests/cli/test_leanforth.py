"""The command line end to end (plan tasks 3.4.1-3.4.3, 6.5.2 in part): bin/leanforth.

1. Every exit code, with the exact text printed:
   0 every declaration accepted (composition; the constant fixture's three;
     tests/cli/chain.ndjson, larger than --record holds; tests/cli/
     inductive.ndjson, an inductive type and a theorem by its recursor;
     tests/cli/sharing.ndjson, proofs shared along 2^40 paths, in little fuel,
     and sharing-universe.ndjson, such a statement at a universe argument;
     tests/cli/nested.ndjson, nested inductive types as Lean writes them),
     or skipped (composition as an unsafe definition, plan task 5.2.7);
   1 rejected (composition with the wrong argument; the wrong twins of
     sharing.ndjson and sharing-universe.ndjson, which Lean's kernel rejects
     too; the lean-kernel-arena's four proofs of False in tests/cli/bugs/,
     each rejected where Lean 4.35.0 rejects it);
   2 unsupported (an axiom; a literal; with --record an inductive type,
     refused while reading) and unknown (UNKNOWN, a block whose check needs
     a recursor reduction the checker does not port yet; tests/cli/
     unfold.ndjson, which needs a definition unfolded, is accepted since
     plan task 4.2.2d, and tests/cli/irrelevance.ndjson, a proof that needs
     proof irrelevance, since plan task 4.2.5); every record kind
     (tests/core/reexport/kinds.ndjson) counted;
   3 a resource limit (chain with --record ends full while reading; a
     name part of 2^64 is beyond the stage's 32 bits; fuel 0 and 30 end
     exhausted);
   4 malformed (a variable without its binder; a missing manifest; a file
     that is not an export; a file that does not open; a tampered or cut
     export, with and without its manifest; a constant no declaration has;
     every kind of mistake on the command line, --json with --record
     too, and a fuel amount above 2^53 - 1; a copy that would overwrite
     its export, also under another name);
   5 an internal fault (a Gforth that ends with a status of its own, and
     the real Gforth with an allocation made to throw, while feeding and
     inside a check, or with the publisher made to throw mid-run);
   6 all accepted but some NOT PROVED, only with --strict-axioms (by
     default NOT PROVED keeps Lean's 0): an export's own axiom
     (composition-postulate.ndjson); tests/cli/leanforth.fs also plants
     an axiom in a slot, and the schema is tested here with planted
     reports too.
2. "accepted" is printed only on a declaration's line, each with its
   axioms and no label (owner, 2026-11-12), and only when the code is 0
   or that line's declaration is accepted while another is not.
3. The tool works from any folder, with relative and absolute names, and
   prints the same bytes on every run.
4. count prints what src/import/ndjson-count.fs prints, and reexport writes
   a copy equal to the export, byte for byte, for every reference export.
5. version, capabilities and help exit 0; capabilities states the limits
   and lists checking a LeanForth text; --jobs N with a text says that it
   checks one declaration at a time (TextJobs).
6. print prints each declaration's proof outline exactly as the outline's
   golden file has it (all five reference exports, one declaration by
   name, every step with --detail); a declaration not accepted is refused,
   with its outcome's code, and no outline appears except below an
   accepted verdict; a name no declaration has, and print's command-line
   mistakes, are 4.
7. --json prints one report that the schema (schemas/check-report-0.4)
   accepts, for every case of 1, with the exit status, every verdict and
   the counts the text gives; it is the same on every run but for
   "measured", and its counts and fuel add up as the schema's $comment
   says. --resources adds the resource report, the same on every run but
   for its time and memory lines. The fuel each check used is exact: a
   budget of that much gives the same verdict, one less runs out.
8. Names are shown as Lean's Name.toString shows them, with escapes for
   control, format and separator characters, so that no name can forge a
   line; of any depth; the export's file name with the same escapes.
9. The engine: gforth-fast by default; --checked runs Gforth's checking
   engine; with GFORTH set it is the engine, and --fast runs the
   gforth-fast beside it, with the same text and the same JSON report but
   for "measured", which names the engine; with no gforth-fast the run
   says so on standard error and uses the default.

Run with GFORTH set to the Forth binary (the Makefile does this).
"""
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tests" / "support"))
from schema_subset import Validator  # noqa: E402
TEST_LIMIT = int(os.environ.get("TEST_TIMEOUT", "1800"))  # seconds; make exports it
TOOL = ROOT / "bin" / "leanforth"
_gforth = os.environ.get("GFORTH", "gforth")
GFORTH = str(Path(_gforth).resolve()) if os.sep in _gforth else _gforth
CASES = "tests/core/check-declaration-cases"
COMPOSITION = "tests/reference/composition.ndjson"
FIXTURE = "tests/reference/constant-fixture.ndjson"
LABEL = "accepted; axioms: none"
INDUCTIVE = "tests/cli/inductive.ndjson"
CHAIN = "tests/cli/chain.ndjson"
EMPTY_BLOCK = "tests/core/check-block-cases/names.empty-block.ndjson"
# Unknown: a block whose positivity check needs iota on Lean's generated
# recursor, which LeanForth does not port yet (diagnostic 81; closed by a
# follow-up of plan task 5.2.1b, tests/core/inductive-table.py).
UNKNOWN = "tests/core/check-block-cases/after.list-left-out-then-lookup-during-param-block.ndjson"
# Proofs whose terms share subterms along 2^40 paths (tests/cli/sharing.lean).
SHARING = "tests/cli/sharing.ndjson"


def shared_twins(text):
    """sharing.ndjson with sharedAnd and sharedBeta made the wrong twins that
    sharing.lean shows Lean's kernel rejects (appTypeMismatch), and without
    the theorem that uses them: in sharedAnd the innermost And.intro gets P
    for both proofs h, in sharedBeta q 0 is True instead of h."""
    records = [json.loads(line) for line in text.splitlines()]
    exprs = {r["ie"]: r for r in records if "ie" in r}
    names = {r["in"]: r["str"]["str"] for r in records if "str" in r and "in" in r}
    values = {names.get(d["thm"]["name"]): d["thm"]["value"] for d in records if "thm" in d}

    def body(e, binders):
        for _ in range(binders):
            e = exprs[e]["lam"]["body"]
        return e

    def args(e):
        """The application records of e's spine, outermost first."""
        spine = []
        while "app" in exprs[e]:
            spine.append(e)
            e = exprs[e]["app"]["fn"]
        return spine
    level = body(values["sharedAnd"], 2)      # And.intro t t q q, 40 times over
    while "bvar" not in exprs[exprs[args(level)[0]]["app"]["arg"]]:
        level = exprs[args(level)[0]]["app"]["arg"]
    spine = args(level)                       # And.intro P P h h
    p = exprs[spine[3]]["app"]["arg"]
    for e in spine[:2]:
        exprs[e]["app"]["arg"] = p
    level = body(values["sharedBeta"], 1)     # (fun y : True => q k) (q k), 10 times
    while "bvar" not in exprs[exprs[level]["app"]["arg"]]:
        level = exprs[level]["app"]["arg"]
    lam = exprs[exprs[level]["app"]["fn"]]["lam"]
    lam["body"] = exprs[level]["app"]["arg"] = lam["type"]
    kept = [r for r in records if "thm" not in r or names.get(r["thm"]["name"]) != "sharing"]
    return "".join(json.dumps(r, ensure_ascii=False, separators=(",", ":")) + "\n" for r in kept)


# A statement shared along 2^40 paths, instantiated at a universe argument
# (tests/cli/sharing-universe.lean).
SHARING_UNIVERSE = "tests/cli/sharing-universe.ndjson"


def universe_twin(text, twin):
    """sharing-universe.ndjson with useU made a wrong twin that
    sharing-universe.lean shows Lean's kernel rejects (declTypeMismatch):
    "argument" proves it by sharedAndU.{1}, "leaves" states its leaves
    ∀ (β : Sort 1), P. Either needs the level 1, a new record (with a new
    sort for the leaves) written just before the record that uses it."""
    records = [json.loads(line) for line in text.splitlines()]
    exprs = {r["ie"]: r for r in records if "ie" in r}
    names = {r["in"]: r["str"]["str"] for r in records if "str" in r and "in" in r}
    use = next(r["thm"] for r in records if "thm" in r and names[r["thm"]["name"]] == "useU")
    one = {"il": 1 + max(r["il"] for r in records if "il" in r), "succ": 0}
    if twin == "argument":
        target, new = exprs[use["value"]], [one]
        target["const"]["us"] = [one["il"]]
    else:
        target = exprs[use["type"]]
        for _ in range(3):                    # under α, P and h
            target = exprs[target["forallE"]["body"]]
        while "app" in target:                # T (k+1) = And (T k) (T k)
            target = exprs[target["app"]["arg"]]
        sort = {"ie": 1 + max(exprs), "sort": one["il"]}
        target["forallE"]["type"] = sort["ie"]
        new = [one, sort]
    at = records.index(target)
    records[at:at] = new
    return "".join(json.dumps(r, ensure_ascii=False, separators=(",", ":")) + "\n"
                   for r in records)


def accepted(n, axioms="none"):
    """The summary line of n accepted declarations, none NOT PROVED: they use
    no axiom, or only the allowlisted ones given."""
    return f"accepted: {n}; axioms: {axioms}"



NO_MANIFEST = "note: the export's manifest is not checked (--no-manifest)"
LIMITS = [
    "note: check --record and replay hold at most 64 names, 64 levels,",
    "note: 64 term nodes and 32 declarations per export; check without --record holds "
    "any size",
]
MANIFEST_HINT = [
    "note: the export is checked against EXPORT.manifest.json, which "
    "scripts/export.sh writes;",
    "note: --no-manifest skips that check",
]
# What capabilities says of a LeanForth text (plan 8.2.1c's notes), under "supported".
TEXT_CAPABILITY = (
    "  check [--env EXPORT | --snapshot FILE] FILE.lf: a LeanForth text, its\n"
    "    declarations built by LeanForth's words and checked as an export's\n"
    "    (plan tasks 8.2.1c-d), one at a time (--jobs does not apply yet); not\n"
    "    with --json, --record or --save-snapshot\n")
# check --jobs N (N above 1) with a LeanForth text, before its verdicts.
TEXT_JOBS_NOTE = ("note: --jobs does not apply to LeanForth text yet; checking one "
                  "declaration at a time")


def run(*args, cwd=ROOT, gforth=GFORTH, tool=TOOL):
    """The exit status and everything printed, standard output first."""
    result = subprocess.run([str(tool), *args], cwd=cwd, env=dict(os.environ, GFORTH=gforth),
                            stdin=subprocess.DEVNULL, capture_output=True, timeout=TEST_LIMIT)
    return result.returncode, result.stdout.decode(), result.stderr.decode()


# Independent runs of one test (each with its own files, or only reading) go side by
# side, at most this many at once: make check runs two targets at once (JOBS=2).
SIDE_BY_SIDE = 2


def side_by_side(function, items):
    """function of each item, at most SIDE_BY_SIDE at once; the results in items' order."""
    with concurrent.futures.ThreadPoolExecutor(max_workers=SIDE_BY_SIDE) as pool:
        return list(pool.map(function, items))


class ExitCodes(unittest.TestCase):
    def expect(self, args, code, lines):
        status, out, err = run(*args)
        self.assertEqual((status, out.splitlines(), err), (code, lines, ""), args)

    def test_0_accepted(self):
        self.expect(["check", COMPOSITION], 0,
                    [f"composition: {LABEL}", "1 declaration: 1 accepted", accepted(1)])
        self.expect(["check", FIXTURE], 0,
                    [f"fixtureId: {LABEL}", f"fixturePoly: {LABEL}", f"fixtureUse: {LABEL}",
                     "3 declarations: 3 accepted", accepted(3)])
        self.expect(["check", CHAIN], 0,
                    [f"chain: {LABEL}", "1 declaration: 1 accepted", accepted(1)])
        # An inductive type, a theorem and a definition by its recursor:
        # Lean's verdicts, accepted, not unsupported (as --record answers).
        self.expect(["check", INDUCTIVE], 0,
                    [f"Two: {LABEL}", f"Two.first: {LABEL}", f"Two.second: {LABEL}",
                     f"Two.rec: {LABEL}", f"Two.cases: {LABEL}", f"Two.swap: {LABEL}",
                     "6 declarations: 6 accepted", accepted(6)])

    def test_1_forged_quotient(self):
        """Lean's export of propext, Classical.choice and Quot.sound
        (tests/reference/inductive/axioms.ndjson) is accepted, the three
        counted as proved; with Quot.mk's record given Quot's type, all
        are still accepted and Quot.sound proved, as Lean's replay
        ignores a quotient record's type and uses its own (ADR 0015 Q1:
        the record gets a warning, Quot.mk Lean's type)."""
        source = ROOT / "tests" / "reference" / "inductive" / "axioms.ndjson"
        status, out, _ = run("check", "--no-manifest", str(source))
        self.assertEqual((status, out.splitlines()[-2]), (0, "16 declarations: 16 accepted"))
        self.assertIn("Quot.sound: accepted; "
                      "axioms: Quot.sound", out.splitlines())
        # The summary names the allowlisted axioms used (review rvAX L4).
        self.assertEqual(out.splitlines()[-1], "accepted: 16; "
                         "axioms: propext, Classical.choice, Quot.sound "
                         "(allowlisted); none NOT PROVED")
        text = source.read_text(encoding="utf-8")
        forged = text.replace('"name":31,"type":121}', '"name":31,"type":115}')
        self.assertNotEqual(forged, text)
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "forged.ndjson"
            path.write_text(forged, encoding="utf-8")
            status, out, _ = run("check", "--no-manifest", str(path))
        lines = out.splitlines()
        self.assertEqual((status, lines[-2]), (0, "16 declarations: 16 accepted"))
        self.assertIn("Quot.sound: accepted; "
                      "axioms: Quot.sound", lines)

    def test_1_rejected(self):
        self.expect(["check", "--no-manifest", f"{CASES}/composition-wrong-argument.ndjson"], 1,
                    [NO_MANIFEST, "composition: rejected",
                     "  rejected: argument type mismatch (D1-D5); diagnostic 59 at mixed-infer "
                     "lf-mixed-infer: 0 0",
                     "1 declaration: 1 rejected"])
        # An empty inductive block, which Lean's kernel rejects (emptyBlock):
        # it has no name, Lean's anonymous one.
        self.expect(["check", "--no-manifest", EMPTY_BLOCK], 1,
                    [NO_MANIFEST, "[anonymous]: rejected",
                     "  rejected: an inductive block without types; diagnostic 78 at check-block "
                     "lf-block-check: 0 0",
                     "1 declaration: 1 rejected"])

    def test_1_shared_terms(self):
        """Terms shared along 2^40 paths (tests/cli/sharing.lean): Lean's
        verdicts, accepted, and on the wrong twins rejected, as Lean's
        kernel rejects them; each node is audited, opened and compared
        once, so the fuel stays small (it ran out at 2,000,000 before,
        agent EX, 2026-11-10)."""
        self.expect(["check", SHARING], 0,
                    [f"{name}: {LABEL}" for name in
                     ["And", "And.intro", "And.rec", "sharedAnd", "True", "True.intro",
                      "True.rec", "sharedBeta", "trivial", "sharing"]]
                    + ["10 declarations: 10 accepted", accepted(10)])
        status, out, _ = run("check", "--json", SHARING)
        fuel = {d["name"]: d["fuel"] for d in json.loads(out)["declarations"]}
        self.assertLess(max(fuel.values()), 100000, fuel)
        mismatch = ("  rejected: argument type mismatch (D1-D5); diagnostic 59 at mixed-infer "
                    "lf-mixed-infer: 0 0")
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "twins.ndjson"
            path.write_text(shared_twins((ROOT / SHARING).read_text(encoding="utf-8")),
                            encoding="utf-8")
            self.expect(["check", "--no-manifest", str(path)], 1,
                        [NO_MANIFEST, *[f"{name}: {LABEL}" for name in
                                        ["And", "And.intro", "And.rec"]],
                         "sharedAnd: rejected", mismatch,
                         *[f"{name}: {LABEL}" for name in ["True", "True.intro", "True.rec"]],
                         "sharedBeta: rejected", mismatch, f"trivial: {LABEL}",
                         "9 declarations: 7 accepted, 2 rejected", accepted(7)])

    def test_1_shared_universe(self):
        """A statement shared along 2^40 paths, instantiated at a universe
        argument (tests/cli/sharing-universe.lean; review rvPSE M1): Lean's
        verdicts, accepted, and on both wrong twins rejected, as Lean's
        kernel rejects them; the level substitution checks and rebuilds
        each shared node once, so the fuel stays small (useU ran out at
        2,000,000 before, agent FX7, 2026-11-11)."""
        own = ["And", "And.intro", "And.rec", "sharedAndU"]
        self.expect(["check", SHARING_UNIVERSE], 0,
                    [f"{name}: {LABEL}" for name in own + ["useU"]]
                    + ["5 declarations: 5 accepted", accepted(5)])
        status, out, _ = run("check", "--json", SHARING_UNIVERSE)
        fuel = {d["name"]: d["fuel"] for d in json.loads(out)["declarations"]}
        self.assertLess(fuel["useU"], 20000, fuel)
        mismatch = ("  rejected: declared type mismatch (D1-D5); diagnostic 60 at "
                    "check-declaration lf-check-declaration: 0 0")
        text = (ROOT / SHARING_UNIVERSE).read_text(encoding="utf-8")
        for twin in ("argument", "leaves"):
            with self.subTest(twin=twin), tempfile.TemporaryDirectory() as folder:
                path = Path(folder) / "twin.ndjson"
                path.write_text(universe_twin(text, twin), encoding="utf-8")
                self.expect(["check", "--no-manifest", str(path)], 1,
                            [NO_MANIFEST, *[f"{name}: {LABEL}" for name in own],
                             "useU: rejected", mismatch,
                             "5 declarations: 4 accepted, 1 rejected", accepted(4)])

    def test_0_not_proved(self):
        """An axiom (plan task 5.3.1): Lean's verdict, accepted, marked NOT
        PROVED with the axiom named; status 0 as Lean, 6 under
        --strict-axioms."""
        postulate = f"{CASES}/composition-postulate.ndjson"
        line = (f"composition: accepted; axioms: unlisted; NOT PROVED: depends on composition")
        lines = [NO_MANIFEST, line, "1 declaration: 1 accepted",
                 "accepted: 1; axioms: 1 NOT PROVED (they depend on an axiom)"]
        note = ["note: NOT PROVED declarations keep Lean's exit status; --strict-axioms",
                "note: makes it 6"]
        self.expect(["check", "--no-manifest", postulate], 0, lines + note)
        self.expect(["check", "--no-manifest", "--strict-axioms", postulate], 6, lines)
        # Every axiom a declaration rests on, through its type and value, as
        # Lean's #print axioms lists them; propext with another statement
        # than Lean's is no allowlisted axiom (inductive-table rows).
        blocks = "tests/core/check-block-cases"
        for case, line in [
                ("postulate.declared-and-used", "IE.usesSecret: accepted; "
                 "axioms: unlisted; NOT PROVED: depends on IE.Secret, "
                 "IE.secret"),
                ("postulate.propext-altered", "IE.anything: accepted; "
                 "axioms: unlisted; NOT PROVED: depends on propext")]:
            status, out, _ = run("check", "--no-manifest", f"{blocks}/{case}.ndjson")
            self.assertEqual(status, 0, case)
            self.assertIn(line, out.splitlines(), case)

    def test_0_skipped(self):
        """An unsafe or partial declaration (plan task 5.2.7): skipped, as Lean's
        replay skips it, with Lean's status 0; a safe declaration that uses one
        is rejected, as the official checker rejects it (unknown constant)."""
        skip = ("  skipped: unsafe or partial, as Lean's replay skips it; diagnostic 97 at "
                "environment lf-env-skip: 1 1")
        self.expect(["check", "--no-manifest", f"{CASES}/composition-unsafe.ndjson"], 0,
                    [NO_MANIFEST, "composition: skipped", skip, "1 declaration: 1 skipped"])
        status, out, _ = run("check", "--no-manifest",
                             "tests/core/check-block-cases/unsafe.def-then-safe-user.ndjson")
        lines = out.splitlines()
        self.assertEqual(status, 1)
        self.assertIn("IE.unsafeLoop: skipped", lines)
        self.assertIn("IE.fromUnsafe: rejected", lines)

    def test_1_arena_bugs(self):
        """Four proofs of False from the lean-kernel-arena (tests/bugs/proj-of-stuck-prop,
        proj-of-subst-prop, rec-missing-ih, rec-of-subst-prop; their exports copied from
        the arena's Lean 4.35.0 run into tests/cli/bugs/), which Lean 4.35.0's checker
        rejects: rejected at the declaration Lean rejects, never unknown (diagnostic 81
        before the follow-up of task 5.2.1b: K and structure eta on a local of a block's
        telescope, iota.fs; is_prop's typeExpected, infer-proj.fs)."""
        for case, first, diagnostic in [
                ("proj-of-stuck-prop", "Native64ResultSortOwner: rejected",
                 "  rejected: inductive type not ending in a Sort (T2); diagnostic 68 at "
                 "check-block lf-block-check: "),
                ("proj-of-subst-prop", "PR14806Subst.observe: rejected",
                 "  rejected: type expected (S1); diagnostic 55 at infer-proj lf-infer-proj: "),
                ("rec-missing-ih", "Native64TwoHashOwner: rejected",
                 "  rejected: non-valid occurrence of the type (P2); diagnostic 80 at "
                 "check-block lf-block-check: 2 2"),
                ("rec-of-subst-prop", "Issue.forallFalse: rejected",
                 "  rejected: type expected (S1); diagnostic 55 at infer-proj lf-infer-proj: ")]:
            status, out, _ = run("check", "--no-manifest", f"tests/cli/bugs/{case}.ndjson")
            lines = out.splitlines()
            self.assertEqual(status, 1, case)
            self.assertEqual([l for l in lines if l.endswith(": unknown")], [], case)
            at = lines.index(first)
            self.assertTrue(lines[at + 1].startswith(diagnostic), (case, lines[at + 1]))
            self.assertEqual([l for l in lines[:at] if l.endswith(": rejected")], [], case)

    def test_1_infer_only(self):
        """Lean's infer-only typing meeting an ill-typed term that beta reduction made
        (tests/cli/shared-depths.lean P5, its ten rows in one export; plan task 4.2.7d,
        ADR 0014 Amendment 10): rejected where pinned Lean's kernel throws (funExpected,
        typeExpected, invalidProj), never unknown, and the pi row, which LeanForth
        accepted while it took a Pi for a type untyped, rejected; accepted where Lean's
        infer-only typing types no lambda domain (lamgood) or let (letgood)."""
        status, out, _ = run("check", "--no-manifest", f"{CASES}/infer-only.ndjson")
        lines = out.splitlines()
        self.assertEqual(status, 1)
        self.assertIn("31 declarations: 27 accepted, 4 rejected", lines)
        for name, diagnostic in [
                ("appbad", "function expected (F1); diagnostic 58 at mixed-infer"),
                ("pibad", "binder domain not a type (S2); diagnostic 56 at mixed-infer"),
                ("lambad", "function expected (F1); diagnostic 58 at mixed-infer"),
                ("projbad", "invalid projection (J2); diagnostic 91 at infer-proj")]:
            at = lines.index(f"InferOnly.{name}: rejected")
            self.assertTrue(lines[at + 1].startswith(f"  rejected: {diagnostic}"), lines[at + 1])
        for name in ["appgood", "pigood", "lam2good", "lamgood", "letgood", "projgood"]:
            self.assertIn(f"InferOnly.{name}: accepted; "
                          "axioms: none", lines)

    def test_1_infer_only_p6(self):
        """Lean's infer-only typing at is_def_eq steps 4, 11 and 14 and in K-like reduction
        (tests/cli/shared-depths.lean P6, the fourteen probe rows of review rvCK in one
        export): rejected where pinned Lean's kernel throws funExpected (pilambody,
        etapibad, pinat, unitpi, kbad), accepted on their good twins and on the rows Lean
        accepts (pilam, letdep, natpi, projarg, etafvar)."""
        status, out, _ = run("check", "--no-manifest", f"{CASES}/infer-only-p6.ndjson")
        lines = out.splitlines()
        self.assertEqual(status, 1)
        self.assertIn("44 declarations: 39 accepted, 5 rejected", lines)
        for name in ["pilambody", "etapibad", "pinat", "unitpi", "kbad"]:
            at = lines.index(f"Ck.{name}: rejected")
            self.assertTrue(lines[at + 1].startswith("  rejected: function expected (F1); "
                                                     "diagnostic 58 at mixed-infer"), lines[at + 1])
        for name in ["pilam", "pilambodygood", "letdep", "etapigood", "natpi", "unitpigood",
                     "projarg", "kgood", "etafvar"]:
            self.assertIn(f"Ck.{name}: accepted; "
                          "axioms: none", lines)

    def test_2_unsupported_and_unknown(self):
        # A proof that is a string literal, typed String, which the file does not
        # declare: rejected, as pinned Lean's kernel rejects it (plan task 5.2.3).
        status, out, _ = run("check", "--no-manifest", f"{CASES}/composition-literal.ndjson")
        self.assertEqual((status, out.splitlines()[1]), (1, "composition: rejected"))
        status, out, _ = run("check", "--no-manifest", "tests/core/reexport/kinds.ndjson")
        self.assertEqual((status, out.splitlines()[-2:]),
                         (2, ["106 declarations: 94 accepted, 1 skipped, 11 unsupported",
                              accepted(94, "propext (allowlisted); none NOT PROVED")]))
        self.expect(["check", "--no-manifest", "--record", "/dev/null",
                     "tests/core/reexport/kinds.ndjson"], 2,
                    [NO_MANIFEST,
                     "error: unsupported: an inductive type (not supported yet) (line 51)"])
        self.expect(["check", "tests/cli/unfold.ndjson"], 0,
                    [f"Implies: {LABEL}", f"impliesSelf: {LABEL}",
                     "2 declarations: 2 accepted", accepted(2)])
        self.expect(["check", "tests/cli/irrelevance.ndjson"], 0,
                    [f"irrelevant: {LABEL}", "1 declaration: 1 accepted", accepted(1)])
        # Nested inductive types as Lean writes them (plan task 5.2.5b; review
        # rvUNNI): through an indexed family and a mutual block, and theorems
        # that reduce through the auxiliary recursor VT.rec_1; all accepted.
        status, out, _ = run("check", "tests/cli/nested.ndjson")
        lines = out.splitlines()
        self.assertEqual((status, lines[-2:]),
                         (0, ["107 declarations: 107 accepted", accepted(107)]))
        for name in ("RvNest.VT.rec_1", "RvNest.AT.rec_2", "RvNest.VT.size_two",
                     "RvNest.R.count_mk"):
            self.assertIn(f"{name}: {LABEL}", lines)
        recursor = ("  undecided: a recursor reduction LeanForth does not port yet; "
                    "diagnostic 81 at whnf lf-whnf: 35 0")
        self.expect(["check", "--no-manifest", UNKNOWN], 2,
                    [NO_MANIFEST, f"IE.L: {LABEL}", f"IE.L.nil: {LABEL}", f"IE.L.cons: {LABEL}",
                     "IE.W: unknown", recursor, "IE.W.mk: unknown", recursor,
                     "5 declarations: 3 accepted, 2 unknown", accepted(3)])

    def test_3_limits(self):
        self.expect(["check", "--record", "/dev/null", CHAIN], 3,
                    ["error: full: too many expression nodes or constant references for the "
                     "check's stores (line 97)", *LIMITS])
        self.expect(["check", "--no-manifest", "tests/cli/composition-huge-number.ndjson"], 3,
                    [NO_MANIFEST, "error: full: number beyond 32 bits (line 12)"])
        # U2 reads the root's data word at no cost (plan step S6 (c)), so
        # the structural audit is the first step that needs fuel.
        exhausted = ["  fuel exhausted; diagnostic 1 at constant-term-boundary "
                     "lf-cterm-check: 0 0"]
        self.expect(["check", "--fuel", "0", FIXTURE], 3,
                    ["fixtureId: exhausted", *exhausted, "fixturePoly: exhausted", *exhausted,
                     "fixtureUse: exhausted", *exhausted, "3 declarations: 3 exhausted",
                     "note: a check ran out of fuel (0 steps each); --fuel N gives each more"])
        status, out, _ = run("check", "--fuel", "30", COMPOSITION)
        self.assertEqual((status, out.splitlines()[0]), (3, "composition: exhausted"))

    def test_4_malformed(self):
        self.expect(["check", "--no-manifest", f"{CASES}/composition-loose.ndjson"], 4,
                    [NO_MANIFEST, "composition: invalid",
                     "  invalid input: out of scope; diagnostic 23 at constant-term-scope "
                     "lf-constant-term-scope: 7 6",
                     "1 declaration: 1 invalid"])
        self.expect(["check", f"{CASES}/composition-loose.ndjson"], 4,
                    ["error: invalid: manifest missing, unreadable or too large (line 0)",
                     *MANIFEST_HINT])
        self.expect(["check", "--no-manifest", "README.md"], 4,
                    [NO_MANIFEST, "error: invalid: unexpected character (line 1, byte 0)"])
        self.expect(["check", "tests/cli/no-such.ndjson"], 4, ["error: cannot open the export"])
        self.expect(["count", "tests/cli/no-such.ndjson"], 4, ["error: cannot open the export"])

    def test_4_command_line(self):
        hint = "try: leanforth help"
        for args, error in [
            (["check"], "error: a wrong number of file names"),
            (["check", "a", "b"], "error: a wrong number of file names"),
            (["check", "a", "b", "c"], "error: one file name too many: c"),
            (["reexport", COMPOSITION], "error: a wrong number of file names"),
            (["version", "x"], "error: a wrong number of file names"),
            (["check", "--fuel", "x", COMPOSITION], "error: not a fuel amount: x"),
            (["check", "--fuel", "-1", COMPOSITION], "error: not a fuel amount: -1"),
            (["check", "--fuel", "99999999999999999999", COMPOSITION],
             "error: not a fuel amount: 99999999999999999999"),
            (["check", "--fuel", str(2**53), COMPOSITION],
             f"error: a fuel amount above {2**53 - 1}: {2**53}"),
            (["replay", "--fuel", str(2**63 - 1), COMPOSITION, "r.json"],
             f"error: a fuel amount above {2**53 - 1}: {2**63 - 1}"),
            (["check", COMPOSITION, "--fuel"], "error: an option without its value: --fuel"),
            (["check", "--bogus", COMPOSITION], "error: an unknown option: --bogus"),
            (["check", "--json", "--record", "r.json", COMPOSITION],
             "error: --json and --resources do not go with --record"),
            (["check", "--record", "r.json", "--resources", COMPOSITION],
             "error: --json and --resources do not go with --record"),
            (["check", "--any-lean-version", "--record", "r.json", COMPOSITION],
             "error: --any-lean-version does not go with --record"),
            (["count", "--any-lean-version", COMPOSITION],
             "error: an option this command does not take: --any-lean-version"),
            (["replay", "--any-lean-version", COMPOSITION, "r.json"],
             "error: an option this command does not take: --any-lean-version"),
            (["print", "--json", COMPOSITION],
             "error: an option this command does not take: --json"),
            (["print", "--strict-axioms", COMPOSITION],
             "error: an option this command does not take: --strict-axioms"),
            (["count", "--fuel", "3", COMPOSITION],
             "error: an option this command does not take: --fuel"),
            (["frobnicate"], "error: an unknown command: frobnicate"),
            ([""], "error: an unknown command"),
        ]:
            self.expect(args, 4, [error, hint])
        status, out, _ = run()
        self.assertEqual((status, out.splitlines()[0]),
                         (4, "usage: leanforth COMMAND [OPTION]... [FILE]..."))

    def test_4_copy_over_export(self):
        self.expect(["reexport", COMPOSITION, COMPOSITION], 4, ["error: COPY must not be EXPORT"])
        self.expect(["reexport", COMPOSITION, "tests/../" + COMPOSITION], 4,
                    ["error: COPY must not be EXPORT"])
        with tempfile.TemporaryDirectory() as folder:
            self.expect(["reexport", COMPOSITION, f"{folder}/missing/copy.ndjson"], 4,
                        ["error: cannot create the copy"])

    def test_4_record_over_export(self):
        self.expect(["check", "--record", COMPOSITION, COMPOSITION], 4,
                    ["error: RECORD must not be EXPORT"])
        self.expect(["check", "--record", "tests/../" + COMPOSITION, COMPOSITION], 4,
                    ["error: RECORD must not be EXPORT"])
        with tempfile.TemporaryDirectory() as folder:
            self.expect(["check", "--record", f"{folder}/missing/run.json", COMPOSITION], 4,
                        [f"composition: {LABEL}", "1 declaration: 1 accepted", accepted(1),
                         "error: the run record was not written: invalid"])

    def test_5_broken_gforth(self):
        with tempfile.TemporaryDirectory() as folder:
            stub = Path(folder) / "gforth"
            stub.write_text("#!/bin/sh\necho 'composition: accepted'\nexit 0\n")
            stub.chmod(stub.stat().st_mode | stat.S_IXUSR)
            status, out, err = run("check", COMPOSITION, gforth=str(stub))
            self.assertEqual((status, err), (5, "leanforth: internal fault: Gforth ended with "
                                                "status 0\n"))
            stub.write_text("#!/bin/sh\nexit 1\n")
            self.assertEqual(run("check", COMPOSITION, gforth=str(stub))[0], 5)

    def test_5_thrown(self):
        """The real Gforth, an allocation of the stores made to throw
        (tests/support/alloc-fail.fs, loaded before src/main.fs): at the
        first, while feeding; at the 24th, the first in composition's check
        (feeding it and making the environment make 23, which
        tests/cli/leanforth.fs counts afresh)."""
        with tempfile.TemporaryDirectory() as folder:
            stub = Path(folder) / "gforth"
            for k, lines in [
                (1, ["internal fault: a Forth exception (THROW -4150)"]),
                (24, ["composition: invalid",
                      "  invalid: internal fault; diagnostic 29 at env-publish lf-env-step: "
                      "0 -4150",
                      "internal fault: the run stopped: a check threw, or publishing failed",
                      "1 declaration: 1 invalid"]),
            ]:
                stub.write_text(f'#!/bin/sh\nmain=$1\nshift\nexec "{GFORTH}" '
                                f'"{ROOT}/tests/support/alloc-fail.fs" "$main" '
                                f'-e "{k} af-arm-throw" "$@"\n')
                stub.chmod(stub.stat().st_mode | stat.S_IXUSR)
                status, out, err = run("check", COMPOSITION, gforth=str(stub))
                self.assertEqual((status, out.splitlines(), err), (5, lines, ""), k)
                # With --json: a THROW outside a check leaves no report; one
                # inside a check, a whole report of a run that stopped.
                status, out, err = run("check", "--json", COMPOSITION, gforth=str(stub))
                if k == 1:
                    self.assertEqual((status, out.splitlines(), err), (5, lines, ""))
                    continue
                got = json.loads(out)
                schema = Validator(json.loads(
                    (ROOT / "schemas/check-report-0.4.schema.json").read_text()))
                self.assertEqual((status, schema.errors(got), got["stopped"], got["exitStatus"],
                                  got["declarations"][0]["diagnostic"]["code"]),
                                 (5, [], True, 5, 29))

    def test_5_stopped_mid_run(self):
        """The real Gforth with the publisher's test hook
        (lf-env-before-final, a DEFER when lf-env-fault-hooks is defined
        before src/main.fs) made to throw before the fixture's second
        declaration's slot is final: the first stays accepted, the second
        is invalid, the third not checked; the JSON report is whole."""
        with tempfile.TemporaryDirectory() as folder:
            stub = Path(folder) / "gforth"
            stub.write_text(f'#!/bin/sh\nmain=$1\nshift\nexec "{GFORTH}" '
                            f'-e ": lf-env-fault-hooks ;" "$main" '
                            f'-e ": throw-at-1 lf-env-limit 1 = if 4242 throw then ;" '
                            f'''-e "' throw-at-1 is lf-env-before-final" "$@"\n''')
            stub.chmod(stub.stat().st_mode | stat.S_IXUSR)
            status, out, err = run("check", FIXTURE, gforth=str(stub))
            lines = out.splitlines()
            self.assertEqual((status, lines[0], lines[1], lines[-4:], err),
                             (5, f"fixtureId: {LABEL}", "fixturePoly: invalid",
                              ["internal fault: the run stopped: a check threw, or publishing "
                               "failed", "fixtureUse: not checked (not reached: the run stopped)",
                               "3 declarations: 1 accepted, 1 invalid, 1 not checked",
                               accepted(1)], ""))
            status, out, err = run("check", "--json", FIXTURE, gforth=str(stub))
            got = json.loads(out)
            self.assertEqual((status, err, JsonReport.schema.errors(got), got["run"],
                              got["stopped"], got["exitStatus"],
                              [d["verdict"] for d in got["declarations"]]),
                             (5, "", [], "invalid", True, 5,
                              ["accepted", "invalid", "not-checked"]))
            JsonReport().sums(got, "stopped")


OUTLINES = ROOT / "tests" / "present" / "outlines.golden"
LATEX_OUTLINES = ROOT / "tests" / "present" / "outlines-latex.golden"
REFUSED = "No proof outline: the declaration was not accepted."


OTHER_LEAN = "tests/core/other-lean.ndjson"
OTHER_NOTE = ("note: export made by Lean 4.29.1 (githash 2fcce7258eeb6e324366bc25f9058293b04b7547), "
              "written by handcrafted 0.1.0; verdicts are Lean 4.35.0's")
FOO_NOT_PROVED = ("foo: accepted; axioms: unlisted; "
                  "NOT PROVED: depends on foo")


class OtherLean(unittest.TestCase):
    """--any-lean-version (check and print): an export whose metadata names
    another exporter and Lean version of format 3.1.0 (here one with sparse
    and repeated indices, as lean4export's own parser reads them) is
    unsupported by default and read with the option, a note saying what it
    named; the JSON report says so in settings and exportMeta."""

    def test_check(self):
        status, out, _ = run("check", "--no-manifest", OTHER_LEAN)
        self.assertEqual((status, out.splitlines()),
                         (2, [NO_MANIFEST, "error: unsupported: unsupported exporter, format or "
                              "Lean version (line 1)"]))
        status, out, _ = run("check", "--no-manifest", "--any-lean-version", OTHER_LEAN)
        self.assertEqual((status, out.splitlines()[:4]),
                         (0, [NO_MANIFEST, OTHER_NOTE, FOO_NOT_PROVED, "1 declaration: 1 accepted"]))
        # A pinned export reads as before: no note.
        self.assertEqual(run("check", "--any-lean-version", COMPOSITION)[:2],
                         (0, f"composition: {LABEL}\n1 declaration: 1 accepted\n{accepted(1)}\n"))

    def test_print(self):
        status, out, _ = run("print", "--no-manifest", "--any-lean-version", OTHER_LEAN)
        self.assertEqual((status, out.splitlines()[:2]), (0, [NO_MANIFEST, OTHER_NOTE]))
        status, out, _ = run("print", "--lf", "--no-manifest", "--any-lean-version", OTHER_LEAN)
        self.assertEqual(status, 0)
        self.assertIn("\\ " + OTHER_NOTE, out.splitlines())

    def test_escaped(self):
        """A crafted version cannot forge a line: it is shown escaped."""
        text = (ROOT / OTHER_LEAN).read_text(encoding="utf-8")
        crafted = text.replace('"version":"4.29.1"', '"version":"4.29.1\\nbar: accepted"')
        self.assertNotEqual(crafted, text)
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "crafted.ndjson"
            path.write_text(crafted, encoding="utf-8")
            status, out, _ = run("check", "--no-manifest", "--any-lean-version", str(path))
        lines = out.splitlines()
        self.assertEqual((status, len(lines)), (0, 7))
        self.assertTrue(lines[1].startswith("note: export made by Lean 4.29.1\\u{A}bar: accepted "),
                        lines[1])

    def test_json(self):
        schema = Validator(json.loads((ROOT / "schemas/check-report-0.4.schema.json").read_text()))
        status, out, _ = run("check", "--json", "--no-manifest", "--any-lean-version", OTHER_LEAN)
        got = json.loads(out)
        self.assertEqual((status, schema.errors(got), got["settings"]["anyLeanVersion"]),
                         (0, [], True))
        self.assertEqual(got["exportMeta"], {
            "exporter": {"name": "handcrafted", "version": "0.1.0"}, "format": {"version": "3.1.0"},
            "lean": {"githash": "2fcce7258eeb6e324366bc25f9058293b04b7547", "version": "4.29.1"}})
        # Without the option, or for a pinned export, no exportMeta.
        status, out, _ = run("check", "--json", "--no-manifest", OTHER_LEAN)
        got = json.loads(out)
        self.assertEqual((status, schema.errors(got), "anyLeanVersion" in got["settings"],
                          "exportMeta" in got, got["read"]["outcome"]),
                         (2, [], False, False, "unsupported"))
        status, out, _ = run("check", "--json", "--any-lean-version", COMPOSITION)
        got = json.loads(out)
        self.assertEqual((status, schema.errors(got), "exportMeta" in got), (0, [], False))


def golden(section):
    """A section of the outlines' golden file (tests/present/outlines.golden,
    printed by tests/present/outline-cases.fs), as lines."""
    parts = re.split(r"^== (.*)$", OUTLINES.read_text(encoding="utf-8"), flags=re.M)
    return dict(zip(parts[1::2], parts[2::2]))[section].strip("\n").splitlines()


class Print(unittest.TestCase):
    """print (plan task 2.4.4): each declaration's proof outline, printed
    from the checker's derivation log right after its check; never one for
    a declaration that is not accepted. The text equals the outline's
    golden file, which the outline printer's own test pins."""

    def lines(self, *args):
        status, out, err = run("print", *args)
        self.assertEqual(err, "", args)
        return status, out.strip("\n").splitlines()

    def test_0_outlines(self):
        for name in ("identity", "composition", "type-identity", "poly-identity",
                     "constant-fixture"):
            self.assertEqual(self.lines(f"tests/reference/{name}.ndjson"), (0, golden(name)))
        self.assertEqual(self.lines("--detail", COMPOSITION), (0, golden("composition --detail")))

    def test_0_statement_forms(self):
        """--statement picks the forms of the statement the header shows (plan task
        8.6.2): each alone, in any order and all (the default); a form that is no
        form, or an empty list, is a command-line mistake (status 4)."""
        full = golden("composition")
        math = next(i for i, l in enumerate(full) if l.startswith("  Statement in mathematics:"))
        forth = next(i for i, l in enumerate(full) if l.startswith("  Statement in LeanForth"))
        end = full.index("    end composition")
        parts = {"lean": full[math - 2:math - 1], "text": full[math - 1:math],
                 "mathematics": full[math:math + 1], "leanforth": full[forth:end + 1]}
        before, after = full[:math - 2], full[end + 1:]
        for forms in ("lean", "text", "mathematics", "leanforth", "lean,leanforth",
                      "leanforth,lean", "mathematics,lean", "text,mathematics", "all"):
            wanted = [name for name in parts if name in forms.split(",") or forms == "all"]
            expected = before + [l for name in wanted for l in parts[name]] + after
            self.assertEqual(self.lines("--statement", forms, COMPOSITION), (0, expected), forms)
        for bad in ("", "lean,", "latin", "lean,,mathematics", "Lean"):
            status, out, err = run("print", "--statement", bad, COMPOSITION)
            self.assertEqual((status, out.startswith("error:")), (4, True), bad)
        status, out, err = run("check", "--statement", "lean", COMPOSITION)
        self.assertEqual((status, out.startswith("error: an option this command does not take")),
                         (4, True))

    def test_0_beyond_the_small_reader(self):
        """print holds what check holds (the stage and the feed, plan task 3.4.1), not the
        64 names and 32 declarations of the first reader: chain.ndjson has 81 expressions,
        inductive.ndjson has inductive types. Each declaration check reports has its
        header, and the status is check's; chain's line is read from the stage."""
        for path in ("tests/cli/chain.ndjson", "tests/cli/inductive.ndjson",
                     "tests/cli/unfold.ndjson"):
            check_status, check_out, _ = run("check", path)
            status, out = self.lines(path)
            self.assertEqual(status, check_status, path)
            names = [l.split(": ")[0] for l in check_out.splitlines()
                     if re.match(r"^\S+: (accepted|rejected|unknown|unsupported)", l)]
            self.assertTrue(names, path)
            heads = {l.split(" ", 1)[1] for l in out if re.match(
                r"^(Theorem|Definition|Axiom|Opaque|Declaration) ", l)}
            # An inductive block's later members are published with its first and
            # printed once, under it.
            members = {"Two.first", "Two.second", "Two.rec"} if "inductive" in path else set()
            self.assertEqual(sorted(set(names) - members), sorted(heads), path)
        status, out = self.lines("tests/cli/chain.ndjson")
        self.assertIn("  Input:     tests/cli/chain.ndjson line 114", out)
        self.assertIn("      L M -> explicit: f12", out)
        self.assertEqual(out[-1], "Templates: let-props/v0, assume/v0, implies-elim/v0, "
                                  "discharge/v0, statement/v0.")

    def test_0_binder_kinds(self):
        """The binder kinds the feed's hook keeps reach the printer: implicit and instance
        binders print in their brackets (declarations that print as types, from an export
        of kinds of declarations; its manifest is not checked)."""
        status, out = self.lines("--no-manifest", "--statement", "lean",
                                 "tests/core/reexport/kinds.ndjson")
        self.assertIn("  Type in Lean:             {α : Type u} → (x : Nat) → [self : OfNat α x] → α",
                      out)
        self.assertIn("  Type in Lean:             {α : Type u_1} → [Add α] → HAdd α α α", out)

    def test_0_latex(self):
        """--latex prints the outlines as the LaTeX fragments of tests/present/
        outlines-latex.golden (plan task 8.6.1); with --detail the steps stay plain."""
        parts = re.split(r"^== (.*)$", LATEX_OUTLINES.read_text(encoding="utf-8"), flags=re.M)
        fragments = dict(zip(parts[1::2], parts[2::2]))
        for name in ("identity", "composition", "constant-fixture"):
            self.assertEqual(self.lines("--latex", f"tests/reference/{name}.ndjson"),
                             (0, fragments[name].strip("\n").splitlines()), name)
        self.assertEqual(self.lines("--latex", "--detail", COMPOSITION),
                         (0, golden("composition --detail")))

    def test_0_named(self):
        fixture = golden("constant-fixture")
        use = fixture[fixture.index("Theorem fixtureUse"):]
        self.assertEqual(self.lines("--name", "fixtureUse", FIXTURE), (0, use))
        poly = fixture[fixture.index("Definition fixturePoly"):fixture.index("Theorem fixtureUse")]
        self.assertEqual(self.lines("--name", "fixturePoly", FIXTURE), (0, poly[:-1]))

    def test_refused(self):
        status, out = self.lines("--no-manifest", f"{CASES}/composition-wrong-argument.ndjson")
        self.assertEqual((status, out), (1, [NO_MANIFEST, *golden("composition-wrong-argument")]))
        status, out = self.lines("--no-manifest", UNKNOWN)
        self.assertEqual(status, 2)
        self.assertEqual(out[out.index("Declaration IE.W"):][1], "  unknown")
        self.assertEqual(out[-1], REFUSED)
        status, out = self.lines("--fuel", "0", FIXTURE)
        self.assertEqual((status, out.count(REFUSED), out.count("  exhausted")), (3, 3, 3))
        status, out = self.lines("--no-manifest", f"{CASES}/composition-postulate.ndjson")
        self.assertEqual((status, out[1:3], out[-1]),
                         (0, ["Axiom composition", f"  accepted; axioms: unlisted"],
                          "No proof outline: an axiom or a quotient constant has no proof;"
                          " Lean's kernel takes it as given."))
        for args, code in [((FIXTURE,), 0), (("--no-manifest", UNKNOWN), 2),
                           (("--fuel", "0", FIXTURE), 3),
                           (("--no-manifest", f"{CASES}/composition-wrong-argument.ndjson"), 1)]:
            status, out = self.lines(*args)
            self.assertEqual(status, code, args)
            # Each verdict, the line after a declaration's title, is accepted
            # with its axioms or a failure; an outline appears only below an
            # accepted one.
            titles = [i for i, line in enumerate(out)
                      if re.match(r"(Theorem|Definition|Axiom|Opaque|Declaration) ", line)]
            verdicts = [out[i + 1] for i in titles]
            self.assertTrue(all(v == f"  {LABEL}" or "accepted" not in v for v in verdicts),
                            verdicts)
            shown = sum(line.startswith(("Proof (", "Construction (", "No outline template"))
                        for line in out)
            self.assertEqual(shown, out.count(f"  {LABEL}"), args)

    def test_4_mistakes(self):
        self.assertEqual(self.lines("--name", "noSuch", FIXTURE),
                         (4, ["error: no declaration named noSuch"]))
        self.assertEqual(self.lines("tests/cli/no-such.ndjson"),
                         (4, ["error: cannot open the export"]))
        hint = "try: leanforth help"
        for args, error in [
            ([], "error: a wrong number of file names"),
            ([FIXTURE, "--name"], "error: an option without its value: --name"),
            (["--record", "r.json", FIXTURE], "error: an option this command does not take: "
                                              "--record"),
        ]:
            self.assertEqual(self.lines(*args), (4, [error, hint]), args)
        status, out, _ = run("check", "--detail", COMPOSITION)
        self.assertEqual((status, out.splitlines()),
                         (4, ["error: an option this command does not take: --detail", hint]))


def git_source():
    """The commit and modified flag bin/leanforth records, or (None, None)."""
    head = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"], capture_output=True,
                          text=True)
    if head.returncode != 0:
        return None, None
    same = subprocess.run(["git", "-C", str(ROOT), "diff", "--quiet", "HEAD"]).returncode == 0
    return head.stdout.strip(), not same


class RunRecords(unittest.TestCase):
    """check --record writes the run record of tests/support/run-records.fs's
    run (src/import/run-record.fs), with the manifest checked and the commit
    named; replay checks again and confirms it, or refuses a changed one."""

    def record(self, folder, export, *options):
        path = Path(folder) / "run.json"
        status, out, err = run("check", *options, "--record", str(path), export)
        return status, out, json.loads(path.read_text())

    def test_record_as_the_driver(self):
        schema = Validator(json.loads((ROOT / "schemas/run-record-0.3.schema.json").read_text()))
        commit, modified = git_source()
        for name in ["composition", "constant-fixture", "identity"]:
            with tempfile.TemporaryDirectory() as folder:
                status, out, got = self.record(folder, f"tests/reference/{name}.ndjson")
            self.assertEqual(status, 0, out)
            self.assertEqual(schema.errors(got), [], name)
            self.assertEqual(got["leanforth"], {"commit": commit, "modified": modified})
            golden = json.loads((ROOT / f"tests/core/run-records/{name}.json").read_text())
            # The command line enforces the manifest; the driver that wrote
            # the golden records does not, and each record says so.
            self.assertEqual((got["input"]["manifest"]["enforced"],
                              golden["input"]["manifest"]["enforced"]), (True, False))
            golden["input"]["manifest"]["enforced"] = True
            # The command line's default fuel is 100,000,000 (since
            # 2026-11-11, agent PF); the driver that wrote the golden records
            # gives 100,000. Fuel used is the same either way.
            self.assertEqual((got["settings"]["fuel"], golden["settings"]["fuel"]),
                             (100000000, 100000))
            golden["settings"]["fuel"] = 100000000
            for section in ["input", "export", "settings", "check", "declarations"]:
                self.assertEqual(got[section], golden[section], f"{name} {section}")

    def test_replay(self):
        with tempfile.TemporaryDirectory() as folder:
            wrong = f"{CASES}/composition-wrong-argument.ndjson"
            status, _, record = self.record(folder, wrong, "--no-manifest")
            self.assertEqual((status, record["declarations"][0]["verdict"]), (1, "rejected"))
            self.assertIs(record["input"]["manifest"]["enforced"], False)   # --no-manifest
            path = str(Path(folder) / "run.json")
            confirmed = '{"schema":"leanforth-replay-report","schemaVersion":"0.1",' \
                        '"result":"confirmed","findings":[],"findingsTotal":0}\n'
            self.assertEqual(run("replay", "--no-manifest", wrong, path), (0, confirmed, ""))
            record["declarations"][0]["verdict"] = "accepted"
            Path(path).write_text(json.dumps(record))
            status, out, _ = run("replay", "--no-manifest", wrong, path)
            report = json.loads(out)
            self.assertEqual((status, report["result"], report["findings"][0]["code"]),
                             (1, "refused", "accepted-not-established"))
            status, out, _ = run("replay", wrong, path)     # read without the manifest before
            self.assertEqual((status, json.loads(out)["result"]), (1, "refused"))
            status, out, _ = run("replay", COMPOSITION, str(Path(folder) / "missing.json"))
            self.assertEqual((status, json.loads(out)["findings"][0]["code"]), (4, "unreadable"))
            self.assertEqual(run("replay", COMPOSITION)[0], 4)


class Behaviour(unittest.TestCase):
    def test_accepted_only_from_slots(self):
        """Every "accepted" is a declaration's line with its axioms, or a
        summary line that counts them; no line carries a label."""
        for args in [["check", COMPOSITION], ["check", "tests/cli/unfold.ndjson"],
                     ["check", "--no-manifest", f"{CASES}/composition-wrong-argument.ndjson"],
                     ["check", INDUCTIVE]]:
            _, out, _ = run(*args)
            for line in out.splitlines():
                if "accepted" in line and not re.match(r"^\d+ declarations?: ", line):
                    self.assertRegex(line, r"^(\S+: " + re.escape(LABEL) + r"|accepted: \d+; "
                                     r"axioms: none)$")

    def test_any_folder_and_deterministic(self):
        first = run("check", COMPOSITION)
        self.assertEqual(run("check", COMPOSITION), first)
        self.assertEqual(run("check", "reference/composition.ndjson", cwd=ROOT / "tests"), first)
        with tempfile.TemporaryDirectory() as folder:
            self.assertEqual(run("check", str(ROOT / COMPOSITION), cwd=folder), first)
            link = Path(folder) / "leanforth"
            link.symlink_to(TOOL)
            self.assertEqual(run("check", str(ROOT / COMPOSITION), cwd=folder, tool=link), first)

    def test_count_as_the_counter(self):
        for export in sorted((ROOT / "tests" / "reference").glob("*.ndjson")):
            name = str(export.relative_to(ROOT))
            counter = subprocess.run(
                [GFORTH, "src/import/ndjson-count.fs", "-e", f's" {name}" count-export bye'],
                cwd=ROOT, stdin=subprocess.DEVNULL, capture_output=True, timeout=TEST_LIMIT)
            self.assertEqual(run("count", name)[:2], (0, counter.stdout.decode()), name)

    def test_reexport_identical(self):
        with tempfile.TemporaryDirectory() as folder:
            for export in sorted((ROOT / "tests" / "reference").glob("*.ndjson")):
                copy = Path(folder) / export.name
                status, out, _ = run("reexport", str(export), str(copy))
                lines = len(export.read_bytes().splitlines())
                self.assertEqual((status, out), (0, f"reexported {lines} lines\n"))
                self.assertEqual(copy.read_bytes(), export.read_bytes())
            copy = Path(folder) / "kinds.ndjson"
            kinds = ROOT / "tests" / "core" / "reexport" / "kinds.ndjson"
            self.assertEqual(run("reexport", str(kinds), str(copy))[0], 4)   # no manifest
            status, _, _ = run("reexport", "--no-manifest", str(kinds), str(copy))
            self.assertEqual((status, copy.read_bytes()), (0, kinds.read_bytes()))

    def capabilities_match_facts(self, out):
        """The capabilities text states what is true: nested inductive types are
        accepted (checked here), so they are not listed as unsupported; the
        Mathlib line gives the count and build PROJECT_PROGRESS.md records and
        does not say that nothing was checked."""
        lacks = out.split("not yet supported")[1].split("limits (")[0]
        self.assertNotIn("nested", lacks)
        self.assertEqual(run("check", "tests/cli/nested.ndjson")[0], 0)
        self.assertNotIn("0 of 729,263", out)
        progress = (ROOT / "docs/project/PROJECT_PROGRESS.md").read_text()
        self.assertRegex(progress, r"729,263 of\s+729,263 accepted\*\* on build `b74a04d`")
        mathlib = out.split("Mathlib: ")[1].split("not re-run since")[0]
        for fact in ("all 729,263 declarations of its Lean export accepted", "b74a04d",
                     "fuel 250M", "--memory-per-check 8192", "--no-manifest"):
            self.assertIn(fact, mathlib)

    def test_informational(self):
        status, out, _ = run("version")
        self.assertEqual(status, 0)
        self.assertRegex(out, r"^leanforth 0\.1\.0-dev\nforth: Gforth \S+\nreads: "
                              r"lean4export 3\.1\.0, format 3\.1\.0, Lean 4\.35\.0 "
                              r"\(eb6cafb7290e8bd5f2937522d8d804f58f02bafc\)\ncommit: ")
        self.assertEqual(run("--version")[:2], (0, out))
        status, out, _ = run("capabilities")
        self.assertEqual(status, 0)
        self.assertIn("  check --record, replay: 64 names, 64 levels, 64 term nodes,\n"
                      "    32 declarations per export\n", out)
        self.assertIn(TEXT_CAPABILITY, out.split("not yet supported")[0])
        self.capabilities_match_facts(out)
        status, out, _ = run("help")
        self.assertEqual((status, run("--help")[1], run("-h")[1]), (0, out, out))


class Tampered(unittest.TestCase):
    """An export changed after it was made is never accepted: with its
    manifest it is refused before anything is checked (invalid, 4); without
    it, a change that breaks the file is invalid too, and one that keeps it
    well formed gets the verdict of what it now says."""

    def copies(self, folder, source, change):
        """source and its manifest copied into folder, the copy changed."""
        text = (ROOT / source).read_text()
        export = Path(folder) / Path(source).name
        export.write_text(change(text))
        manifest = ROOT / f"{source}.manifest.json"
        Path(f"{export}.manifest.json").write_text(manifest.read_text())
        return str(export)

    def refused(self, export, code, error):
        """With the manifest: invalid (the reader's own refusal, or the
        manifest's SHA-256 at the end of the read). Without it: code, and
        error as the line after the note."""
        for options in [[], ["--no-manifest"]]:
            status, out, err = run("check", *options, export)
            self.assertNotIn(LABEL, out, (options, export))
            if not options:
                self.assertEqual((status, out.splitlines()[0][:16]), (4, "error: invalid: "),
                                 export)
            else:
                self.assertEqual((status, out.splitlines()[1:2]), (code, error), export)

    def test_tampered(self):
        with tempfile.TemporaryDirectory() as folder:
            # The proof replaced by the statement: rejected without the manifest.
            proof = self.copies(folder, COMPOSITION,
                                lambda t: t.replace('"value":20', '"value":10'))
            self.refused(proof, 1, ["composition: rejected"])
            self.assertEqual(run("check", proof)[1].splitlines()[0],
                             "error: invalid: export differs from its manifest "
                             "(field sha256, line 0)")
            # A reference to an expression that does not exist.
            dangling = self.copies(folder, COMPOSITION,
                                   lambda t: t.replace('"arg":12,"fn":1}', '"arg":12,"fn":99}'))
            self.refused(dangling, 4, ["error: invalid: bad reference (field fn, line 27)"])
            # Cut inside its last line; and the fixture cut after its
            # second-last line, a shorter library that reads well: only its
            # manifest tells (without it, its two declarations are accepted).
            cut = self.copies(folder, COMPOSITION, lambda t: t[:-5])
            self.refused(cut, 4,
                         ["error: invalid: missing final line feed, or a read error (line 35)"])
            shorter = self.copies(folder, FIXTURE,
                                  lambda t: t[:t.rstrip("\n").rindex("\n") + 1])
            status, out, _ = run("check", shorter)
            self.assertEqual((status, out.split(" (")[0]),
                             (4, "error: invalid: export differs from its manifest"))
            self.assertEqual(run("check", "--no-manifest", shorter)[0], 0)
            # Another Lean version than the pinned one: unsupported, 2.
            other = self.copies(folder, COMPOSITION,
                                lambda t: t.replace('"version":"4.35.0"', '"version":"4.36.0"'))
            status, out, _ = run("check", "--no-manifest", other)
            self.assertEqual((status, out.splitlines()[1][:20]), (2, "error: unsupported: "))
            # A constant no declaration has: the stage refuses it at sealing.
            lines = (ROOT / FIXTURE).read_text().splitlines(keepends=True)
            unknown = Path(folder) / "unknown.ndjson"
            unknown.write_text("".join(line for line in lines if '"def":{"all":[1]' not in line))
            self.assertEqual(run("check", "--no-manifest", str(unknown)),
                             (4, f"{NO_MANIFEST}\nerror: invalid: unknown constant (line 0)\n",
                                 ""))


def report(*args):
    """The exit status and the JSON report of check --json."""
    status, out, err = run("check", "--json", *args)
    return status, json.loads(out), err


# The label reports and records carried until the owner withdrew it
# (2026-11-12): reports 0.2 and 0.3 and run records 0.2 require it.
OLD_LABEL = "experimental, not independently audited"


def as_labelled(got, version):
    """A copy of report or record got as the version before the withdrawal
    had it: that version, the label at the top (reports only) and on each
    accepted declaration."""
    back = json.loads(json.dumps(got))
    back["schemaVersion"] = version
    if back.get("schema") == "leanforth-check-report":
        back["label"] = OLD_LABEL
    for d in back["declarations"]:
        if d["verdict"] == "accepted":
            d["label"] = OLD_LABEL
    return back


def as_0_2(got):
    """A report 0.4 as report 0.2 had it."""
    return as_labelled(got, "0.2")


def as_0_1(got):
    """A report 0.4 as report 0.1 had it: no skipped count either."""
    back = as_labelled(got, "0.1")
    if back["counts"] is not None:
        del back["counts"]["skipped"]
    return back


# What no output may say since the owner withdrew the label (2026-11-12).
LABEL_WORDS = ("experimental", "independently audited", "pre-alpha")


def keys(value):
    """Every member name of a JSON value, at any depth."""
    if isinstance(value, dict):
        return set(value) | {k for v in value.values() for k in keys(v)}
    if isinstance(value, list):
        return {k for v in value for k in keys(v)}
    return set()


class NoLabel(unittest.TestCase):
    """No output carries the withdrawn label (owner, 2026-11-12): not check's
    text, its JSON report (no label member at any depth), print's outlines
    (text and LaTeX), a snapshot run's text, version, capabilities or help;
    an accepted declaration that depends on an axiom outside the allowlist
    is still NOT PROVED, here one named sorryAx as Lean's sorry is."""

    def clean(self, text, where):
        for word in LABEL_WORDS:
            self.assertNotIn(word, text, where)

    def test_text_json_and_print(self):
        for args in CASES_ALL:
            status, out, err = run("check", *args)
            self.clean(out + err, args)
            status, got, err = report(*args)
            self.assertNotIn("label", keys(got), args)
            self.clean(json.dumps(got) + err, args)
        for args in ([FIXTURE], ["--detail", COMPOSITION], ["--latex", FIXTURE],
                     ["--no-manifest", f"{CASES}/composition-postulate.ndjson"]):
            status, out, err = run("print", *args)
            self.assertEqual(status, 0, args)
            self.clean(out + err, args)
            self.assertIn("  accepted; axioms: ", out, args)
        for command in ("version", "capabilities", "help"):
            status, out, err = run(command)
            self.assertEqual(status, 0, command)
            self.clean(out + err, command)

    def test_snapshot_text(self):
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "s.lfsnap"
            self.assertEqual(run("check", "--save-snapshot", str(path), FIXTURE)[0], 0)
            status, out, err = run("check", "--snapshot", str(path))
            self.assertEqual(status, 0)
            self.clean(out + err, "snapshot")
            status, got, err = report("--snapshot", str(path))
            self.assertNotIn("label", keys(got))

    def test_sorry_not_proved(self):
        source = ROOT / CASES / "composition-postulate.ndjson"
        text = source.read_text(encoding="utf-8")
        old = '{"pre":0,"str":"composition"}'
        self.assertEqual(text.count(old), 1)
        with tempfile.TemporaryDirectory() as folder:
            export = Path(folder) / "sorry.ndjson"
            export.write_text(text.replace(old, '{"pre":0,"str":"sorryAx"}'), encoding="utf-8")
            status, out, _ = run("check", "--no-manifest", str(export))
            self.assertEqual((status, out.splitlines()[1:]),
                             (0, ["sorryAx: accepted; axioms: unlisted; NOT PROVED: depends on "
                                  "sorryAx", "1 declaration: 1 accepted",
                                  "accepted: 1; axioms: 1 NOT PROVED (they depend on an axiom)",
                                  "note: NOT PROVED declarations keep Lean's exit status; "
                                  "--strict-axioms", "note: makes it 6"]))
            self.assertEqual(run("check", "--no-manifest", "--strict-axioms", str(export))[0], 6)
            status, got, _ = report("--no-manifest", str(export))
            d = got["declarations"][0]
            self.assertEqual((status, d["verdict"], d["notProved"], d["notProvedBy"],
                              "label" in keys(got)), (0, "accepted", True, ["sorryAx"], False))
            status, out, _ = run("print", "--no-manifest", str(export))
            self.assertEqual((status, out.splitlines()[1:3]),
                             (0, ["Axiom sorryAx", "  accepted; axioms: unlisted"]))


CASES_ALL = [
    [COMPOSITION], [FIXTURE], [CHAIN], [INDUCTIVE], ["tests/cli/unfold.ndjson"],
    [f"{CASES}/composition-wrong-argument.ndjson"],
    ["--no-manifest", f"{CASES}/composition-wrong-argument.ndjson"],
    ["--no-manifest", f"{CASES}/composition-postulate.ndjson"],
    ["--no-manifest", f"{CASES}/composition-loose.ndjson"],
    ["--no-manifest", f"{CASES}/composition-unsafe.ndjson"],
    ["--no-manifest", "README.md"], ["tests/cli/no-such.ndjson"],
    ["--no-manifest", "tests/cli/composition-huge-number.ndjson"],
    ["--no-manifest", "tests/core/reexport/kinds.ndjson"], ["--fuel", "0", FIXTURE],
    ["--no-manifest", EMPTY_BLOCK],
]


class JsonReport(unittest.TestCase):
    """check --json (plan task 3.4.3): one report the schema accepts, which
    says what the text says, the same on every run but for "measured"."""

    schema = Validator(json.loads((ROOT / "schemas/check-report-0.4.schema.json").read_text()))
    VERDICTS = {"accepted": "accepted", "skipped": "skipped", "rejected": "rejected",
                "unknown": "unknown",
                "unsupported": "unsupported", "invalid": "invalid", "exhausted": "exhausted",
                "full": "full", "notChecked": "not-checked"}

    def sums(self, got, args):
        """The rules the schema cannot state (its $comment): the counts, the
        fuel and the most fuel used agree with the declarations."""
        decls, counts, fuel = got["declarations"], got["counts"], got["fuel"]
        if counts is not None:
            self.assertEqual(counts["declarations"], len(decls), args)
            self.assertEqual(counts["declarations"],
                             sum(counts[key] for key in self.VERDICTS), args)
            for key, verdict in self.VERDICTS.items():
                self.assertEqual(counts[key], sum(d["verdict"] == verdict for d in decls),
                                 (args, key))
            self.assertEqual(counts["notProved"], sum(d.get("notProved", False) for d in decls),
                             args)
            if got["input"] is not None:
                self.assertEqual(got["input"]["declarations"], counts["declarations"], args)
        self.assertEqual([d["index"] for d in decls], list(range(len(decls))), args)
        known = [d["fuel"] for d in decls if d["fuel"] is not None]
        self.assertEqual((fuel["unknown"], fuel["total"]),
                         (len(decls) - len(known), sum(known)), args)
        tops = [t["fuel"] for t in fuel["top"]]
        self.assertEqual(tops, sorted(tops, reverse=True), args)
        for top in fuel["top"]:
            d = decls[top["index"]]
            self.assertEqual((top["name"], top["fuel"], top["verdict"]),
                             (d["name"], d["fuel"], d["verdict"]), args)

    def test_valid_and_as_the_text(self):
        for args in CASES_ALL:
            status, got, err = report(*args)
            self.assertEqual((self.schema.errors(got), err), ([], ""), args)
            self.sums(got, args)
            text_status, text, _ = run("check", *args)
            self.assertEqual((status, got["exitStatus"]), (text_status, text_status), args)
            self.assertEqual(got["stopped"], "internal fault: the run stopped" in text, args)
            # Each declaration's line, in order, says the report's verdict.
            # An accepted one's line names its axioms and, when NOT PROVED,
            # says so (plan task 5.3.1).
            words = {"accepted": "accepted; axioms: ",
                     "not-checked": "not checked (not reached: the run stopped)"}
            lines = text.splitlines()
            at = 0
            for d in got["declarations"]:
                line = f"{d['name']}: {words.get(d['verdict'], d['verdict'])}"
                accepted_one = d["verdict"] == "accepted"
                found = [k for k in range(at, len(lines))
                         if lines[k] == line or (accepted_one and lines[k].startswith(line))]
                self.assertTrue(found, (line, args))
                at = found[0] + 1
                self.assertEqual("; NOT PROVED: depends on " in lines[at - 1],
                                 bool(d.get("notProved")), args)
            shown = [line for line in lines if re.match(r"^\d+ declarations?: ", line)]
            counts = got["counts"]
            self.assertEqual(len(shown), int(counts is not None), args)
            if counts is not None:
                words = {"accepted": "accepted", "skipped": "skipped", "rejected": "rejected",
                         "unknown": "unknown",
                         "unsupported": "unsupported", "invalid": "invalid",
                         "exhausted": "exhausted", "full": "full", "notChecked": "not checked"}
                summary = ", ".join(f"{counts[k]} {w}" for k, w in words.items() if counts[k])
                plural = "" if counts["declarations"] == 1 else "s"
                self.assertEqual(shown[0], f"{counts['declarations']} declaration{plural}: "
                                           f"{summary}", args)

    def test_versions_kept(self):
        """Reports are version 0.4 since the label was withdrawn (owner,
        2026-11-12), 0.2 having been the first with the verdict skipped (plan
        task 5.2.7; review rvUNNI M2); schemas 0.1 and 0.2 are kept unchanged
        for earlier reports. A report set back to 0.2 (its version, and the
        label at the top and on each accepted declaration) is valid under
        0.2, so the label is all that changed; without a skipped declaration,
        set back to 0.1 (no skipped count either), it is valid under 0.1; one
        with a skipped declaration is not, nor is any 0.4 report as written
        valid under either."""
        old = Validator(json.loads((ROOT / "schemas/check-report-0.1.schema.json").read_text()))
        v02 = Validator(json.loads((ROOT / "schemas/check-report-0.2.schema.json").read_text()))
        _, plain, _ = report(INDUCTIVE)
        _, skipped, _ = report("--no-manifest", f"{CASES}/composition-unsafe.ndjson")
        _, postulate, _ = report("--no-manifest", f"{CASES}/composition-postulate.ndjson")
        self.assertEqual((plain["schemaVersion"], v02.errors(as_0_2(plain)),
                          v02.errors(as_0_2(skipped)), v02.errors(as_0_2(postulate))),
                         ("0.4", [], [], []))
        self.assertEqual(old.errors(as_0_1(plain)), [])
        self.assertNotEqual(old.errors(as_0_1(skipped)), [])
        self.assertNotEqual(old.errors(plain), [])
        self.assertNotEqual(v02.errors(plain), [])

    def test_schema_refuses(self):
        """The schema refuses a report whose parts disagree."""
        _, good, _ = report(INDUCTIVE)
        _, unread, _ = report("--no-manifest", "README.md")

        def changed(base, edit):
            copy = json.loads(json.dumps(base))
            edit(copy)
            return self.schema.errors(copy)

        def not_proved(r, strict=True):
            """Declaration 0 NOT PROVED and counted; under --strict-axioms
            the status 6, else Lean's 0."""
            r["declarations"][0].update(axiomBits=8, notProved=True, notProvedBy=["sorryAx"])
            r["counts"].update(notProved=1)
            r["settings"].update(strictAxioms=strict)
            r.update(exitStatus=6 if strict else 0)

        def rejected(r, status):
            """Declaration 5 rejected, counted, and the status given."""
            d = r["declarations"][5]
            for key in ("axiomBits", "notProved", "notProvedBy"):
                d.pop(key, None)
            d.update(verdict="rejected", diagnostic=None)
            r["counts"].update(accepted=5, rejected=1)
            r.update(exitStatus=status)
        cases = [
            (good, lambda r: r["declarations"][4].update(verdict="rejected")),   # status 0
            (good, lambda r: r["declarations"][0].update(axiomBits=8)),          # notProved false
            (good, lambda r: r["declarations"][0].update(label="experimental, not independently audited")),
            (good, lambda r: r.update(label="experimental, not independently audited")),
            (good, lambda r: r["declarations"][1].update(diagnostic=None)),      # accepted
            (good, lambda r: r.update(run="not-run")),                           # read ok
            (good, lambda r: r["fuel"]["top"].append(r["fuel"]["top"][0]) or
             r["fuel"]["top"].extend(r["fuel"]["top"] * 5)),                    # more than 10
            (good, lambda r: r.update(extra=1)),
            (good, lambda r: r.update(stopped=True)),                            # status 0
            (good, lambda r: r["declarations"][4].update(verdict="not-checked")),  # run ok
            (unread, lambda r: r.update(counts=good["counts"])),                 # not read
            (unread, lambda r: r["read"].update(phase=None)),                    # failed read
            # Status 0 only with every count but the accepted 0, at least one
            # declaration, every fuel known, and a run that did not stop.
            (good, lambda r: r["counts"].update(rejected=1)),
            (good, lambda r: r["counts"].update(notChecked=1)),
            (good, lambda r: r["fuel"].update(unknown=1)),
            (good, lambda r: r.update(declarations=[])),
            (good, lambda r: r["counts"].update(declarations=0, accepted=0)),
            (good, lambda r: r.update(counts=None)),
            # A run that stopped did not end ok; status 6 needs
            # --strict-axioms and a NOT PROVED declaration, all accepted;
            # under --strict-axioms a NOT PROVED one never leaves status 0;
            # there is no status 7; settings say whether it is strict.
            (good, lambda r: r.update(stopped=True, exitStatus=5)),
            (good, lambda r: r.update(exitStatus=6)),
            (good, lambda r: r.update(exitStatus=7)),
            (good, lambda r: not_proved(r) or r.update(exitStatus=0)),
            (good, lambda r: not_proved(r, strict=False) or r.update(exitStatus=6)),
            (good, lambda r: not_proved(r) or rejected(r, 6)),
            (good, lambda r: r["settings"].pop("strictAxioms")),
            (good, lambda r: r["measured"].pop("engine")),
            (good, lambda r: r["measured"].update(engine="")),
        ]
        for base, edit in cases:
            self.assertNotEqual(changed(base, edit), [], cases.index((base, edit)))
        self.assertEqual(changed(good, lambda r: None), [])
        # Planted reports, since no check can make a NOT PROVED declaration
        # yet: status 6 under --strict-axioms, Lean's 0 without it, and a
        # rejected declaration beside a NOT PROVED one (1 outranks 6), all
        # accepted; so is a report whose engine is not known.
        self.assertEqual(changed(good, not_proved), [])
        self.assertEqual(changed(good, lambda r: not_proved(r, strict=False)), [])
        self.assertEqual(changed(good, lambda r: not_proved(r) or rejected(r, 1)), [])
        self.assertEqual(changed(good, lambda r: r["measured"].update(engine=None)), [])

    def test_deterministic(self):
        for args in [[INDUCTIVE], ["--no-manifest", "tests/core/reexport/kinds.ndjson"]]:
            first, second = report(*args)[1], report(*args)[1]
            for got in (first, second):
                self.assertIsInstance(got.pop("measured")["peakResidentBytes"], (int, type(None)))
            self.assertEqual(first, second, args)

    def test_strict_axioms(self):
        """settings records --strict-axioms; with no NOT PROVED declaration
        (inductive.ndjson uses no axiom) it changes nothing else."""
        status, got, _ = report(INDUCTIVE)
        strict_status, strict, _ = report("--strict-axioms", INDUCTIVE)
        self.assertEqual((got["settings"]["strictAxioms"], strict["settings"]["strictAxioms"],
                          self.schema.errors(strict)), (False, True, []))
        for one in (got, strict):
            one.pop("measured")
            one["settings"].pop("strictAxioms")
        self.assertEqual((strict_status, strict), (status, got))
        self.assertEqual(run("check", "--strict-axioms", INDUCTIVE), run("check", INDUCTIVE))

    def test_contents(self):
        status, got, _ = report(INDUCTIVE)
        self.assertEqual((status, got["run"], got["read"]["outcome"], got["manifest"]),
                         (0, "ok", "ok", "checked"))
        self.assertEqual([d["fuel"] > 0 for d in got["declarations"]],
                         [True, False, False, False, True, True])   # the block's is Two's
        self.assertEqual((got["fuel"]["total"], got["fuel"]["unknown"]),
                         (sum(d["fuel"] for d in got["declarations"]), 0))
        self.assertEqual([t["name"] for t in got["fuel"]["top"]],
                         ["Two.cases", "Two.swap", "Two"])
        self.assertEqual((got["input"]["declarations"], got["stopped"]), (6, False))
        # Fuel not known: a check that failed in inference gave its counter
        # up; it is in no total and never among the most fuel used.
        _, got, _ = report("--no-manifest", "tests/core/reexport/kinds.ndjson")
        unknown = [d for d in got["declarations"] if d["fuel"] is None]
        self.assertEqual(len(unknown), got["fuel"]["unknown"])
        self.assertTrue(unknown and all(d["verdict"] not in ("accepted", "exhausted")
                                        for d in unknown))
        self.assertEqual(got["fuel"]["total"],
                         sum(d["fuel"] for d in got["declarations"] if d["fuel"] is not None))
        fuels = [t["fuel"] for t in got["fuel"]["top"]]
        self.assertEqual(fuels, sorted(fuels, reverse=True))
        self.assertEqual(fuels[0], max(d["fuel"] or 0 for d in got["declarations"]))
        status, got, _ = report("--no-manifest", "README.md")
        self.assertEqual((status, got["read"]["phase"], got["read"]["line"], got["run"]),
                         (4, "stage", 1, "not-run"))
        status, got, _ = report("tests/cli/no-such.ndjson")
        self.assertEqual((status, got["read"]["phase"], got["input"]), (4, "open", None))


class Names(unittest.TestCase):
    """Names as Lean's Name.toString shows them (src/cli/name-text.fs), in
    the text and the JSON report alike: a component that is not an
    identifier between « and », and every character the text rule bans
    escaped, so that no name can start a line of its own or reorder the
    text after it; names of any depth. composition's theorem renamed, its
    proof unchanged, so every case is accepted."""

    def renamed(self, folder, records):
        """composition with its theorem's name made of records, name
        records ("str" or "num" and "pre") given ids after its own 12, the
        last the theorem's name."""
        lines = (ROOT / COMPOSITION).read_text().splitlines()
        names = [json.dumps({"in": 13 + i, **record}, ensure_ascii=False)
                 for i, record in enumerate(records)]
        last = 12 + len(records)
        thm = lines[-1].replace('"all":[1]', f'"all":[{last}]').replace('"name":1,', f'"name":{last},')
        path = Path(folder) / "renamed.ndjson"
        path.write_text("\n".join(lines[:-1] + names + [thm]) + "\n")
        return str(path)

    def shown(self, records, shown):
        with tempfile.TemporaryDirectory() as folder:
            export = self.renamed(folder, records)
            status, out, err = run("check", "--no-manifest", export)
            self.assertEqual((status, out.splitlines(), err),
                             (0, [NO_MANIFEST, f"{shown}: {LABEL}", "1 declaration: 1 accepted",
                                  accepted(1)], ""), shown)
            status, got, err = report("--no-manifest", export)
            self.assertEqual((status, got["declarations"][0]["name"], err,
                              JsonReport.schema.errors(got)), (0, shown, "", []), shown)

    def test_escaped(self):
        forged = f"composition: rejected\nforged: {LABEL}\nx"
        for text, shown in [
            ("composition", "composition"),
            (forged, "«composition: rejected\\u{A}forged: " + LABEL + "\\u{A}x»"),
            ("a\r\x1b[2Kb", "«a\\u{D}\\u{1B}[2Kb»"),
            ("ab‮cd⁦", "«ab\\u{202E}cd\\u{2066}»"),     # bidirectional controls
            ("a\x00b\x85c ", "«a\\u{0}b\\u{85}c\\u{2028}»"),  # NUL, C1, line separator
            ("a\\u{A}", "«a\\\\u{A}»"),                            # a backslash, not an escape
            ("with space", "«with space»"),
            ("", "«»"),
            ("αβ₁", "αβ₁"),                                         # an identifier as it is
            ("x₊", "«x₊»"),                                         # a subscript sign
            # Lean shows these without « »: here the component is always
            # between « », a » in it escaped, so no line starts "fake: ".
            (f"fake: {LABEL}\n» x", "«fake: " + LABEL + "\\u{A}\\u{BB} x»"),
            (f"fake: {LABEL}✝", f"«fake: {LABEL}✝»"),         # inaccessible
            ("#fake: x", "«#fake: x»"),                            # pseudo-syntax
        ]:
            self.shown([{"str": {"pre": 0, "str": text}}], shown)
        # Macro scopes: Lean shows fake: x._@._hyg bare.
        self.shown([{"str": {"pre": 0, "str": f"fake: {LABEL}"}},
                    {"str": {"pre": 13, "str": "_@"}}, {"str": {"pre": 14, "str": "_hyg"}}],
                   f"«fake: {LABEL}».«_@»._hyg")

    def test_print_escaped(self):
        """print shows every declaration name as check does (name-text.fs): a name
        holding a newline cannot start a line of the outline, in the header, the
        statement or the input line."""
        forged = f"composition: rejected\nforged: {LABEL}\nx"
        shown = "«composition: rejected\\u{A}forged: " + LABEL + "\\u{A}x»"
        with tempfile.TemporaryDirectory() as folder:
            export = self.renamed(folder, [{"str": {"pre": 0, "str": forged}}])
            status, out, err = run("print", "--no-manifest", export)
            lines = out.splitlines()
            self.assertEqual((status, err), (0, ""))
            self.assertIn("Theorem " + shown, lines)
            self.assertFalse([l for l in lines if l.startswith("forged")], lines)
            self.assertEqual(sum(l.startswith("Theorem ") for l in lines), 1)
            # a name no word of LeanForth can spell is not printed as words
            self.assertTrue(any("(not complete:" in l for l in lines))
            status, out, err = run("print", "--no-manifest", "--name", forged, export)
            self.assertEqual((status, err), (0, ""))
            self.assertIn("Theorem " + shown, out.splitlines())
            status, out, err = run("print", "--no-manifest", "--name", "x\ny", export)
            self.assertEqual((status, out.splitlines()[-1], err),
                             (4, "error: no declaration named x\\u{A}y", ""))

    def test_print_crafted_binder_and_constant(self):
        """A binder name and a referenced constant's name holding LF and U+202E (and
        an invalid byte) cannot forge an outline line, reorder text or reach the output
        raw, in every statement form, in --detail and in the LaTeX style (review rvPR B1)."""
        forged = "q\nTheorem forged\n  accepted; axioms: forged‮"
        cases = [("tests/reference/identity.ndjson", '"str":"P"'),
                 ("tests/reference/constant-fixture.ndjson", '"str":"fixtureId"')]
        for forged, (source, old) in [(f, c) for f in (forged, "r\u202es") for c in cases]:
            text = (ROOT / source).read_text(encoding="utf-8")
            self.assertEqual(text.count(old), 1, source)
            crafted = text.replace(old, '"str":' + json.dumps(forged, ensure_ascii=False))
            with tempfile.TemporaryDirectory() as folder:
                export = Path(folder) / "crafted.ndjson"
                export.write_text(crafted, encoding="utf-8")
                for options in ([], ["--detail"], ["--statement", "mathematics"],
                                ["--statement", "leanforth"], ["--statement", "lean"],
                                ["--latex"], ["--latex", "--statement", "mathematics"]):
                    status, out, err = run("print", "--no-manifest", *options, str(export))
                    where = (source, options)
                    self.assertEqual((status, err), (0, ""), where)
                    self.assertNotIn("‮", out, where)
                    lines = out.splitlines()
                    self.assertEqual([l for l in lines if l.startswith(("Theorem forged",
                                                                       "  accepted; axioms: forged",
                                                                       "forged"))], [], where)
                    heads = [l for l in lines if re.match(r"^(\\textbf\{)?(Theorem|Definition)", l)]
                    self.assertEqual(len(heads), 1 if "identity" in source else 3, where)

    def test_print_latex_odd_names(self):
        """LaTeX specials and a long binder name keep the fragment well formed: braces and
        environments balance, and a name of 1,100 bytes is not cut (the line buffer grows)."""
        text = (ROOT / "tests/reference/identity.ndjson").read_text(encoding="utf-8")
        for name in ["a_b#c%d&e{f}g$h^i~j\\k", "x" * 1100, "p\n\nq"]:
            crafted = text.replace('"str":"P"', '"str":' + json.dumps(name))
            with tempfile.TemporaryDirectory() as folder:
                export = Path(folder) / "odd.ndjson"
                export.write_text(crafted, encoding="utf-8")
                status, out, err = run("print", "--no-manifest", "--latex", str(export))
                self.assertEqual((status, err), (0, ""), name[:20])
                plain = re.sub(r"\\[{}$%&#_ ]", "", out)
                self.assertEqual(plain.count("{"), plain.count("}"), name[:20])
                self.assertEqual(out.count("\\begin{"), out.count("\\end{"), name[:20])
                if shutil.which("pdflatex"):
                    tex = Path(folder) / "odd.tex"
                    tex.write_text("\\documentclass{article}\n\\usepackage[utf8]{inputenc}\n"
                                   "\\usepackage{amsmath,amssymb}\n\\begin{document}\n"
                                   + out.split("\n", 1)[1] + "\n\\end{document}\n")
                    run_tex = subprocess.run(["pdflatex", "-no-shell-escape", "-halt-on-error",
                                              "-interaction=nonstopmode", tex.name], cwd=folder,
                                             capture_output=True, text=True,
                                             stdin=subprocess.DEVNULL, timeout=120)
                    self.assertEqual(run_tex.returncode, 0, run_tex.stdout[-800:])
                if len(name) > 1000:
                    self.assertIn("x" * 1100, out)
                    status, plain_out, err = run("print", "--no-manifest", str(export))
                    self.assertIn("x" * 1100, plain_out)

    def test_print_long_names(self):
        """--name picks a declaration by its whole name, however long: no fixed
        buffer (review B-L3: a 256-byte one dropped components, so a long name
        could select the wrong declaration)."""
        long = "a" * 300
        deep = [{"str": {"pre": 12 + i if i else 0, "str": "b" * 100}} for i in range(5)]
        for records, name in [([{"str": {"pre": 0, "str": long}}], long),
                              (deep, ".".join(["b" * 100] * 5))]:
            with tempfile.TemporaryDirectory() as folder:
                export = self.renamed(folder, records)
                status, out, err = run("print", "--no-manifest", "--name", name, export)
                self.assertEqual((status, err), (0, ""), name[:20])
                self.assertIn(f"Theorem {name}", out.splitlines())
                # the first 256 characters, or all but the last component, name nothing
                for wrong in (name[:256], name[:-1], name[1:]):
                    status, out, err = run("print", "--no-manifest", "--name", wrong, export)
                    self.assertEqual(status, 4, wrong[:20])

    def test_components(self):
        # A numeric component in decimal, an empty one as «», and a name
        # deeper than any fixed limit: 100 components.
        self.shown([{"str": {"pre": 0, "str": "a"}}, {"num": {"pre": 13, "i": 7}},
                    {"str": {"pre": 14, "str": ""}}], "a.7.«»")
        deep = [{"str": {"pre": 12 + i if i else 0, "str": f"a{i}"}} for i in range(100)]
        self.shown(deep, ".".join(f"a{i}" for i in range(100)))

    def test_export_name(self):
        """The export's file name in the report: the same escapes, without
        « »; the check is unchanged."""
        with tempfile.TemporaryDirectory() as folder:
            export = Path(folder) / "caf\udcff\n.ndjson"
            export.write_bytes((ROOT / COMPOSITION).read_bytes())
            status, got, err = report("--no-manifest", str(export))
            self.assertEqual((status, got["export"], err, JsonReport.schema.errors(got)),
                             (0, f"{folder}/caf\\x{{FF}}\\u{{A}}.ndjson", "", []))


class Resources(unittest.TestCase):
    """check --resources (plan task 6.5.2, the command line's part)."""

    def test_report(self):
        status, out, err = run("check", "--resources", INDUCTIVE)
        lines = out.splitlines()
        self.assertEqual((status, err, lines[:9]),
                         (0, "", run("check", INDUCTIVE)[1].splitlines() + ["resources:"]))
        rest = lines[9:]
        self.assertEqual(rest[0], "  time (s)     wall      cpu")
        self.assertEqual([line.split()[0] for line in rest[1:5]],
                         ["stage", "feed", "check", "total"])
        self.assertRegex(rest[5], r"^  memory: peak resident \d+(\.\d)? [kM]B; "
                                  r"the stage's heap blocks \d+(\.\d)? [kM]B$")
        # The engine bin/leanforth ran: the file name of GFORTH here.
        self.assertEqual(rest[6], "  engine: " + os.path.basename(GFORTH))
        self.assertEqual(rest[7:], [
            "  input: 6 declarations, 92 term nodes, 3 levels, 5 constant references, 31 names",
            "  fuel: 415 steps in all, at most 100000000 per declaration",
            "  most fuel used:",
            "          244 Two.cases (accepted)",
            "          113 Two.swap (accepted)",
            "           58 Two (accepted)"])

    def test_stable_but_for_time_and_memory(self):
        def steady(out):
            return [line for line in out.splitlines()
                    if not re.match(r"^  (stage|feed|check|total) |^  memory: ", line)]
        args = ["--resources", "--no-manifest", "tests/core/reexport/kinds.ndjson"]
        self.assertEqual(steady(run("check", *args)[1]), steady(run("check", *args)[1]))


def fast_engine():
    """The gforth-fast bin/leanforth finds beside GFORTH (in its folder:
    scripts/gforth-fast under make), or None."""
    folder = os.path.dirname(GFORTH)
    if not folder:
        return shutil.which("gforth-fast")
    path = os.path.join(folder, "gforth-fast")
    return path if os.access(path, os.X_OK) else None


class Engines(unittest.TestCase):
    """gforth-fast by default (the tests set GFORTH); --fast looks beside GFORTH, with the
    same verdicts, the same report but for "measured" (owner, 2026-11-04)."""

    def test_fast_same_reports(self):
        fast = fast_engine()
        for args in [[COMPOSITION], [FIXTURE], [CHAIN], [INDUCTIVE], ["tests/cli/unfold.ndjson"],
                     ["--no-manifest", f"{CASES}/composition-wrong-argument.ndjson"],
                     ["--no-manifest", "tests/core/reexport/kinds.ndjson"],
                     ["--fuel", "0", FIXTURE]]:
            status, got, err = report(*args)
            fast_status, fast_got, fast_err = report("--fast", *args)
            engines = got.pop("measured")["engine"], fast_got.pop("measured")["engine"]
            self.assertEqual((fast_status, fast_got), (status, got), args)
            self.assertEqual(run("check", "--fast", *args)[1], run("check", *args)[1], args)
            if fast:
                self.assertEqual((engines, fast_err), ((os.path.basename(GFORTH),
                                                        os.path.basename(fast)), ""), args)
            else:   # no gforth-fast beside GFORTH (such as Gforth 0.7.3's wrapper)
                self.assertEqual(engines, (os.path.basename(GFORTH),) * 2, args)
                self.assertRegex(fast_err, r"^leanforth: note: no .* found; "
                                           r"checking with .*\n$")

    def test_fast_missing(self):
        """--fast with no gforth-fast beside GFORTH: the run uses GFORTH and
        says so on standard error."""
        with tempfile.TemporaryDirectory() as folder:
            stub = Path(folder) / "myforth"
            stub.write_text(f'#!/bin/sh\nexec "{GFORTH}" "$@"\n')
            stub.chmod(stub.stat().st_mode | stat.S_IXUSR)
            status, out, err = run("check", "--fast", "--json", COMPOSITION, gforth=str(stub))
            note = (f"leanforth: note: no {folder}/gforth-fast found; "
                    f"checking with {stub}\n")
            self.assertEqual((status, json.loads(out)["measured"]["engine"], err),
                             (0, "myforth", note))

    def test_gforth_unset(self):
        """With GFORTH unset the wrapper finds the engines itself, in this
        checkout's .tools or on PATH: gforth-fast, and gforth with --checked."""
        tools = ROOT / ".tools" / "gforth" / "bin"

        def found(name):
            return (tools / name).exists() or shutil.which(name)
        if not (found("gforth") and found("gforth-fast")):
            self.skipTest("no gforth and gforth-fast to find without GFORTH")
        env = {key: value for key, value in os.environ.items() if key != "GFORTH"}
        for options, engine in [([], "gforth-fast"), (["--fast"], "gforth-fast"), (["--checked"], "gforth")]:
            result = subprocess.run([str(TOOL), "check", "--json", *options, COMPOSITION],
                                    cwd=ROOT, env=env, stdin=subprocess.DEVNULL,
                                    capture_output=True, timeout=TEST_LIMIT)
            self.assertEqual((result.returncode, json.loads(result.stdout)["measured"]["engine"],
                              result.stderr), (0, engine, b""), options)

    def test_options(self):
        """--fast goes with check, replay and print; it is no file name,
        and the value of --fuel is not the option."""
        for args in [["check", "--fast", COMPOSITION], ["print", "--fast", COMPOSITION],
                     ["check", "--checked", COMPOSITION], ["print", "--checked", COMPOSITION]]:
            self.assertEqual(run(*args)[0], 0, args)
        self.assertEqual(run("check", "--fast", "--checked", COMPOSITION)[:2],
                         (4, "error: --fast and --checked together\ntry: leanforth help\n"))
        self.assertEqual(run("count", "--fast", COMPOSITION)[:2],
                         (4, "error: an option this command does not take: --fast\n"
                             "try: leanforth help\n"))
        self.assertEqual(run("check", "--fuel", "--fast", COMPOSITION)[:2],
                         (4, "error: not a fuel amount: --fast\ntry: leanforth help\n"))


class Fuel(unittest.TestCase):
    """The fuel an accepted declaration's check used is exactly what it
    needs: with a budget of that much it is accepted, with one less it runs
    out. Taken for the accepted declaration that used the most, so every
    accepted one before it, its dependencies among them, used less and
    stays accepted."""

    def test_exact(self):
        for export in [COMPOSITION, FIXTURE, CHAIN, INDUCTIVE, "tests/cli/unfold.ndjson"]:
            _, got, _ = report(export)
            accepted = [d for d in got["declarations"] if d["verdict"] == "accepted"]
            most = max(accepted, key=lambda d: d["fuel"])
            self.assertEqual(sum(d["fuel"] == most["fuel"] for d in accepted), 1, export)
            for budget, verdict in [(most["fuel"], "accepted"),
                                    (most["fuel"] - 1, "exhausted")]:
                _, again, _ = report("--fuel", str(budget), export)
                self.assertEqual(again["declarations"][most["index"]]["verdict"], verdict,
                                 (export, budget))

    def test_most(self):
        """--fuel takes at most 2^53 - 1, the largest integer every JSON
        reader holds exactly; a report with it is valid and says it."""
        status, got, _ = report("--fuel", str(2**53 - 1), INDUCTIVE)
        self.assertEqual((status, got["settings"]["fuel"], got["fuel"]["perDeclaration"],
                          JsonReport.schema.errors(got)), (0, 2**53 - 1, 2**53 - 1, []))
        self.assertEqual(run("check", "--fuel", str(2**53), INDUCTIVE)[0], 4)


def pinned_digest(*args):
    """check --json's report as a digest: without "measured", and without
    what depends on how the input is numbered (the count of term numbers,
    and the numbers of a diagnostic, which may name a term by its
    number); with the exit status."""
    result = subprocess.run([GFORTH, "src/main.fs", "-e", "cli-main", "check", "--json", *args],
                            cwd=ROOT, stdin=subprocess.DEVNULL, capture_output=True,
                            timeout=300)
    got = json.loads(result.stdout.decode())
    got.pop("measured")
    if got["input"]:
        got["input"].pop("terms")
    for declaration in got["declarations"]:
        declaration.get("diagnostic", {}).pop("numbers", None)
    blob = json.dumps([result.returncode, got], sort_keys=True).encode()
    return hashlib.sha256(blob).hexdigest()[:16]


# The digests of these exports' reports when every expression was copied
# into the term store (src/import/feed.fs's lf-feed-copy!, compact-store
# plan step S5 parts 1-3, removed by parts 4-5 once the input read in
# place gave the same report for each: every declaration's verdict, fuel
# and diagnostic, the counts and the exit status; agent S5B, 2026-11-11).
# nested.ndjson is re-pinned after merging main 5a3b68d, whose parallel
# checking (step S7) gave List.brecOn.go 2,669 fuel instead of 2,656 on
# main itself; the rest of its report is unchanged. Those marked IO are
# re-pinned after the follow-up of task 5.2.1b (agent IO, 2026-11-11): a
# block's check opens each binder of its type's telescope on the inference
# scope, as Lean does, for 1 or 2 more fuel per block (nested.ndjson: 7
# blocks, +11); every verdict and diagnostic is unchanged. The eleven whose
# digest changed again are re-pinned after agent PF's ADR 0014 Amendment 6
# (an argument put into a Pi body without loose bound variables is not
# closed): only fuel moved, 97 declarations less and none more; every
# verdict, diagnostic and count is unchanged. All but the --fuel 0 entry
# are re-pinned once more for the default fuel of 100,000,000 (owner,
# 2026-11-11): with settings.fuel and fuel.perDeclaration put back to
# 20,000,000 each report gives the digest pinned before. Four are
# re-pinned after ADR 0014 Amendment 7 (a check is given only the earlier
# nodes and levels it reached): against main 0627845 every report is the
# same but for fuel, 40 declarations with more and none with less.
# Those marked R5 are also re-pinned after ADR 0014 Amendment 9 (an application typed aside from
# its spine's head, as Lean's infer_app in infer-only mode): compared with
# the tree before it, every report is the same but for fuel, 34
# declarations less (the two spine exports added with it included) and
# none more.
# Those marked NS
# (six entries) are re-pinned after agent NS (2026-11-11): an inductive
# block's walks meet each shared node once and B3 compares by Lean's ==,
# so only block fuel moved, 41 declarations less and none more; every
# verdict, diagnostic and count is unchanged (each report compared with
# the one before with its fuel fields left out).
# Those marked MO (two entries) are re-pinned after review MO (2026-11-12):
# a nested block's translation, lowering and restoration keep each (node,
# offset) pair's result, as Lean's replace does, so only block fuel moved,
# 3 declarations less and none more; every verdict, diagnostic and count
# is unchanged (each report compared with main 703c729's, fuel left out).
# The one marked CK is re-pinned after plan task 4.2.7d (agent CK,
# 2026-11-12): proof irrelevance types the Pi A → A as Lean's infer_pi
# does, so impliesSelf takes 68 fuel (65 before); every verdict, diagnostic
# and count is unchanged (the report compared with main 390197d's, fuel
# left out). infer-only.ndjson is tests/cli/shared-depths.lean P5's p5all.
# All of them are re-pinned after task PA (2026-11-12): the owner withdrew the
# label, so each report lost its member label (at the top and on each
# accepted declaration) and is version 0.4; main 9965c2b's report of each,
# which gave the digest pinned before, with the label taken out and the
# version read as 0.4, equals this build's report member by member
# ("measured" left out).
PINNED = {
    "tests/reference/composition.ndjson": "2e99beb93733fe3c",
    "tests/reference/constant-fixture.ndjson": "3e777d5fc8f5ff2c",
    "tests/cli/chain.ndjson": "268dac385bac9a60",
    "tests/cli/inductive.ndjson": "9747bfdf954a0d32",
    "tests/cli/unfold.ndjson": "9e60570bde0484f1",  # CK
    f"{CASES}/composition-wrong-argument.ndjson": "f0a9dc145b6000df",
    f"--no-manifest {CASES}/composition-wrong-argument.ndjson": "f840d07c81e64bde",
    f"--no-manifest {CASES}/composition-postulate.ndjson": "1e03b3224287bf78",
    f"--no-manifest {CASES}/composition-loose.ndjson": "afa2d221c59541d4",
    f"--no-manifest {CASES}/composition-unsafe.ndjson": "bf8466416648c453",
    "--no-manifest README.md": "37b9bcecc9e4fa22",
    "tests/cli/no-such.ndjson": "9bb0bf1002d40192",
    "--no-manifest tests/cli/composition-huge-number.ndjson": "b04f25902757c91e",
    "--no-manifest tests/core/reexport/kinds.ndjson": "ccfb4f5380d614c7",  # IO, R5, MO
    f"--fuel 0 {FIXTURE}": "f935e2d2bf3631d9",
    f"--no-manifest {EMPTY_BLOCK}": "e14d55a114b54710",
    "tests/cli/sharing.ndjson": "9109a215328715cc",  # re-pinned (IO)
    "tests/cli/sharing-universe.ndjson": "76371ee25566bc72",  # re-pinned (IO)
    "tests/cli/nested.ndjson": "1dd14a85b734d07b",  # re-pinned, see above; R5, MO
    "tests/cli/irrelevance.ndjson": "3fb3676909ac5430",
    f"--no-manifest {CASES}/composition-literal.ndjson": "ecaba8d3d589abce",
    # tests/cli/shared-depths.lean P4's exports (agent R5, ADR 0014 Amendment 9):
    # 48-argument spines typed aside; accepted with 15,749 units, and rejected.
    f"--no-manifest {CASES}/spine-good.ndjson": "e65bf7bfd762e240",
    f"--no-manifest {CASES}/spine-bad.ndjson": "2d15817e2ca7834c",
    f"--no-manifest {CASES}/infer-only.ndjson": "2104f0c7dc5178ad",  # CK
    # P6 (agent CT, review rvCK 3): the fourteen probe rows, p6all.
    f"--no-manifest {CASES}/infer-only-p6.ndjson": "d9b652cecb9cbae4",
    "--no-manifest tests/core/check-block-cases/primitive.string-opaque-expansion.ndjson":
        "e6d37fe6c3a1830f",  # re-pinned (IO, R5)
}


class AsCopied(unittest.TestCase):
    """The input read in place (compact-store plan step S5; core/terms.fs's
    view) gives the report the copy into the term store, the way before
    it, gave for each export (PINNED)."""

    def test_same(self):
        for args, want in PINNED.items():
            self.assertEqual(pinned_digest(*args.split()), want, args)


class Jobs(unittest.TestCase):
    """check --jobs N (plan tasks 6.5.4, 7.3.1; src/kernel/env-schedule.fs)
    prints exactly what --jobs 1 prints, text and JSON (but for "measured"),
    with the same exit status, on every export of the JSON tests and on
    larger ones; the resource report names the workers. --jobs takes a
    number of at least 1 and does not go with --record (status 4)."""

    MORE = [["tests/cli/sharing.ndjson"], ["tests/cli/nested.ndjson"],
            ["tests/cli/irrelevance.ndjson"], ["--fuel", "3000", "tests/cli/nested.ndjson"],
            ["tests/cli/jobs/wide60.ndjson"], ["tests/cli/jobs/dupl80.ndjson"],
            ["--no-manifest", "tests/cli/jobs/renamed20.ndjson"]]

    def text(self, *args):
        return run("check", *args)[:2]

    def json(self, *args):
        status, got, _ = report(*args)
        got.pop("measured")
        return status, got

    def test_same_output(self):
        """Each case's four runs, the cases side by side (each only reads its export)."""
        cases = CASES_ALL + self.MORE

        def four(args):
            return (self.text(*args), self.text("--jobs", "3", *args),
                    self.json(*args), self.json("--jobs", "4", *args))
        for args, (text, text3, json1, json4) in zip(cases, side_by_side(four, cases)):
            self.assertEqual(text, text3, args)
            self.assertEqual(json1, json4, args)

    def test_resources(self):
        status, out, _ = run("check", "--resources", "--jobs", "2", "tests/cli/nested.ndjson")
        self.assertEqual(status, 0)
        self.assertRegex(out, r"\n  workers: 2 \(--jobs\), on \d+ cores\n    checks handed "
                              r"out [1-9]\d*, run again 0, not ready 0, forced 0, workers "
                              r"replaced 0\n")
        self.assertNotIn("workers:", run("check", "--resources", CHAIN)[1])

    def test_workers_share_merged_binders(self):
        """Binders equal up to their names, which the importer makes one node
        (ADR 0014 Amendment 7): each worker makes the source's copies of them,
        so workers are made (before, the workers' input had another
        fingerprint and the run fell back to one declaration at a time)."""
        status, out, _ = run("check", "--resources", "--jobs", "2", "--no-manifest",
                             "tests/cli/jobs/renamed20.ndjson")
        self.assertEqual(status, 0)
        self.assertIn("20 declarations: 20 accepted", out)
        self.assertRegex(out, r"\n  workers: 2 \(--jobs\), on \d+ cores\n    checks handed "
                              r"out 20, run again 0, not ready 0, forced 0, workers "
                              r"replaced 0\n")

    def test_workers_share_merged_lets(self):
        """Lets equal up to their names (tests/cli/jobs/gen.py lets 20), which
        the importer makes one node (review rvRS F2): each worker makes the
        source's copies of them and of the applications above them, so its
        input's fingerprint is the source's and workers are made."""
        with tempfile.TemporaryDirectory() as tmp:
            export = Path(tmp) / "lets20.ndjson"
            made = subprocess.run([sys.executable, str(ROOT / "tests/cli/jobs/gen.py"), "lets",
                                   "20"], capture_output=True, check=True)
            export.write_bytes(made.stdout)
            status, out, _ = run("check", "--resources", "--jobs", "2", "--no-manifest",
                                 str(export))
        self.assertEqual(status, 0)
        self.assertIn("20 declarations: 20 accepted", out)
        self.assertRegex(out, r"\n  workers: 2 \(--jobs\), on \d+ cores\n    checks handed "
                              r"out 20, run again 0, not ready 0, forced 0, workers "
                              r"replaced 0\n")

    def test_large_counts(self):
        """The count is cut to the cores and the pool's queue of 1024: a larger
        one used to refuse a job (exit 5, declarations "not checked") or make
        a copy of the input per worker. Same output as --jobs 1, and no more
        workers than cores in the report."""
        args = ["--no-manifest", "tests/cli/jobs/wide60.ndjson"]
        serial = self.text(*args)
        self.assertEqual(serial[0], 0)
        for value in ["1100", "9223372036854775807"]:
            self.assertEqual(self.text("--jobs", value, *args), serial, value)
            status, out, _ = run("check", "--resources", "--jobs", value, *args)
            self.assertEqual(status, 0, value)
            workers = int(re.search(r"\n  workers: (\d+) \(--jobs\)", out).group(1))
            self.assertTrue(1 < workers <= max(os.cpu_count(), 2) and workers <= 1024, workers)
            self.assertIn("60 declarations: 60 accepted", out)

    def test_4_mistakes(self):
        for value in ["0", "x", "-1", ""]:
            status, out, _ = run("check", "--jobs", value, CHAIN)
            self.assertEqual(status, 4, value)
            self.assertIn("error: not a number of jobs", out)
        status, out, _ = run("check", "--jobs", "2", "--record", "r.json", CHAIN)
        self.assertEqual((status, out.splitlines()[0]),
                         (4, "error: --jobs does not go with --record"))


class TextJobs(unittest.TestCase):
    """check --jobs N with a LeanForth text (plan 8.2.1c's notes): no worker
    can share the input a text's run leaves, so the text is checked one
    declaration at a time, and with N above 1 a note says so before the
    verdicts (after the --no-manifest note); the verdicts, the rest of the
    text and the exit status are --jobs 1's, for every outcome. --jobs 1 or
    none prints no note; a text that stops before its check gets none; a
    wrong N is still a mistake (4); capabilities and help name the text."""

    LIBRARY = ["--env", "tests/author/init-slice.ndjson"]
    TEXT = "tests/author/07-add-comm.lf"
    WRONG_TEXT = "tests/author/wrong/07-add-comm.lf"

    def noted(self, *args):
        """The run with --jobs 2: its status, and its text without the note,
        which must be its first line."""
        status, out, err = run("check", "--jobs", "2", *args)
        self.assertEqual((out.split("\n")[0], err), (TEXT_JOBS_NOTE, ""), args)
        return status, out.split("\n", 1)[1]

    def test_note_then_serial_verdicts(self):
        """Accepted, rejected and out of fuel: the same as one at a time."""
        for args, code in [(self.LIBRARY + [self.TEXT], 0), (self.LIBRARY + [self.WRONG_TEXT], 1),
                           (["--fuel", "50"] + self.LIBRARY + [self.TEXT], 3)]:
            serial = run("check", *args)[:2]
            self.assertEqual(serial[0], code, args)
            self.assertNotIn("--jobs", serial[1], args)
            self.assertEqual(self.noted(*args), serial, args)
            self.assertEqual(run("check", "--jobs", "64", *args)[:2],
                             (code, TEXT_JOBS_NOTE + "\n" + serial[1]), args)

    def test_no_note_without_workers(self):
        for args in [[], ["--jobs", "1"]]:
            status, out, _ = run("check", *args, *self.LIBRARY, self.TEXT)
            self.assertEqual(status, 0, args)
            self.assertNotIn("--jobs", out, args)

    def test_note_order_and_resources(self):
        """After the --no-manifest note; --resources says why (no workers)."""
        status, out, _ = run("check", "--no-manifest", "--jobs", "2", "--resources",
                             *self.LIBRARY, self.TEXT)
        self.assertEqual(status, 0)
        self.assertEqual(out.split("\n")[:2], [NO_MANIFEST, TEXT_JOBS_NOTE])
        self.assertIn("\n  workers: none could be made (no heap, or this context's input "
                      "differs\n    from a new one's): checked one at a time\n", out)

    def test_snapshot_library(self):
        with tempfile.TemporaryDirectory() as tmp:
            snapshot = str(Path(tmp) / "slice.lfsnap")
            self.assertEqual(run("check", "--save-snapshot", snapshot,
                                 "tests/author/init-slice.ndjson")[0], 0)
            status, out = self.noted("--snapshot", snapshot, self.TEXT)
            self.assertEqual(status, 0)
            self.assertIn("60 declarations: 60 accepted; 59 from the snapshot, 1 checked in "
                          "this run\n", out)

    def test_stopped_text_has_no_note(self):
        """A mistake (4), a form not supported (2): not checked, no note."""
        with tempfile.TemporaryDirectory() as tmp:
            unsupported = Path(tmp) / "let.lf"
            unsupported.write_text("theorem t\n  Prop explicit: p  p\n:=\n  p let:\nend t\n",
                                   encoding="utf-8")
            for path, code in [("tests/author/10b-typo.lf", 4), (str(unsupported), 2)]:
                status, out, _ = run("check", "--jobs", "2", path)
                self.assertEqual(status, code, path)
                self.assertIn("the LeanForth text was not checked", out)
                self.assertNotIn("note:", out, path)

    def test_4_mistakes(self):
        for value in ["0", "x", "-1", ""]:
            status, out, _ = run("check", "--jobs", value, *self.LIBRARY, self.TEXT)
            self.assertEqual(status, 4, value)
            self.assertIn("error: not a number of jobs", out)
            self.assertNotIn(TEXT_JOBS_NOTE, out)
        status, out, _ = run("check", "--jobs", "2", "--json", self.TEXT)
        self.assertEqual(status, 4)
        self.assertNotIn(TEXT_JOBS_NOTE, out)

    def test_named_by_capabilities_and_help(self):
        capabilities, helped = run("capabilities")[1], run("help")[1]
        self.assertIn(TEXT_CAPABILITY, capabilities.split("not yet supported")[0])
        self.assertEqual(capabilities.count("FILE.lf"), 1)
        self.assertIn("  check [--env EXPORT | --snapshot FILE] [--fuel N] [--resources] "
                      "[--jobs N]\n", helped)


class MemoryPerCheck(unittest.TestCase):
    """check --memory-per-check MB (core/scratch-meter.fs; ADR 0014
    Amendment 8): a check whose scratch would pass MB megabytes is full,
    with diagnostic 101, never accepted; the others keep their verdicts,
    serially and with --jobs. The export (tests/cli/jobs/gen.py double 12)
    has one theorem, big, whose check unfolds 2^12 - 1 definitions (Lean
    accepts it; its scratch measured between 2 and 4 MB, 2026-11-11), and
    small theorems beside it."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        cls.export = str(Path(cls.tmp.name) / "double12.ndjson")
        made = subprocess.run([sys.executable, str(ROOT / "tests/cli/jobs/gen.py"), "double",
                               "12"], capture_output=True, check=True)
        Path(cls.export).write_bytes(made.stdout)

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def verdicts(self, *args):
        status, got, _ = report("--no-manifest", *args, self.export)
        self.assertEqual(JsonReport.schema.errors(got), [], args)
        return status, got, {d["name"]: d["verdict"] for d in got["declarations"]}

    def test_full_with_limit(self):
        status, got, verdicts = self.verdicts("--memory-per-check", "1")
        self.assertEqual((status, verdicts.pop("big")), (3, "full"))
        self.assertEqual(set(verdicts.values()), {"accepted"})
        big = [d for d in got["declarations"] if d["name"] == "big"][0]
        self.assertEqual((big["diagnostic"]["code"], big["diagnostic"]["reason"],
                          big["diagnostic"]["numbers"][1]),
                         (101, "memory limit per check", 2**20))
        self.assertEqual(got["settings"]["memoryPerCheck"], 1)

    def test_accepted_without_or_enough(self):
        for args in [[], ["--memory-per-check", "64"]]:
            status, got, verdicts = self.verdicts(*args)
            self.assertEqual((status, set(verdicts.values())), (0, {"accepted"}), args)
            self.assertEqual(got["settings"].get("memoryPerCheck"), int(args[1]) if args else None)

    def test_jobs(self):
        """With --jobs 2 big is full while the small ones beside it are
        accepted: the same text as one at a time, with the note."""
        args = ["--no-manifest", "--memory-per-check", "1", self.export]
        serial = run("check", *args)[:2]
        self.assertEqual(serial[0], 3)
        self.assertIn("big: full\n  memory limit per check; diagnostic 101", serial[1])
        self.assertIn("note: a check passed its memory limit (1 MB each); --memory-per-check MB "
                      "gives each more\n", serial[1])
        self.assertEqual(run("check", "--jobs", "2", *args)[:2], serial)
        status, got, verdicts = self.verdicts("--jobs", "2", "--memory-per-check", "1")
        self.assertEqual((status, verdicts.pop("big"), set(verdicts.values())),
                         (3, "full", {"accepted"}))

    def test_sweep(self):
        """From 1 to 5 MB big is full up to some limit and accepted from
        there on, never earlier, and each limit prints the same text with
        --jobs 3 as one at a time."""
        seen = []
        for mb in range(1, 6):
            args = ["--no-manifest", "--memory-per-check", str(mb), self.export]
            serial = run("check", *args)[:2]
            self.assertEqual(run("check", "--jobs", "3", *args)[:2], serial, mb)
            seen.append(re.search(r"^big: (\w+)", serial[1], re.M).group(1))
        full = seen.count("full")
        self.assertTrue(0 < full < 5, seen)
        self.assertEqual(seen, ["full"] * full + ["accepted"] * (5 - full))

    def test_counted_not_measured(self):
        """The bytes are counted per record, not read from the heap: big2,
        the same theorem after big, asks for exactly as many bytes, though
        big's check grew the stores of the context big2 then runs in."""
        with tempfile.TemporaryDirectory() as tmp:
            export = str(Path(tmp) / "double2.ndjson")
            made = subprocess.run([sys.executable, str(ROOT / "tests/cli/jobs/gen.py"),
                                   "double2", "12"], capture_output=True, check=True)
            Path(export).write_bytes(made.stdout)
            args = ["--no-manifest", "--memory-per-check", "1", export]
            status, out = run("check", *args)[:2]
            reasons = re.findall(r"^big2?: full\n  (memory limit per check; .*)$", out, re.M)
            self.assertEqual((status, len(reasons)), (3, 2), out)
            self.assertEqual(reasons[0], reasons[1])
            self.assertEqual(run("check", "--jobs", "3", *args)[:2], (status, out))

    def test_snapshot_pair(self):
        """A check's count does not depend on the other records of the tier
        (review rvRS F1): B's check (tests/cli/jobs/gen.py refs 2800) makes
        2,800 references D_i.{0..0}; checked fresh, against a snapshot of
        the export whose Z_i hold every one of them (refsz), and in the
        export with the Z_i after B (refsbz), serially and with --jobs 2, B
        is full asking for the same bytes. Before, a reference made before
        the check was given uncharged: 1,048,608 bytes fresh, 1,048,640 in
        the others (and the reviewer's larger probe: full fresh, accepted
        in the others)."""
        with tempfile.TemporaryDirectory() as tmp:
            exports = {kind: str(Path(tmp) / f"{kind}.ndjson") for kind in ["refs", "refsz",
                                                                            "refsbz"]}

            def made(kind):
                done = subprocess.run([sys.executable, str(ROOT / "tests/cli/jobs/gen.py"), kind,
                                       "2800"], capture_output=True, check=True)
                Path(exports[kind]).write_bytes(done.stdout)
            side_by_side(made, exports)
            snapshot = str(Path(tmp) / "refsz.lfsnap")
            limit = ["--no-manifest", "--memory-per-check", "1"]
            # The snapshot written beside the three checks that do not read it, then the one
            # that does; every run only reads its export.
            first = side_by_side(lambda args: run("check", *args), [
                ["--no-manifest", "--save-snapshot", snapshot, exports["refsz"]],
                [*limit, exports["refs"]], [*limit, exports["refsbz"]],
                [*limit, "--jobs", "2", exports["refsbz"]]])
            self.assertEqual(first[0][0], 0)
            seen = []
            for status, out, _ in first[1:2] + [run("check", *limit, "--snapshot", snapshot,
                                                    exports["refs"])] + first[2:]:
                found = re.search(r"^B: (\w+)\n  (.*)$", out, re.M)
                seen.append((status, found and found.groups()))
            self.assertEqual(seen[0][:1] + seen[0][1][:1], (3, "full"), seen[0])
            self.assertIn("diagnostic 101", seen[0][1][1])
            self.assertEqual(seen, [seen[0]] * 4)

    def test_4_mistakes(self):
        for value in ["0", "x", "-1", ""]:
            status, out, _ = run("check", "--memory-per-check", value, CHAIN)
            self.assertEqual(status, 4, value)
        status, out, _ = run("check", "--memory-per-check", "1", "--record", "r.json", CHAIN)
        self.assertEqual((status, out.splitlines()[0]),
                         (4, "error: --memory-per-check does not go with --record"))
        self.assertEqual(run("print", "--memory-per-check", "1", CHAIN)[0], 4)


def sectioned(path):
    """A sectioned file's bytes and its table (lib/sections.fs): per section
    (kind, unit, count, offset, length)."""
    data = bytearray(Path(path).read_bytes())
    table = []
    for i in range(int.from_bytes(data[16:20], "little")):
        base = 96 + 64 * i
        kind, unit = int.from_bytes(data[base:base + 4], "little"), int.from_bytes(
            data[base + 4:base + 8], "little")
        count, offset, length = (int.from_bytes(data[base + 8 + 8 * k:base + 16 + 8 * k], "little")
                                 for k in range(3))
        table.append((kind, unit, count, offset, length))
    return data, table


def resealed(data, table, section=None):
    """The bytes with section's SHA-256 (when given) and the header's made
    again, so that only the snapshot's own checks can refuse a change."""
    if section is not None:
        _, _, _, offset, length = table[section]
        base = 96 + 64 * section + 32
        data[base:base + 32] = hashlib.sha256(bytes(data[offset:offset + length])).digest()
    data[4064:4096] = hashlib.sha256(bytes(data[:4064])).digest()
    return data


def u32(data, at):
    return int.from_bytes(data[at:at + 4], "little")


def put32(data, at, value):
    data[at:at + 4] = value.to_bytes(4, "little")


SLOTS, DEPS, LOOKS = 11, 12, 13   # the environment's sections (kernel/env-snapshot.fs)


class Snapshots(unittest.TestCase):
    """check --save-snapshot FILE and check --snapshot FILE (plan task 6.2.5,
    step SN3; ADR 0020): a snapshot read back reports what the run that
    wrote it reported -- every verdict, axiom set, diagnostic and fuel --
    each labelled as taken from the snapshot (text, and report 0.5, which
    the schema accepts, and which set back to 0.3 with the withdrawn label
    0.3 accepts); --jobs 1 and --jobs 4, and two runs, write the
    same bytes; a damaged, altered or stale snapshot is refused (planted
    faults, each file's SHA-256s made again so that only the snapshot's own
    checks can refuse it); the misuses are refused (status 4)."""

    schema = Validator(json.loads((ROOT / "schemas/check-report-0.5.schema.json").read_text()))
    final = Validator(json.loads((ROOT / "schemas/check-report-0.4.schema.json").read_text()))
    labelled = Validator(json.loads((ROOT / "schemas/check-report-0.3.schema.json").read_text()))

    def setUp(self):
        self.dir = Path(tempfile.mkdtemp(prefix="leanforth-snapshots-"))

    def tearDown(self):
        shutil.rmtree(self.dir)

    def saved(self, *args, name="s.lfsnap"):
        path = self.dir / name
        status, got, _ = report("--save-snapshot", str(path), *args)
        return path, status, got

    @staticmethod
    def plain(got, keys=("schemaVersion", "export", "measured", "mode", "snapshot")):
        got = dict(got)
        for key in keys:
            got.pop(key, None)
        got["declarations"] = [{k: v for k, v in d.items() if k != "provenance"}
                               for d in got["declarations"]]
        return got

    def test_both_ways(self):
        for k, args in enumerate(CASES_ALL + [["tests/cli/nested.ndjson"], [SHARING]]):
            path, status, fresh = self.saved(*args, name=f"s{k}.lfsnap")
            self.assertEqual(self.final.errors(fresh), [], args)
            if fresh["run"] != "ok" or fresh["stopped"]:
                self.assertFalse(path.exists(), args)
                continue
            again, loaded, _ = report("--snapshot", str(path))
            self.assertEqual(self.schema.errors(loaded), [], args)
            self.assertEqual(self.labelled.errors(as_labelled(loaded, "0.3")), [], args)
            # The names a check made beyond its input (nested blocks) are
            # written with the tier's names (plan step SN5): the loaded
            # tier holds them too.
            names = loaded["input"].pop("names"), fresh["input"].pop("names")
            self.assertGreaterEqual(*names, args)
            self.assertEqual((again, self.plain(loaded)), (status, self.plain(fresh)), args)
            self.assertEqual({d["provenance"] for d in loaded["declarations"]}, {"snapshot"})
            self.assertEqual(loaded["mode"], "development")
            self.assertEqual(loaded["snapshot"]["sha256"],
                             hashlib.sha256(path.read_bytes()[:4064]).hexdigest(), args)

    def test_text(self):
        path, _, _ = self.saved(FIXTURE)
        status, out, _ = run("check", "--snapshot", str(path))
        self.assertEqual(status, 0)
        lines = out.splitlines()
        self.assertEqual(lines[0], "fixtureId: accepted (from snapshot, not re-checked in this run); "
                                   "axioms: none")
        self.assertRegex(lines[-3], r"^snapshot: .*s\.lfsnap \(sha256 [0-9a-f]{64}\), export "
                                    rf"sha256 [0-9a-f]{{64}}, verdict version {verdict_version()}, "
                                    r"written by "
                                    r"LeanForth \S+: 3 results taken from it, not re-checked "
                                    r"in this run$")
        self.assertEqual(lines[-2:], [
            "note: development and research mode: a final run re-checks everything from the",
            "note: export and reads no snapshot; only its results support a claim"])
        status, out, _ = run("check", "--save-snapshot", str(self.dir / "t"), FIXTURE)
        self.assertEqual(out.splitlines()[-1], f"snapshot: written to {self.dir / 't'}")

    def test_same_bytes(self):
        for args in [[INDUCTIVE], ["tests/cli/nested.ndjson"],
                     ["--no-manifest", "tests/cli/jobs/dupl80.ndjson"]]:
            one, _, _ = self.saved(*args, name="one")
            four, _, _ = self.saved("--jobs", "4", *args, name="four")
            again, _, _ = self.saved(*args, name="again")
            self.assertEqual(one.read_bytes(), four.read_bytes(), args)
            self.assertEqual(one.read_bytes(), again.read_bytes(), args)

    def refused(self, path, status, text, *args):
        got, out, _ = run("check", "--snapshot", str(path), *args)
        self.assertEqual((got, out.splitlines()[0]),
                         (status, f"error: {text}"), (path, args))

    def test_planted_faults(self):
        path, _, _ = self.saved(FIXTURE)
        data, table = sectioned(path)
        tampered = self.dir / "x.lfsnap"

        def write(changed):
            tampered.write_bytes(bytes(changed))
            return tampered
        for field, value, status, why in [
                (0, 0, 4, "invalid: the snapshot was refused: not a LeanForth snapshot"),
                (1, 2, 2, "unsupported: the snapshot was refused: format version"),
                (2, 1, 2, "unsupported: the snapshot was refused: verdict version"),
                (5, 2, 4, "invalid: the snapshot was refused: axiom allowlist"),
                (6, 1, 4, "invalid: the snapshot was refused: axiom allowlist"),
                (8, 1, 2, "unsupported: the snapshot was refused: layer")]:
            changed = bytearray(data)
            put32(changed, 24 + 4 * field, value)
            self.refused(write(resealed(changed, table)), status, why)
        changed = bytearray(data)
        put32(changed, 24 + 4 * 2, 1)   # an older verdict version
        status, got, _ = report("--snapshot", str(write(resealed(changed, table))))
        self.assertEqual((status, self.schema.errors(got), got["read"]["phase"],
                          got["read"]["reason"], got["run"]),
                         (2, [], "snapshot", "verdict version", "not-run"))
        self.refused(path, 4, "invalid: the snapshot was refused: fuel", "--fuel", "5")
        self.assertEqual(run("check", "--snapshot", str(path), "--fuel", "100000000")[0], 0)
        # A dependency past its slot: fixturePoly (slot 1) on itself.
        _, _, _, deps, _ = table[DEPS]
        changed = bytearray(data)
        put32(changed, deps, 1)
        self.refused(write(resealed(changed, table, DEPS)), 4,
                     "invalid: the snapshot was refused: slots (record 1)")
        # A lookup list out of order: fixtureUse's first two lookups swapped.
        _, _, _, slots, _ = table[SLOTS]
        before = sum(u32(data, slots + 72 * d + 40) for d in range(2))
        _, _, _, looks, _ = table[LOOKS]
        at = looks + 8 * before
        self.assertGreaterEqual(u32(data, slots + 72 * 2 + 40), 2)
        changed = bytearray(data)
        changed[at:at + 16] = data[at + 8:at + 16] + data[at:at + 8]
        self.refused(write(resealed(changed, table, LOOKS)), 4,
                     "invalid: the snapshot was refused: slot published otherwise (record 2)")
        # A byte changed without its SHA-256; a cut file.
        changed = bytearray(data)
        changed[slots] ^= 1
        self.refused(write(changed), 4, "invalid: the snapshot was refused: sections")
        self.refused(write(data[:len(data) - 4096]), 4,
                     "invalid: the snapshot was refused: header or section table")

    def test_review_faults(self):
        """Review rvSN3's crafted snapshots, each refused or shown safely:
        list counts past their sections (M1), fuel used above the fuel per
        declaration (m2), provenance in a base snapshot (m3), a lookup key of
        a name beyond the tier or the quotient's kind under another name
        (m5), a definition marked added (m4), whose JSON report lists no
        verdict (M2); a commit text that is not plain (m1)."""
        path, _, _ = self.saved(FIXTURE)
        data, table = sectioned(path)
        tampered = self.dir / "r.lfsnap"
        slots, looks = table[SLOTS][3], table[LOOKS][3]

        def slot_changed(field, value, d=0):
            changed = bytearray(data)
            put32(changed, slots + 72 * d + 4 * field, value)
            tampered.write_bytes(bytes(resealed(changed, table, SLOTS)))
            return tampered
        first = next(d for d in range(3) if u32(data, slots + 72 * d + 40))
        for field, value, why in [
                (9, 0x7FFFFFFF, "slots (record 0)"), (10, 0x7FFFFFFF, "slots (record 0)"),
                (9, 1 + len(data), "slots (record 0)"),
                (8, 0xFFFF, "slots (record 0)"), (2, 1, "slots (record 0)"),
                (2, 3, "slots (record 0)")]:
            self.refused(slot_changed(field, value), 4,
                         f"invalid: the snapshot was refused: {why}")
        for key in [(0x7FFFFFF << 4) | 0, (1 << 4) | 8]:
            changed = bytearray(data)
            put32(changed, looks, key)
            tampered.write_bytes(bytes(resealed(changed, table, LOOKS)))
            self.refused(tampered, 4, f"invalid: the snapshot was refused: slots (record {first})")
        changed = bytearray(data)
        put32(changed, slots, 4)
        put32(changed, slots + 4, 2)
        tampered.write_bytes(bytes(resealed(changed, table, SLOTS)))
        self.refused(tampered, 4,
                     "invalid: the snapshot was refused: slot published otherwise (record 0)")
        status, got, _ = report("--snapshot", str(tampered))
        self.assertEqual((status, self.schema.errors(got), got["read"]["outcome"],
                          got["declarations"]), (4, [], "invalid", []))
        _, _, _, info, length = table[16]
        text = b'{"leanforth":"0.1.0-dev","commit":"x\nNat.fake: accepted","modified":false}'
        self.assertLessEqual(len(text), length)
        changed = bytearray(data)
        changed[info:info + length] = text + b" " * (length - len(text))
        tampered.write_bytes(bytes(resealed(changed, table, 16)))
        status, out, _ = run("check", "--snapshot", str(tampered))
        self.assertEqual(status, 0)
        self.assertNotIn("Nat.fake", out)
        self.assertIn("written by LeanForth unknown: 3 results", out)

    def test_stale(self):
        """--snapshot-stale-ok (ADR 0020 amendment 3): a snapshot of an
        older verdict version loads, every result taken from it labelled
        stale and counted apart, never as this build's verdict; a newer one
        is refused still; the flag needs --snapshot and writes no snapshot."""
        path, _, fresh = self.saved(FIXTURE)
        data, table = sectioned(path)
        old = self.dir / "old.lfsnap"
        put32(data, 24 + 4 * 2, 1)
        old.write_bytes(bytes(resealed(data, table)))
        self.refused(old, 2, "unsupported: the snapshot was refused: verdict version")
        status, out, _ = run("check", "--snapshot-stale-ok", "--snapshot", str(old))
        lines = out.splitlines()
        self.assertEqual((status, lines[0]), (0, (
            "fixtureId: accepted (from a stale "
            "snapshot (an older verdict version), not this build's verdict); axioms: none")))
        self.assertIn(f"stale: build's ({verdict_version()}): its 3 results are not this "
                      "build's verdicts", lines)
        status, got, _ = report("--snapshot-stale-ok", "--snapshot", str(old))
        self.assertEqual(self.schema.errors(got), [])
        self.assertEqual((got["snapshot"]["verdictVersion"], got["snapshot"]["stale"]),
                         (1, {"thisVerdictVersion": verdict_version(), "results": 3}))
        self.assertEqual({d["provenance"] for d in got["declarations"]}, {"stale-snapshot"})
        self.assertEqual(report("--snapshot", str(path))[1]["snapshot"]["stale"], None)
        status, got, _ = report("--snapshot-stale-ok", "--snapshot", str(old), FIXTURE)
        self.assertEqual((status, self.schema.errors(got)), (0, []))
        self.assertEqual({d["provenance"] for d in got["declarations"]}, {"stale-snapshot"})
        put32(data, 24 + 4 * 2, verdict_version() + 1)   # newer than this build's
        old.write_bytes(bytes(resealed(data, table)))
        self.refused(old, 2, "unsupported: the snapshot was refused: verdict version",
                     "--snapshot-stale-ok")
        for args, why in [(["--snapshot-stale-ok", FIXTURE], "needs --snapshot"),
                          (["--snapshot-stale-ok", "--snapshot", str(path), "--save-snapshot",
                            str(self.dir / "x"), FIXTURE], "does not go with --save-snapshot")]:
            status, out, _ = run("check", *args)
            self.assertEqual((status, out.splitlines()[0]),
                             (4, f"error: --snapshot-stale-ok {why}"), args)

    def test_outcome_changed(self):
        """A rejected verdict made accepted, every SHA-256 made again: the
        loader cannot tell, and reports it as the snapshot's verdict, never as
        one checked in this run (a snapshot vouches for no forgery, ADR 0020
        D4)."""
        args = ["--no-manifest", f"{CASES}/composition-wrong-argument.ndjson"]
        path, status, fresh = self.saved(*args)
        self.assertEqual((status, fresh["declarations"][0]["verdict"]), (1, "rejected"))
        data, table = sectioned(path)
        put32(data, table[SLOTS][3], 0)
        path.write_bytes(bytes(resealed(data, table, SLOTS)))
        status, got, _ = report("--snapshot", str(path))
        self.assertEqual((status, got["declarations"][0]["verdict"],
                          got["declarations"][0]["provenance"]), (0, "accepted", "snapshot"))

    def test_4_misuses(self):
        path, _, _ = self.saved(CHAIN)
        for args, why in [
                (["--record", "r.json", "--snapshot", str(path)],
                 "--snapshot and --save-snapshot do not go with --record"),
                (["--snapshot", str(path), "--save-snapshot", "x"],
                 "--snapshot and --save-snapshot go together only with an export (a layer)")]:
            status, out, _ = run("check", *args)
            self.assertEqual((status, out.splitlines()[0]), (4, f"error: {why}"), args)
        status, out, _ = run("check", "--save-snapshot", CHAIN, CHAIN)
        self.assertEqual((status, out), (4, "error: FILE must not be EXPORT\n"))
        status, out, _ = run("check", "--save-snapshot", str(self.dir / "u"), "--no-manifest",
                             "README.md")
        self.assertEqual(status, 4)
        self.assertFalse((self.dir / "u").exists())


class Progress(unittest.TestCase):
    """check --progress[=SECONDS] (docs/user/COMMAND_LINE.md): a status line
    on standard error every SECONDS (default 60; 0: after every report) and a
    last one; standard output, the JSON report and the exit status are what
    they are without it, serial and with --jobs; the text report's lines are
    written as declarations become final, so a finished run's output is
    unchanged. It does not go with --record, and replay does not take it."""

    LINE = re.compile(r"progress: \d+ s elapsed; (\d+)/(\d+) declarations final \((\d+)%\); "
                      r"(\d+) accepted, (\d+) other; \d+ declarations/s; "
                      r"eta (\d+ s|unknown); resident (\d+ MB|\? MB)")

    def lines(self, err):
        return [self.LINE.fullmatch(line) or self.fail(line) for line in err.splitlines()]

    def test_same_output(self):
        for args in [[INDUCTIVE], ["--fuel", "3000", "tests/cli/nested.ndjson"],
                     ["--no-manifest", "tests/cli/jobs/wide60.ndjson"]]:
            for jobs in [[], ["--jobs", "3"]]:
                plain = run("check", *jobs, *args)
                self.assertEqual(plain[2], "", args)
                for form in ["--progress=0", "--progress"]:
                    status, out, err = run("check", form, *jobs, *args)
                    self.assertEqual((status, out), plain[:2], (form, jobs, args))
                    if form == "--progress=0":
                        found = self.lines(err)
                        total = int(found[-1].group(2))
                        self.assertEqual(found[-1].group(1), str(total))
                        self.assertEqual(found[-1].group(3), "100")
                        self.assertEqual(int(found[-1].group(4)) + int(found[-1].group(5)), total)

    def test_counts_rejections(self):
        """The accepted and other counts follow the verdicts."""
        path = "tests/cli/bugs/rec-missing-ih.ndjson"
        status, out, err = run("check", "--no-manifest", "--progress=0", path)
        self.assertEqual(status, 1)
        last = self.lines(err)[-1]
        self.assertGreater(int(last.group(5)), 0)
        self.assertEqual(int(last.group(4)) + int(last.group(5)), int(last.group(2)))

    def test_json(self):
        status, want, _ = report(INDUCTIVE)
        want.pop("measured")
        code, out, err = run("check", "--progress=0", "--json", INDUCTIVE)
        self.assertEqual(code, status)
        self.assertEqual(len(self.lines(err)), 7)
        got = json.loads(out)
        got.pop("measured")
        self.assertEqual(got, want)

    def test_default_is_quiet_for_a_short_run(self):
        """The default interval is 60 s: a short run writes only the last line."""
        status, out, err = run("check", "--progress", INDUCTIVE)
        self.assertEqual((status, len(self.lines(err))), (0, 1))

    def test_4_mistakes(self):
        for form, why in [("--progress=x", "not a number of seconds: x"),
                          ("--progress=", "not a number of seconds"),
                          ("--progress=-1", "not a number of seconds: -1")]:
            status, out, _ = run("check", form, CHAIN)
            self.assertEqual((status, out.splitlines()[0]), (4, f"error: {why}"), form)
        status, out, _ = run("check", "--progress", "--record", "r.json", CHAIN)
        self.assertEqual((status, out.splitlines()[0]),
                         (4, "error: --progress does not go with --record"))
        for form in ["--progress", "--progress=5"]:
            status, out, _ = run("replay", form, CHAIN, "r.json")
            self.assertEqual((status, out.splitlines()[0]),
                             (4, f"error: an option this command does not take: {form}"))


class Slice(unittest.TestCase):
    """scripts/export-slice.py EXPORT NAME... (docs/development/TESTING_STRATEGY.md):
    the smallest export holding the named declarations and what they need,
    in the original order with the original header, accepted by check
    --no-manifest with the same verdicts; an unknown name is exit 2."""

    TOOL = ROOT / "scripts" / "export-slice.py"

    def cut(self, source, *names):
        result = subprocess.run([sys.executable, "-I", str(self.TOOL), source, *names],
                                cwd=ROOT, capture_output=True, timeout=TEST_LIMIT)
        return result.returncode, result.stdout.decode(), result.stderr.decode()

    def check(self, text):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "slice.ndjson"
            path.write_text(text)
            return run("check", "--no-manifest", str(path))

    def test_inductive(self):
        status, text, err = self.cut(INDUCTIVE, "Two.swap")
        self.assertEqual(status, 0, err)
        original = Path(ROOT / INDUCTIVE).read_text().splitlines()
        lines = text.splitlines()
        self.assertEqual(lines[0], original[0])
        self.assertLess(len(lines), len(original))
        position = 0
        for line in lines:        # a subsequence, in the original order
            position = original.index(line, position) + 1
        self.assertRegex(err, r"export-slice: \d+ of 3 declarations, \d+ lines")
        status, out, _ = self.check(text)
        self.assertEqual(status, 0)
        self.assertIn("Two.swap: accepted", out)
        self.assertNotIn("Two.cases", out)       # not needed by Two.swap
        self.assertIn("Two.rec: accepted", out)   # the recursor's block is whole

    def test_the_builtins_come_with_it(self):
        """Quot and Eq (the checker's own lookups) are in a slice of anything,
        when the export declares them."""
        source = "tests/reference/inductive/axioms.ndjson"
        status, text, err = self.cut(source, "propext")
        self.assertEqual(status, 0, err)
        status, out, _ = self.check(text)
        self.assertEqual(status, 0)
        for name in ["propext", "Quot.sound", "Classical.choice", "Eq"]:
            self.assertIn(f"{name}: accepted", out)

    def test_several_names(self):
        status, text, err = self.cut(INDUCTIVE, "Two.first", "Two.cases")
        self.assertEqual(status, 0, err)
        status, out, _ = self.check(text)
        self.assertEqual(status, 0)
        self.assertIn("Two.cases: accepted", out)

    def test_unknown_name(self):
        status, text, err = self.cut(INDUCTIVE, "Two.nothing")
        self.assertEqual((status, text), (2, ""))
        self.assertIn("Two.nothing: not declared in the export", err)
        self.assertEqual(self.cut(INDUCTIVE, "a..b")[0], 2)
        self.assertEqual(self.cut(INDUCTIVE)[0], 4)

    def test_not_an_export(self):
        status, text, err = self.cut("README.md", "x")
        self.assertNotEqual(status, 0)
        self.assertEqual(text, "")


DEPENDENT = "tests/cli/dependent.ndjson"   # a library on inductive.lean (dependent.lean)
SIBLING = "tests/cli/sibling.ndjson"       # another one (sibling.lean)
TWO = ["Two", "Two.first", "Two.second", "Two.rec"]


def records(path):
    return [json.loads(line) for line in Path(path).read_text().splitlines()]


def ndjson_text(lines):
    return "".join(json.dumps(r, separators=(",", ":")) + "\n" for r in lines)


def swapped_minors(lines, name):
    """The export with theorem name's value `fun t => R m1 m2 t` made
    `fun t => R m2 m1 t` (new expressions, appended before the theorem)."""
    names = {r["in"]: r["str"]["str"] for r in lines if "in" in r and "str" in r}
    exprs = {r["ie"]: r for r in lines if "ie" in r}
    at = next(i for i, r in enumerate(lines)
              if "thm" in r and names.get(r["thm"]["name"]) == name)
    top = max(exprs) + 1
    lam = exprs[lines[at]["thm"]["value"]]["lam"]
    body = exprs[lam["body"]]["app"]
    f = exprs[body["fn"]]["app"]
    g = exprs[f["fn"]]["app"]
    new = [{"ie": top, "app": {"fn": g["fn"], "arg": f["arg"]}},
           {"ie": top + 1, "app": {"fn": top, "arg": g["arg"]}},
           {"ie": top + 2, "app": {"fn": top + 1, "arg": body["arg"]}},
           {"ie": top + 3, "lam": dict(lam, body=top + 2)}]
    thm = dict(lines[at], thm=dict(lines[at]["thm"], value=top + 3))
    return lines[:at] + new + [thm] + lines[at + 1:]


def kept_back(snapshot):
    """Per slot of a snapshot checked against its own export: whether the
    import rule I1 keeps it back -- an outcome invalid, exhausted or full; a lookup
    no import replays (the key 2^32 - 1 of verdict version 1, or another module's
    test, kind 7; since plan step SN5 a name a check made beyond its input is
    written as a name of the tier, and replayed); a lookup answered or a
    dependency met by a slot kept back; a slot published with the one before,
    as that one."""
    data, table = sectioned(snapshot)
    _, _, n, slots, _ = table[SLOTS]
    looks, deps = table[LOOKS][3], table[DEPS][3]
    back, j, k = [], 0, 0
    for d in range(n):
        at = slots + 72 * d
        outcome, marks = u32(data, at), u32(data, at + 4)
        nd, nl = u32(data, at + 36), u32(data, at + 40)
        pairs = [(u32(data, looks + 8 * (k + i)), u32(data, looks + 8 * (k + i) + 4))
                 for i in range(nl)]
        met = [u32(data, deps + 4 * (j + i)) for i in range(nd)] + \
              [(a >> 4) - 1 for _, a in pairs if a >> 4]
        j, k = j + nd, k + nl
        back.append(back[-1] if marks & 4 else
                    outcome in (1, 2, 6) or any(key == 0xFFFFFFFF or key & 15 == 7
                                             for key, _ in pairs) or any(back[s] for s in met))
    return back


class Imports(unittest.TestCase):
    """check --snapshot S EXPORT (plan task 6.2.5, step SN4; ADR 0020 D5):
    the export read on into S's tier, every declaration for which the import
    rule I1 holds taken from S, the rest checked. Both ways: the report is
    the export's fresh check's, field by field (verdicts, details, fuel,
    counts, exit status) but for the mode, the snapshot member and each
    declaration's provenance, which say exactly which were taken (i)-(vii);
    a fresh check is unchanged (ix: the other classes' pinned reports)."""

    schema = Snapshots.schema

    def setUp(self):
        self.dir = Path(tempfile.mkdtemp(prefix="leanforth-imports-"))

    def tearDown(self):
        shutil.rmtree(self.dir)

    def snapshot(self, *args, name="s.lfsnap"):
        path = self.dir / name
        status, _, _ = run("check", "--save-snapshot", str(path), *args)
        self.assertTrue(path.exists(), (status, args))
        return path

    def edited(self, lines, name):
        path = self.dir / name
        path.write_text(ndjson_text(lines))
        return ["--no-manifest", str(path)]

    def both_ways(self, snap, args, taken, other=0, extra=()):
        """The export checked fresh and against snap: the same report but
        for the labels; exactly the names taken are from the snapshot."""
        status, fresh, _ = report(*extra, *args)
        again, got, _ = report("--snapshot", str(snap), *extra, *args)
        self.assertEqual(self.schema.errors(got), [], args)
        # The input's sizes count the snapshot's records too (one tier).
        keys = ("schemaVersion", "measured", "mode", "snapshot", "input")
        self.assertEqual((again, Snapshots.plain(got, keys)),
                         (status, Snapshots.plain(fresh, keys)), args)
        self.assertEqual(got["input"]["declarations"], fresh["input"]["declarations"], args)
        names = [d["name"] for d in got["declarations"]]
        provenance = {d["name"]: d["provenance"] for d in got["declarations"]}
        self.assertEqual(sorted(n for n in names if provenance[n] == "snapshot"),
                         sorted(taken), args)
        self.assertEqual(got["snapshot"]["import"],
                         {"taken": len(taken), "checked": len(names) - len(taken),
                          "otherContent": other}, args)
        return got

    def test_i_own_export(self):
        """(i) the snapshot's own export: everything taken, as fresh, nested
        blocks included (plan step SN5: the names their checks made beyond
        the input are replayed), but what I1 keeps back (an exhausted, full
        or invalid verdict) and what reaches it; (v) two equal declarations
        of one name told apart."""
        for k, args in enumerate([[COMPOSITION], [FIXTURE], [CHAIN], [INDUCTIVE], [DEPENDENT],
                                  ["tests/cli/unfold.ndjson"], ["tests/cli/nested.ndjson"],
                                  ["--no-manifest", f"{CASES}/composition-twice.ndjson"],
                                  ["--no-manifest", f"{CASES}/composition-wrong-argument.ndjson"],
                                  ["--no-manifest", f"{CASES}/composition-unsafe.ndjson"],
                                  ["--no-manifest", "tests/core/reexport/kinds.ndjson"],
                                  [SHARING]]):
            snap = self.snapshot(*args, name=f"s{k}.lfsnap")
            status, fresh, _ = report(*args)
            back = kept_back(snap)
            names = [d["name"] for i, d in enumerate(fresh["declarations"]) if not back[i]]
            self.assertEqual(sum(back), 0, args)
            self.both_ways(snap, args, names)

    def test_dependent(self):
        """A library checked against its base: the base's declarations
        taken, the rest checked and labelled as resting on the snapshot;
        with --jobs too."""
        snap = self.snapshot(INDUCTIVE)
        got = self.both_ways(snap, [DEPENDENT], TWO + ["Two.cases", "Two.swap"])
        uses = {d["name"] for d in got["declarations"] if d["provenance"] == "uses-snapshot"}
        self.assertEqual(uses, {"Two.swap_swap", "Two.swap_swap_first", "Two.cases_first"})
        self.both_ways(snap, [DEPENDENT], TWO + ["Two.cases", "Two.swap"],
                       extra=("--jobs", "3"))
        self.both_ways(snap, [SIBLING], TWO + ["Two.swap"])

    def test_ii_proof_altered(self):
        """(ii) one proof altered: exactly it and its user checked again."""
        snap = self.snapshot(DEPENDENT)
        args = self.edited(swapped_minors(records(DEPENDENT), "swap_swap"), "altered.ndjson")
        names = [d["name"] for d in report(DEPENDENT)[1]["declarations"]]
        self.both_ways(snap, args, [n for n in names
                                    if n not in ("Two.swap_swap", "Two.swap_swap_first")],
                       other=1)

    def test_iii_forward_reference(self):
        """(iii) a declaration moved after its user: the user is not taken,
        and rejected as fresh; the moved one is taken."""
        snap = self.snapshot(DEPENDENT)
        lines = records(DEPENDENT)
        at = next(i for i, r in enumerate(lines) if r.get("thm", {}).get("name") == 32)
        user = next(i for i, r in enumerate(lines) if r.get("thm", {}).get("name") == 33)
        moved = lines[:at] + lines[at + 1:user + 1] + [lines[at]] + lines[user + 1:]
        names = [d["name"] for d in report(DEPENDENT)[1]["declarations"]]
        got = self.both_ways(snap, self.edited(moved, "moved.ndjson"),
                             [n for n in names if n != "Two.swap_swap_first"])
        verdicts = {d["name"]: d["verdict"] for d in got["declarations"]}
        self.assertEqual(verdicts["Two.swap_swap_first"], "rejected")

    def test_iv_name_reused(self):
        """(iv) a name of the snapshot reused with other content and no other
        link: checked, accepted as fresh, counted."""
        snap = self.snapshot(COMPOSITION)
        lines = records(FIXTURE)
        lines[1]["str"]["str"] = "composition"
        got = self.both_ways(snap, self.edited(lines, "reused.ndjson"), [], other=1)
        self.assertEqual(got["declarations"][0]["verdict"], "accepted")

    def test_vi_block_member_changed(self):
        """(vi) a block with one member changed (the recursor's K flag): the
        whole block checked, and every user of it."""
        snap = self.snapshot(INDUCTIVE)
        text = Path(INDUCTIVE).read_text().replace('"k":false', '"k":true')
        path = self.dir / "k.ndjson"
        path.write_text(text)
        self.both_ways(snap, ["--no-manifest", str(path)], [], other=4)

    def test_vii_full_slot(self):
        """(vii) a slot saved full is checked again, and nothing that reaches
        it is taken."""
        snap = self.snapshot(INDUCTIVE)
        data, table = sectioned(snap)
        put32(data, table[SLOTS][3] + 72 * 4, 6)   # Two.cases: full
        snap.write_bytes(bytes(resealed(data, table, SLOTS)))
        self.both_ways(snap, [INDUCTIVE], TWO + ["Two.swap"])

    def test_exhausted(self):
        """A slot saved exhausted is checked again: fuel used depends on how
        the tier numbers its records too (measured on a Mathlib prefix
        against Init's snapshot), so an exhausted verdict is not taken."""
        snap = self.snapshot("--fuel", "200", INDUCTIVE)
        self.assertEqual(kept_back(snap), [False] * 4 + [True, False])
        got = self.both_ways(snap, [INDUCTIVE], TWO + ["Two.swap"], extra=("--fuel", "200"))
        self.assertEqual(got["declarations"][4]["verdict"], "exhausted")

    def test_undecided_slot(self):
        """A lookup that meets a slot not taken is no match, even when its
        answer is the saved one: a crafted snapshot in which
        Two.swap_swap_first's lookup of Two.swap_swap answered invalid, as
        the too-early lookup of an export whose Two.swap_swap is checked
        again answers, and which depends on rfl instead."""
        snap = self.snapshot(DEPENDENT)
        data, table = sectioned(snap)
        slots, looks, deps = table[SLOTS][3], table[LOOKS][3], table[DEPS][3]
        first = sum(u32(data, slots + 72 * d + 40) for d in range(10))
        at = next(looks + 8 * (first + i) for i in range(u32(data, slots + 72 * 10 + 40))
                  if u32(data, looks + 8 * (first + i) + 4) >> 4 == 10
                  and u32(data, looks + 8 * (first + i)) & 15 == 0)
        put32(data, at + 4, 1)
        first = sum(u32(data, slots + 72 * d + 36) for d in range(10))
        self.assertEqual([u32(data, deps + 4 * (first + i)) for i in range(5)], [0, 1, 4, 7, 9])
        put32(data, deps + 4 * (first + 4), 8)
        snap.write_bytes(bytes(resealed(resealed(data, table, LOOKS), table, DEPS)))
        args = self.edited(swapped_minors(records(DEPENDENT), "swap_swap"), "altered.ndjson")
        names = [d["name"] for d in report(DEPENDENT)[1]["declarations"]]
        self.both_ways(snap, args, [n for n in names
                                    if n not in ("Two.swap_swap", "Two.swap_swap_first")],
                       other=1)

    def test_refused(self):
        """The snapshot refused before the export is read; the export's
        own failures stay the export's; a refused snapshot lists no
        verdict."""
        snap = self.snapshot(FIXTURE)
        status, out, _ = run("check", "--snapshot", str(snap), "--fuel", "5", INDUCTIVE)
        self.assertEqual((status, out.splitlines()[0]),
                         (4, "error: invalid: the snapshot was refused: fuel"))
        status, got, _ = report("--snapshot", str(snap), "--fuel", "5", INDUCTIVE)
        self.assertEqual((status, got["declarations"], got["read"]["phase"]),
                         (4, [], "snapshot"))
        status, out, _ = run("check", "--snapshot", str(snap), "--no-manifest", "README.md")
        self.assertEqual(status, 4)
        self.assertNotIn("the snapshot was refused", out)
        status, out, _ = run("check", "--snapshot", str(snap), "tests/cli/no-such.ndjson")
        self.assertEqual(status, 4)


class Layers(unittest.TestCase):
    """Layered snapshots (ADR 0020 amendment 1, F5; plan step SN4): check
    --snapshot BASE --save-snapshot LAYER EXPORT writes only what the run
    added to BASE, with BASE's identity; --snapshot BASE --snapshot LAYER
    ... loads them in order: base and layer report what base and the
    dependent export checked against it did; two layers written on one
    base load together, sharing what both hold; a layer on another base, a
    layer given first, and a name two layers declare with other content are
    refused."""

    def setUp(self):
        self.dir = Path(tempfile.mkdtemp(prefix="leanforth-layers-"))
        self.base = self.dir / "base.lfsnap"
        self.assertEqual(run("check", "--save-snapshot", str(self.base), INDUCTIVE)[0], 0)

    def tearDown(self):
        shutil.rmtree(self.dir)

    def layer(self, name, *args):
        path = self.dir / name
        status, got, _ = report("--snapshot", str(self.base), "--save-snapshot", str(path),
                                *args)
        self.assertTrue(path.exists(), (status, args))
        return path, got

    def test_layer_as_its_run(self):
        layer, got = self.layer("dependent.lfsnap", DEPENDENT)
        data, table = sectioned(layer)
        base, _ = sectioned(self.base)
        self.assertEqual((u32(data, 24 + 4 * 7), data[56:88]),
                         (1, hashlib.sha256(bytes(base[:4064])).digest()))
        self.assertEqual(table[SLOTS][2], 7)          # Eq's block, rfl and the three new ones
        status, loaded, _ = report("--snapshot", str(self.base), "--snapshot", str(layer))
        self.assertEqual(Imports.schema.errors(loaded), [])
        def fields(report):
            return {d["name"]: {k: v for k, v in d.items() if k not in ("index", "provenance")}
                    for d in report["declarations"]}
        self.assertEqual(fields(loaded), fields(got))
        self.assertEqual({d["provenance"] for d in loaded["declarations"]}, {"snapshot"})
        again, imported, _ = report("--snapshot", str(self.base), "--snapshot", str(layer),
                                    DEPENDENT)
        keys = ("schemaVersion", "measured", "mode", "snapshot", "input")
        self.assertEqual((again, Snapshots.plain(imported, keys)),
                         (status, Snapshots.plain(got, keys)))
        self.assertEqual(imported["snapshot"]["import"]["checked"], 0)

    def test_twin_lookups(self):
        """A layer's declaration equal to a loaded one in content and verdict but
        not in its lookups (review rvSS 1; plan task 6.2.5b): nested.ndjson with an
        axiom named as a nested block's auxiliary type, _nested.List_1 (review rvSS's
        nested-aux), checked against nested's snapshot, checks R's and Q's blocks and
        their users again (their checks ask that name and find it) and saves them in
        a layer; against base and layer every declaration is taken (94 of 108 while
        the layer's slot was merged into the base's), each with a fresh check's
        verdict and fuel; base and layer loaded alone hold each name once."""
        lines = (ROOT / "tests/cli/nested.ndjson").read_text().splitlines(keepends=True)
        aux = self.dir / "nested-aux.ndjson"
        aux.write_text("".join(lines[:1768]) + '{"in":363,"str":{"pre":0,"str":"_nested"}}\n'
                       '{"in":364,"str":{"pre":363,"str":"List_1"}}\n'
                       '{"axiom":{"isUnsafe":false,"levelParams":[],"name":364,"type":3}}\n'
                       + "".join(lines[1768:]))
        base = self.dir / "nested.lfsnap"
        self.assertEqual(run("check", "--save-snapshot", str(base), "tests/cli/nested.ndjson")[0],
                         0)
        path = self.dir / "aux.lfsnap"
        status, got, _ = report("--snapshot", str(base), "--save-snapshot", str(path),
                                "--no-manifest", str(aux))
        self.assertEqual((status, got["snapshot"]["import"]["checked"]), (0, 15))
        _, fresh, _ = report("--no-manifest", str(aux))
        status, both, _ = report("--snapshot", str(base), "--snapshot", str(path),
                                 "--no-manifest", str(aux))
        self.assertEqual((status, both["snapshot"]["import"]["taken"]), (0, 108))
        def fields(report):
            return [(d["name"], d["verdict"], d["fuel"]) for d in report["declarations"]]
        self.assertEqual(fields(both), fields(fresh))
        status, alone, _ = report("--snapshot", str(base), "--snapshot", str(path))
        names = [d["name"] for d in alone["declarations"]]
        self.assertEqual((status, len(names), len(set(names))), (0, 108, 108))

    def test_siblings(self):
        one, _ = self.layer("dependent.lfsnap", DEPENDENT)
        two, sib = self.layer("sibling.lfsnap", SIBLING)
        status, got, _ = report("--snapshot", str(self.base), "--snapshot", str(one),
                                "--snapshot", str(two))
        names = [d["name"] for d in got["declarations"]]
        self.assertEqual((status, len(names), len(set(names))), (0, 15, 15))
        self.assertEqual(names[-2:], ["Two.swap_first", "Two.swap_second"])
        status, both, _ = report("--snapshot", str(self.base), "--snapshot", str(two),
                                 "--snapshot", str(one), SIBLING)
        self.assertEqual((status, both["snapshot"]["import"]["checked"]), (0, 0))

    def test_refused(self):
        one, _ = self.layer("dependent.lfsnap", DEPENDENT)
        other = self.dir / "other.lfsnap"
        run("check", "--save-snapshot", str(other), DEPENDENT)
        clash, _ = self.layer("clash.lfsnap", *Imports.edited(
            self, swapped_minors(records(DEPENDENT), "swap_swap"), "altered.ndjson"))
        for args, why in [
                ([one, self.base], "unsupported: the snapshot was refused: layer"),
                ([other, one], "invalid: the snapshot was refused: base snapshot of the layer"),
                ([self.base, one, clash], "invalid: the snapshot was refused: a name of two "
                                          "snapshots with other content (record 5)")]:
            options = [x for path in args for x in ("--snapshot", str(path))]
            status, out, _ = run("check", *options)
            self.assertEqual((status, out.splitlines()[0]), (2 if "unsupported" in why else 4,
                                                             f"error: {why}"), args)
            status, got, _ = report(*options)
            self.assertEqual(got["declarations"], [], args)
        status, out, _ = run("check", "--snapshot", str(self.base), "--snapshot", str(one),
                             "--save-snapshot", str(self.dir / "x"), DEPENDENT)
        self.assertEqual((status, out.splitlines()[0]),
                         (4, "error: --save-snapshot writes a layer on one snapshot only"))
        # The base with another information text: the same records and
        # counts, another identity.
        data, table = sectioned(self.base)
        _, _, _, info, length = table[16]
        data[info + length - 2] ^= 0x20
        renamed = self.dir / "renamed.lfsnap"
        renamed.write_bytes(bytes(resealed(data, table, 16)))
        status, out, _ = run("check", "--snapshot", str(renamed), "--snapshot", str(one))
        self.assertEqual((status, out.splitlines()[0]), (4, "error: invalid: the snapshot was "
                         "refused: base snapshot of the layer"))
        # Eq's block, which both layers hold, with another fuel in one.
        two, _ = self.layer("sibling.lfsnap", SIBLING)
        data, table = sectioned(two)
        put32(data, table[SLOTS][3] + 4 * 7, u32(data, table[SLOTS][3] + 4 * 7) + 1)
        two.write_bytes(bytes(resealed(data, table, SLOTS)))
        status, out, _ = run("check", "--snapshot", str(self.base), "--snapshot", str(one),
                             "--snapshot", str(two))
        self.assertEqual((status, out.splitlines()[0]), (4, "error: invalid: the snapshot was "
                         "refused: a declaration of two snapshots with other verdicts (record 0)"))

    def test_reported(self):
        """Every layer loaded is named in the text and the JSON report, with
        its identity, its export's and its base's (review rvSN4 M1)."""
        one, _ = self.layer("dependent.lfsnap", DEPENDENT)
        options = ["--snapshot", str(self.base), "--snapshot", str(one)]
        status, out, _ = run("check", *options)
        sha = hashlib.sha256(sectioned(one)[0][:4064]).hexdigest()
        self.assertEqual(status, 0)
        self.assertIn(f"layer: {one} (sha256 {sha}), export sha256 "
                      f"{hashlib.sha256(Path(DEPENDENT).read_bytes()).hexdigest()}, "
                      f"verdict version {verdict_version()}, on the snapshot above", out.splitlines())
        status, got, _ = report(*options)
        self.assertEqual(Imports.schema.errors(got), [])
        self.assertEqual([(x["file"], x["sha256"], x["base"]) for x in got["snapshot"]["layers"]],
                         [(str(one), sha, got["snapshot"]["sha256"])])
        self.assertEqual(report("--snapshot", str(self.base))[1]["snapshot"]["layers"], [])

    def test_member_clash(self):
        """A layer whose block declares, as a constructor, a name of the
        base with other content: refused, whichever member holds the name
        (review rvSN4 M2), when loaded and as an import's base."""
        base = self.dir / "fixture.lfsnap"
        run("check", "--save-snapshot", str(base), FIXTURE)
        lines = records(INDUCTIVE)
        renamed = next(r for r in lines if r.get("str", {}).get("str") == "first")
        renamed["str"] = {"pre": 0, "str": "fixtureId"}
        args = Imports.edited(self, lines, "renamed.ndjson")
        path = self.dir / "clash.lfsnap"
        run("check", "--snapshot", str(base), "--save-snapshot", str(path), *args)
        why = ("error: invalid: the snapshot was refused: a name of two snapshots with other "
               "content (record 0)")
        for more in [[], args]:
            status, out, _ = run("check", "--snapshot", str(base), "--snapshot", str(path), *more)
            self.assertEqual((status, out.splitlines()[0]), (4, why), more)

    def test_record_twice(self):
        """A layer holding one expression twice (its second made a copy of
        its first): refused, never loaded as another tier (review rvSN4
        m1)."""
        one, _ = self.layer("dependent.lfsnap", DEPENDENT)
        data, table = sectioned(one)
        exprs = table[7][3]
        data[exprs + 16:exprs + 32] = data[exprs:exprs + 16]
        one.write_bytes(bytes(resealed(data, table, 7)))
        status, out, _ = run("check", "--snapshot", str(self.base), "--snapshot", str(one))
        self.assertEqual((status, out.splitlines()[0]),
                         (4, "error: invalid: the snapshot was refused: expressions (record 1)"))

    def test_not_written(self):
        """No "written to" line when the run read nothing and so wrote
        nothing (review rvSN4 m2)."""
        target = self.dir / "never.lfsnap"
        status, out, _ = run("check", "--save-snapshot", str(target), "--no-manifest",
                             "README.md")
        self.assertEqual(status, 4)
        self.assertNotIn("snapshot: written to", out)
        self.assertIn("error: the snapshot was not written: invalid", out.splitlines())
        self.assertFalse(target.exists())


GOLDEN = ROOT / "tests/cli/golden-snapshots"
GOLDEN_EXPORTS = {   # the small pinned exports whose snapshots the guard keeps
    "composition": [COMPOSITION], "constant-fixture": [FIXTURE], "chain": [CHAIN],
    "inductive": [INDUCTIVE], "dependent": [DEPENDENT], "unfold": ["tests/cli/unfold.ndjson"],
    "nested": ["tests/cli/nested.ndjson"], "sharing": [SHARING],
    "kinds": ["--no-manifest", "tests/core/reexport/kinds.ndjson"],
    "composition-wrong-argument": ["--no-manifest",
                                   f"{CASES}/composition-wrong-argument.ndjson"],
    # == lets, one record (review rvSS G1): a let rule's change must bump too
    "let-b": ["tests/cli/let-b.ndjson"]}
SLOT_FIELDS = ["outcome", "marks", "provenance", "axioms", "warnings", "recipe", "shape",
               "fuel (low)", "fuel (high)", "dependencies", "lookups"]


def verdict_version():
    text = (ROOT / "src/kernel/verdict-version.fs").read_text()
    return int(re.search(r"^(\d+) constant lf-verdict-version$", text, re.M).group(1))


def golden_fields(path):
    """What the verdict version covers, read from a snapshot (ADR 0020 D3):
    the header's settings, the tier and identity sections (their SHA-256),
    and per slot its fields but the diagnostic, its dependencies and its
    lookups. The information section, which names the build, is left out."""
    data, table = sectioned(path)
    def section(i):
        return bytes(data[table[i][3]:table[i][3] + table[i][4]])
    _, _, n, slots, _ = table[SLOTS]
    deps, looks = table[DEPS][3], table[LOOKS][3]
    rows, j, k = [], 0, 0
    for d in range(n):
        fields = [u32(data, slots + 72 * d + 4 * f) for f in range(len(SLOT_FIELDS))]
        nd, nl = fields[9], fields[10]
        rows.append({"fields": fields,
                     "deps": [u32(data, deps + 4 * (j + i)) for i in range(nd)],
                     "looks": [[u32(data, looks + 8 * (k + i)), u32(data, looks + 8 * (k + i) + 4)]
                               for i in range(nl)]})
        j, k = j + nd, k + nl
    return {"verdictVersion": u32(data, 24 + 4 * 2),
            "header": [u32(data, 24 + 4 * f) for f in range(16)],
            "tier": hashlib.sha256(b"".join(section(i) for i in range(10))).hexdigest(),
            "identity": hashlib.sha256(section(10)).hexdigest(),
            "slots": rows}


def golden_text(fields):
    """One slot to a line, so that a change shows as a short diff."""
    head = {k: v for k, v in fields.items() if k != "slots"}
    lines = [json.dumps(head, separators=(",", ":"))[:-1] + ',"slots":[']
    lines += [json.dumps(r, separators=(",", ":")) + ("," if i + 1 < len(fields["slots"]) else "")
              for i, r in enumerate(fields["slots"])]
    return "\n".join(lines) + "\n]}\n"


def write_golden():
    """Write the guard's golden files again (after a verdict-version bump,
    whose commit must hold them): python3 tests/cli/test_leanforth.py
    --write-golden."""
    GOLDEN.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory() as tmp:
        for stem, args in GOLDEN_EXPORTS.items():
            path = Path(tmp) / f"{stem}.lfsnap"
            run("check", "--save-snapshot", str(path), *args)
            (GOLDEN / f"{stem}.json").write_text(golden_text(golden_fields(path)))
            print("written", GOLDEN / f"{stem}.json")


class VerdictGuard(unittest.TestCase):
    """The verdict-version guard (ADR 0020 D3; plan step SN5): the snapshot
    of each small pinned export, written now, has every field the verdict
    version covers as the golden one written with this verdict version.
    A change that moves one without bumping lf-verdict-version fails here;
    a bump makes the golden files stale, so its commit writes them again
    (write_golden). Only what these exports reach is guarded; ADR 0020 D3's
    both-ways comparison on Init and a Mathlib prefix covers the rest."""

    def test_golden(self):
        version = verdict_version()
        with tempfile.TemporaryDirectory() as tmp:
            for stem, args in GOLDEN_EXPORTS.items():
                golden = json.loads((GOLDEN / f"{stem}.json").read_text())
                self.assertEqual(golden["verdictVersion"], version,
                                 f"{stem}: golden snapshot of another verdict version (stale): "
                                 "write them again, python3 tests/cli/test_leanforth.py "
                                 "--write-golden")
                path = Path(tmp) / f"{stem}.lfsnap"
                run("check", "--save-snapshot", str(path), *args)
                now = golden_fields(path)
                for key in ("header", "tier", "identity"):
                    self.assertEqual(now[key], golden[key], f"{stem}: {key}")
                self.assertEqual(len(now["slots"]), len(golden["slots"]), stem)
                moved = [f"slot {d} {name}: {a} -> {b}"
                         for d, (g, s) in enumerate(zip(golden["slots"], now["slots"]))
                         for name, a, b in
                         [(SLOT_FIELDS[f], g["fields"][f], s["fields"][f])
                          for f in range(len(SLOT_FIELDS))] +
                         [("dependencies", g["deps"], s["deps"]), ("lookups", g["looks"], s["looks"])]
                         if a != b]
                self.assertEqual(moved[:10], [], f"{stem}: a field the verdict version covers "
                                 "moved without a bump of lf-verdict-version")


if __name__ == "__main__":
    if sys.argv[1:] == ["--write-golden"]:
        write_golden()
        sys.exit(0)
    unittest.main()
