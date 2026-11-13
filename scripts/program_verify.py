#!/usr/bin/env python3
"""leanforth verify, driver v0 (plan 8.4.1b; docs/design/VERIFY_COMMAND.md).

Usage (from any folder; the files must lie inside the LeanForth checkout):
  python3 scripts/program_verify.py SOURCE.fs --contract CONTRACT [--out DIR]
      [--fuel N] [--jobs N] [--memory-per-check MB] [--checked]
      [--lean-time-limit SECONDS] [--keep-export] [--paths-limit N] [--search-limit N]
      [--detail]

Checks one Forth word against one contract (contract language 0.1,
docs/programming/PROGRAM_VC.md), the pipeline of plan 5.5.1 for any word:

  1 the program words (src/program/verify.fs, ADR 0019) write the IR of
    SOURCE.fs, hashed before and after;
  2 the contract is read and its `ir` file must be that IR byte for byte;
  3 the untrusted generator (scripts/program_vc.py) writes the obligations,
    the contract theorem and their tactic scripts for this contract alone,
    within a path limit and a counterexample-search limit, or a theorem
    `refuted` when it finds inputs that break the contract;
  4 pinned Lean 4.35.0 compiles that file, which writes the proofs, prints
    the program back (it must equal the IR) and reports `#print axioms`;
    scripts/export.sh exports the theorems with every declaration they use,
    and the manifest;
  6 LeanForth's checker (bin/leanforth check --json, a final run, no
    snapshot) checks the export: the only judge;
  7 each accepted theorem's axioms must be Lean's own;
  8 the receipt (schema 0.3, docs/programming/PROGRAM_RECEIPTS.md) is
    written atomically (a .partial file, then renamed), with the evidence
    record beside it; RUN is `not-run` (plan 8.4.2).

Lean writes the proofs and LeanForth's checker re-checks them; LeanForth
writes no proof. A receipt is about the IR, under the assumptions it lists,
and never about compiled code. It says `discharged` only when LeanForth
accepted the contract theorem, every obligation's theorem and every
declaration of the export, each theorem with allowlisted axioms equal to
Lean's; `refuted` only when it accepted the theorem `refuted`.

Writes in --out (default verify-out/WORD in the current folder), after
removing by name the files an earlier run wrote there: obligations.lean,
WORD.ndjson (removed after the check unless --keep-export),
WORD.ndjson.manifest.json, WORD.evidence.json and WORD.receipt.json.

Prints one line per step, `error: CODE: MESSAGE` for each problem, and a
summary line that says `discharged` or `NOT VERIFIED`; --detail also
prints the postcondition as Lean printed it in this run. Exit status, the
CLI's (most severe first: 5, 4, 1, 3, 2, 6, 0): 0 discharged; 1 refuted;
2 undecided (unsupported, Lean failed, LeanForth unsupported or unknown);
3 a resource limit; 4 malformed input, a file outside the checkout, a tool
not found; 5 an internal fault, or the two checkers disagree (LeanForth
rejected what Lean accepted; any Python fault too, never 1); 6 a theorem
NOT PROVED (an axiom outside the allowlist). Problem codes: CODES below
and docs/programming/PROGRAM_VERIFY.md. Untrusted tooling: the receipt
is checked by `python3 scripts/program_receipt.py validate`.

Tools: the checkout's pinned Lean 4.35.0 and its leanexport, whatever LEAN
and LEANEXPORT say, except under LEANFORTH_VERIFY_TEST_TOOLS=1, which the
test suites set (stand-ins, the Lean cache); Gforth is $GFORTH, else the
checkout's, else gforth on the PATH. The evidence record names each tool
run with its SHA-256.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import traceback


def crashed(kind, error, trace):
    """An exception nothing caught is an internal fault, exit status 5 (review M1):
    Python's own status 1 would read as refuted."""
    traceback.print_exception(kind, error, trace)
    print(f"error: internal: {kind.__name__}: {error}", flush=True)
    os._exit(5)


sys.excepthook = crashed
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "tests" / "support"))
import program_receipt as receipts  # noqa: E402
import program_vc  # noqa: E402
from schema_subset import InstanceError, load_strict  # noqa: E402

VERSION = "0.1"
GENERATOR = {"name": "python", "version": f"program_vc.py {program_vc.GENERATOR_VERSION}"}
# A path receipt 0.3 can name: relative, inside the checkout, no segment starting with a dot.
RECEIPT_PATH = re.compile(r"[A-Za-z0-9_][A-Za-z0-9_.-]*(/[A-Za-z0-9_][A-Za-z0-9_.-]*)*")
LOCATION = re.compile(r" @\d+:\d+$")   # an IR line's source location
PROGRAM_WORDS_LIMIT = 600   # seconds for the program words (they read one file)
PINNED_LEAN = (ROOT / ".tools" / "elan" / "toolchains" / "leanprover--lean4---v4.35.0"
               / "bin" / "lean")
TEST_TOOLS = "LEANFORTH_VERIFY_TEST_TOOLS"   # =1: LEAN and LEANEXPORT are honoured (tests only)
# Appended to the generator's file: Lean prints the postcondition and the whole theorem
# (the contract theorem with its pre hypotheses, or refuted) as it elaborated them, the
# statement that is proved, for the report and the evidence (review B1).
POST_PRINT = ("\n-- Added by leanforth verify: what is proved, as Lean elaborated it.\n"
              '#eval IO.println "vc-post-begin"\n#print {namespace}.post\n'
              '#eval IO.println "vc-post-end"\n'
              '#eval IO.println "vc-statement-begin"\n#check {theorem}\n'
              '#eval IO.println "vc-statement-end"\n')
# The declarations the generator writes outside a contract's namespace, and the auxiliary
# lemmas Lean adds under a declaration (`O1._proof_1_4`, `contract._simp_1_7`: abstracted
# proofs and simp lemmas; any other name under them is refused).
COMMON_NAMES = ("ir_max", "ir_min", "ir_cell_min", "ir_shift_one", "ir_not_lt", "cells64")
AUXILIARY = r"\._(proof|simp)_\d+(_\d+)*"

# Each problem code: its exit status (None: given with the problem) and its step.
CODES = {
    "usage": (4, "command-line"),
    "outside-folder": (4, "command-line"),
    "gforth-not-found": (4, "read-word"),
    "source-unreadable": (4, "read-word"),
    "source-refused": (None, "read-word"),
    "source-changed": (4, "read-word"),
    "contract-unreadable": (4, "read-contract"),
    "contract-malformed": (4, "read-contract"),
    "word-not-found": (4, "read-contract"),
    "contract-ir-differs": (4, "read-contract"),
    "ir-needs-receipt-0.4": (2, "generate"),
    "generator-unsupported": (2, "generate"),
    "paths-limit": (3, "generate"),
    "search-limit": (3, "generate"),
    "lean-not-found": (4, "prove"),
    "lean-failed": (2, "prove"),
    "lean-time-limit": (3, "prove"),
    "program-print-back-differs": (5, "prove"),
    "export-failed": (5, "prove"),
    "file-changed": (4, None),
    "export-invalid": (4, "check"),
    "export-differs": (5, "check"),
    "checkers-disagree": (5, "check"),
    "proof-undecided": (2, "check"),
    "proof-exhausted": (3, "check"),
    "not-proved": (6, "check"),
    "axioms-differ": (5, "decide"),
    "internal": (5, None),
    "receipt-not-written": (4, "write"),
}
SEVERITY = (5, 4, 1, 3, 2, 6, 0)   # the CLI's order: the first that occurs is the status
# The program words' outcome (ADR 0008) when they refuse the source, as an exit status.
REFUSED_STATUS = {1: 4, 2: 3, 3: 2, 4: 1, 5: 2, 6: 3}
# LeanForth's verdicts other than accepted, as problem codes; any other verdict (invalid,
# not checked, a theorem missing, a stopped run) is an internal fault. Each kind found is
# reported, so the exit status follows the CLI's order, as bin/leanforth check's does.
# Lean accepted every declaration before LeanForth checks the export, so a rejection is
# the two checkers disagreeing (review M1): one of them is wrong, status 5.
VERDICT_PROBLEMS = [("checkers-disagree", {"rejected"}),
                    ("proof-undecided", {"unknown", "unsupported"}),
                    ("proof-exhausted", {"exhausted", "full"})]


class Problem(Exception):
    """A problem that ends the run with no receipt: its code, message and exit status."""

    def __init__(self, code, message, status=None):
        super().__init__(message)
        self.code, self.message = code, message
        self.status = CODES[code][0] if status is None else status


class Parser(argparse.ArgumentParser):
    def error(self, message):
        raise Problem("usage", message)


def positive(text):
    if not re.fullmatch(r"[0-9]{1,15}", text) or int(text) < 1:
        raise argparse.ArgumentTypeError(f"not a whole number of at least 1: {text}")
    return int(text)


def parse(argv):
    parser = Parser(prog="program_verify.py", description=__doc__.splitlines()[0])
    parser.add_argument("source", metavar="SOURCE.fs")
    parser.add_argument("--contract", required=True)
    parser.add_argument("--out")
    parser.add_argument("--fuel", type=positive)
    parser.add_argument("--jobs", type=positive, default=int(receipts.LEANFORTH_JOBS))
    parser.add_argument("--memory-per-check", type=positive, metavar="MB")
    parser.add_argument("--checked", action="store_true")
    parser.add_argument("--lean-time-limit", type=positive, default=1800, metavar="SECONDS")
    parser.add_argument("--keep-export", action="store_true")
    parser.add_argument("--detail", action="store_true")
    parser.add_argument("--paths-limit", type=positive, default=program_vc.PATHS_LIMIT)
    parser.add_argument("--search-limit", type=positive, default=program_vc.SEARCH_LIMIT)
    return parser.parse_args(argv)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def short(sha):
    return sha[:8] + "…"


def file_sha(relative):
    """The SHA-256 of a file of the checkout, or None when it cannot be read."""
    try:
        return digest((ROOT / relative).read_bytes())
    except OSError:
        return None


def checkout_path(given, what):
    """A path given on the command line (relative to the current folder) as the path
    relative to the checkout that receipt 0.3 names; outside-folder when it has none."""
    absolute = Path(os.path.realpath(given))
    try:
        relative = absolute.relative_to(ROOT).as_posix()
    except ValueError:
        raise Problem("outside-folder", f"{what} {given} is outside the LeanForth checkout "
                      f"{ROOT}: receipt 0.3 names files inside it only (plan 8.4.1j)") from None
    if not RECEIPT_PATH.fullmatch(relative):
        raise Problem("outside-folder", f"{what} {given} is not a path receipt 0.3 can name "
                      "(segments of letters, digits, _ . -, none starting with a dot)")
    return relative


def safe_name(word):
    """A file name for a word: its characters outside letters, digits, _ . - as _."""
    name = re.sub(r"[^A-Za-z0-9_.-]", "_", word)
    return name if re.match(r"[A-Za-z0-9_]", name) else "_" + name


def find_gforth():
    """$GFORTH, else the checkout's pinned Gforth, else gforth on the PATH."""
    pinned = ROOT / ".tools" / "gforth" / "bin" / "gforth"
    return os.environ.get("GFORTH") or (str(pinned) if pinned.is_file() else "gforth")


def test_tools():
    return os.environ.get(TEST_TOOLS) == "1"


def tool_record(tool):
    """A tool as the evidence names it: its path (relative to the checkout when inside it)
    and the SHA-256 of its file, or None when it is not a file."""
    found = tool if "/" in tool else shutil.which(tool)
    if not found or not Path(found).is_file():
        return {"path": tool, "sha256": None}
    absolute = os.path.abspath(found)
    inside = absolute.startswith(str(ROOT) + os.sep)
    return {"path": os.path.relpath(absolute, ROOT) if inside else absolute,
            "sha256": digest(Path(absolute).read_bytes())}


def runnable(tool):
    """Whether tool names a program that can be started."""
    if "/" in tool:
        return Path(tool).is_file() and os.access(tool, os.X_OK)
    return shutil.which(tool) is not None


class Tools:
    """Starts the tools, each in a process group of its own, so that a time limit or a
    signal stops the tool and everything it started."""

    def __init__(self):
        self.active = None

    def run(self, args, limit=None, env=None, cwd=ROOT):
        """The finished process (CompletedProcess), run in cwd; TimeoutExpired after limit
        seconds, OSError when it cannot be started."""
        self.active = subprocess.Popen(
            args, cwd=cwd, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, text=True, errors="replace", start_new_session=True,
            env=None if env is None else dict(os.environ, **env))
        try:
            out, err = self.active.communicate(timeout=limit)
        except subprocess.TimeoutExpired:
            self.stop()
            raise
        finally:
            process, self.active = self.active, None
        return subprocess.CompletedProcess(args, process.returncode, out, err)

    def stop(self, *_):
        """Kill the running tool's process group (on a time limit or a signal)."""
        if self.active is not None:
            try:
                os.killpg(self.active.pid, signal.SIGKILL)
            except OSError:
                pass
            self.active.communicate()


def printed_programs(output):
    """The programs Lean printed back: {name: lines} from vc-program ... vc-program-end."""
    programs, name, lines = {}, None, []
    for line in output.splitlines():
        if line.startswith("vc-program-end"):
            programs[name], name = lines, None
        elif line.startswith("vc-program "):
            name, lines = line.split()[1], []
        elif name is not None:
            lines.append(line)
    return programs


def lean_errors(output):
    """Lean's first error lines, for a message."""
    errors = [line for line in output.splitlines() if "error" in line]
    return "; ".join(errors[:3]) or output.strip()[-300:] or "no output"


def numbered(assumptions):
    """The assumptions with ids A1, A2, ... in order."""
    return [dict(a, id=f"A{i}") for i, a in enumerate(assumptions, 1)]


def axioms_text(axioms):
    return ", ".join(axioms) or "none"


class Verify:
    """One run of leanforth verify: the steps of the design's §4, each printing its line."""

    def __init__(self, args):
        self.args, self.tools, self.source = args, Tools(), args.source
        self.problems, self.word, self.receipt_path, self.verdict = [], None, None, None
        self.export = self.out = self.files = self.vc = self.gen = None
        self.lean = self.leanforth = self.manifest = None
        self.check_status = "not-checked"
        self.tool_files, self.evidence_ref = {}, None

    # ------------------------------------------------------------------ output

    def say(self, line):
        print(line, flush=True)

    def problem(self, code, message, status=None):
        """Record a problem the run goes on after (a receipt is still written)."""
        status = CODES[code][0] if status is None else status
        self.problems.append((code, message, status))
        self.say(f"error: {code}: {message}")

    def exit_status(self):
        found = {status for _, _, status in self.problems} | {self.verdict or 0}
        return next(s for s in SEVERITY if s in found)

    # --------------------------------------------------------------- the steps

    def run(self):
        """Every step; the exit status."""
        try:
            self.locate()
            os.chdir(ROOT)   # the generator and the receipt's helpers read paths from here
            self.read_word()
            self.read_contract()
            self.generate()
            if self.gen is not None and self.prove():
                self.check()
            self.write()
        except Problem as stop:
            self.problem(stop.code, stop.message, stop.status)
            self.say(f"{self.word or self.source}: NOT VERIFIED: {stop.code}; no receipt written")
        except receipts.Refusal as refusal:
            self.problem(refusal.problem, str(refusal))
            self.say(f"{self.word}: NOT VERIFIED: {refusal.problem}; no receipt written")
        except Exception as error:   # a fault of the driver's: never a verdict (exit 1)
            self.problem("internal", f"{type(error).__name__}: {error}")
            self.say(f"{self.word or self.source}: NOT VERIFIED: internal; no receipt written")
        finally:
            self.remove_export()
        return self.exit_status()

    def locate(self):
        """Step 0: the source, the contract and --out as paths inside the checkout."""
        self.cwd = os.getcwd()   # where the default --out lies
        self.source = checkout_path(self.args.source, "the source")
        self.contract_path = checkout_path(self.args.contract, "the contract")
        if self.args.out is not None:
            self.out = checkout_path(self.args.out, "--out")

    def read_word(self):
        """Step 1: the program words write the IR of the whole source file."""
        before = file_sha(self.source)
        if before is None:
            raise Problem("source-unreadable", f"{self.source} cannot be read")
        gforth = find_gforth()
        if not re.fullmatch(receipts.FORTH_PATH, self.source):
            raise Problem("outside-folder", f"{self.source} cannot be named in a Forth string")
        try:
            done = self.tools.run(receipts.program_words_args(gforth, self.source),
                                  PROGRAM_WORDS_LIMIT)
        except OSError as error:
            raise Problem("gforth-not-found", f"{gforth}: {error.strerror}") from None
        except subprocess.TimeoutExpired:
            raise Problem("internal", f"the program words ran over {PROGRAM_WORDS_LIMIT} s on "
                          f"{self.source}") from None
        if file_sha(self.source) != before:
            raise Problem("source-changed", f"{self.source} changed while the program words "
                          "read it")
        outcome, text, diagnostic = receipts.program_words_output(done.stdout)
        if done.returncode != 0 or outcome is None:
            raise Problem("internal", f"the program words ended with status {done.returncode} "
                          f"and no outcome: {(done.stdout + done.stderr)[-300:]}")
        if outcome != 0:
            raise Problem("source-refused", f"{self.source}: {diagnostic}",
                          REFUSED_STATUS.get(outcome, 5))
        self.source_sha, self.ir_text = before, text
        self.ir_sha = digest(text.encode("utf-8"))
        self.forth = self.forth_version(gforth)
        self.tool_files = {"gforth": tool_record(gforth)}

    def forth_version(self, gforth):
        """The Forth's name and version (gforth --version), for the receipt's tools."""
        try:
            done = self.tools.run([gforth, "--version"], 120)
        except (OSError, subprocess.TimeoutExpired) as error:
            raise Problem("internal", f"{gforth} --version: {error}") from None
        return ((done.stdout + done.stderr).split() + ["gforth", "unknown"])[:2]

    def read_contract(self):
        """Step 2: the contract, its word in the IR, and its ir file equal to the IR."""
        try:
            data = (ROOT / self.contract_path).read_bytes()
            text = data.decode("utf-8")
        except (OSError, UnicodeDecodeError) as error:
            raise Problem("contract-unreadable", f"{self.contract_path}: {error}") from None
        try:
            self.contract = program_vc.parse_contract(text, self.contract_path)
        except (program_vc.Malformed, ValueError, IndexError, KeyError, TypeError,
                RecursionError) as error:
            raise Problem("contract-malformed", str(error) or type(error).__name__) from None
        self.contract_sha = digest(data)
        self.word = self.contract["word"]
        self.prepare_out()
        if not re.search(rf"^word {re.escape(self.word)} @", self.ir_text, re.M):
            raise Problem("word-not-found", f"{self.source} defines no word {self.word} (names "
                          "are as the IR writes them, lower case)")
        ir_file = self.contract["ir"]
        if not RECEIPT_PATH.fullmatch(ir_file) or (ROOT / ir_file).resolve() != ROOT / ir_file:
            raise Problem("contract-malformed", f"{self.contract_path}: its ir line {ir_file} "
                          "does not name a file inside the checkout")
        try:
            named = (ROOT / ir_file).read_bytes()
        except OSError as error:
            raise Problem("contract-ir-differs", f"{ir_file}, the contract's IR file, cannot "
                          f"be read: {error.strerror}") from None
        if named != self.ir_text.encode("utf-8"):
            raise Problem("contract-ir-differs", f"{ir_file} is not the IR the program words "
                          f"write for {self.source}")
        line = receipts.word_line(self.ir_text, self.word)
        self.say(f"word: {self.word} {self.contract['stack']}, {self.source}:{line}, sha256 "
                 f"{short(self.source_sha)}")
        version = self.ir_text.split("\n", 1)[0].split()[-1]
        self.say(f"IR: {version}, sha256 {short(self.ir_sha)}, equal to {ir_file}")
        self.say(f"contract: {self.contract['id']}, {self.contract_path}, sha256 "
                 f"{short(self.contract_sha)}")

    def prepare_out(self):
        """The --out folder (default verify-out/WORD here), with the files an earlier run
        wrote there removed by name, so that none is read as this run's."""
        self.name = safe_name(self.word)
        if self.out is None:
            self.out = checkout_path(os.path.join(self.cwd, "verify-out", self.name), "--out")
        self.files = {"lean": f"{self.out}/obligations.lean",
                      "export": f"{self.out}/{self.name}.ndjson",
                      "manifest": f"{self.out}/{self.name}.ndjson.manifest.json",
                      "evidence": f"{self.out}/{self.name}.evidence.json",
                      "receipt": f"{self.out}/{self.name}.receipt.json"}
        try:
            (ROOT / self.out).mkdir(parents=True, exist_ok=True)
            for key in ("lean", "export", "manifest", "evidence", "receipt"):
                for path in (self.files[key], self.files[key] + ".partial"):
                    (ROOT / path).unlink(missing_ok=True)
        except OSError as error:
            raise Problem("receipt-not-written", f"{self.out}: {error}") from None

    def generate(self):
        """Step 3: the obligations, the contract theorem (or `refuted`) and their proof
        scripts for this contract alone, within the path and search limits."""
        receipts.refuse_ir_02(self.ir_text, self.contract["ir"])
        limits = (self.args.paths_limit, self.args.search_limit)
        try:
            text, summary, generators = program_vc.generate_parsed(
                [(self.contract, self.ir_text)], limits)
        except program_vc.Limit as limit:
            raise Problem(limit.code, str(limit)) from None
        except program_vc.Malformed as error:
            raise Problem("contract-malformed", str(error)) from None
        self.vc, self.gen = summary[0], generators[0]
        for note in self.vc.get("searchNotes", []):
            self.say(f"note: search: {note}")
        if self.gen is None:
            self.say(f"obligations: none, from the untrusted generator {GENERATOR['version']}")
            self.problem("generator-unsupported", self.vc["reason"])
            return
        if self.vc["status"] == "refuted":
            self.say(f"obligations: none: the untrusted generator {GENERATOR['version']} found "
                     "inputs that break the contract")
            self.say(f"  refutation: {self.refutation()}")
        else:
            self.say(f"obligations: {len(self.vc['obligations'])}, from the untrusted "
                     f"generator {GENERATOR['version']}")
            for o in self.vc["obligations"]:
                self.say(f"  {o['id']}: {receipts.obligation_text(o)}")
        main = self.vc["theorems"][-1]   # the contract theorem, or refuted
        text += POST_PRINT.format(namespace=self.vc["namespace"], theorem=main)
        self.lean_text = text
        try:
            (ROOT / self.files["lean"]).write_text(text, encoding="utf-8")
        except OSError as error:
            raise Problem("receipt-not-written", f"{self.files['lean']}: {error}") from None

    def refutation(self):
        """The counterexample in words: the inputs, what the word does, and why it fails."""
        found = self.vc["counterexample"]
        combo = [found["inputs"][x] for x in self.contract["inputs"]]
        inputs = ", ".join(f"{x} = {v}" for x, v in found["inputs"].items())
        output = self.gen.output_on(combo)
        why = "the contract does not hold" if output.startswith("the IR fails") else \
            found["reason"]
        return f"on 64-bit cells with {inputs}, {output}; {why}"

    def lean_tool(self):
        """The pinned Lean, its version and commit: the checkout's, or under the test switch
        $LEAN (a stand-in or the Lean cache)."""
        lean = receipts.pinned_lean() if test_tools() else str(PINNED_LEAN)
        if not runnable(lean):
            raise Problem("lean-not-found", f"{lean} is not a program; install the pinned Lean "
                          "4.35.0 with scripts/install-lean.sh")
        try:
            version = self.tools.run([lean, "--version"], 120).stdout
            commit = self.tools.run([lean, "--githash"], 120).stdout.strip()
        except (OSError, subprocess.TimeoutExpired) as error:
            raise Problem("lean-not-found", f"{lean}: {error}") from None
        found = re.match(r"Lean \(version ([0-9.]+),", version)
        if not found or found.group(1) != "4.35.0":
            raise Problem("lean-not-found", f"{lean} is not Lean 4.35.0: {version.strip()[:80]}")
        self.tool_files["lean"] = tool_record(lean)
        return lean, {"version": found.group(1), "commit": commit}

    def exporter(self, lean):
        """LEANEXPORT for scripts/export.sh: the pinned toolchain's leanexport, or under the
        test switch $LEANEXPORT when set."""
        chosen = os.environ.get("LEANEXPORT") if test_tools() else None
        chosen = chosen or str(Path(lean).parent / "leanexport")
        self.tool_files["leanexport"] = tool_record(chosen)
        return chosen

    def prove(self):
        """Step 4a: pinned Lean writes the proofs (warnings are errors), prints the program
        back and reports the axioms; its exporter writes the theorems with their closure and
        the manifest. False when Lean failed (a receipt says so, nothing checked). Lean runs
        in --out on obligations.lean, so the module name it derives from the path, which the
        export's private names carry, is `obligations` whatever --out is: the same word and
        contract give the same export bytes in any folder."""
        lean, self.lean = self.lean_tool()
        theorems, written = self.vc["theorems"], digest(self.lean_text.encode("utf-8"))
        limit = self.args.lean_time_limit
        with tempfile.TemporaryDirectory() as folder:
            try:
                done = self.tools.run(receipts.lean_compile_args(
                    lean, Path(self.files["lean"]).name, folder), limit, cwd=ROOT / self.out)
            except subprocess.TimeoutExpired:
                self.problem("lean-time-limit", f"Lean ran over {limit} s on "
                             f"{self.files['lean']}; nothing was checked")
                return False
            self.unchanged(self.files["lean"], written)
            output = done.stdout + done.stderr
            if done.returncode != 0:
                self.problem("lean-failed", f"Lean failed on {self.files['lean']} (status "
                             f"{done.returncode}): {lean_errors(output)}")
                return False
            self.printed_back(output)
            for key in ("post", "statement"):
                self.lean[key] = self.printed(output, key)
                self.lean[f"{key}Sha256"] = digest(self.lean[key].encode("utf-8"))
            try:
                self.lean["axioms"] = receipts.lean_axioms(output, theorems)
            except SystemExit as error:
                raise Problem("internal", f"Lean's output: {error}") from None
            self.say("proofs: written by Lean 4.35.0 from the generator's tactic scripts; Lean "
                     "printed the program back equal to the IR")
            if self.args.detail:
                for key, what in (("statement", "the theorem"), ("post", "post")):
                    self.say(f"{what}, as Lean printed it in this run:")
                    for line in self.lean[key].splitlines():
                        self.say(f"  {line}")
            self.export = self.files["export"]
            try:
                done = self.tools.run(receipts.export_args(ROOT / self.files["export"],
                                                          theorems),
                                      limit, env={"LEAN_PATH": folder, "LEAN": lean,
                                                  "LEANEXPORT": self.exporter(lean)})
            except subprocess.TimeoutExpired:
                self.problem("lean-time-limit", f"Lean's exporter ran over {limit} s; nothing "
                             "was checked")
                return False
        if done.returncode != 0:
            raise Problem("export-failed", f"scripts/export.sh failed ({done.returncode}): "
                          f"{(done.stdout + done.stderr).strip()[-300:]}")
        try:
            self.manifest = receipts.read_json(ROOT / self.files["manifest"])
        except SystemExit as error:
            raise Problem("export-failed", f"no manifest: {error}") from None
        self.say(f"export: {self.export} and its manifest ({self.manifest['bytes']:,} bytes)")
        return True

    def unchanged(self, path, sha):
        if file_sha(path) != sha:
            raise Problem("file-changed", f"{path} changed during the run")

    def printed(self, output, key):
        """What Lean printed between the markers POST_PRINT adds (post, statement)."""
        found = re.search(rf"^vc-{key}-begin\n(.*?)^vc-{key}-end$", output, re.M | re.S)
        if not found or not found.group(1).strip():
            raise Problem("internal", f"Lean printed no {key}")
        return found.group(1)

    def printed_back(self, output):
        """Lean's print-back of the generated program must be the IR (without locations)."""
        name = self.vc["namespace"].split(".")[-1]
        printed = printed_programs(output).get(name)
        ir = [LOCATION.sub("", line) for line in self.ir_text.splitlines()]
        if printed != ir:
            raise Problem("program-print-back-differs", "the program Lean printed back is not "
                          f"the IR of {self.source}: the generator's translation is wrong")

    def check_options(self):
        a = self.args
        return (["--jobs", str(a.jobs)] + (["--fuel", str(a.fuel)] if a.fuel else [])
                + (["--memory-per-check", str(a.memory_per_check)] if a.memory_per_check else [])
                + (["--checked"] if a.checked else []))

    def theorem_names(self):
        """The theorems the receipt lists: the contract theorem, then the obligations'; or
        the theorem refuted."""
        if self.vc["status"] == "refuted":
            return list(self.vc["theorems"])
        return [f"{self.vc['namespace']}.contract"] + [o["theorem"]
                                                         for o in self.vc["obligations"]]

    def check(self):
        """Steps 6 and 7: LeanForth's final check of the export, its verdicts as the check
        status, and each accepted theorem's axioms against Lean's."""
        names, export = self.theorem_names(), self.files["export"]
        hashes = (file_sha(export), file_sha(self.files["manifest"]))
        try:
            identity = receipts.leanforth_identity()
            done = self.tools.run(receipts.leanforth_args(ROOT / export, self.check_options()))
        except (OSError, SystemExit) as error:
            raise Problem("internal", f"LeanForth's checker could not run: {error}") from None
        self.unchanged(export, hashes[0])
        self.unchanged(self.files["manifest"], hashes[1])
        try:
            report = load_strict(done.stdout)
            read, counts = report["read"]["outcome"], report["counts"]
        except (InstanceError, ValueError, KeyError, TypeError) as error:
            self.leanforth = {**identity, "exitStatus": done.returncode, "declarations": 0,
                              "accepted": 0, "theorems": receipts.leanforth_theorems(
                                  {"declarations": []}, names)}
            self.check_status = "failed"
            self.problem("internal", f"LeanForth's check gave no report (status "
                         f"{done.returncode}): {error}; {done.stderr.strip()[-200:]}")
            return
        if (report.get("schema"), report.get("schemaVersion")) != (
                "leanforth-check-report", "0.4") or "snapshot" in report:
            raise Problem("internal", "LeanForth's report is not a final run's check report "
                          f"0.4: {report.get('schemaVersion')!r}, snapshot "
                          f"{'snapshot' in report}")
        if read != "ok" or done.returncode == 4 or counts is None:
            raise Problem("export-invalid", f"LeanForth refused the export {export}: "
                          f"{json.dumps(report['read'])[:300]}")
        self.leanforth = {**identity, "exitStatus": done.returncode,
                          "declarations": counts["declarations"], "accepted": counts["accepted"],
                          "counts": counts, "theorems": receipts.leanforth_theorems(report, names)}
        self.namespace_problems(report)
        self.decide(report, names)

    def namespace_problems(self, report):
        """The export's declarations named in the generator's ProgramVC namespace must be
        exactly the generator's (program, post, the theorems), with only Lean's auxiliary
        lemmas under them, and every one of them present (review B1)."""
        space = self.vc["namespace"]
        own = {f"{space}.program", f"{space}.post", *self.vc["theorems"]}
        common = {f"ProgramVC.{n}" for n in COMMON_NAMES}
        aux = re.compile("(" + "|".join(map(re.escape, sorted(own | common))) + ")" + AUXILIARY)
        names = {d["name"] for d in report["declarations"]}
        extra = sorted(n for n in names if n.startswith("ProgramVC.")
                       and n not in own | common and not aux.fullmatch(n))
        missing = sorted(own - names)
        if extra or missing:
            raise Problem("export-differs", f"the export's ProgramVC declarations are not the "
                          f"generator's: extra {extra[:5]}, missing {missing[:5]}")

    def decide(self, report, names):
        status = receipts.check_status(self.leanforth, names)
        whole = report.get("stopped") is False and report.get("run") == "ok"
        if status == "accepted-by-leanforth" and not (whole and self.leanforth["exitStatus"] == 0
                                                      and report.get("exitStatus") == 0):
            status = "failed"
        for name in names:
            found = self.leanforth["theorems"][name]
            axioms = f"; axioms: {axioms_text(found['axioms'])}" if found["verdict"] == \
                "accepted" else ""
            self.say(f"{name}: {found['verdict']}{axioms}")
        self.check_status = status
        if status == "accepted-by-leanforth":
            receipts.lean_agrees(self.lean, self.leanforth, names)
            self.say(f"check: accepted-by-leanforth: LeanForth's checker re-checked the export "
                     f"and accepted all {self.leanforth['accepted']} declarations; each "
                     "theorem's axioms equal Lean's #print axioms")
            self.verdict = 1 if self.vc["status"] == "refuted" else 0
            return
        verdicts = receipts.export_verdicts(self.leanforth) | {
            self.leanforth["theorems"][n]["verdict"] for n in names}
        codes = [code for code, found in VERDICT_PROBLEMS if verdicts & found]
        known = {"accepted"}.union(*(found for _, found in VERDICT_PROBLEMS))
        if verdicts - known or not codes:
            codes.append("internal")
        counts = ", ".join(f"{n} {k}" for k, n in sorted(self.leanforth["counts"].items())
                           if n and k != "declarations")
        for code in codes:
            self.problem(code, f"LeanForth's checker did not accept the export: {counts}; "
                         f"check status {status}")
        self.say(f"check: {status}: LeanForth's verdict on the export; nothing discharged")

    # --------------------------------------------------------------- the receipt

    def outcome(self):
        """The verify status the evidence gives."""
        if self.gen is None:
            return "unsupported"
        if self.check_status != "accepted-by-leanforth":
            return "open"
        return "refuted" if self.vc["status"] == "refuted" else "discharged"

    def write(self):
        """Step 8: the evidence record and the receipt, which names it with its SHA-256,
        each written atomically."""
        evidence = receipts.dump(self.evidence())
        self.evidence_ref = {"path": self.files["evidence"],
                             "sha256": digest(evidence.encode("utf-8"))}
        receipt = self.build()
        problems = receipts.receipt_problems(receipt)
        if problems:
            raise Problem("internal", f"the receipt built is not valid: {problems[:3]}")
        for key, text in (("evidence", evidence), ("receipt", receipts.dump(receipt))):
            atomic(ROOT / self.files[key], text)
        self.receipt_path = self.files["receipt"]
        self.say_outcome(receipt)
        self.say(f"receipt: {self.receipt_path} (schema {receipt['schemaVersion']})")

    def say_outcome(self, receipt):
        verify, contract = receipt["verify"], f"contract {self.contract['id']}"
        self.say(f"verify: {verify['status']}" + (
            f", settled by {verify['settledBy']}" if "settledBy" in verify else ""))
        self.say("run: not-run (plan 8.4.2)")
        status, n = verify["status"], len(verify["obligations"])
        if status == "discharged":
            self.say(f"{self.word}: {contract} discharged ({n} of {n} obligations; Lean wrote the "
                     "proofs, LeanForth's checker accepted them); about the IR, under the "
                     f"receipt's {len(receipt['assumptions'])} assumptions; compiled code is not "
                     "covered")
        elif status == "refuted":
            self.say(f"{self.word}: {contract} NOT VERIFIED: refuted: {self.refutation()}")
        elif status == "unsupported":
            self.say(f"{self.word}: {contract} NOT VERIFIED: unsupported: {self.vc['reason']}")
        else:
            self.say(f"{self.word}: {contract} NOT VERIFIED: open: no obligation is discharged "
                     f"({self.check_status})")
        expect = self.contract.get("expect")
        if expect and expect != status:
            self.say(f"note: the contract expects {expect}; verify found {status}")

    def lean_ran(self):
        return self.lean is not None and "axioms" in self.lean

    def build(self):
        """The receipt (schema 0.3) from what this run found."""
        status, accepted = self.outcome(), self.check_status == "accepted-by-leanforth"
        refuted = self.vc is not None and self.vc["status"] == "refuted"
        contract = {"id": self.contract["id"], "statement": self.contract["statement"]}
        if status in ("discharged", "open") and not refuted:
            contract["lean"] = f"{self.vc['namespace']}.contract"
        contract["file"] = {"path": self.contract_path, "sha256": self.contract_sha}
        tools = ([{"name": "lean", **{k: self.lean[k] for k in ("version", "commit")}}]
                 if self.lean else [])
        if self.leanforth:
            tools.append({"name": "leanforth",
                          "version": receipts.leanforth_version(self.leanforth)})
        tools += [{"name": "gforth", "version": self.forth[1]}, GENERATOR]
        return {
            "schema": "leanforth-program-receipt",
            "schemaVersion": receipts.SCHEMA_VERSION,
            "provenance": {
                "kind": "generated",
                "generator": {"name": "python", "version": f"program_verify.py {VERSION}"},
                "createdAt": datetime.date.today().isoformat(),
                "note": "Written by leanforth verify (scripts/program_verify.py) from the files "
                        "named below, at the hashes given, and the evidence record it wrote "
                        f"beside this receipt, {self.evidence_ref['path']}, SHA-256 "
                        f"{self.evidence_ref['sha256']}. A receipt is a statement of evidence, "
                        "not an approval; it passes no review gate."},
            "program": {"word": self.word, "stackEffect": self.contract["stack"],
                        "source": {"path": self.source,
                                   "line": receipts.word_line(self.ir_text, self.word),
                                   "sha256": self.source_sha},
                        "ir": {"version": "0.1", "sha256": self.ir_sha},
                        "floatingPoint": False},
            "contract": contract,
            "check": self.check_part(refuted),
            "verify": self.verify_part(status, refuted, accepted),
            "run": {"status": "not-run", "cases": 0, "failures": 0, "label": "not run",
                    "note": "No runtime test ran: plan 8.4.2 adds them. A receipt about the IR "
                            "says nothing about the compiled code or the runtime."},
            "assumptions": self.assumptions(refuted, accepted),
            "tools": tools,
        }

    def check_part(self, refuted):
        if self.leanforth is None:
            why = ("the generator made no obligations (unsupported), so neither Lean nor "
                   "LeanForth's checker ran" if self.gen is None else
                   f"Lean 4.35.0 did not finish the generated file {self.files['lean']} (a "
                   "tactic script failed or the time limit was reached), so nothing was "
                   "exported and LeanForth's checker did not run")
            return {"status": "not-checked", "axioms": [], "evidence": [],
                    "note": f"Nothing was checked: {why}."}
        accepted = self.check_status == "accepted-by-leanforth"
        theorems = [{"name": n, "axioms": receipts.allowlist_order(
            self.leanforth["theorems"][n]["axioms"]) if accepted else []}
            for n in self.theorem_names()]
        files = [self.files["lean"], "scripts/program_vc.py", "scripts/export.sh",
                 self.files["manifest"], self.evidence_ref]
        proofs = (f"the proof of {self.theorem_names()[0]}, that the contract is false" if
                  refuted else None)
        return receipts.check_part(
            self.check_status, f"{self.vc['namespace']}.contract", theorems, self.evidence(),
            files=files, pinned=f"whose manifest is {self.files['manifest']}", proofs=proofs)

    def verify_part(self, status, refuted, accepted):
        if status == "unsupported":
            return {"status": "unsupported", "generator": GENERATOR, "obligations": [],
                    "note": f"The untrusted generator made no obligations: {self.vc['reason']}."}
        if not refuted:
            why = ("Lean did not finish the generated file and LeanForth's checker did not run"
                   if self.leanforth is None else
                   "LeanForth's checker did not accept the theorems")
            return receipts.verify_part(self.check_status, self.vc, unsettled=why)
        obligation = {"id": "O1", "statement": f"The contract is false: {self.refutation()}.",
                      "status": "refuted" if accepted else "open"}
        part = {"status": status}
        if accepted:
            part["settledBy"] = self.check_status
            obligation["theorem"] = self.theorem_names()[0]
        part.update(generator=GENERATOR, obligations=[obligation], note=(
            "The untrusted generator found inputs that break the contract and wrote the theorem "
            "refuted, the contract's negation, proved by running the IR in Lean on them; " +
            ("LeanForth's checker accepted it." if accepted else
             "it is not settled, since LeanForth's checker did not accept it.")))
        return part

    def assumptions(self, refuted, accepted):
        later = receipts.later_version(self.ir_text, (ROOT / self.source).read_text(
            encoding="utf-8", errors="replace"), self.word)
        found = receipts.assumptions(
            self.word, receipts.prim_words(self.ir_text, self.word), None,
            receipts.version_sentence(self.word, receipts.word_line(self.ir_text, self.word),
                                      later),
            lean_file=self.files["lean"] if self.files else "",
            stated="the theorem refuted, the contract's negation, is" if refuted else
            "the contract theorem is",
            checked=f"leanforth verify wrote this IR with the program words and required it to "
                    f"equal {self.contract['ir']}, the contract's IR file, byte for byte.")
        if not self.lean_ran():
            found = [a for a in found if a["kind"] != "trusted-lean"]
            found[0]["text"] = ("Every value is one signed host cell. No theorem about the word "
                                f"was checked, and {receipts.NOT_RUN}.")
        if self.gen is None:
            for a in found:
                if a["kind"] == "untrusted-generator":
                    a["text"] = ("The untrusted generator (scripts/program_vc.py) found the word "
                                 f"outside what it supports ({self.vc['reason']}) and made no "
                                 "obligation; no theorem was stated or checked.")
        if accepted:
            found.append(receipts.leanforth_assumption(
                self.leanforth, "theorem refuted" if refuted else
                "contract theorem, its obligations"))
        return numbered(found)

    def evidence(self):
        """What this run recorded, beside the receipt (for its replay, plan 8.4.1d)."""
        return {"recordedAt": datetime.date.today().isoformat(),
                "options": {"fuel": self.args.fuel,
                            "memoryPerCheck": self.args.memory_per_check,
                            "pathsLimit": self.args.paths_limit,
                            "searchLimit": self.args.search_limit},
                "ir": {"words": receipts.IR_WORDS, "sha256": self.ir_sha,
                       "source": self.source_sha},
                "generator": self.vc,
                "tools": self.tool_files,
                "testTools": test_tools(),
                "lean": self.lean,
                "export": None if self.manifest is None else
                {"sha256": self.manifest["sha256"], "bytes": self.manifest["bytes"]},
                "leanforth": self.leanforth}

    def remove_export(self):
        """The export this run wrote, removed by name unless --keep-export."""
        if self.export:
            (ROOT / f"{self.export}.partial").unlink(missing_ok=True)
            if not self.args.keep_export:
                (ROOT / self.export).unlink(missing_ok=True)


def atomic(path, text):
    """Write text to path through path.partial, renamed only when written in full."""
    partial = Path(f"{path}.partial")
    try:
        with open(partial, "w", encoding="utf-8") as file:
            file.write(text)
            file.flush()
            os.fsync(file.fileno())
        os.replace(partial, path)
    except OSError as error:
        partial.unlink(missing_ok=True)
        raise Problem("receipt-not-written", f"{path}: {error}") from None


def main(argv=None):
    try:
        args = parse(sys.argv[1:] if argv is None else argv)
    except Problem as stop:
        print(f"error: usage: {stop.message}\ntry: python3 scripts/program_verify.py --help")
        return 4
    run = Verify(args)
    handler = lambda signum, frame: (run.tools.stop(), sys.exit(5))  # noqa: E731
    previous = {s: signal.signal(s, handler) for s in (signal.SIGTERM, signal.SIGINT)}
    try:
        return run.run()
    finally:
        for s, h in previous.items():
            signal.signal(s, h)


if __name__ == "__main__":
    sys.exit(main())
