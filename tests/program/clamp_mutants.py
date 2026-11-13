"""Mutants of the clamp export: its program, contract or proof changed, all else kept.

Usage: python3 tests/program/clamp_mutants.py KIND EXPORT.ndjson MUTANT.ndjson
       python3 tests/program/clamp_mutants.py copies EXPORT.ndjson MUTANTS.ndjson
       python3 tests/program/clamp_mutants.py --constants EXPORT.ndjson DECLARATION FIELD
       python3 tests/program/clamp_mutants.py --test [--lean]

EXPORT is the export of ProgramVC.LfClamp0.contract, O1 and O2 with every
declaration they use (`python3 scripts/program_receipt.py export EXPORT`
writes it with pinned Lean). KIND changes one declaration in place:
  program   the word's program, ProgramVC.LfClamp0.program, with MAX and MIN
            exchanged (the IR of `>r min r> max`), as vc_check.py's planted
            fault does in the Lean source; nothing that uses it is changed
  contract  the postcondition, ProgramVC.LfClamp0.post, with min and max
            exchanged (r = max(min(v, l), u), the refuted contract of
            tests/program/contracts/wrong-clamp-swapped.contract)
  proof     the contract theorem's proof term with the lemma ir_max
            (`if a < b then b else a = max a b`) replaced by ir_min, which has
            the same shape and another statement
A checker must then reject the theorems whose proofs no longer fit:
`contract` for program and proof, `O1`, `O2` and so `contract` for contract.
`copies` makes all three in one file instead, each changed declaration
added at the end under a name of its own (programMutant, postMutant, ...)
and each theorem that used the original copied to use it, the originals
kept; one check of that file then shows the originals accepted and every
copy that must fail rejected (COPIES lists the expected verdicts).

A change rebuilds only the expressions on the way from the declaration's
type or value down to the replaced constants: new expression records, each
with the next free number, go just before the declaration, which then points
to its new expression; an expression already defined before it is reused,
as Lean's exporter shares them. No other declaration changes, and every
changed declaration still has a well-formed type, so the file is never
malformed. The manifest beside the output is written afresh
(scripts/export_manifest.py), so the manifest check passes and a rejection
is the kernel's.

--constants lists the constants a declaration's type or value refers to,
for choosing a mutation. --test checks the rebuilding on a committed export
(Python and Gforth) and the snapshot accounting of the --lean test
(taken_problems) on fabricated reports; with --lean it exports the clamp theorems with pinned
Lean and checks them with LeanForth, saving the checked environment as a
snapshot (make check does both once, for this and the receipt's test:
program-clamp-record), then checks the copies against that snapshot (the
originals, unchanged, taken from it; every copy checked) and requires
every original accepted and the verdicts of COPIES.
Untrusted test tool: it never accepts anything.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
CHILDREN = {"app": ("fn", "arg"), "lam": ("type", "body"), "forallE": ("type", "body"),
            "letE": ("type", "value", "body"), "proj": ("struct",), "mdata": ("expr",)}
DECLARATIONS = ("axiom", "def", "thm", "opaque")
# Records that are neither names nor expressions: declarations, levels, the header.
SKIPPED = tuple(f'{{"{kind}"' for kind in DECLARATIONS + ("inductive", "quot", "meta", "il"))
SPACE = "ProgramVC.LfClamp0."
# KIND: (declaration, field, constants exchanged in pairs)
MUTANTS = {
    "program": (SPACE + "program", "value", [("ProgramIR.Prim.max", "ProgramIR.Prim.min")]),
    "contract": (SPACE + "post", "value", [("Max.max", "Min.min"),
                                           ("Int.instMax", "Int.instMin")]),
    "proof": (SPACE + "contract", "value", [("ProgramVC.ir_max", "ProgramVC.ir_min")]),
}
# The copies, in order: (new name, original, constants renamed in its type and value, the
# change of MUTANTS made in its value, LeanForth's expected verdict).
COPIES = [
    ("programMutant", "program", {}, "program", "accepted"),
    ("contractProgramMutant", "contract", {"program": "programMutant"}, None, "rejected"),
    ("postMutant", "post", {}, "contract", "accepted"),
    ("O1ContractMutant", "O1", {"post": "postMutant"}, None, "rejected"),
    ("O2ContractMutant", "O2", {"post": "postMutant"}, None, "rejected"),
    ("contractContractMutant", "contract",
     {"post": "postMutant", "O1": "O1ContractMutant", "O2": "O2ContractMutant"}, None, "rejected"),
    ("contractProofMutant", "contract", {}, "proof", "rejected"),
]
ORIGINALS = ["program", "post", "O1", "O2", "contract"]


class Export:
    """An export's lines, its names by number and its expressions by number."""

    def __init__(self, text):
        self.lines = text.split("\n")
        self.names, self.exprs, self.content = {0: ""}, {}, {}
        self.where = {}   # ("in" or "ie", number) -> the line that defines it
        for index, line in enumerate(self.lines):
            if line and not line.startswith(SKIPPED):
                self.read(json.loads(line), index)
        self.next = max(self.exprs) + 1
        self.next_name = max(self.names) + 1
        self.limit = len(self.lines)   # only records defined before this line are reused

    def read(self, record, index):
        if "in" in record:
            part = record.get("str") or record.get("num")
            text = part["str"] if "str" in record else str(part["i"])
            prefix = self.names[part["pre"]]
            self.names[record["in"]] = f"{prefix}.{text}" if prefix else text
            self.where["in", record["in"]] = index
        elif "ie" in record:
            body = {k: v for k, v in record.items() if k != "ie"}
            self.exprs[record["ie"]] = body
            self.content.setdefault(key(body), record["ie"])
            self.where["ie", record["ie"]] = index

    def name_id(self, name):
        """The number of a name defined before the line limit."""
        found = [number for number, text in self.names.items() if text == name]
        if len(found) != 1 or self.where["in", found[0]] >= self.limit:
            raise SystemExit(f"the export has {len(found)} names {name} before line {self.limit}")
        return found[0]

    def new_name(self, prefix, part, added):
        """A new name prefix.part, as a record appended to added."""
        number, self.next_name = self.next_name, self.next_name + 1
        self.names[number] = f"{self.names[prefix]}.{part}"
        self.where["in", number] = -1
        added.append({"in": number, "str": {"pre": prefix, "str": part}})
        return number

    def declaration(self, name):
        """(line index, kind, record) of the declaration named name."""
        wanted = self.name_id(name)
        for index, line in enumerate(self.lines):
            for kind in DECLARATIONS:
                if line.startswith(f'{{"{kind}"'):
                    record = json.loads(line)[kind]
                    if record["name"] == wanted:
                        return index, kind, record
        raise SystemExit(f"no declaration {name} in the export")

    def constants(self, root):
        """The names of the constants an expression refers to, each once, in order of first visit."""
        seen, order, stack = set(), [], [root]
        while stack:
            number = stack.pop()
            if number in seen:
                continue
            seen.add(number)
            body = self.exprs[number]
            kind = next(iter(body))
            if kind == "const":
                order.append(self.names[body["const"]["name"]])
            stack += [body[kind][c] for c in CHILDREN.get(kind, ())]
        return list(dict.fromkeys(order))

    def rebuilt(self, root, renaming, added):
        """The number of root with each constant renamed (name number to name number); new
        expressions are appended to added, as records."""
        done, stack = {}, [root]
        while stack:
            number = stack[-1]
            if number in done:
                stack.pop()
                continue
            body = self.exprs[number]
            kind = next(iter(body))
            pending = [body[kind][c] for c in CHILDREN.get(kind, ()) if body[kind][c] not in done]
            if pending:
                stack += pending
                continue
            stack.pop()
            new = json.loads(json.dumps(body))
            for child in CHILDREN.get(kind, ()):
                new[kind][child] = done[body[kind][child]]
            if kind == "const":
                new["const"]["name"] = renaming.get(body["const"]["name"], body["const"]["name"])
            done[number] = number if new == body else self.share(new, added)
        return done[root]

    def share(self, body, added):
        """The number of an expression with this content: an existing one, else a new record."""
        found = self.content.get(key(body))
        if found is None or self.where["ie", found] >= self.limit:
            found, self.next = self.next, self.next + 1
            self.exprs[found], self.content[key(body)] = body, found
            self.where["ie", found] = -1   # it goes just before the declaration
            added.append(dict(body, ie=found))
        return found

    def swaps(self, pairs):
        """The renaming that exchanges each pair of constants."""
        renaming = {}
        for left, right in pairs:
            a, b = self.name_id(left), self.name_id(right)
            renaming.update({a: b, b: a})
        return renaming


def key(body):
    return json.dumps(body, sort_keys=True, separators=(",", ":"))


def line(record):
    return json.dumps(record, sort_keys=True, separators=(",", ":"))


def mutate(text, name, field, pairs):
    """The export text with the pairs of constants exchanged in the field (type or value) of
    the declaration name, in place, and how many expressions that added."""
    export = Export(text)
    index, decl_kind, record = export.declaration(name)
    export.limit = index
    added = []
    root = export.rebuilt(record[field], export.swaps(pairs), added)
    if root == record[field]:
        raise SystemExit(f"{name}'s {field} refers to none of {pairs}")
    record[field] = root
    export.lines[index] = line({decl_kind: record})
    export.lines[index:index] = [line(r) for r in added]
    return "\n".join(export.lines), len(added)


def copied(text, prefix, steps):
    """The export text with copies added at its end: for each step (new, original, renamed,
    pairs), the declaration prefix.original as prefix.new, the constants prefix.a renamed
    prefix.b for each a: b of renamed in its type and value, and the pairs exchanged in its
    value."""
    export = Export(text)
    tail, space = [], export.name_id(prefix) if prefix else 0
    dotted = f"{prefix}." if prefix else ""
    for new, original, renamed, pairs in steps:
        _, decl_kind, record = export.declaration(dotted + original)
        renaming = {export.name_id(dotted + a): export.name_id(dotted + b)
                    for a, b in renamed.items()}
        added = []
        number = export.new_name(space, new, added)
        for field in ("type", "value"):
            changes = {**renaming, **(export.swaps(pairs) if field == "value" else {})}
            record[field] = export.rebuilt(record[field], changes, added)
        record["name"], record["all"] = number, [number]
        tail += [line(r) for r in added] + [line({decl_kind: record})]
    lines = export.lines[:-1] if export.lines[-1] == "" else export.lines
    return "\n".join(lines + tail) + "\n"


def copies(text):
    """The clamp export with every copy of COPIES added at its end."""
    return copied(text, SPACE.rstrip("."), [(new, original, renamed,
                                            MUTANTS[kind][2] if kind else [])
                                           for new, original, renamed, kind, _ in COPIES])


# ------------------------------------------------------------------------ tests

def leanforth(export, *options):
    """(exit status, the JSON report) of bin/leanforth check --json on an export."""
    done = subprocess.run(["bash", str(ROOT / "bin" / "leanforth"), "check", "--json", *options,
                           str(export)], capture_output=True, text=True, stdin=subprocess.DEVNULL,
                          timeout=int(os.environ.get("TEST_TIMEOUT", "1800")))
    try:
        return done.returncode, json.loads(done.stdout)
    except ValueError:
        return done.returncode, {"declarations": [], "counts": {"declarations": 0},
                                 "error": done.stdout[-500:] + done.stderr[-500:]}


FIXTURE = ROOT / "tests/reference/constant-fixture.ndjson"
SWAP = [("fixtureId", "fixturePoly")]   # same type, and fixturePoly unfolds to fixtureId


def self_test():
    """Rebuilding on the constant fixture (fixtureId, fixturePoly, fixtureUse), without Lean:
    exchanging two constants of the same type in fixtureUse's proof adds records just before
    it, numbered after every other, changes no other line and leaves a proof LeanForth
    accepts; a copy under a new name keeps every line and is accepted too. So the tool writes
    well-formed exports, and a rejection of a clamp mutant is the change's, not the tool's."""
    fixture = FIXTURE.read_text(encoding="utf-8")
    old = fixture.split("\n")
    problems = []
    text, count = mutate(fixture, "fixtureUse", "value", SWAP)
    new = text.split("\n")
    at = next(i for i, x in enumerate(old) if x.startswith('{"thm"'))
    numbers = [json.loads(x)["ie"] for x in new[at:at + count]]
    if (count < 1 or new[:at] != old[:at] or new[at + count + 1:] != old[at + 1:]
            or min(numbers) <= max(Export(fixture).exprs)):
        problems.append(f"the in-place change is not {count} new records just before the theorem")
    shared = Export(fixture)   # an expression is reused only when defined before the limit
    last = max(shared.exprs)
    body = dict(shared.exprs[last])
    shared.limit = shared.where["ie", last]
    if shared.share(body, []) == last:
        problems.append("an expression defined after the declaration was reused")
    shared = Export(fixture)
    if shared.share(dict(shared.exprs[last]), []) != last:
        problems.append("an expression defined before the declaration was not reused")
    copy = copied(fixture, "", [("fixtureUseCopy", "fixtureUse", {}, SWAP)])
    if copy.split("\n")[:len(old) - 1] != old[:len(old) - 1]:
        problems.append("a copy changed an existing line")
    with tempfile.TemporaryDirectory() as folder:
        for name, content, declarations in (("swapped", text, 3), ("copy", copy, 4)):
            path = Path(folder) / f"{name}.ndjson"
            path.write_text(content, encoding="utf-8")
            code, report = leanforth(path, "--no-manifest")
            if code != 0 or report["counts"].get("accepted") != declarations:
                problems.append(f"{name}: exit {code}, {report.get('counts')}")
    return problems


# The clamp export checked alone, with the snapshot of that check: make check records the
# receipt's evidence once per run (target program-clamp-record, `program_receipt.py record
# --keep DIR`) and names DIR here; run alone, without it, this script checks the export itself.
RECORDED = os.environ.get("PROGRAM_CLAMP_RECORDED")


def checked_clamp(folder):
    """(export, snapshot, LeanForth's evidence of the export checked alone): those of make
    check's record, else made in folder the way record makes them."""
    sys.path.insert(0, str(ROOT / "scripts"))
    import program_receipt  # noqa: E402
    if RECORDED:
        evidence = program_receipt.read_json(Path(RECORDED) / "evidence.json")
        return (Path(RECORDED) / program_receipt.KEPT_EXPORT,
                program_receipt.kept_snapshot(RECORDED), evidence["leanforth"])
    export = Path(folder) / program_receipt.KEPT_EXPORT
    vc = program_receipt.vc_entry("lf-clamp/0")
    program_receipt.export_theorems(program_receipt.pinned_lean(), vc["theorems"], export)
    alone = program_receipt.leanforth_check(export, vc["theorems"],
                                            Path(folder) / program_receipt.KEPT_SNAPSHOT)
    return export, program_receipt.kept_snapshot(folder), alone


def taken_problems(report, declarations, copied_names):
    """The check of an export with copies added, against the snapshot of the export's own
    check of its declarations: every original taken from it unchanged, every copy (named
    in copied_names) checked in this run."""
    taken = (report.get("snapshot") or {}).get("import")
    want = {"taken": declarations, "checked": len(copied_names), "otherContent": 0}
    wrong = [d["name"] for d in report["declarations"]
             if (d.get("provenance") == "snapshot") == (d["name"] in copied_names)]
    return ([f"from the snapshot: {taken}, expected {want}"] if taken != want else []) + (
        [f"provenance not as expected: {wrong[:5]}"] if wrong else [])


def taken_report(provenances, counts=(2, 1, 0)):
    """A fabricated report of a check against a snapshot: declarations a, b and the copy c
    with the given provenances (None: no provenance member), and the import's counts
    (taken, checked, otherContent), or None for a report without a snapshot."""
    declarations = [dict({"name": name}, **({} if p is None else {"provenance": p}))
                    for name, p in zip("abc", provenances)]
    snapshot = None if counts is None else {"import": dict(zip(
        ("taken", "checked", "otherContent"), counts))}
    return {"snapshot": snapshot, "declarations": declarations}


# (what is wrong, provenances of a, b, c, import counts): each must be flagged.
TAKEN_WRONG = [
    ("a copy taken from the snapshot", ("snapshot", "snapshot", "snapshot"), (3, 0, 0)),
    ("a copy taken, the counts as expected", ("snapshot", "snapshot", "snapshot"), (2, 1, 0)),
    ("an original checked again", ("snapshot", "checked", "checked"), (2, 1, 0)),
    ("an original without provenance", ("snapshot", None, "checked"), (2, 1, 0)),
    ("one original fewer taken", ("snapshot", "snapshot", "checked"), (1, 1, 0)),
    ("one more checked", ("snapshot", "snapshot", "checked"), (2, 2, 0)),
    ("a name the snapshot holds with other content", ("snapshot", "snapshot", "checked"),
     (2, 1, 1)),
    ("no snapshot at all (a plain check)", ("checked", "checked", "checked"), None),
]


def kept_self_test():
    """program_receipt.kept_snapshot (review L3 of speed-lf): a folder without the snapshot,
    or with an empty one, stops; a written one is returned."""
    sys.path.insert(0, str(ROOT / "scripts"))
    import program_receipt  # noqa: E402
    problems = []
    with tempfile.TemporaryDirectory() as folder:
        snapshot = Path(folder) / program_receipt.KEPT_SNAPSHOT
        for written in (None, b""):
            if written is not None:
                snapshot.write_bytes(written)
            try:
                program_receipt.kept_snapshot(folder)
                problems.append(f"kept_snapshot took {'an empty' if written == b'' else 'no'} file")
            except SystemExit:
                pass
        snapshot.write_bytes(b"x")
        if program_receipt.kept_snapshot(folder) != snapshot:
            problems.append("kept_snapshot did not give the snapshot written")
    return problems


def taken_self_test():
    """taken_problems on fabricated reports, without Lean (review L2 of speed-lf): the report
    a right check against the export's snapshot gives has no problem; each of TAKEN_WRONG
    has one."""
    right = taken_problems(taken_report(("snapshot", "snapshot", "checked")), 2, {"c"})
    problems = [f"taken_problems flags a correct report: {right}"] if right else []
    return problems + [f"taken_problems misses {what}" for what, provenances, counts in TAKEN_WRONG
                       if not taken_problems(taken_report(provenances, counts), 2, {"c"})]


def lean_test():
    """The clamp copies against LeanForth: the export checked alone (exit 0, every declaration
    accepted), then the copies against the snapshot of that check, the originals taken
    from it unchanged: the originals accepted, each copy as COPIES says."""
    problems = []
    with tempfile.TemporaryDirectory() as folder:
        export, snapshot, alone = checked_clamp(folder)
        import program_receipt  # noqa: E402 (on the path since checked_clamp)
        if alone["exitStatus"] != 0 or alone["accepted"] != alone["declarations"]:
            problems.append(f"the export alone: exit {alone['exitStatus']}, "
                            f"{alone['accepted']} of {alone['declarations']} accepted")
        mutants = Path(folder) / "mutants.ndjson"
        mutants.write_text(copies(export.read_text(encoding="utf-8")), encoding="utf-8")
        subprocess.run([sys.executable, str(ROOT / "scripts" / "export_manifest.py"),
                        str(mutants)], check=True, stdin=subprocess.DEVNULL)
        code, report = leanforth(mutants, "--jobs", program_receipt.LEANFORTH_JOBS, "--snapshot",
                                 str(snapshot))
    verdicts = {d["name"]: d["verdict"] for d in report["declarations"]}
    expected = {SPACE + n: "accepted" for n in ORIGINALS}
    expected.update({SPACE + new: verdict for new, _, _, _, verdict in COPIES})
    for name, verdict in expected.items():
        if verdicts.get(name) != verdict:
            problems.append(f"{name}: {verdicts.get(name)}, expected {verdict}")
    others = [n for n, v in verdicts.items() if v != "accepted" and n not in expected]
    if others or code != 1:
        problems.append(f"exit {code}, other declarations not accepted: {others[:5]}")
    copied_names = {SPACE + new for new, *_ in COPIES}
    return problems + taken_problems(report, alone["declarations"], copied_names), report


def main(arguments):
    if arguments[:1] == ["--constants"] and len(arguments) == 4:
        export = Export(Path(arguments[1]).read_text(encoding="utf-8"))
        _, _, record = export.declaration(arguments[2])
        print("\n".join(export.constants(record[arguments[3]])))
        return 0
    if arguments[:1] == ["--test"]:
        problems = self_test() + taken_self_test() + kept_self_test()
        report = None
        if "--lean" in arguments and not problems:
            problems, report = lean_test()
        for problem in problems:
            print(problem, file=sys.stderr)
        if problems:
            return 1
        print("clamp mutants: rebuilding checked on the constant fixture, the snapshot "
              f"accounting on {len(TAKEN_WRONG) + 1} fabricated reports" + (
            f"; LeanForth accepted the originals and rejected {sum(v == 'rejected' for *_, v in COPIES)}"
            f" mutated theorems of {report['counts']['declarations']:,} declarations "
            "(program, contract and proof changed)" if report else ""))
        return 0
    if len(arguments) != 3 or arguments[0] not in list(MUTANTS) + ["copies"]:
        print(__doc__.split("\n\n")[1], file=sys.stderr)
        return 2
    kind, source, target = arguments
    text = Path(source).read_text(encoding="utf-8")
    if kind == "copies":
        text, count = copies(text), len(COPIES)
    else:
        text, count = mutate(text, *MUTANTS[kind])
    Path(target).write_text(text, encoding="utf-8")
    subprocess.run([sys.executable, str(ROOT / "scripts" / "export_manifest.py"), target],
                   check=True, stdin=subprocess.DEVNULL)
    print(f"{target}: {kind}, {count} new " + ("declarations" if kind == "copies" else "expressions"))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
