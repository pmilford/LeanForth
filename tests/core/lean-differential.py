"""Pinned-Lean differentials of the current checker on small finite tables.

Usage: python3 tests/core/lean-differential.py NAME   (from the repository root;
LEAN and GFORTH name the toolchains). NAME is one of the TABLES below. Each
compares one Forth table (or export stream) of current src/core and
src/kernel code with a Lean 4.35.0 table in tests/reference. They port the
pinned-Lean comparisons of the superseded legacy code (D1-D11 of the legacy
coverage map; the legacy code was retired on 2026-11-02) onto the current
passes.

Every comparison is finite differential evidence about the stated cases; it
never accepts a theorem. Where the current Forth code is knowingly more
conservative than Lean (it answers unknown), the case is listed explicitly
in KNOWN_UNKNOWN with the reason; any other difference fails.
"""
import os
from pathlib import Path
import subprocess
import sys
import tempfile

sys.path.insert(0, "tests/support")
from export_definition import decode, encode, succ_chain  # noqa: E402
from ndjson_preview import LEAN_HASH  # noqa: E402

LEAN = os.environ.get("LEAN", "lean")
GFORTH = os.environ.get("GFORTH", "gforth")
EQUAL, INVALID, UNKNOWN = "0", "1", "3"

# Cases where Lean succeeds but the current Forth code answers unknown.
KNOWN_UNKNOWN = {
    # max u v and max v u are equal for every u and v; lf-level-compare does
    # not decide this commutation symbolically.
    ("convert", ("2", "6")),
    # The claim's binder domain is the redex (fun X : Sort 1 => X) Sort 0;
    # lf-mixed-infer needs the inferred type of a domain to be a Sort
    # without weak-head reduction (src/kernel/mixed-infer.fs, the word
    # lf-minfer-sort-level), so it answers unknown.
    ("definition", ("0", "4")),
}


class Mismatch(Exception):
    pass


def check_toolchain():
    version = subprocess.run([LEAN, "--version"], check=True, capture_output=True,
                             text=True).stdout
    revision = subprocess.run([LEAN, "--githash"], check=True, capture_output=True,
                              text=True).stdout.strip()
    if not version.startswith("Lean (version 4.35.0,") or revision != LEAN_HASH:
        raise Mismatch("unexpected Lean toolchain")


def rows(text):
    return [line.split() for line in text.splitlines()]


def lean_rows(path, run=False, lean_path=None):
    command = [LEAN, "-DwarningAsError=true"] + (["--run"] if run else []) + [path]
    env = dict(os.environ, LEAN_PATH=lean_path) if lean_path else None
    return rows(subprocess.run(command, check=True, capture_output=True, text=True,
                               env=env).stdout)


def forth_rows(path):
    return rows(subprocess.run([GFORTH, path], check=True, capture_output=True,
                               text=True, stdin=subprocess.DEVNULL).stdout)


def section(table, letter):
    return [row[1:] for row in table if row[0] == letter]


def same(name, lean, forth, count):
    if len(lean) != count or lean != forth:
        raise Mismatch(f"{name}: Forth differs from Lean (expected {count} equal rows)\n"
                       f"Lean:  {lean}\nForth: {forth}")
    return count


def mapped(name, lean, forth, count, accept):
    """Rows keyed by their first two fields; accept(key, lean, forth) decides."""
    if len(lean) != count or len(forth) != count:
        raise Mismatch(f"{name}: expected {count} rows")
    for lrow, frow in zip(lean, forth):
        if lrow[:2] != frow[:2] or not accept(tuple(lrow[:2]), lrow[2:], frow[2:]):
            raise Mismatch(f"{name}: Lean {lrow} and Forth {frow} disagree")
    return count


def scope():
    return same("scope", lean_rows("tests/reference/scope-table.lean", run=True),
                forth_rows("tests/core/constant-term-scope-table.fs"), 64)


def shift():
    return same("shift", lean_rows("tests/reference/shift-table.lean", run=True),
                forth_rows("tests/core/mixed-shift-plain-table.fs"), 80)


def instantiate():
    return same("instantiate", lean_rows("tests/reference/instantiate-table.lean", run=True),
                forth_rows("tests/core/mixed-instantiate-plain-table.fs"), 25)


def beta():
    return same("beta", lean_rows("tests/reference/beta-table.lean"),
                forth_rows("tests/core/mixed-beta-plain-table.fs"), 15)


def convert():
    def accept(key, lean, forth):
        if lean == ["1"]:
            expected = UNKNOWN if ("convert", key) in KNOWN_UNKNOWN else EQUAL
            return forth == [expected]
        return lean == ["0"] and forth == [UNKNOWN]
    return mapped("convert", lean_rows("tests/reference/convert-table.lean"),
                  forth_rows("tests/core/mixed-convert-plain-table.fs"), 15, accept)


def infer():
    forth = forth_rows("tests/core/mixed-infer-plain-table.fs")
    count = same("infer positive", lean_rows("tests/reference/infer-table.lean"),
                 section(forth, "P"), 7)
    negative = section(forth, "N")
    lean = lean_rows("tests/reference/infer-negative-table.lean")
    if len(lean) != 6 or any(row[1:] != ["1"] for row in lean):
        raise Mismatch("infer negative: Lean accepted a case")
    # Cases 1, 3 and 4 are rejected by rules F1, S2 and D1 of ADR 0011 (the
    # kinds Lean gives are checked in the first-checker table).
    for lrow, frow in zip(lean, negative):
        unbound = lrow[0] in ("0", "2", "5")
        allowed = (INVALID,) if unbound else (INVALID, UNKNOWN, REJECTED)
        if frow[0] != lrow[0] or frow[1] not in allowed:
            raise Mismatch(f"infer negative: Forth {frow} for a case Lean rejects")
    count += len(negative)
    oracle = lean_rows("tests/reference/symbolic-infer-oracle.lean")
    if oracle != [["symbolic", "Pi", "universe", "equivalent;", "invalid", "application",
                   "rejected"]]:
        raise Mismatch("infer oracle: unexpected Lean result")
    if section(forth, "O") != [["0", "OK"], ["1", "OK"], ["2", "REJECT"]]:
        raise Mismatch("infer oracle: Forth universes or rejection differ")
    count += 3
    count += same("infer binder", lean_rows("tests/reference/tagged-binder-table.lean"),
                  section(forth, "B"), 18)
    count += same("infer application",
                  lean_rows("tests/reference/tagged-application-table.lean"),
                  section(forth, "A"), 18)
    return count


def definition():
    def accept(key, lean, forth):
        theorem, defined = lean
        if theorem not in ("0", "1"):
            return False
        if defined == "0":
            expected = UNKNOWN if ("definition", key) in KNOWN_UNKNOWN else EQUAL
            return forth == [expected]
        return defined == "1" and forth[0] in (INVALID, UNKNOWN, REJECTED)
    return mapped("definition", lean_rows("tests/reference/definition-table.lean"),
                  forth_rows("tests/core/mixed-definition-table.fs"), 9, accept)


def level_substitute():
    return same("level substitute",
                lean_rows("tests/reference/term-level-substitute-table.lean", run=True),
                forth_rows("tests/core/mixed-level-substitute-plain-table.fs"), 48)


def constant():
    lean = lean_rows("tests/reference/term-level-substitute-table.lean", run=True)
    forth = forth_rows("tests/core/mixed-infer-constant-table.fs")
    return (same("constant specialize", lean, section(forth, "S"), 48)
            + same("constant infer", lean, section(forth, "T"), 48))


def with_poly_identity(table):
    """Lean rows of a table that imports the compiled poly-identity fixture."""
    with tempfile.TemporaryDirectory() as temporary:
        subprocess.run([LEAN, "-DwarningAsError=true", "-o",
                        str(Path(temporary) / "LeanForthPolyIdentity.olean"),
                        "tests/reference/poly-identity.lean"], check=True)
        return lean_rows(table, lean_path=temporary)


def run_stream(path, data):
    result = subprocess.run([GFORTH, path], input=bytes(data), capture_output=True)
    if result.returncode != 0:
        raise Mismatch(f"{path} failed: {result.stderr.decode()}")
    return result.stdout.decode().split()


def poly_levels(decoded, k):
    extra, records = succ_chain(0, len(decoded["levelExpressions"]), 3)
    return dict(actuals=[records[k]], extra_levels=extra)


def signature_fixture():
    lean = with_poly_identity("tests/reference/signature-fixture.lean")
    decoded = decode("poly-identity")
    forth = [[str(k)] + run_stream("tests/core/export-signature-stream.fs",
                                   encode(decoded, **poly_levels(decoded, k)))
             for k in range(4)]
    return same("signature fixture", lean, forth, 4)


def poly_specialization():
    lean = with_poly_identity("tests/reference/poly-specialization-table.lean")
    decoded = decode("poly-identity")
    claim = decoded["declarations"][0]["type"]
    forth = []
    for k in range(4):
        for kind in range(2):
            data = encode(decoded, value=claim if kind else None, **poly_levels(decoded, k))
            status, claim_shape, value_shape = run_stream("tests/core/export-definition-stream.fs",
                                                          data)
            forth.append([str(k), str(kind), status, claim_shape, value_shape])

    def accept(key, lean_rest, forth_rest):
        if lean_rest[1:] != forth_rest[1:]:
            return False
        if key[1] == "0":
            return lean_rest[0] == "0" and forth_rest[0] == EQUAL
        return lean_rest[0] == "1" and forth_rest[0] in (INVALID, UNKNOWN, REJECTED)
    return mapped("poly specialization", lean, forth, 8, accept)


REJECTED, UNSUPPORTED = "4", "5"

# The first checker's table (plan task 2.2.1, ADR 0011): each rejection's
# diagnostic code, the rule it names and the Lean kernel exception that rule
# stands for (src/core/diagnostics.fs, kernel/environment.fs).
REJECTION_CODES = {
    50: ("N1", "unknownConstant"), 51: ("N2", "alreadyDeclared"),
    52: ("L1", "levelCount"), 53: ("L2", "undefinedLevelParam"),
    54: ("L3", "duplicateLevelParam"), 55: ("S1", "typeExpected"),
    56: ("S2", "typeExpected"), 57: ("S3", "thmTypeIsNotProp"),
    58: ("F1", "funExpected"), 59: ("D", "appTypeMismatch"),
    60: ("D", "declTypeMismatch"),
}
OUTCOMES = {"ok": "accepted", "rejected": "rejected", "unknown": "unknown",
            "unsupported": "unsupported", "invalid": "invalid",
            "exhausted": "exhausted", "full": "full"}
# Rows whose answer comes from first-checker-driver.fs's stand-in for the
# declaration audit of plan task 2.2.3 (rules U1, U2), not from kernel code.
AUDIT_RULES = {"U1", "U2"}
# Rows where today's code gives another failure than the table, with the
# reason. Neither answer is accepted or rejected.
FIRST_CHECKER_KNOWN = {
    # The 64-node term store fills while the value's type is inferred, before
    # the comparison that would be undecided (K2); the same before 2.2.1.
    "composition.proof-irrelevance": "full",
}


def first_checker_cases():
    """Lean's table rows, and the cases as text from first-checker-terms.lean."""
    with tempfile.TemporaryDirectory() as temporary:
        compiled = subprocess.run(
            [LEAN, "-DwarningAsError=true", "-o",
             str(Path(temporary) / "LeanForthFirstChecker.olean"),
             "tests/reference/first-checker-expected.lean"],
            check=True, capture_output=True, text=True).stdout
        if compiled != Path("tests/reference/first-checker-expected.tsv").read_text():
            raise Mismatch("first checker: Lean's rows differ from the expected table")
        text = subprocess.run([LEAN, "-DwarningAsError=true",
                               "tests/reference/first-checker-terms.lean"],
                              check=True, capture_output=True, text=True,
                              env=dict(os.environ, LEAN_PATH=temporary)).stdout
    table = [line.split("\t") for line in compiled.splitlines()[1:]]
    return {row[0]: row[1:] for row in table}, text


def first_checker_rows(text):
    """Run every case through tests/support/first-checker-driver.fs."""
    driver = Path("tests/support/first-checker-driver.fs").resolve()
    script = [f"require {driver}"]
    for line in text.splitlines():
        word, rest = line.split(" ", 1)
        if word == "CASE":
            if len(script) > 1:
                script.append("fc-run")
            script.append(f"fc-case {rest}")
        elif word == "DECL":
            script.append(f"fc-decl {rest}")
        else:
            raise Mismatch(f"first checker: unexpected line {line!r}")
    script += ["fc-run", "bye"]
    with tempfile.TemporaryDirectory() as temporary:
        path = Path(temporary) / "first-checker-cases.fs"
        path.write_text("\n".join(script) + "\n")
        result = subprocess.run([GFORTH, str(path)], capture_output=True, text=True,
                                stdin=subprocess.DEVNULL)
    if result.returncode != 0:
        raise Mismatch(f"first checker: Forth failed: {result.stderr}")
    rows = {}
    for line in result.stdout.splitlines():
        words = line.split()
        if words and words[0] == "ROW":
            rows[words[1]] = (OUTCOMES[words[2]], int(words[3]), int(words[4]),
                              int(words[5]), words[6])
    return rows


def first_checker_row(case, lean, expected, rule, measured):
    """Check one row; give its line for the summary."""
    outcome, code, first, _, source = measured
    if outcome == "rejected":
        if code not in REJECTION_CODES:
            raise Mismatch(f"{case}: rejected without a rejection rule (code {code})")
        named, kind = REJECTION_CODES[code]
        if expected != "rejected":
            raise Mismatch(f"{case}: {named} rejects a row the table says is {expected}")
        if kind != lean:
            raise Mismatch(f"{case}: {named} stands for {kind}, Lean raised {lean}")
        if named == "D":
            # first is the set of D rules used: bit k-1 for Dk.
            if not rule.startswith("D") or not (first >> (int(rule[1]) - 1)) & 1:
                raise Mismatch(f"{case}: D rules {first} lack the table's {rule}")
        elif named != rule:
            raise Mismatch(f"{case}: rule {named} where the table says {rule}")
    elif outcome == "accepted" and (lean != "accepted" or expected != "accepted"):
        raise Mismatch(f"{case}: accepted where Lean says {lean}")
    if outcome != expected and FIRST_CHECKER_KNOWN.get(case) != outcome:
        raise Mismatch(f"{case}: LeanForth gave {outcome}, the table says {expected}")
    if (source == "audit") != (rule in AUDIT_RULES):
        raise Mismatch(f"{case}: decided by the {source}, the table's rule is {rule}")
    return f"{case} {outcome} {rule} {source}"


def first_checker():
    table, text = first_checker_cases()
    rows = first_checker_rows(text)
    if sorted(rows) != sorted(table) or len(rows) != 62:
        raise Mismatch("first checker: the Forth rows are not the table's 62 cases")
    for case, (lean, expected, rule) in table.items():
        first_checker_row(case, lean, expected, rule, rows[case])
    mix = {}
    for outcome, *_ in rows.values():
        mix[outcome] = mix.get(outcome, 0) + 1
    audit = sum(rows[case][4] == "audit" for case in rows)
    print(f"first checker: {', '.join(f'{n} {o}' for o, n in sorted(mix.items()))}; "
          f"{len(rows) - audit} decided by kernel code, {audit} by the stand-in audit "
          f"(U1, U2); known differences: {', '.join(FIRST_CHECKER_KNOWN)}")
    return len(rows)


TABLES = {
    "scope": (scope, "constant-term scope cases agree with Lean's hasLooseBVars"),
    "shift": (shift, "plain shift cases agree with Lean's liftLooseBVars"),
    "instantiate": (instantiate, "plain instantiation cases agree with Lean's instantiate1"),
    "beta": (beta, "closed weak-head beta cases agree with Lean's Kernel.whnf"),
    "convert": (convert, "conversion cases agree with Lean's isDefEq "
                         "(one known conservative unknown)"),
    "infer": (infer, "inference cases agree with Lean's Kernel.check"),
    "definition": (definition, "definition-probe cases agree with Lean's kernel "
                               "(one known conservative unknown)"),
    "level-substitute": (level_substitute, "universe substitution observations agree with Lean"),
    "constant": (constant, "constant specialization and inference observations agree with Lean"),
    "signature-fixture": (signature_fixture, "specialized poly_identity signatures agree "
                                             "with Lean's instantiateLevelParams"),
    "poly-specialization": (poly_specialization, "specialized poly_identity definitions "
                                                 "agree with Lean's kernel"),
    "first-checker": (first_checker, "first-checker table rows agree with Lean's kernel "
                                     "and the expected LeanForth outcomes"),
}


def main(argv):
    if len(argv) != 2 or argv[1] not in TABLES:
        print(f"usage: {argv[0]} {{{','.join(TABLES)}}}", file=sys.stderr)
        return 2
    check_toolchain()
    run, summary = TABLES[argv[1]]
    print(f"{run()} {summary}.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv))
    except (Mismatch, OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"Differential failed: {error}", file=sys.stderr)
        sys.exit(1)
