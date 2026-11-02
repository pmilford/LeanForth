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
    for lrow, frow in zip(lean, negative):
        unbound = lrow[0] in ("0", "2", "5")
        if frow[0] != lrow[0] or frow[1] not in ((INVALID,) if unbound else (INVALID, UNKNOWN)):
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
        return defined == "1" and forth[0] in (INVALID, UNKNOWN)
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
        return lean_rest[0] == "1" and forth_rest[0] in (INVALID, UNKNOWN)
    return mapped("poly specialization", lean, forth, 8, accept)


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
