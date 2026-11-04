"""The program words in two modes (ADR 0019) against today's reader.

Usage (from the repository root):
  GFORTH=... python3 tests/program/verify_check.py [--list]

Every input below runs, in one Gforth, through three translators from Forth
source to IR 0.1: today's reader (src/program/ir-reader.fs, kept only as the
test oracle), the mode shift (src/program/verify.fs, the primary design) and
the separate vocabulary (src/program/verify-alias.fs). The inputs:

  reader   every verdict case of tests/program/ir-reader.fs, the lines it
           feeds given as one text (today's reader is fed them one by one);
  hostile  the hostile inputs of ADR 0019's prototype (recognizer and number
           syntaxes, host words, forged structure, names, comments) and more;
  files    the files with every kind of line end of ir_reader_files.py, the
           three golden sources (their IR must equal tests/program/ir/*.ir),
           a missing file, a directory and /dev/zero.

The two designs must agree exactly: every line written, the outcome, the
reason, the line and the column. Each must agree with today's reader in the
same way, except for the improvements the owner's answers and ADR 0019 §2-§3
make, each recognised by a rule and counted:

  core-word    a Forth-2012 Core or Core Ext word outside IR 0.1 is refused as
               "a Forth word outside IR 0.1" where today's reader says
               "not a known word": same place, same lines before it;
  core-name    a definition of such a word is refused as a redefinition, where
               today's reader accepted it (`: . drop ;`, `: depth 0 ;`);
  number-name  a definition whose name reads as a number is refused (owner's
               answer 4), where today's reader accepted it.

For the last two, the lines written before the refusal must be the lines
today's reader wrote for the same text up to there. Any other difference is
a failure, and so is a reader case on which today's reader no longer gives
its test's verdict (the extraction would be wrong). --list prints every
difference with its rule. Finite tests on the Gforth that GFORTH names.
"""
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tests" / "program"))
import ir_reader_files  # noqa: E402

TESTS = (ROOT / "tests/program/ir-reader.fs").read_text(encoding="utf-8")
READER = (ROOT / "src/program/ir-reader.fs").read_text(encoding="utf-8")
SEMANTICS = (ROOT / "src/program/verify-semantics.fs").read_text(encoding="utf-8")

WHY = {m.group(2): int(m.group(1))
       for m in re.finditer(r"^(\d+) constant ir-why-([\w-]+)", READER, re.M)}
OUTCOME = {"ok": 0, "invalid": 1, "unsupported": 5, "full": 6}
UNKNOWN, NOT_IR, REDEFINED, NUMBER_NAME = 1, 2, 10, 30
UNKNOWN_TEXT = "not a known word or 32-bit decimal"
NOT_IR_TEXT = "a Forth word outside IR 0.1"


def reserved_names():
    """The reserved names of verify-semantics.fs (its s\\" strings)."""
    names = []
    for m in re.finditer(r'^s\\" (.*)"\s*(?:\n)?pv-reserve-all', SEMANTICS, re.M):
        text = m.group(1).replace("\\\\", "\0").replace("\\q", '"').replace("\0", "\\")
        names += text.split()
    return set(names)


RESERVED = reserved_names()
OLD_VOCABULARY = set(re.findall(r's" (\S+)" ir-(?:word|data|division|return)\b', READER))


def number_like(name):
    """verify-semantics.fs's rule for names that read as numbers."""
    if len(name) > 1 and name[0] == "'":
        return True
    i = 0
    while i < len(name) and name[i] in "+-#$%&":
        i += 1
    rest = name[i:]
    if not rest:
        return False
    if len(rest) > 1 and rest[0] == "." and rest[1] in "0123456789":
        return True
    return rest[0] in "0123456789" or (i > 0 and rest[0].lower() in "abcdef")


# ---------------------------------------------------------------- the inputs

S_QUOTE = re.compile(r'\bs" ([^"]*)"')


def macros():
    """Words of the reader tests made only of `s" ..." feed`."""
    found = {}
    for m in re.finditer(r"^: ([\w-]+) \( -- \)\n((?:  s\" [^\"]*\" feed(?: ;)?\n)+)",
                         TESTS, re.M):
        found[m.group(1)] = S_QUOTE.findall(m.group(2))
    return found


def feeds(body, macro):
    """The lines a test feeds, with odd-line pokes applied, or None."""
    lines, tokens, i = [], re.findall(r's" [^"]*"|\S+', body), 0
    while i < len(tokens):
        t = tokens[i]
        if t.startswith('s" '):
            text, j = bytearray(t[3:-1], "ascii"), i + 1
            if j < len(tokens) and tokens[j] == "odd-line":
                j += 1
                while j + 2 < len(tokens) and tokens[j + 2] == "poke":
                    text[int(tokens[j + 1])] = int(tokens[j])
                    j += 3
            if j < len(tokens) and tokens[j] == "feed":
                lines.append(bytes(text))
                i = j + 1
                continue
            return None
        if t in macro:
            lines += [x.encode() for x in macro[t]]
        elif t not in ("start", "start-transcript", "verdict"):
            return None
        i += 1
    return lines


def reader_cases():
    """(name, text, expected verdict of today's reader) for each verdict case."""
    macro, cases = macros(), []
    for m in re.finditer(r"T\{(.*?)\}T", TESTS, re.S):
        block = re.sub(r"\s*\n\s*", " ", m.group(1)).strip()
        v = re.match(r"(start(?:-transcript)?) (.*?)verdict(?: as-reference\?)? -> "
                     r"outcome-(\w+) ir-why-([\w-]+) (\d+) (\d+)( true)?$", block)
        if not v:
            continue
        lines = feeds(v.group(2), macro)
        if lines is None:
            continue
        text = b"\n".join(lines) + (b"\n" if lines and not lines[-1] else b"")
        expected = (OUTCOME[v.group(3)], WHY[v.group(4)], int(v.group(5)), int(v.group(6)))
        cases.append((f"reader: {block[:70]}", text, expected))
    return cases


# The prototype's hostile inputs (docs/development/measurements/two-mode-
# prototype-2026-11-03/adversarial.fs, its F part, a run while compiling, is
# in tests/program/verify.fs), then more: names that read as numbers, Core
# words as names, control characters, comments, lengths.
HOSTILE = [
    # A. Recognizer and number syntaxes.
    ': f "x" ;', ': f "x dup y" ;', ": f `dup ;", ": f ``dup ;", ": f <dup> ;", ": f ->x ;",
    ": f +>x ;", ": f '>x ;", ": f ${HOME} ;", ": f forth:dup ;", ": f forth:bye ;",
    ": f 1. ;", ": f 1.5 ;", ": f .5 ;", ": f 1e ;", ": f 2p ;", ": f 'a' ;", ": f '' ;",
    ": f $10 ;", ": f #10 ;", ": f %10 ;", ": f &10 ;", ": f 0x10 ;", ": f 1_000 ;",
    ": f --5 ;", ": f +5 ;", ": f -2147483648 ;", ": f 2147483648 ;",
    ": f 18446744073709551616 ;", "-1 1e constant x", "1. constant x", "$ff constant x",
    # B. Forth words that change the interpreter, compile, or reach the host.
    ": f immediate ;", ": f ; immediate", ": f postpone dup ;", ": f [ 1 throw ] ;",
    ": f ] ;", ": f ' dup ;", ": f ['] dup ;", ": f [ 5 ] literal ;", "state @ constant s",
    's" bye" evaluate', "hex : f 10 ;", "16 base ! : f 10 ;", "bye", ": f bye ;", "quit",
    "abort", ":noname 1 ;", ": f does> ;", ": f recurse ;", ": f execute ;", ': f s" x" ;',
    ': f ." hi" ;', ".( hi)", ": f char x ;", "marker m", "only forth",
    "forth-wordlist 1 set-order", "include /etc/passwd", "0 0 ! 1 throw", ": f >in @ ;",
    "[defined] dup", "[if]", "words",
    # C. Structure cannot be forged by a literal.
    ": f 0 then ;", ": f 1 2 repeat ;", ": f if -1 ;", ": f begin 0 while 5 then ;",
    ": f -1 if 1 then ;",
    # D. Names.
    ": dup ;", ": DUP 1 ;", ": : ;", ": ; ;", ": ( ;", ": \\ ;",
    ": foo 1 ; : bar foo ; : FOO 2 ;", ": 5 7 ; : g 5 05 ;", ": x:dup 1 ; : g x:dup ;",
    ": . drop ;",
    # E. Comments and lines.
    ": f ( no close ;", ": f \\ ok ;\n;", ": f ) ;", ": f\nf ;", ":\nf ;",
    # More: names that read as numbers, and names that do not.
    ": 5 ;", ": -0 ;", ": 1e 1 ;", ": $10 ;", ": 'a' ;", ": .5 ;", ": -.5 ;", ": #10 ;",
    ": %1 ;", ": &7 ;", ": +5 ;", ": -a ;", ": $-1 ;", "5 constant 7", "1 constant -1",
    ": ->x 1 ; : g ->x ;", ': "x" 2 ; : g "x" ;', ": -rot 3 ; : g -rot ;",
    ": #tib 4 ; : g #tib ;", ": x:dup 5 ; : y X:DUP ;", ": g 1 ; : h g ;",
    # Core and Core Ext names, used and defined; Gforth's own words.
    ": emit ;", ": cells 1 ;", "1 constant base", ": depth 0 ;", ": f 1 cells ;",
    ": f 2over ;", ": f pick ;", ": f s>d ;", ": f u. ;", ": f within ;", ": f rdrop ;",
    ": f -rot ;", ": f 2nip ;", ": f lf-clamp ;",
    # Control characters and lengths.
    ":\tf\tdup\t;", ": f\x0cdup ;", ": f \x0b ;", ": f\x7f ;", "\\ \x80",
    ": abcdefghijklmnopqrstuvwxyz01234 1 ;", ": abcdefghijklmnopqrstuvwxyz012345 1 ;",
    "\\ " + "x" * 125, "\\ " + "x" * 126,
    # Comments and structure.
    ": f ( bye ) ;", ": f (x) ;", "( a ) : f ( b ) 1 ( c ) ; ( d )", ": f ( ) ;",
    ": f begin dup while 1- repeat drop ;", ": f if if if then then then ;",
    ": f 1 2 3 4 5 6 7 8 9 10 ;", "decimal : f 1 ; DECIMAL", ": f DECIMAL ;",
    ": f 1 ;\n: g f f + ;\n2 constant two\n: h two g * ;",
]


def hostile_cases():
    return [(f"hostile: {text!r}", text.encode("latin-1"), None) for text in HOSTILE]


# ---------------------------------------------------------------- the driver

DRIVER_HEAD = f"""require {ROOT}/src/program/ir-reader.fs
require {ROOT}/src/program/verify.fs
require {ROOT}/src/program/verify-alias.fs
: show ( c-addr u -- ) ." | " type cr ;
' show lf-verify-to
: four. ( a b c d -- ) 2swap swap . . swap . . ;
: old-lines ( c-addr u -- )
  begin dup while 2dup text-line-end drop >r over r@ lf-ir-feed r> 1+ over min /string
  repeat 2drop ;
: old-text ( c-addr u -- ) ." OLD" cr ['] show s" t.fs" lf-ir-start old-lines
  lf-ir-finish lf-ir-reason lf-ir-where ." = " four. cr ;
: new-text ( c-addr u -- ) ." NEW" cr s" t.fs" lf-verify-text lf-verify-reason
  lf-verify-where ." = " four. cr ;
: alias-text ( c-addr u -- ) ." ALIAS" cr s" t.fs" lf-alias-text lf-verify-reason
  lf-verify-where ." = " four. cr ;
: old-file ( c-addr u -- ) ." OLD" cr ['] show -rot lf-ir-read-file lf-ir-reason
  lf-ir-where ." = " four. cr ;
: new-file ( c-addr u -- ) ." NEW" cr lf-verify-file lf-verify-reason lf-verify-where
  ." = " four. cr ;
: alias-file ( c-addr u -- ) ." ALIAS" cr lf-alias-file lf-verify-reason lf-verify-where
  ." = " four. cr ;
: case. ( n -- ) ." CASE " . cr ;
: end. ( -- ) ." DEPTH " depth . cr ;
: texts ( c-addr u n -- ) case. 2dup old-text 2dup new-text alias-text end. ;
: files ( c-addr u n -- ) case. 2dup old-file 2dup new-file alias-file end. ;
"""


def forth_string(data):
    out = []
    for b in data:
        out.append("\\x%02x" % b if b in (34, 92) or not 32 <= b < 127 else chr(b))
    return 's\\" ' + "".join(out) + '"'


def run_driver(gforth, entries, directory):
    """Run every (kind, data) entry; for each, the three results."""
    lines = [DRIVER_HEAD]
    for n, (kind, data) in enumerate(entries):
        lines.append(f": c{n} ( -- c-addr u ) {forth_string(data)} ;")
        lines.append(f"c{n} {n} {kind}")
    lines.append("bye")
    driver = Path(directory) / "verify-check.fs"
    driver.write_text("\n".join(lines) + "\n", encoding="ascii")
    done = subprocess.run(["timeout", "-k", "5", "300", gforth, str(driver)],
                          stdin=subprocess.DEVNULL, capture_output=True, text=True,
                          errors="replace", cwd=ROOT)
    results, current, who = {}, None, None
    for line in done.stdout.splitlines():
        if line.startswith("CASE "):
            current = int(line.split()[1])
            results[current] = {"depth": None}
        elif line in ("OLD", "NEW", "ALIAS"):
            who = line
            results[current][who] = [[], None]
        elif line.startswith("| "):
            results[current][who][0].append(line[2:])
        elif line.startswith("= "):
            results[current][who][1] = tuple(int(x) for x in line.split()[1:])
        elif line.startswith("DEPTH "):
            results[current]["depth"] = int(line.split()[1])
    if len(results) != len(entries):
        raise SystemExit(f"{len(results)} results for {len(entries)} inputs:\n"
                         f"{done.stdout[-2000:]}{done.stderr[-2000:]}")
    return results


# ------------------------------------------------------------ the comparison

def token_of(line):
    """The token a diagnostic line quotes, after its reason."""
    parts = line.split(": ", 2)
    return parts[2] if len(parts) == 3 else ""


def prefix_rule(old, new):
    """The new run's lines before its diagnostic were the old run's too."""
    return new[0][:-1] == old[0][:len(new[0]) - 1]


def intended(old, new):
    """The rule that explains a difference between today's reader and the new
    code, or None."""
    (old_lines, old_verdict), (new_lines, new_verdict) = old, new
    if not new_lines:
        return None
    last = new_lines[-1]
    if (new_verdict[1] == NOT_IR and old_verdict == (5, UNKNOWN) + new_verdict[2:]
            and token_of(last).lower() in RESERVED
            and new_lines[:-1] == old_lines[:-1]
            and old_lines[-1] == last.replace(NOT_IR_TEXT, UNKNOWN_TEXT, 1)):
        return "core-word"
    if new_verdict[:2] == (5, REDEFINED) and prefix_rule(old, new):
        name = token_of(last).lower()
        if name in RESERVED and name not in OLD_VOCABULARY:
            return "core-name"
    if new_verdict[:2] == (5, NUMBER_NAME) and prefix_rule(old, new) \
            and number_like(token_of(last)):
        return "number-name"
    return None


def file_entries(directory):
    entries, names = [], []
    for name, (data, *_rest) in ir_reader_files.CASES.items():
        path = Path(directory) / f"{name}.fs"
        path.write_bytes(data)
        entries.append(("files", str(path).encode()))
        names.append((f"file: {name}", None))
    for source, _ in GOLDEN:
        entries.append(("files", source.encode()))
        names.append((f"golden: {source}", None))
    for path in ("tests/program/no-such-file.fs", "src", "/dev/zero"):
        entries.append(("files", path.encode()))
        names.append((f"file: {path}", None))
    return entries, names


GOLDEN = [("src/program/clamp.fs", "tests/program/ir/clamp.ir"),
          ("src/program/examples.fs", "tests/program/ir/examples.ir"),
          ("tests/program/ir/all-primitives.fs", "tests/program/ir/all-primitives.ir")]


def main():
    gforth = os.environ.get("GFORTH", "gforth")
    texts = reader_cases() + hostile_cases()
    with tempfile.TemporaryDirectory() as directory:
        files, file_names = file_entries(directory)
        entries = [("texts", text) for _, text, _ in texts] + files
        names = [(name, expected) for name, _, expected in texts] + file_names
        results = run_driver(gforth, entries, directory)
    problems, counts, listed = [], {}, []
    golden = {f"golden: {s}": (ROOT / g).read_text(encoding="utf-8").splitlines()
              for s, g in GOLDEN}
    for n, (name, expected) in enumerate(names):
        r = results[n]
        old, new, alias = r["OLD"], r["NEW"], r["ALIAS"]
        group = name.split(":")[0]
        if r["depth"] != 0:
            problems.append(f"{name}: data stack depth {r['depth']} after the runs")
        if expected is not None and old[1] != expected:
            problems.append(f"{name}: today's reader gave {old[1]}, its test says {expected}")
        if new != alias:
            problems.append(f"{name}: the designs differ:\n  shift {new}\n  alias {alias}")
        if name in golden and (new[1][0] != 0 or new[0] != golden[name]):
            problems.append(f"{name}: IR differs from the golden file")
        rule = "identical" if new == old else intended(old, new)
        if rule is None:
            problems.append(f"{name}: differs from today's reader:\n  old {old}\n  new {new}")
            rule = "unexplained"
        counts.setdefault(group, {}).setdefault(rule, 0)
        counts[group][rule] += 1
        if rule != "identical":
            listed.append(f"{rule:12} {name}  old {old[1]} -> new {new[1]}")
    if "--list" in sys.argv:
        print("\n".join(listed))
    for problem in problems:
        print(problem, file=sys.stderr)
    summary = "; ".join(f"{group} " + ", ".join(f"{k} {v}" for k, v in sorted(c.items()))
                        for group, c in counts.items())
    print(f"program words cross-check: {len(names)} inputs, both designs identical on "
          f"{sum(1 for n in range(len(names)) if results[n]['NEW'] == results[n]['ALIAS'])}; "
          f"against today's reader: {summary}")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
