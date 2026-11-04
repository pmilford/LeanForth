#!/usr/bin/env python3
"""Round trip (test tooling only): IR -> Forth text -> correctness mode -> IR.

For each IR file, write it back as Forth source (calls in upper case, a
literal whose spelling is a name the file defines written with a leading
zero, a different layout), run the prototype's correctness vocabulary on
that source, and require the same IR apart from locations and the source
line. Then IR that no Forth source can produce (a name of the vocabulary,
a forward call, recursion) must be refused.

Usage: roundtrip.py GFORTH IR... (from the repository root).
"""
import re
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
WORK = Path(tempfile.mkdtemp())


def to_forth(ir_text):
    names = set()
    out, kept = [], []
    pending = None   # constant name while its body is collected
    for line in ir_text.splitlines()[2:]:
        line = re.sub(r" @\d+:\d+$", "", line).strip()
        op, _, arg = line.partition(" ")
        if op == "word":
            out.append(": " + arg)
            names.add(arg)
        elif op == "constant":
            pending = arg
        elif op == "end":
            if pending is None:
                out.append(";")
            else:
                out.append("  ".join(kept) + "  CONSTANT " + pending)
                names.add(pending)
                pending, kept = None, []
        else:
            if op == "prim":
                tok = arg.upper()
            elif op == "call":
                tok = arg.upper()
            elif op == "lit":
                tok = arg
                while tok.lstrip("-") and tok.lower() in names:
                    tok = tok.replace("-", "-0", 1) if tok.startswith("-") else "0" + tok
            else:
                tok = op.upper()
            if pending is None:
                out.append("    " + tok)
            else:
                kept.append(tok)
    return "\n".join(out) + "\n"


def strip(ir_text):
    lines = ir_text.splitlines()
    return [re.sub(r" @\d+:\d+$", "", x) for x in lines if not x.startswith("source ")]


def run(gforth, path):
    out = subprocess.run(["bash", str(HERE / "ir-of.sh"), gforth, str(path)],
                         capture_output=True, text=True).stdout
    *ir, last = out.rstrip("\n").split("\n")
    return "\n".join(ir) + "\n", last.split()[1]


def main():
    gforth, files = sys.argv[1], sys.argv[2:]
    bad = 0
    for f in files:
        ir = Path(f).read_text()
        src = WORK / (Path(f).stem + ".fs")
        src.write_text(to_forth(ir))
        back, outcome = run(gforth, src)
        same = outcome == "0" and strip(back) == strip(ir)
        bad += not same
        print("%s: %s (%d instructions)" % (f, "identical IR" if same else "DIFFERENT, outcome " + outcome,
                                            len(strip(ir)) - 1))
    # Forth source that no accepted IR can come from must be refused.
    for name, text in (("vocabulary-name", ": dup 1 ;\n"),
                       ("forward-call", ": f g ;\n: g 1 ;\n"),
                       ("recursion", ": f f ;\n"),
                       ("redefinition", ": foo 1 ;\n: bar foo ;\n: FOO 2 ;\n")):
        src = WORK / (name + ".fs")
        src.write_text(text)
        back, outcome = run(gforth, src)
        print("%s: outcome %s: %s" % (name, outcome, back.rstrip("\n").split("\n")[-1]))
        bad += outcome == "0"
    print("round trip: %d failures" % bad)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
