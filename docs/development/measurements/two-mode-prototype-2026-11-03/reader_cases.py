#!/usr/bin/env python3
"""Replay today's reader tests on the two-mode prototype (test tooling only).

Reads tests/program/ir-reader.fs, takes every test of the form
  T{ start[-transcript] <feeds> verdict -> OUTCOME REASON LINE COLUMN }T
together with the checks that follow it on the written diagnostic
(written ... compare), the transcript (contains?, transcribed?) and the
reference transcript (keep-reference, as-reference?), runs the same lines
through the prototype's correctness vocabulary (cv.fs) on the given Gforth,
and compares outcome, reason, line, column, diagnostic text and IR.

Usage: reader_cases.py GFORTH [ms] (from the repository root); with ms,
the lines run in the mode-shift prototype's verification state (ms.fs).
"""
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
TESTS = Path("tests/program/ir-reader.fs").read_text()
READER = Path("src/program/ir-reader.fs").read_text()

WHY = {m.group(2): int(m.group(1))
       for m in re.finditer(r"^(\d+) constant ir-why-([\w-]+)", READER, re.M)}
OUTCOME = {"ok": 0, "invalid": 1, "unsupported": 2, "full": 3}

S_QUOTE = re.compile(r'\bs" ([^"]*)"')


def macros():
    """Words of the test file made only of `s" ..." feed`."""
    found = {}
    for m in re.finditer(r"^: ([\w-]+) \( -- \)\n((?:  s\" [^\"]*\" feed(?: ;)?\n)+)", TESTS, re.M):
        found[m.group(1)] = S_QUOTE.findall(m.group(2))
    return found


def feeds(body, macro):
    """The lines a test feeds, with odd-line pokes applied."""
    lines = []
    tokens = re.findall(r's" [^"]*"|\S+', body)
    i = 0
    while i < len(tokens):
        t = tokens[i]
        if t.startswith('s" '):
            text = bytearray(t[3:-1], "ascii")
            j = i + 1
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


def forth_string(data):
    out = []
    for b in data:
        c = chr(b)
        if c == '"' or c == "\\" or not (32 <= b < 127):
            out.append("\\x%02x" % b)
        else:
            out.append(c)
    return 's\\" ' + "".join(out) + '"'


def main():
    gforth = sys.argv[1]
    macro = macros()
    cases, events, skipped, current = [], [], 0, None
    for m in re.finditer(r"T\{(.*?)\}T|^keep-reference$", TESTS, re.S | re.M):
        if m.group(0) == "keep-reference":
            if current is not None:
                events.append(("keep", current, None))
            continue
        b = re.sub(r"\s*\n\s*", " ", m.group(1)).strip()
        v = re.match(r"(start(?:-transcript)?) (.*?)verdict(?: as-reference\?)? -> "
                     r"outcome-(\w+) ir-why-([\w-]+) (\d+) (\d+)( true)?$", b)
        if v and (lines := feeds(v.group(2), macro)) is not None:
            n = len(cases)
            cases.append((n, lines, (OUTCOME[v.group(3)], WHY[v.group(4)], int(v.group(5)),
                                     int(v.group(6))), b))
            current = n
            if "as-reference?" in b:
                events.append(("as-reference", n, None))
            continue
        for kind, pat in (("written", r'written s" ([^"]*)" compare -> 0$'),
                          ("contains", r'transcript-text s" ([^"]*)" contains\? -> true$'),
                          ("equals", r's" ([^"]*)" transcribed\? -> true$')):
            w = re.match(pat, b)
            if w:
                if current is None:
                    skipped += 1
                else:
                    events.append((kind, current, w.group(1)))
                break
        else:
            skipped += 1
            current = None
    mode = (sys.argv[2:] or ["cv"])[0]
    shift = mode in ("ms", "g1")
    lines = ["require " + str(HERE / "cv.fs")]
    lines += ["require " + str(HERE / "ms.fs")] if shift else []
    lines += ["require " + str(HERE / "ms-gforth1.fs")] if mode == "g1" else []
    lines += ["create case-text 4096 allot",
             "variable case#",
             ": run-case ( c-addr u n -- ) case# ! case-text swap 2dup 2>r move",
             '  ." BEGIN " case# @ . cr 2r> s" t.fs" %s drop' % {"ms": "ms-run", "g1": "g1-run"}.get(mode, "cv-run"),
             '  ." RESULT " case# @ . cv-outcome @ . cv-why @ .',
             "  cv-outcome @ if cv-err-line @ . cv-err-col @ . else cv-line# @ . 0 . then cr ;"]
    for n, feed_lines, _, _ in cases:
        text = b"\n".join(feed_lines)
        lines.append(forth_string(text) + " %d run-case" % n)
    lines.append("bye")
    script = Path(tempfile.mkdtemp()) / "reader-cases.gen.fs"
    script.write_text("\n".join(lines) + "\n")
    out = subprocess.run(["timeout", "-k", "5", "120", gforth, str(script)],
                         stdin=subprocess.DEVNULL, capture_output=True, text=True).stdout
    results, outputs, current = {}, {}, None
    for line in out.splitlines():
        if line.startswith("BEGIN "):
            current = int(line.split()[1])
            outputs[current] = []
        elif line.startswith("RESULT "):
            f = [int(x) for x in line.split()[1:]]
            results[f[0]] = tuple(f[1:])
            current = None
        elif current is not None:
            outputs[current].append(line)
    bad = 0
    for n, _, expected, text in cases:
        if results.get(n) != expected:
            bad += 1
            print("DIFF verdict case %d: expected %s got %s: %s" % (n, expected, results.get(n), text))
    ref, checks = None, 0
    for kind, n, want in events:
        transcript = "".join(x + "|" for x in outputs.get(n, []))
        if kind == "keep":
            ref = transcript
            continue
        checks += 1
        written = outputs[n][-1] if outputs.get(n) else ""
        if kind == "written":
            ok = written == want
        elif kind == "contains":
            ok = want in transcript
        elif kind == "equals":
            ok = transcript == want
        else:
            ok = transcript == ref
        if not ok:
            bad += 1
            print("DIFF %s case %d: want %r\n  got %r" % (kind, n, want, transcript))
    print("reader tests replayed: %d verdict cases, %d output checks, %d differences; "
          "%d test blocks not of these shapes skipped" % (len(cases), checks, bad, skipped))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
