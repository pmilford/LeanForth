#!/usr/bin/env python3
"""The derivation log's isolation (ADR 0013 L5, item 6), checked on the
source text:
1. In src/kernel/, a file names no log word but the protocol: the hot test
   lf-log?, the open and close words, lf-log-begin and lf-log-publish, the
   reference lf-log-none and the rule codes lf-rule-*; and it loads nothing
   from src/present/.
2. In src/present/, a file names none of the protocol words that write a
   log (open, close, begin, publish, start, stop, set, limits): the
   printers only read it; and it loads nothing from src/kernel/.
3. In src/cli/, a file names only the log's switches (its level and
   limits, set outside a check) and the read-only questions whether the
   last log is complete and at which level it was kept: the command line
   turns the log on for print, never writes a record. Every other file
   under src/ names no log word at all.
4. src/core/derivation-log.fs names none of the words that would let it
   change a verdict or the checker's state: no diagnostic, THROW, ABORT,
   heap memory, printing, store allocation or rollback, walk, or fuel word.
Test-only; prints one line and exits 0 when all hold, 1 otherwise."""
import pathlib
import re
import sys

LOG_MODULE = pathlib.Path("src/core/derivation-log.fs")
PROTOCOL = {
    "lf-log?", "lf-log-open", "lf-log-infer", "lf-log-close", "lf-log-decided",
    "lf-log-close-handle", "lf-log-close-maybe", "lf-log-close-whnf", "lf-log-close-all",
    "lf-log-begin", "lf-log-publish", "lf-log-none",
}
WRITERS = PROTOCOL - {"lf-log?", "lf-log-none"} | {
    "lf-log-start", "lf-log-stop", "lf-log-set", "lf-log-limits", "lf-log-auto",
}
FORBIDDEN_IN_LOG = {
    "lf-diag-note", "lf-diag!", "lf-diag-store", "lf-diag-walk", "lf-diag-frames",
    "throw", "abort", 'abort"', "allocate", "resize", "free", "type", "emit", "cr", ".",
    ".r", "u.", "lf-term-add", "lf-level-add", "lf-term-binary", "lf-term-app", "lf-term-lam",
    "lf-term-pi", "lf-term-sort", "lf-term-bvar", "lf-level-succ", "lf-level-max",
    "lf-level-imax", "lf-level-param", "node-new", "store-new", "store-new-slot", "store-claim",
    "store-rollback", "store-clear", "lf-input-rollback", "lf-term-reset", "lf-level-reset",
    "walk-run", "walk-run-pair", "walk-budget", "frame-call", "frame-budget",
    "lf-cref-new", "lf-cterm-new", "lf-hterm-sort",
}
SWITCHES = {
    "lf-log-set", "lf-log-limits", "lf-log-capacities", "lf-log-off", "lf-log-steps",
    "lf-log-terms", "lf-log-level", "lf-log-complete?",
}
TOKEN = re.compile(r"\S+")


def words(path):
    """The tokens of a Forth file, without comments and strings, and
    without load-time assertions ([if] ... [then] on one line, which run
    while the file loads, never in a check)."""
    out = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if "[if]" in line and "[then]" in line:
            continue
        line = re.sub(r'(^|\s)\\(\s.*|$)', " ", line)          # line comments
        line = re.sub(r'(^|\s)\(\s[^)]*\)', " ", line)          # stack comments
        line = re.sub(r'(^|\s)(s|c|\.|abort|s\\)"\s[^"]*"', lambda m: m.group(0).split('"')[0] + '"', line)
        out.extend(TOKEN.findall(line.lower()))
    return out


def log_words(tokens):
    return {t for t in tokens if t.startswith("lf-log") or t.startswith("lf-rule-")}


def main():
    problems = []
    for path in sorted(pathlib.Path("src").rglob("*.fs")):
        if path == LOG_MODULE:
            continue
        tokens = words(path)
        named = log_words(tokens)
        if path.parts[1] == "kernel":
            extra = {w for w in named if w not in PROTOCOL and not w.startswith("lf-rule-")}
            if extra:
                problems.append(f"{path}: names log words outside the protocol: {sorted(extra)}")
            text = path.read_text(encoding="utf-8")
            if re.search(r"^\s*require\s+\.\./present/", text, flags=re.M):
                problems.append(f"{path}: loads presentation code")
        elif path.parts[1] == "present":
            writes = named & WRITERS
            if writes:
                problems.append(f"{path}: writes the log: {sorted(writes)}")
            text = path.read_text(encoding="utf-8")
            if re.search(r"^\s*require\s+\.\./kernel/", text, flags=re.M):
                problems.append(f"{path}: presentation code loads the checker")
        elif path.parts[1] == "cli":
            extra = named - SWITCHES
            if extra:
                problems.append(f"{path}: names log words beyond its switches: {sorted(extra)}")
        elif named:
            problems.append(f"{path}: names log words: {sorted(named)}")
    forbidden = set(words(LOG_MODULE)) & FORBIDDEN_IN_LOG
    if forbidden:
        problems.append(f"{LOG_MODULE}: names words it must not use: {sorted(forbidden)}")
    for problem in problems:
        print(problem)
    if problems:
        return 1
    print("derivation log isolation: the kernel uses only the protocol, the printers only "
          "read, the command line only switches, the log module uses no forbidden word")
    return 0


if __name__ == "__main__":
    sys.exit(main())
