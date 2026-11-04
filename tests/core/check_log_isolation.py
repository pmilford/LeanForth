#!/usr/bin/env python3
"""The derivation log's isolation (ADR 0013 L5, item 6), checked on the
source text as allow-lists (L2 of the review of 2026-11-03):
1. In src/kernel/, a file names no log word but the protocol: the hot test
   lf-log?, the open and close words, lf-log-begin and lf-log-publish, the
   reference lf-log-none and the rule codes lf-rule-*; and it loads nothing
   from src/present/.
2. In src/present/, a file names only the log's reading words (READERS):
   the printers only read it; and it loads nothing from src/kernel/.
3. In src/cli/, a file names only the log's switches (its level and
   limits, set outside a check) and the read-only questions whether the
   last log is complete and at which level it was kept: the command line
   turns the log on for print, never writes a record. Every other file
   under src/ names no log word at all.
4. Outside the log module, no field of a record, mark, copied reference,
   the header, the pools or the options is followed by ! or +!.
5. src/core/derivation-log.fs names only its own words and the words in
   LOG_USES: standard Forth words, the context words, and the stores'
   read-only accessors, so no diagnostic, printing, store allocation or
   rollback, walk or fuel word. Heap memory and THROW appear only where
   RESTRICTED says: ALLOCATE in the word that makes the pools, FREE in the
   word that gives them back, THROW in the context's teardown, ABORT" in
   the catalogue's load-time index.
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
READERS = {
    "lf-log-count", "lf-log-level", "lf-log-decl", "lf-log-cut", "lf-log-complete?",
    "lf-log-record", "lf-log-input", "lf-log-published", "lf-log-premise",
    "lf-log-term-copies", "lf-log-level-copies", "lf-log-cref-copies", "lf-log-term-slot",
    "lf-log-level-slot", "lf-log-cref-slot", "lf-log-arg-ref", "lf-log-copy?",
    "lf-log-copy-index", "lf-log-written", "lf-log-restarts", "lf-log-rule-name",
    "lf-log-kind", "lf-kind-a", "lf-kind-b", "lf-kind-out", "lf-log-entry",
    "lf-log-entry-code", "lf-log-entry-kinds", "lf-log-entry-name", "lf-log-none",
    "lf-log-unkept", "lf-log-off", "lf-log-steps", "lf-log-terms",
    "lf-log-record-capacity", "lf-log-mark-capacity", "lf-log-term-capacity",
    "lf-log-level-capacity", "lf-log-cref-capacity", "lf-log-arg-capacity",
    "logrec-rule", "logrec-outcome", "logrec-start", "logrec-depth", "logrec-a", "logrec-b",
    "logrec-out", "logcref-name", "logcref-generation", "logcref-count", "logcref-args",
}
SWITCHES = {
    "lf-log-set", "lf-log-limits", "lf-log-capacities", "lf-log-off", "lf-log-steps",
    "lf-log-terms", "lf-log-level", "lf-log-complete?",
}
FIELD = re.compile(r"(logrec|logmark|logcref)-|lf-logs-|lf-logp-|lf-logopt-")
LOG_WORD = re.compile(r"lf-log|lf-rule-|lf-bound-|lf-kind-(a|b|out)$|(logrec|logmark|logcref)-|"
                      r"lf-logs-|lf-logp-|lf-logopt-")
FORTH = set("""
! ' * + +! , - -rot / /mod 0< 0<> 0= 0> 1+ 1- 2* 2@ 2! 2drop 2dup 2swap : :noname ; < <> =
> >r ?do ?dup @ [defined] [if] [then] align aligned allot and begin case cell+ cells
constant create do drop dup else endcase endof erase execute exit false here i if invert
loop max min mod move negate nip of or over pick r> r@ repeat require rot rshift lshift
s" swap then true tuck unloop while within begin-structure end-structure field: +field
max-n abort" allocate free throw
""".split())
CONTEXT = {"context-in-job?", "context-record:", "context-setup", "context-teardown"}
STORES = {
    "lf-term-read", "lf-term-identity", "lf-term-binary-tag?", "lf-level-read",
    "lf-level-identity", "lf-level-binary-tag?", "lf-level-tag-succ", "lf-level-tag-zero",
    "lf-level-tag-param", "lf-cref-read", "lf-cref-levels", "lf-cref-pair@",
    "lf-input-intact?", "lf-input-mark", "lf-input-fingerprint", "mark-count", "/node",
    "node!", "ok?", "upto?", "lf-tag-sort", "lf-tag-symbolic-sort", "lf-tag-bvar",
    "lf-tag-constant", "lf-tag-app", "lf-tag-lam", "lf-tag-pi", "lf-log-preset-level",
    "lf-log-preset-records", "lf-log-preset-marks", "lf-log-preset-terms",
    "lf-log-preset-levels",
    # The local context, read only: a free variable is copied as the bound
    # variable it stands for (plan task 4.2.2a).
    "lf-tag-fvar", "lf-fvar-live?", "lf-fvar-depth",
}
LOG_USES = FORTH | CONTEXT | STORES
RESTRICTED = {
    "allocate": {"lf-log-allocate"},
    "free": {"lf-log-release"},
    "throw": {":noname"},
    'abort"': {"lf-log-index"},
}
DEFINERS = {":", "constant", "create", "field:", "+field", "begin-structure", "context-record:"}
TOKEN = re.compile(r"\S+")


def lines(path):
    """The code of a Forth file, line by line, without comments and
    strings, and without load-time assertions ([if] ... [then] on one
    line, or a condition whose [if] follows on the next line)."""
    out = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if "[if]" in line and "[then]" in line:
            continue
        line = re.sub(r'(^|\s)\\(\s.*|$)', " ", line)          # line comments
        line = re.sub(r'(^|\s)\(\s[^)]*\)', " ", line)          # stack comments
        line = re.sub(r'(^|\s)(s|c|\.|abort|s\\)"\s[^"]*"', lambda m: m.group(0).split('"')[0] + '"', line)
        line = re.sub(r'(^|\s)\.\(\s[^)]*\)', " ", line)        # .( ... )
        out.append(line.lower())
    return out


def words(path):
    return [t for line in lines(path) for t in TOKEN.findall(line)]


def log_words(tokens):
    return {t for t in tokens if LOG_WORD.match(t)}


def field_stores(tokens):
    return {a for a, b in zip(tokens, tokens[1:]) if FIELD.match(a) and b in ("!", "+!")}


def definitions(tokens):
    """Each colon definition's name (":noname" for a nameless one) with its
    tokens; the tokens outside any definition under the name None."""
    out, name, body = [], None, []
    it = iter(tokens)
    for t in it:
        if name is None and t in (":", ":noname"):
            out.append((None, body))
            name, body = (next(it, "") if t == ":" else ":noname"), []
        elif name is not None and t == ";":
            out.append((name, body))
            name, body = None, []
        else:
            body.append(t)
    out.append((name, body))
    return out


def log_module_problems():
    tokens = words(LOG_MODULE)
    own = {b for a, b in zip(tokens, tokens[1:]) if a in DEFINERS}
    problems = []
    unknown = {t for t in tokens if t not in own and t not in LOG_USES
               and not re.fullmatch(r"-?\d+", t) and not t.endswith(".fs")}
    if unknown:
        problems.append(f"{LOG_MODULE}: names words outside its allow-list: {sorted(unknown)}")
    for name, body in definitions(tokens):
        for word, allowed in RESTRICTED.items():
            if word in body and name not in allowed:
                problems.append(f"{LOG_MODULE}: {word} in {name or 'top-level code'}")
    return problems


def main():
    problems = []
    for path in sorted(pathlib.Path("src").rglob("*.fs")):
        if path == LOG_MODULE:
            continue
        tokens = words(path)
        named = log_words(tokens)
        text = path.read_text(encoding="utf-8")
        layer = path.parts[1]
        if layer == "kernel":
            extra = {w for w in named if w not in PROTOCOL and not w.startswith("lf-rule-")}
            if extra:
                problems.append(f"{path}: names log words outside the protocol: {sorted(extra)}")
            if re.search(r"^\s*require\s+\.\./present/", text, flags=re.M):
                problems.append(f"{path}: loads presentation code")
        elif layer == "present":
            extra = {w for w in named if w not in READERS and not w.startswith("lf-rule-")
                     and not w.startswith("lf-bound-")}
            if extra:
                problems.append(f"{path}: names log words beyond its readers: {sorted(extra)}")
            if re.search(r"^\s*require\s+\.\./kernel/", text, flags=re.M):
                problems.append(f"{path}: presentation code loads the checker")
        elif layer == "cli":
            extra = named - SWITCHES
            if extra:
                problems.append(f"{path}: names log words beyond its switches: {sorted(extra)}")
        elif named:
            problems.append(f"{path}: names log words: {sorted(named)}")
        stores = field_stores(tokens)
        if stores:
            problems.append(f"{path}: writes the log's fields: {sorted(stores)}")
    problems += log_module_problems()
    for problem in problems:
        print(problem)
    if problems:
        return 1
    print("derivation log isolation: the kernel uses only the protocol, the printers only "
          "read, the command line only switches, the log module only its allow-list")
    return 0


if __name__ == "__main__":
    sys.exit(main())
