#!/usr/bin/env python3
"""The derivation log's isolation (ADR 0013 L5, item 6), checked on the
source text as allow-lists (L2 of the review of 2026-11-03, N2 of the
second review).

What it checks, on every file under src/ (comments, strings and the
exact load-time assertion `[if] .( ... ) cr abort [then]` removed; every
other token checked, also inside [if] ... [then] and after ' or [']):
1. In src/kernel/, a file names no log word but the protocol: the hot test
   lf-log?, the open and close words, lf-log-begin and lf-log-publish, the
   reference lf-log-none and the rule codes lf-rule-*; and it loads nothing
   from src/present/ or src/cli/.
2. In src/present/, a file names only the log's reading words (READERS),
   which all give values, never an address of the log's records, pools or
   header; it loads only from ./, ../lib/ and ../core/; and it uses no word
   that looks a name up or runs text (NAME_LOOKUP).
3. In src/cli/, a file names only the log's switches (its level and
   limits, set outside a check) and the read-only questions whether the
   last log is complete and at which level it was kept: the command line
   turns the log on for print, never writes a record. Every other file
   under src/ names no log word at all.
4. Outside the log module, no field of a record, mark, copied reference,
   the header, the pools or the options is followed by ! or +!.
5. src/core/derivation-log.fs names only its own words and the words in
   LOG_USES: standard Forth words, the context words, and the stores'
   read-only accessors, every one of which gives values, not addresses
   (so no diagnostic, printing, store allocation or rollback, walk, fuel
   or name-lookup word, and no address of another module's state); it
   loads only from ./ and ../lib/. Some words appear only where
   RESTRICTED says: ALLOCATE in the word that makes the pools, FREE in the
   word that gives them back, THROW in the context's teardown, ABORT" in
   the catalogue's load-time index, and ALLOT, HERE, `,` and ALIGN only at
   load time (top-level code and the catalogue's entry builder), CREATE
   and CONSTANT only at top level.

What it cannot see (the behavioural tests are the evidence there):
addresses computed by arithmetic from an allowed address (the log
module's own state plus an offset, say); an execution token taken
elsewhere and passed in; and anything a word it allows does in turn
(its allow-list is reviewed by hand). Checking by word reference instead
(the compiled code's references) is not done: Gforth's threaded code has
no portable reader, and 0.7.3 and 1.0 differ.
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
    "lf-log-input", "lf-log-published", "lf-log-premise", "lf-log-rule@", "lf-log-outcome@",
    "lf-log-depth@", "lf-log-a@", "lf-log-b@", "lf-log-out@", "lf-log-term-node@",
    "lf-log-level-node@", "lf-log-cref@", "lf-log-term-copies", "lf-log-level-copies",
    "lf-log-cref-copies", "lf-log-arg-ref", "lf-log-copy?", "lf-log-copy-index",
    "lf-log-written", "lf-log-restarts", "lf-log-rule-name", "lf-log-kind", "lf-kind-a",
    "lf-kind-b", "lf-kind-out", "lf-log-entry", "lf-log-entry-code", "lf-log-entry-kinds",
    "lf-log-entry-name", "lf-log-none", "lf-log-unkept", "lf-log-off", "lf-log-steps",
    "lf-log-terms", "lf-log-record-capacity", "lf-log-mark-capacity",
    "lf-log-term-capacity", "lf-log-level-capacity", "lf-log-cref-capacity",
    "lf-log-arg-capacity", "lf-log-flaw",
}
SWITCHES = {
    "lf-log-set", "lf-log-limits", "lf-log-capacities", "lf-log-off", "lf-log-steps",
    "lf-log-terms", "lf-log-level", "lf-log-complete?",
}
NAME_LOOKUP = {"evaluate", "find", "sfind", "find-name", "search-wordlist", "included",
               "execute-parsing", "(find)"}
FIELD = re.compile(r"(logrec|logmark|logcref)-|lf-logs-|lf-logp-|lf-logopt-")
LOG_WORD = re.compile(r"lf-log|lf-rule-|lf-bound-|lf-kind-(a|b|out)$|(logrec|logmark|logcref)-|"
                      r"lf-logs-|lf-logp-|lf-logopt-")
FORTH = set("""
! ' * + +! , - -rot / /mod 0< 0<> 0= 0> 1+ 1- 2* 2@ 2! 2drop 2dup 2swap : :noname ; < <> =
> >r ?do ?dup @ [defined] [if] [then] [else] align aligned allot and begin case cell+ cells
constant create do drop dup else endcase endof erase execute exit false here i if invert
loop max min mod move negate nip of or over pick r> r@ repeat require rot rshift lshift
s" swap then true tuck unloop while within begin-structure end-structure field: +field
max-n abort" allocate free throw
""".split())
CONTEXT = {"context-in-job?", "context-record:", "context-setup", "context-teardown"}
STORES = {
    "lf-term-read", "lf-term-identity", "lf-term-binary-tag?", "lf-level-read",
    "lf-level-identity", "lf-level-binary-tag?", "lf-level-tag-succ", "lf-level-tag-zero",
    "lf-level-tag-param", "lf-cref-read", "lf-cref-level", "lf-input-intact?",
    "lf-input-mark-count", "lf-input-fingerprint", "/node", "node!", "node@", "ok?",
    "upto?", "lf-tag-sort", "lf-tag-symbolic-sort", "lf-tag-bvar", "lf-tag-constant",
    "lf-tag-app", "lf-tag-lam", "lf-tag-pi", "lf-log-preset-level", "lf-log-preset-records",
    "lf-log-preset-marks", "lf-log-preset-terms", "lf-log-preset-levels",
}
LOG_USES = FORTH | CONTEXT | STORES
LOAD_TIME = {None, "lf-log-entry,"}
RESTRICTED = {
    "allocate": {"lf-log-allocate"},
    "free": {"lf-log-release"},
    "throw": {":noname"},
    'abort"': {"lf-log-index"},
    "allot": LOAD_TIME, "here": LOAD_TIME, ",": LOAD_TIME, "align": LOAD_TIME,
    "create": {None}, "constant": {None},
}
LOADS = {
    "log": ("./", "../lib/"),
    "present": ("./", "../lib/", "../core/"),
}
DEFINERS = {":", "constant", "create", "field:", "+field", "begin-structure", "context-record:"}
TOKEN = re.compile(r"\S+")
ASSERTION = re.compile(r"\[if\]\s+\.\(\s[^)]*\)\s+cr\s+abort\s+\[then\]")


def lines(path):
    """The code of a Forth file, line by line, without comments, strings
    and the exact load-time assertion `[if] .( ... ) cr abort [then]`."""
    out = []
    for line in path.read_text(encoding="utf-8").splitlines():
        line = ASSERTION.sub(" ", line)
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


def loads(tokens):
    """The files a file loads (require and include)."""
    return [b for a, b in zip(tokens, tokens[1:]) if a in ("require", "include")]


def bad_loads(path, tokens, allowed):
    return [f"{path}: loads {target}" for target in loads(tokens)
            if not target.startswith(allowed) or "/kernel/" in target or "/cli/" in target
            or "/present/" in target and not target.startswith("./")]


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
    targets = set(loads(tokens))
    unknown = {t for t in tokens if t not in own and t not in LOG_USES
               and not re.fullmatch(r"-?\d+", t) and t not in targets}
    if unknown:
        problems.append(f"{LOG_MODULE}: names words outside its allow-list: {sorted(unknown)}")
    problems += bad_loads(LOG_MODULE, tokens, LOADS["log"])
    for name, body in definitions(tokens):
        for word, allowed in RESTRICTED.items():
            if word in body and name not in allowed:
                problems.append(f"{LOG_MODULE}: {word} in {name or 'top-level code'}")
    return problems


def layer_problems(path, tokens, named):
    layer = path.parts[1]
    if layer == "kernel":
        extra = {w for w in named if w not in PROTOCOL and not w.startswith("lf-rule-")}
        loaded = [t for t in loads(tokens) if "/present/" in t or "/cli/" in t]
        return ([f"{path}: names log words outside the protocol: {sorted(extra)}"] if extra
                else []) + [f"{path}: loads {t}" for t in loaded]
    if layer == "present":
        extra = {w for w in named if w not in READERS and not w.startswith("lf-rule-")
                 and not w.startswith("lf-bound-")}
        lookups = sorted(NAME_LOOKUP & set(tokens))
        return (([f"{path}: names log words beyond its readers: {sorted(extra)}"] if extra
                 else []) + bad_loads(path, tokens, LOADS["present"])
                + ([f"{path}: looks names up: {lookups}"] if lookups else []))
    if layer == "cli":
        extra = named - SWITCHES
        return [f"{path}: names log words beyond its switches: {sorted(extra)}"] if extra else []
    return [f"{path}: names log words: {sorted(named)}"] if named else []


def main():
    problems = []
    for path in sorted(pathlib.Path("src").rglob("*.fs")):
        if path == LOG_MODULE:
            continue
        tokens = words(path)
        problems += layer_problems(path, tokens, log_words(tokens))
        stores = field_stores(tokens)
        if stores:
            problems.append(f"{path}: writes the log's fields: {sorted(stores)}")
    problems += log_module_problems()
    for problem in problems:
        print(problem)
    if problems:
        return 1
    print("derivation log isolation: the kernel uses only the protocol, the printers only "
          "read values, the command line only switches, the log module only its allow-list")
    return 0


if __name__ == "__main__":
    sys.exit(main())
