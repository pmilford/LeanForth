#!/usr/bin/env python3
"""The derivation log's isolation (ADR 0013 L5, item 6), checked on the
source text as allow-lists (L2 of the review of 2026-11-03, N2 of the
second review).

What it checks, on every file under src/, read left to right as Forth
reads it (a string ends at its quote before any comment is recognised, so
no code hides behind a string holding \\ or ( ; comments, string texts and
the exact load-time assertion `[if] .( ... ) cr abort [then]` removed;
every other token checked, also inside [if] ... [then] and after ' or
[']); and, N7 of the third review, in every layer but the two that run
program text by design (src/author/, src/program/), no word that looks a
name up or runs text (EVALUATE, FIND, INCLUDED and the like), and an
INCLUDED or REQUIRED counted as a load of the string before it:
1. In src/kernel/, a file names no log word but the protocol: the hot test
   lf-log?, the open and close words, lf-log-begin and lf-log-publish, the
   reference lf-log-none and the rule codes lf-rule-*; and it loads nothing
   from src/present/ or src/cli/.
2. In src/present/, a file names only the log's reading words (READERS),
   which all give values, never an address of the log's records, pools or
   header; and it loads only from ./, ../lib/ and ../core/.
3. In src/cli/, a file names only the log's switches (its level and
   limits, set outside a check) and the read-only questions whether the
   last log is complete and at which level it was kept: the command line
   turns the log on for print, never writes a record. Every other file
   under src/ names no log word at all.
4. Outside the log module, no field of a record, mark, copied reference,
   the header, the pools or the options is followed by !, +!, 2!,
   cell-pair! or cell-triple!.
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
    # The free variables a conversion opens (kernel/defeq.fs): the number open,
    # and the depth a new variable's binder stands at, so that the copier
    # writes it as the bound variable it stands for (lf-log-fvar).
    "lf-log-binders!", "lf-log-depth",
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
               "required", "include-file",
               "execute-parsing", "(find)"}
# The layers that run program text by design (the authoring words and the
# verified-program runner evaluate what a user wrote); every other layer may
# not look a name up or run text.
RUNS_TEXT = {"author", "program"}
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
    "lf-term-read", "lf-term-identity", "lf-term-binary-tag?", "lf-term-binder-tag?",
    "lf-level-read",
    "lf-level-identity", "lf-level-binary-tag?", "lf-level-tag-succ", "lf-level-tag-zero",
    "lf-level-tag-param", "lf-cref-read", "lf-cref-level", "lf-cref-current",
    "lf-input-intact?",
    "lf-input-mark-count", "lf-input-fingerprint", "/node", "node!", "node@", "ok?",
    "upto?",
    # lib/outcome.fs's loop over every index (review reuse-1a re-check): no
    # state; its test is the log's own word, given by ['] (a compile-time
    # reference, no name looked up while running).
    "all?", "[']",
    # lib/outcome.fs's 2dup-under (review reuse-out S1), a pure stack word
    # for that loop's step: no state, no name looked up while running.
    "2dup-under",
    # lib/bounds.fs's cell-counted, and cell-count (review reuse-out-2 rc3
    # B1): the rule table's names, laid down while loading and read back;
    # dictionary and stack words only, no state, no name looked up.
    "cell-counted,", "cell-count",
    # lib/bounds.fs's cell-pair@, cell-pair! and cell-triple! (cleanup-families-2):
    # @ and ! of two or three adjacent cells at the address given, the log's
    # own header and records; no state, no name looked up. Rule 4 counts
    # them (and 2!) as stores after a field, as ! and +!.
    "cell-pair@", "cell-pair!", "cell-triple!",
    "lf-tag-sort", "lf-tag-symbolic-sort", "lf-tag-bvar", "lf-tag-constant",
    "lf-tag-app", "lf-tag-lam", "lf-tag-pi", "lf-log-preset-level", "lf-log-preset-records",
    "lf-log-preset-marks", "lf-log-preset-terms", "lf-log-preset-levels",
    # The local context's (plan task 4.2.2a), read only, values: a free
    # variable's tag, whether its entry names it, and the depth of its
    # binder, so that the copier writes it as the bound variable it stands
    # for (lf-log-fvar).
    "lf-tag-fvar", "lf-fvar-live?", "lf-fvar-depth",
    # Projections (plan task 5.2.2), read only: a projection leaf's tag, so
    # that the copier keeps the leaf (a projection node, like a let term's,
    # is a binary node whose step has the rule form, lf-log-node-rule).
    "lf-tag-proj",
    # Literals (plan task 5.2.3), read only: the leaves' tags, natural-number
    # and string, kept by the copier.
    "lf-tag-lit", "lf-tag-str",
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
STRINGS = {'s"', 'c"', '."', 'abort"', ',"'}        # text up to the next "
ESCAPED = {'s\\"', '.\\"'}                          # the same, \" not ending it
CHARACTER = {"char", "[char]"}                      # the next token is data
STRING = "<string>"                                 # a string's text, as a token
DISPLAY = "<display>"                               # a .( ... ) text
ASSERTION = ["[if]", DISPLAY, "cr", "abort", "[then]"]


def tokens(text):
    """The tokens of Forth source, read left to right as Forth reads them:
    a backslash comment runs to the end of its line, ( and .( to the next
    ), a string word's text to its closing quote (kept as one token
    "<string>:TEXT"), and the word after CHAR or [CHAR] is data. Lower case."""
    out, i, n = [], 0, len(text)
    while i < n:
        while i < n and text[i].isspace():
            i += 1
        j = i
        while j < n and not text[j].isspace():
            j += 1
        word = text[i:j].lower()
        i = j
        if not word:
            break
        if word == "\\":
            i = text.find("\n", i) if "\n" in text[i:] else n
        elif word in ("(", ".("):
            close = text.find(")", i)
            i = n if close < 0 else close + 1
            if word == ".(":
                out.append(DISPLAY)
        elif word in STRINGS or word in ESCAPED:
            start, k = i + 1, i + 1
            while k < n and text[k] != '"':
                k += 2 if word in ESCAPED and text[k] == "\\" else 1
            out += [word, f"{STRING}:{text[start:k]}"]
            i = k + 1
        elif word in CHARACTER:
            out.append(word)
            while i < n and text[i].isspace():
                i += 1
            while i < n and not text[i].isspace():
                i += 1
        else:
            out.append(word)
    return without_assertions(out)


def without_assertions(toks):
    """Without the exact load-time assertion [if] .( ... ) cr abort [then];
    any other display text is dropped."""
    out, k = [], 0
    while k < len(toks):
        if toks[k:k + len(ASSERTION)] == ASSERTION:
            k += len(ASSERTION)
            continue
        if toks[k] != DISPLAY:
            out.append(toks[k])
        k += 1
    return out


def words(path):
    """A file's tokens, without string texts."""
    return [t for t in all_tokens(path) if not t.startswith(STRING)]


def all_tokens(path):
    return tokens(path.read_text(encoding="utf-8"))


def log_words(tokens):
    return {t for t in tokens if LOG_WORD.match(t)}


FIELD_WRITES = ("!", "+!", "2!", "cell-pair!", "cell-triple!")


def field_stores(tokens):
    return {a for a, b in zip(tokens, tokens[1:]) if FIELD.match(a) and b in FIELD_WRITES}


def loads(tokens):
    """The files a file loads: after require or include, and a string's
    text before included or required (any other included or required is
    reported as a load of "?")."""
    out = [b for a, b in zip(tokens, tokens[1:]) if a in ("require", "include")]
    for k, t in enumerate(tokens):
        if t in ("included", "required"):
            before = tokens[k - 1] if k else ""
            out.append(before[len(STRING) + 1:] if before.startswith(STRING) else "?")
    return out


def bad_loads(path, allowed):
    return [f"{path}: loads {target}" for target in loads(all_tokens(path))
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
    targets = set(loads(all_tokens(LOG_MODULE)))
    unknown = {t for t in tokens if t not in own and t not in LOG_USES
               and not re.fullmatch(r"-?\d+", t) and t not in targets}
    if unknown:
        problems.append(f"{LOG_MODULE}: names words outside its allow-list: {sorted(unknown)}")
    problems += bad_loads(LOG_MODULE, LOADS["log"])
    for name, body in definitions(tokens):
        for word, allowed in RESTRICTED.items():
            if word in body and name not in allowed:
                problems.append(f"{LOG_MODULE}: {word} in {name or 'top-level code'}")
    return problems


def layer_problems(path, tokens, named):
    layer = path.parts[1]
    if layer == "kernel":
        extra = {w for w in named if w not in PROTOCOL and not w.startswith("lf-rule-")}
        loaded = [t for t in loads(all_tokens(path)) if "/present/" in t or "/cli/" in t]
        return ([f"{path}: names log words outside the protocol: {sorted(extra)}"] if extra
                else []) + [f"{path}: loads {t}" for t in loaded]
    if layer == "present":
        extra = {w for w in named if w not in READERS and not w.startswith("lf-rule-")
                 and not w.startswith("lf-bound-")}
        return (([f"{path}: names log words beyond its readers: {sorted(extra)}"] if extra
                 else []) + bad_loads(path, LOADS["present"]))
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
        lookups = sorted(NAME_LOOKUP & set(tokens))
        if lookups and path.parts[1] not in RUNS_TEXT:
            problems.append(f"{path}: looks names up or runs text: {lookups}")
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
