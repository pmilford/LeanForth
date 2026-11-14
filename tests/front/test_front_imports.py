#!/usr/bin/env python3
"""front/ calls only an importer stage's read-only words (plan S1;
docs/design/S1_INTERFACE.md §1, trust point 1; ADR 0021 D13 as amended).

Every word that src/import/*.fs defines (a colon definition, a constant,
variable, value, create, defer or structure field) and that a file of
src/front/ names outside a comment must be in ALLOWED below, the stage's
and the tier's readers: none that writes, extends, seals or feeds a stage
(stage-read, stage-extend, stage-seal, lf-feed, ...). Likewise every word
of the tier itself (src/core/compact*.fs, and the sets and pools under it,
src/lib/cons.fs and pools.fs) that such a file names must be in
TIER_READERS: a record's fields, a name sought without adding it
(name-seek-*), the format's tags; none that makes a name, level or
expression (name-str, expr-make, ...: review s1-meta-b M1). Only the files
in OWN_TIER, which build a construction's scratch tier over the stage's
(tier-extend) and write that tier alone, may name the tier's writers. A
word added to a list must be read-only; the lists are reviewed with the
[import] gate. Prints the words found and exits 1 on any outside them.
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]

# The stage's read-only words front/ may use, with what each reads.
ALLOWED = {
    # import/stage.fs, import/stage-records.fs: a stage's declarations.
    "stage-tier": "the stage's tier",
    "stage-decls": "how many declarations it holds",
    "stage-find": "the newest declaration of a name",
    "stage-tuples": "the tier's tuples",
    "staged-kind@": "a declaration's kind",
    "staged-name@": "its name",
    "staged-params@": "its universe parameters' tuple",
    "staged-type@": "its type",
    "staged-value@": "its value",
    "staged-hint@": "its height",
    "staged-hints@": "its hints",
    "staged-item": "an item of its inductive data",
    "staged-k?": "a recursor's K flag",
    "staged-rec?": "a type's recursive flag",
    "staged-reflexive?": "a type's reflexive flag",
    "+1>number": "a stored number + 1 read back (no state)",
    "none?": "whether a stored number is none (no state)",
    # import/ndjson.fs, import/stage-records.fs: constants of the format.
    "kind-axiom": "a kind code", "kind-type": "a kind code", "kind-ctor": "a kind code",
    "kind-recursor": "a kind code", "kind-inductive": "a kind code",
    "more-type-params": "a field number", "more-type-indices": "a field number",
    "more-type-all": "a field number", "more-type-ctors": "a field number",
    "more-type-nested": "a field number", "more-ctor-induct": "a field number",
    "more-ctor-cidx": "a field number", "more-ctor-params": "a field number",
    "more-ctor-fields": "a field number", "more-rec-all": "a field number",
    "more-rec-params": "a field number", "more-rec-indices": "a field number",
    "more-rec-motives": "a field number", "more-rec-minors": "a field number",
    "more-rec-rules": "a field number", "rule-ctor-item": "a field number",
    "rule-fields-item": "a field number", "rule-rhs-item": "a field number",
    "/rule-items": "a record size",
    "stage-by-name": "the name-to-declaration array, read",
    "resolution": "what a constant of a name resolves to, read",
    "stage-sealed?": "whether the stage is sealed",
    "kind-def": "a kind code",
    # import/manifest.fs: a manifest's digest (elab-data.fs binds the data
    # to it) and its JSON readers, functions of their arguments.
    "stage-manifest": "the stage's manifest record",
    "manifest-digest": "its SHA-256",
    "key-next": "the next key of a constant key list",
    "exact-keys?": "whether a JSON object has exactly a list's keys",
    "string-value": "a JSON value's string",
    "natural-at": "a JSON value's digits",
    "hex-text?": "whether a text is n hex digits",
    "pinned-lean-version": "a constant text",
    "pinned-lean-githash": "a constant text",
    # The elaborator's test trace (front/elab-pending.fs) writes numbers.
    "decimal-text": "a number's decimal digits, a function of its argument",
}
# The tier's readers a file reading the stage may name (core/compact-*.fs,
# lib/cons.fs, lib/pools.fs), with what each reads.
TIER_READERS = {
    "tier-exprs": "a tier's expressions", "tier-levels": "its levels",
    "tier-texts": "its literals' texts", "tier-tuples": "its lists",
    "cons-numbers": "how many records a family holds",
    "expr-tag@": "an expression's tag", "expr-payload@": "its payload",
    "expr-a@": "its first part", "expr-b@": "its second part",
    "expr-body@": "a let's body", "binder-tag?": "whether a tag is a binder's",
    "let-tag?": "whether a tag is a let's",
    "level-tag@": "a level's tag", "level-a@": "its first part",
    "level-b@": "its second part", "level-name@": "a parameter's name",
    "name-tag@": "a name's tag", "name-prefix@": "its prefix",
    "name-number@": "a numeric part", "name-text@": "a text part",
    "name-seek-str": "a name sought, none added (the candidate only)",
    "name-seek-num": "a name sought, none added (the candidate only)",
    "tuple-length": "a list's length", "tuple-item": "a list's item",
    "text@": "a literal's text",
    "tag-app": "a tag", "tag-bvar": "a tag", "tag-const": "a tag", "tag-lam": "a tag",
    "tag-let": "a tag", "tag-let-nondep": "a tag", "tag-nat": "a tag", "tag-pi": "a tag",
    "tag-proj": "a tag", "tag-sort": "a tag", "tag-name-num": "a tag",
    "tag-level-zero": "a tag", "tag-level-succ": "a tag", "tag-level-max": "a tag",
    "tag-level-imax": "a tag", "tag-level-param": "a tag",
}
# Files that build a tier of their own, a construction's scratch tier
# over the stage's (front/constructions.fs: tier-extend), and write it.
OWN_TIER = {"constructions.fs", "ctor-idx.fs", "cases-several.fs", "expr-remap.fs"}
TIER_FILES = ["src/core/compact.fs", "src/core/compact-tier.fs", "src/core/compact-names.fs",
              "src/core/compact-levels.fs", "src/core/compact-exprs.fs",
              "src/lib/cons.fs", "src/lib/pools.fs"]
# Standard Forth words that an import file defines again in a private
# word list of its own (its JSON writer's , and ;, its ['] and the like).
STANDARD = {",", ";", "[']", "here", "swap"}

DEFINING = re.compile(
    r"(?:^|\s):\s+(\S+)|(?:^|\s)(?:constant|variable|value|create|defer|field:|"
    r"\+field|2constant|2variable|context-record:|context-slab:)\s+(\S+)")


def code_tokens(text):
    """The words of Forth source, comments removed."""
    out = []
    for line in text.splitlines():
        line = re.sub(r"(^|\s)\\(\s.*)?$", " ", line)
        line = re.sub(r"(^|\s)\((\s[^)]*)?\)", " ", line)
        line = re.sub(r'(^|\s)(s|c|\.|abort|s\\)"[^"]*"', " ", line)
        out.extend(line.split())
    return out


def defined(path):
    names = set()
    for line in path.read_text(encoding="utf-8").splitlines():
        line = re.sub(r"(^|\s)\\(\s.*)?$", " ", line)
        for m in DEFINING.finditer(line):
            names.add(m.group(1) or m.group(2))
    return names


def words_of(paths):
    names = set()
    for path in paths:
        names |= defined(path)
    return names


def named(words, skip, paths):
    """The words of words, not in skip, that the files name: word -> files."""
    used = {}
    for path in paths:
        for tok in code_tokens(path.read_text(encoding="utf-8")):
            if tok in words and tok not in skip:
                used.setdefault(tok, set()).add(path.name)
    return used


def report(what, used, allowed):
    outside = sorted(set(used) - set(allowed))
    print(f"front/ names {len(used)} words of {what}, "
          f"{len(used) - len(outside)} on the read-only allowlist: {', '.join(sorted(used))}")
    for word in outside:
        print(f"not allowed: {word} (in {', '.join(sorted(used[word]))})", file=sys.stderr)
    return len(outside)


def main():
    front = sorted((ROOT / "src/front").glob("*.fs"))
    skip = words_of(front) | STANDARD
    import_words = words_of(sorted((ROOT / "src/import").glob("*.fs")))
    tier_words = words_of(ROOT / f for f in TIER_FILES) - import_words
    readers = [p for p in front if p.name not in OWN_TIER]
    bad = report("src/import/", named(import_words, skip, front), ALLOWED)
    bad += report("the tier", named(tier_words, skip, readers), TIER_READERS)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
