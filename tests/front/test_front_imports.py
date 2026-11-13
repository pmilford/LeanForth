#!/usr/bin/env python3
"""front/ calls only an importer stage's read-only words (plan S1;
docs/design/S1_INTERFACE.md §1, trust point 1; ADR 0021 D13 as amended).

Every word that src/import/*.fs defines (a colon definition, a constant,
variable, value, create, defer or structure field) and that a file of
src/front/ names outside a comment must be in ALLOWED below, the stage's
and the tier's readers: none that writes, extends, seals or feeds a stage
(stage-read, stage-extend, stage-seal, lf-feed, ...). A word added to the
list must be read-only; the list is reviewed with the [import] gate.
Prints the words found and exits 1 on any outside the list.
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
}
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


def main():
    import_words = set()
    for path in sorted((ROOT / "src/import").glob("*.fs")):
        import_words |= defined(path)
    front_words = set()
    for path in sorted((ROOT / "src/front").glob("*.fs")):
        front_words |= defined(path)
    used = {}
    for path in sorted((ROOT / "src/front").glob("*.fs")):
        for tok in code_tokens(path.read_text(encoding="utf-8")):
            if tok in import_words and tok not in front_words | STANDARD:
                used.setdefault(tok, set()).add(path.name)
    outside = sorted(set(used) - set(ALLOWED))
    print(f"front/ names {len(used)} words of src/import/, "
          f"{len(used) - len(outside)} on the read-only allowlist: {', '.join(sorted(used))}")
    if outside:
        for word in outside:
            print(f"not allowed: {word} (in {', '.join(sorted(used[word]))})", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
