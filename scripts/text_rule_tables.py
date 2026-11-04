#!/usr/bin/env python3
"""The tables of the text rule (src/lib/text-rule.fs), from Unicode data.

Usage (from the repository root):
  python3 scripts/text_rule_tables.py forth-banned   # the Forth table tr-banned
  python3 scripts/text_rule_tables.py forth-unseen   # the Forth table tr-unseen
  python3 scripts/text_rule_tables.py json-unseen    # the schema's "shown" class, as JSON text

The rule is the one the owner approved for program receipts 0.2
(docs/programming/PROGRAM_RECEIPTS.md), which run records follow
(docs/programming/RUN_RECORDS.md):
- banned: control characters (Cc), format characters (Cf), line and
  paragraph separators (Zl, Zp) and surrogates (Cs);
- not seen: spaces (Zs), the blank-looking fillers U+115F, U+1160, U+2800,
  U+3164 and U+FFA0, combining marks (M) and default-ignorable code points
  (DerivedCoreProperties.txt, Default_Ignorable_Code_Point, listed below).
Each table is a sorted list of merged ranges. The categories come from
Python's unicodedata. Unicode 15.0 and 15.1 give the same tables (the
general categories used here did not change between them), so either is
accepted; any other version is refused, since the tables in the source
and the schema say Unicode 15.1. tests/core/test_run_records.py imports
this module and checks that the Forth tables and the schema's patterns
are exactly these ranges.
"""
import sys
import unicodedata

VERSIONS = ("15.0.0", "15.1.0")
FILLERS = [(0x115f, 0x1160), (0x2800, 0x2800), (0x3164, 0x3164), (0xffa0, 0xffa0)]
# DerivedCoreProperties.txt, Unicode 15.1 (unchanged from 15.0).
IGNORABLE = [(0x00ad, 0x00ad), (0x034f, 0x034f), (0x061c, 0x061c), (0x115f, 0x1160),
             (0x17b4, 0x17b5), (0x180b, 0x180f), (0x200b, 0x200f), (0x202a, 0x202e),
             (0x2060, 0x206f), (0x3164, 0x3164), (0xfe00, 0xfe0f), (0xfeff, 0xfeff),
             (0xffa0, 0xffa0), (0xfff0, 0xfff8), (0x1bca0, 0x1bca3), (0x1d173, 0x1d17a),
             (0xe0000, 0xe0fff)]


def supported():
    """Whether Python's Unicode data gives the tables of Unicode 15.1."""
    return unicodedata.unidata_version in VERSIONS


def merged(ranges):
    out = []
    for lo, hi in sorted(ranges):
        if out and lo <= out[-1][1] + 1:
            out[-1] = (out[-1][0], max(out[-1][1], hi))
        else:
            out.append((lo, hi))
    return out


def category_ranges(test):
    """The ranges of the code points whose general category passes test."""
    out, start = [], None
    for cp in range(0x110001):
        hit = cp <= 0x10ffff and test(unicodedata.category(chr(cp)))
        if hit and start is None:
            start = cp
        if not hit and start is not None:
            out.append((start, cp - 1))
            start = None
    return out


def banned():
    return merged(category_ranges(lambda c: c in ("Cc", "Cf", "Zl", "Zp", "Cs")))


def unseen():
    marks_and_spaces = category_ranges(lambda c: c.startswith("M") or c == "Zs")
    return merged(marks_and_spaces + FILLERS + IGNORABLE)


def points(ranges):
    return {cp for lo, hi in ranges for cp in range(lo, hi + 1)}


def forth(ranges):
    cells = [f"${lo:x} , ${hi:x} ," for lo, hi in ranges]
    return "\n".join("  " + "  ".join(cells[i:i + 4]) for i in range(0, len(cells), 4))


def json_char(cp):
    """A code point inside a JSON string that holds a regular expression:
    a regex escape inside the Basic Multilingual Plane, else the JSON escape
    of its surrogate pair, which JSON reads as the character itself."""
    if cp < 0x10000:
        return "\\\\u%04x" % cp
    v = cp - 0x10000
    return "\\u%04x\\u%04x" % (0xd800 + (v >> 10), 0xdc00 + (v & 0x3ff))


def json_class(ranges):
    return "".join(json_char(lo) if lo == hi else json_char(lo) + "-" + json_char(hi)
                   for lo, hi in ranges)


def main(argv):
    if not supported():
        print(f"Python's Unicode is {unicodedata.unidata_version}, not one of {VERSIONS}",
              file=sys.stderr)
        return 2
    outputs = {"forth-banned": lambda: forth(banned()),
               "forth-unseen": lambda: forth(unseen()),
               "json-unseen": lambda: json_class(unseen())}
    if len(argv) != 2 or argv[1] not in outputs:
        print(__doc__.split("\n\n")[1], file=sys.stderr)
        return 2
    print(outputs[argv[1]]())
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
