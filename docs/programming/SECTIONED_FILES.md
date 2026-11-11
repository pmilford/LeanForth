# Sectioned binary files: the container format

Implemented by `src/lib/sections.fs` (version 1; written 2026-11-11 for the
checked snapshot of ADR 0020, but a general container that knows nothing
about what its sections hold). Untrusted until reviewed. What a particular
snapshot puts in the sections and in the caller's header fields is that
snapshot's own format decision, not this page's.

All numbers are unsigned and little-endian. A file is a header of 4,096
bytes followed by sections, each starting at a multiple of 4,096 and padded
with zero bytes to the next multiple.

## Header (bytes 0 to 4095)

| Offset | Size | Field |
|---|---|---|
| 0 | 8 | magic `SECTFILE` |
| 8 | 4 | format version, 1 |
| 12 | 4 | byte-order value `0x01020304` (a reader that sees `0x04030201` knows the file was written the other way round) |
| 16 | 4 | number of sections n, at most 62 |
| 20 | 4 | reserved, 0 |
| 24 | 64 | the caller's 16 fields, 32 bits each (unused ones 0) |
| 88 | 8 | reserved, 0 |
| 96 | 64 n | the section table, one 64-byte entry per section |
| 96 + 64 n | to 4063 | zero |
| 4064 | 32 | SHA-256 of bytes 0 to 4063 |

A table entry: kind (4 bytes, the caller's number), unit size (4 bytes, at
least 1), count (8), offset (8), length in bytes (8) and the SHA-256 of the
section's `length` bytes (32). The length must equal unit size times count.

## Layout rule

Section 0 starts at 4096; each next section starts where the previous one's
padded end is (an empty section occupies no space); the file ends at the
last padded end. The reader requires exactly this, so a section cannot
overlap another, sit outside the file, be misaligned or leave a gap, and a
file with bytes missing or added is refused. The padding is not under a
SHA-256 (it is not data); the writer always writes zeros.

## Reading and the outcomes

`sections-open` checks, in this order: the file has at least 4,096 bytes;
the magic (invalid); the version (unsupported unless 1); the byte-order value
(unsupported for the opposite order, invalid for any other); the header's
SHA-256 (rejected); the section count, the unit sizes, lengths, offsets and
the file size against the layout rule (invalid, and any 64-bit number that
does not fit a non-negative cell). `sections-read` copies one section into
the caller's block and compares its SHA-256 (rejected on a difference; full
when the block is too small). An unreadable file or failed read is invalid.

## Writing

The file is built as `FILE.partial` and renamed over `FILE` only when
complete, so an earlier `FILE` survives every failure. On a failure, or a
THROW (thrown again), the partial is closed and deleted by name. Output is
deterministic: the same sections and fields give the same bytes, on every
host (the little-endian words in `src/lib/u32.fs` fix the byte order).

Trust: a matching SHA-256 shows the bytes are those that were written, not
who wrote them; the file is not signed or encrypted.
