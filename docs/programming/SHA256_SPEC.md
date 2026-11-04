# SHA-256 specification in Lean (stage SHA-1)

**Status:** implemented; checked by pinned Lean 4.35.0, not by LeanForth;
part of `make check`. It proves **nothing about the Forth code yet**.

The program track's flagship target is to prove that LeanForth's own
[`src/lib/sha256.fs`](../../src/lib/sha256.fs) computes exactly SHA-256 as
the standard FIPS 180-4 defines it, for every message
([plan](../project/PLAN_DRAFT.md), "Flagship program target: SHA-256",
stages SHA-1 to SHA-5). A proof needs two things to compare: the program,
and a precise statement of what it should compute. This page is about the
second. [`sha256-spec.lean`](../../tests/reference/sha256-spec.lean) states
SHA-256 in Lean, written from the standard's text section by section, not
translated from the Forth code, so that the two stay independent: a mistake
copied from one into the other could not hide.

## In plain words

- **The specification** is about 200 lines of commented Lean definitions: the
  word operations, the six functions, the 64 constants, padding, splitting
  into blocks, the message schedule, the 64 rounds and the final digest.
  Each definition names the section of FIPS 180-4 it follows and reads
  like the standard's formula.
- **The checks.** Lean's *kernel*, the small part of Lean that has the last
  word on whether a proof is correct, runs the specification on test
  messages and compares the result with the published digests. It does
  this by evaluating the definitions step by step itself, not by running
  compiled code, so no compiler is trusted (`decide +kernel`; the
  forbidden shortcut `native_decide` would trust the compiler through the
  axiom `Lean.ofReduceBool`).
- **The lemmas** are small proved facts that the later stages will need,
  for example that padding always gives a multiple of 64 bytes.
- **Not proved:** that the Forth code computes this function. That is the
  work of stages SHA-2 to SHA-5. Also not proved, because it cannot be: that
  the Lean text says what the standard says. That needs a person (or an
  independent reviewer) to read the two side by side; the test vectors, the
  constants check and the mutants below are evidence for it, not proof. An
  independent review on 2026-11-03 compared the definitions with FIPS 180-4
  clause by clause and found no deviation; all 64 K and 8 H(0) values
  matched.

## Running it

```sh
make reference      # part of make check; prints one summary line for SHA-256
LEAN=.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean \
  bash tests/reference/sha256-spec-check.sh
```

The script [`sha256-spec-check.sh`](../../tests/reference/sha256-spec-check.sh)
prints, for example, `SHA-256 specification: 74 theorems (26
kernel-evaluated vectors) proved in 33 s; axioms of all 280 declarations
within the allowlist; 7 mutants rejected by the kernel.` It fails if Lean
rejects anything (warnings count as errors, so `sorry` fails), if the
file's axiom audit is incomplete, misses a theorem of the source or names
an axiom outside the allowlist, or if a mutant is accepted.

**The axiom audit.** The last command of the Lean file prints the axioms of
every declaration the file makes, in the words of `#print axioms` (it calls
the same function, `collectAxioms`): definitions and theorems, private,
protected and attribute-carrying ones, and the auxiliary declarations Lean
generates (280 today), so no declaration can escape the check by how it is
written. The file therefore imports `Lean`. Before trusting the audit, the
script checks that it refuses planted faults: a private theorem with an
attribute and a protected theorem, both using an axiom outside the
allowlist; an audit with one report missing; and a `lemma`, which Lean
without Mathlib does not accept at all.

## The standard, section by section

| FIPS 180-4 | What it says | Lean |
| --- | --- | --- |
| 2.1, 3.1, 3.2 | A word is 32 bits; AND, OR, XOR, complement, addition modulo 2^32, shifts | `Word` (`BitVec 32`) and Lean's operators |
| 3.2 | SHR^n(x) = x >> n; ROTR^n(x) = (x >> n) ∨ (x << 32 − n) | `SHR`, `ROTR` |
| 4.1.2 (4.2)–(4.7) | Ch, Maj, Σ0, Σ1, σ0, σ1 | `Ch`, `Maj`, `bigSigma0`, `bigSigma1`, `smallSigma0`, `smallSigma1` |
| 4.2.2 | The constants K0 … K63 | `K` |
| 5.3.3 | The initial hash value H(0) | `initialHash` |
| 5.1.1 | Padding: the bit 1, k zero bits with l + 1 + k ≡ 448 (mod 512), then l as 64 bits | `padZeroBits`, `padding`, `pad` |
| 5.2.1 | Parsing into 512-bit blocks of sixteen 32-bit words, big-endian | `wordOf`, `words`, `parse`, `blocks` |
| 6.2.2 step 1 | The message schedule W0 … W63 | `scheduleNext`, `schedule` |
| 6.2.2 steps 2–3 | The working variables a … h and the 64 rounds | `Vars`, `start`, `round`, `rounds` |
| 6.2.2 step 4 | The next hash value H(i) | `compress`, `hashBlocks` |
| 6.2.2 | The digest H0(N) ‖ … ‖ H7(N) | `digest`, `sha256` |

## One function in three forms

Σ0, the function the rounds apply to the working variable a, as the
standard writes it, as the Forth code computes it, and as the Lean
specification states it, with H0(0) = 6a09e667 as the input:

| Form | Text |
| --- | --- |
| Mathematics (FIPS 180-4, (4.4)) | Σ0(x) = ROTR^2(x) ⊕ ROTR^13(x) ⊕ ROTR^22(x); Σ0(6a09e667) = da827999 ⊕ 333b504f ⊕ 27999da8 = ce20b47e |
| Forth ([`sha256.fs`](../../src/lib/sha256.fs)) | `: sha-big-sigma0 ( u -- u' ) dup 2 sha-rotr over 13 sha-rotr xor swap 22 sha-rotr xor ;` and `hex 6a09e667 sha-big-sigma0 u.` prints `CE20B47E` |
| Lean ([`sha256-spec.lean`](../../tests/reference/sha256-spec.lean)) | `def bigSigma0 (x : Word) : Word := ROTR 2 x ^^^ ROTR 13 x ^^^ ROTR 22 x` and `theorem bigSigma0_example : bigSigma0 0x6a09e667 = 0xce20b47e`, checked by the kernel |

The Forth line is a run on Gforth, a test of one input. The Lean line is
the specification's own value. Stage SHA-2 is to prove that the Forth word
agrees with the Lean function for all 2^32 inputs.

## Representation choices

- **Words are `BitVec 32`**, Lean's 32-bit strings, rather than `UInt32`.
  The standard defines a word as a string of bits, and `BitVec` is exactly
  that: Lean defines its operations from the numbers they stand for, and
  its rotation is the standard's formula ((x >>> n) ||| (x <<< (w − n)),
  proved equal to `ROTR` by `ROTR_eq_rotateRight`). Lean's library has the
  most lemmas about `BitVec`, and `toNat` gives the number from 0 to
  2^32 − 1 that a Forth cell holds, which is what the later proofs compare.
  `UInt32` is a wrapper around `BitVec 32` that only makes compiled code
  faster; nothing here is compiled.
- **Messages are `List UInt8`**, a list of bytes, rather than `ByteArray`.
  Proofs about messages split into pieces (stage SHA-4, any number of
  `sha256-update` calls) need lists: appending, prefixes and induction all
  come with lemmas. A `ByteArray` holds a list inside anyway.
- **Whole bytes only.** The standard allows any number of bits; the Forth
  code, `sha256sum` and these test vectors take whole bytes. Each byte's
  bits are read most significant first (section 3.1), so the bit 1 that
  padding appends and the next seven zero bits are the byte `0x80`; the
  lemma `padZeroBits_byte` proves that the remaining zero bits always fill
  whole bytes.
- **Length.** The standard covers messages of fewer than 2^64 bits. For a
  longer one (2 exabytes or more) the specification, like the Forth code,
  uses the length modulo 2^64.
- **Computing by the kernel.** Every function is defined by plain
  structural recursion over lists and numbers, which the kernel can
  evaluate; Lean's kernel has fast built-in arithmetic for the numbers
  inside `BitVec`.

## What the kernel checks

Each check is one theorem proved by `decide +kernel`. Times are wall-clock
seconds on the development machine for a file with the specification and
that one theorem, minus the 0.27 s and 0.49 GB that Lean needs to start;
memory is the peak of the whole run. Times vary by about 20% between runs.

### Exactly which NIST vectors are covered

- **FIPS 180-2 examples** (the examples FIPS 180-4 publishes):
  B.1 "abc" and B.2, the 448-bit message. Not B.3, one million 'a' (below).
- **NIST CAVP byte-oriented vectors** (Cryptographic Algorithm Validation
  Program, CAVS 11.0, `shabytetestvectors.zip` from csrc.nist.gov; SHA-256
  of `SHA256ShortMsg.rsp`: `75e1cb83994638481808e225b9eb0c1ebd0c232d952ac42b61abce6363be283c`,
  of `SHA256LongMsg.rsp`: `6fac36f37360bcf74ffcf4465c18e30d6d5a04cc90885b901fc3130c16060974`).
  16 of the 65 short messages, Len = 0, 8, 16, 24, 32, 64, 128, 248, 256,
  384, 432, 440, 448, 456, 504 and 512 bits (0 to 64 bytes, including the
  padding boundaries 55, 56, 63 and 64 bytes), and 1 of the 64 long
  messages, Len = 1304 bits (163 bytes, three blocks). Each theorem copies
  its entry's `Len`, `Msg` and `MD` text verbatim; the file reads the
  hexadecimal with a small helper, `hex`, that `sha256` does not use. The
  short-message file stops at 64 bytes, so a 65-byte message has no CAVP
  vector; `boundary_119` and `boundary_120` below cover two and three
  blocks with non-NIST digests.
- **Not covered:** the other 49 short and 63 long CAVP messages, the CAVP
  Monte Carlo test (`SHA256Monte.rsp`), and B.3.

The plan's acceptance wording "agrees with every NIST vector" is therefore
met for this list only. Checking all 65 short messages would add about a
minute to every `make check`.

### The checks

| Theorem | Message | Source of the expected digest | Blocks | Kernel time | Peak memory |
| --- | --- | --- | --- | --- | --- |
| `nist_abc` | "abc" | NIST: FIPS 180-2 B.1 | 1 | 0.4 s | 0.65 GB |
| `nist_448` | "abcdbcdecdef…nopq", 448 bits | NIST: FIPS 180-2 B.2 | 2 | 1.0 s | 0.79 GB |
| `cavp_short_0` … `cavp_short_440` (12) | 0 to 55 bytes | NIST: CAVP `SHA256ShortMsg.rsp` | 1 | 0.7–0.9 s each | 0.66–0.72 GB |
| `cavp_short_448` … `cavp_short_512` (4) | 56, 57, 63, 64 bytes | NIST: CAVP `SHA256ShortMsg.rsp` | 2 | about 1.6 s each | 0.85–0.86 GB |
| `cavp_long_1304` | 163 bytes | NIST: CAVP `SHA256LongMsg.rsp` | 3 | 3.6–4.3 s, half of it reading the 326 hexadecimal digits | 1.36 GB |
| `published_896` | "abcdefghbcdefghi…nopqrstu", 896 bits | **not NIST**: NIST's SHA-384/512 example message, with the SHA-256 digest that test-vector lists publish and OpenSSL gives | 2 | 1.0 s | 0.80 GB |
| `boundary_55` … `boundary_120` | 55, 56, 64, 119 and 120 bytes 255, 254, … | **not NIST**: Python `hashlib` (OpenSSL) | 1, 2, 2, 2, 3 | 0.5–1.4 s | up to 0.90 GB |
| `nist_abc_wrong_refuted` | "abc" with the digest's last bit flipped | must be unequal | 1 | 0.4 s | 0.64 GB |
| `K_cube_roots`, `initialHash_square_roots` | the constants | sections 4.2.2 and 5.3.3 | — | 1.6 s together | 0.84 GB |

The whole file takes about 30 s and 2.6 GB; `import Lean`, which the
axiom audit needs, accounts for 0.5 s and 1.1 GB of that. The boundary
messages test the padding where it changes: 55 bytes is the longest
message of one block and 56 the shortest of two; 64 is exactly one block;
119 is the longest of two blocks and 120 the shortest of three. Their
bytes are all 128 or more, which the ASCII test messages never are. Every
expected digest, NIST's included, was also recomputed with Python's
`hashlib` before it was written into the file.

The constants check proves that the hexadecimal tables of sections 4.2.2
and 5.3.3 match their description, the first 32 bits of the fractional
parts of the cube roots of the first 64 primes and the square roots of the
first 8 primes, using exact whole-number arithmetic: r = ⌊∛p⌋ · 2^32 + K
must satisfy r^3 ≤ p · 2^96 < (r + 1)^3.

**Mutants.** The check script also makes seven copies of the specification
cut down to the "abc" vector, each with one deliberate slip, and requires
the kernel to reject every one: the last constant K63 off by one; ROTR^12
for ROTR^13 in Σ0; a rotation for the shift SHR^3 in σ0; Ch without the
complement; W(t−6) for W(t−7) in the schedule; e = c + T1 for e = d + T1;
and the message length written little-endian. The unchanged cut-down file
must pass, so each rejection comes from its slip.

**The one-million-'a' vector** (FIPS 180-2 B.3, digest cdc76e5c …) is not
checked. It has 15,626 blocks, and the kernel keeps every intermediate
result of one theorem in memory. Measured on messages of 'a': 1,000 bytes
(16 blocks) took 9.4 s and 2.6 GB, 4,000 bytes (63 blocks) 39 s and 8.6 GB,
that is about 0.6 s and 130 MB per block. One theorem for a million bytes
would need about 2.6 hours and 2 TB of memory. Splitting it into 15,626
theorems, one per block with each intermediate hash value written out,
would fit in memory but still take about 2 hours, far too long for
`make check`.

## Lemmas for the later stages

All are proved for every input, not tested.

| Lemmas | What they say | For |
| --- | --- | --- |
| `SHR_toNat`, `ROTR_toNat`, `Ch_toNat`, `Maj_toNat`, `bigSigma0_toNat`, `bigSigma1_toNat`, `smallSigma0_toNat`, `smallSigma1_toNat` | Each function as operations on the number a Forth cell holds: shifts, `or`, `and`, `xor`, and `% 2^32` only where a bit can leave the word | SHA-2: the helper words, as rewrite rules ([MiniForth review](../development/MINIFORTH_REVIEW.md), recommendation 6) |
| `Ch_eq_select`, `Maj_eq_or` | Ch(x, y, z) = z ⊕ (x ∧ (y ⊕ z)) and Maj(x, y, z) = (x ∧ y) ∨ (z ∧ (x ∨ y)), the forms `sha256.fs` computes | SHA-2 |
| `ROTR_eq_rotateRight` | ROTR is Lean's own rotation | Reuse of Lean's rotation lemmas |
| `padZeroBits_spec`, `padZeroBits_least`, `padZeroBits_byte` | The padding formula gives the smallest k with l + 1 + k ≡ 448 (mod 512); for whole bytes, k ≡ 7 (mod 8) | SHA-4 |
| `length_pad`, `length_pad_mod`, `length_pad_bounds`, `pad_prefix`, `pad_after_message`, `pad_suffix` | The padded message has 64 · ((n + 8) / 64 + 1) bytes, a multiple of 64, 9 to 72 more than the message; the message is its beginning, then the byte 0x80; it ends with the length in bits | SHA-4: `sha-pad` |
| `wordOf_toNat`, `length_words`, `length_parse`, `length_blocks_pad`, `length_of_mem_blocks_pad` | Four bytes make the word b0 · 2^24 + b1 · 2^16 + b2 · 2^8 + b3; a padded message has (n + 8) / 64 + 1 blocks of 16 words | SHA-3, SHA-4: `sha-be@`, `sha-load` |
| `schedule_message`, `schedule_formula`, `length_schedule` | The schedule satisfies step 1 as the standard writes it: W(t) = M(t) for t ≤ 15, W(t) = σ1(W(t−2)) + W(t−7) + σ0(W(t−15)) + W(t−16) for 16 ≤ t ≤ 63 | SHA-3: `sha-expand` |
| `rounds_zero`, `rounds_succ` | The rounds one at a time: what a counted loop's invariant needs | SHA-3: `sha-rounds-run` |
| `hashBlocks_append`, `blocks_append`, `sha256_append_blocks` | Hashing a message whose first part is whole blocks: hash those blocks as they come, then the rest with the padding for the whole length | SHA-4: `sha256-update`, `sha256-final` |

## Axioms

The owner's allowlist ([`AGENTS.md`](../../AGENTS.md)) is `propext`,
`Classical.choice` and `Quot.sound`; `Lean.ofReduceBool` and
`Lean.trustCompiler` are never allowed. The check script holds every
declaration of the file to that allowlist. Today the specification uses
less: every declaration depends on `propext` and `Quot.sound` at most,
and none uses `Classical.choice`.

- The kernel-evaluated vectors depend on `propext` and `Quot.sound`. Both
  come from Lean's own definitions of `&&&`, `|||` and `^^^` on `BitVec`,
  which carry a proof that the result stays below 2^32, not from any step
  of the checks. Any specification on `BitVec` or `UInt32` inherits them.
- `K_cube_roots`, `initialHash_square_roots` and `pad_prefix` depend on no
  axioms at all.
- `Ch_eq_select` does without `Classical.choice`, which Lean's lemmas
  about the complement use, by letting the kernel check the 32 bits of the
  all-ones word (`allOnes_getLsbD`). This is a preference, not a rule: the
  allowlist would accept it.

## What is proved and what is not

Proved by Lean 4.35.0's kernel (untrusted by LeanForth; *experimental —
not independently audited*):

- the specification gives NIST's digest for the 19 NIST vectors listed
  above (2 FIPS 180-2 examples, 17 CAVP messages), the published or
  OpenSSL digest for six more messages that are not NIST vectors (896
  bits and five padding boundaries), and a different digest from a wrong
  one;
- its constants match the standard's description of them;
- the lemmas above, for every input.

Not proved:

- **anything about `src/lib/sha256.fs`**, whose correctness is still only
  tested ([`tests/lib/sha256.fs`](../../tests/lib/sha256.fs));
- that the specification says what FIPS 180-4 says: that is a reading of
  the two side by side (done once, by the independent review of
  2026-11-03, which found no deviation);
- the NIST vectors not listed above, including the one-million-'a' vector;
- messages whose length is not a whole number of bytes.

Trusted: Lean 4.35.0's kernel and the definitions of `BitVec`, `List` and
`Nat` in Lean's core library.

## What stage SHA-2 needs

Stage SHA-2 proves each helper word of `sha256.fs` (`sha-shr`, `sha-rotr`,
`sha-ch`, `sha-maj`, `sha-big-sigma0`, `sha-big-sigma1`, `sha-small-sigma0`,
`sha-small-sigma1`) equal to its function here for all 32-bit inputs:

- program IR 0.2 ([PROGRAM_IR.md](PROGRAM_IR.md)): `lshift`, and
  constants such as the mask 2^32 − 1 beyond today's literal limit;
- a statement relating a cell's value to `x.toNat`, with the cell width at
  least 33 bits (`sha-rotr` shifts a word left before masking) or exactly
  32;
- the `toNat` lemmas above as rewrite rules, and each word's contract
  stated as a rewrite over an arbitrary continuation so that later proofs
  never reopen a callee (MiniForth review, recommendation 6);
- deliberately wrong variants of each word refuted.
