import Lean

/-
SHA-256 as FIPS 180-4 specifies it (Secure Hash Standard, August 2015),
stage SHA-1 of the program track's flagship target (docs/project/PLAN_DRAFT.md,
"Flagship program target: SHA-256"; docs/programming/SHA256_SPEC.md).
Untrusted: Lean, not LeanForth, checks everything in this file.

The definitions are written from the standard's text, section by section,
and NOT from src/lib/sha256.fs, so that a later proof that the Forth code
computes `sha256` compares two independent descriptions. Each definition
names the section it follows. The file has six parts:
1. Words and the operations on them (FIPS 180-4 sections 2.2.2, 3.1, 3.2).
2. The functions and constants (4.1.2, 4.2.2, 5.3.3).
3. Preprocessing: padding and parsing (5.1.1, 5.2.1, 6.2.1).
4. The hash computation (6.2.2).
5. Checks that Lean's kernel evaluates (`decide +kernel`; never
   `native_decide`, which would trust Lean's compiler through the axiom
   `Lean.ofReduceBool`): the constants match the roots of primes that
   sections 4.2.2 and 5.3.3 describe, and `sha256` gives the expected
   digest of each test vector.
6. Lemmas for the later stages: the helper functions as rewrite rules on
   the numbers a Forth cell holds, padding, parsing, the message schedule
   in the standard's form, one round at a time, and hashing block by block.

What this does not show: anything about the Forth code. Nothing here
mentions src/lib/sha256.fs; proving that it computes `sha256` is the work
of stages SHA-2 to SHA-5.
-/

namespace Sha256Spec

/-! ## Part 1. Words and operations -/

/-- A word: a string of 32 bits (sections 2.1 and 3.1). `BitVec 32` is
Lean's 32-bit string; its number (`toNat`, from 0 to 2^32 - 1) reads the
bits big-endian, the most significant bit on the left, as section 3.1
says. Its operations are the standard's (section 3.2): `&&&`, `|||`, `^^^`
and `~~~` are bitwise AND, OR, XOR and complement; `+` is addition modulo
2^32; `x >>> n` and `x <<< n` shift right and left, filling with zeros
and dropping the bits that leave the word. -/
abbrev Word := BitVec 32

/-- Section 3.2: the right shift SHR^n(x) = x >> n, for 0 ≤ n < 32. -/
def SHR (n : Nat) (x : Word) : Word := x >>> n

/-- Section 3.2: the rotate right (circular right shift)
ROTR^n(x) = (x >> n) ∨ (x << 32 - n), for 0 ≤ n < 32. -/
def ROTR (n : Nat) (x : Word) : Word := (x >>> n) ||| (x <<< (32 - n))

/-! ## Part 2. Functions and constants -/

/-- Section 4.1.2, (4.2): Ch(x, y, z) = (x ∧ y) ⊕ (¬x ∧ z). -/
def Ch (x y z : Word) : Word := (x &&& y) ^^^ (~~~x &&& z)

/-- Section 4.1.2, (4.3): Maj(x, y, z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z). -/
def Maj (x y z : Word) : Word := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- Section 4.1.2, (4.4): Σ0(x) = ROTR^2(x) ⊕ ROTR^13(x) ⊕ ROTR^22(x).
(Lean reserves the letter Σ, hence the spelled-out names.) -/
def bigSigma0 (x : Word) : Word := ROTR 2 x ^^^ ROTR 13 x ^^^ ROTR 22 x

/-- Section 4.1.2, (4.5): Σ1(x) = ROTR^6(x) ⊕ ROTR^11(x) ⊕ ROTR^25(x). -/
def bigSigma1 (x : Word) : Word := ROTR 6 x ^^^ ROTR 11 x ^^^ ROTR 25 x

/-- Section 4.1.2, (4.6): σ0(x) = ROTR^7(x) ⊕ ROTR^18(x) ⊕ SHR^3(x). -/
def smallSigma0 (x : Word) : Word := ROTR 7 x ^^^ ROTR 18 x ^^^ SHR 3 x

/-- Section 4.1.2, (4.7): σ1(x) = ROTR^17(x) ⊕ ROTR^19(x) ⊕ SHR^10(x). -/
def smallSigma1 (x : Word) : Word := ROTR 17 x ^^^ ROTR 19 x ^^^ SHR 10 x

/-- Section 4.2.2: the 64 constants K0 … K63, the first 32 bits of the
fractional parts of the cube roots of the first 64 primes, in the
standard's order (read left to right, row by row). -/
def K : List Word := [
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- A hash value H(i): its eight words H0 … H7 (sections 2.2.1 and 6.2.2). -/
structure HashValue where
  H0 : Word
  H1 : Word
  H2 : Word
  H3 : Word
  H4 : Word
  H5 : Word
  H6 : Word
  H7 : Word

/-- Section 5.3.3: the initial hash value H(0), the first 32 bits of the
fractional parts of the square roots of the first 8 primes. -/
def initialHash : HashValue :=
  ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
   0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19⟩

/-! ## Part 3. Preprocessing

A message here is a list of bytes (`List UInt8`). The standard allows a
message of any number of bits; like the Forth code, `sha256sum` and the
byte-oriented test vectors, this specification takes whole bytes, and
reads each byte's bits most significant first (section 3.1), so the
message of l = 8 · n bits is its n bytes in order. -/

/-- Section 5.1.1: the number k of zero bits appended after the bit 1 to a
message of l bits: the smallest k ≥ 0 with l + 1 + k ≡ 448 (mod 512).
`padZeroBits_spec` and `padZeroBits_least` below prove that this formula
gives exactly that k. -/
def padZeroBits (l : Nat) : Nat := (448 + 512 - (l + 1) % 512) % 512

/-- Byte i of a bit string of w bits, counting from the left (byte 0 holds
the most significant bits): bits w - 8i - 1 down to w - 8i - 8. -/
def byteAt (x : BitVec w) (i : Nat) : UInt8 :=
  UInt8.ofBitVec (x.extractLsb' (w - 8 * (i + 1)) 8)

/-- A bit string of w bits (w a multiple of 8) as its w / 8 bytes, the
leftmost first (big-endian, section 3.1). -/
def bytesBE (x : BitVec w) : List UInt8 := (List.range (w / 8)).map (byteAt x)

/-- Section 5.1.1: what padding appends to a message of n bytes, which
depends only on n. With l = 8n bits: the bit 1 and then k zero bits,
where k = `padZeroBits l`; since l is a multiple of 8, k ≡ 7 (mod 8)
(`padZeroBits_byte`), so the bit 1 and the first seven zero bits are the
byte 0x80 and the other k - 7 zero bits are (k - 7) / 8 zero bytes. Then
the 64-bit block equal to l in binary. The standard requires l < 2^64;
`BitVec.ofNat 64 l` is l modulo 2^64, as the Forth code also counts. -/
def padding (n : Nat) : List UInt8 :=
  let l := 8 * n
  0x80 :: List.replicate ((padZeroBits l - 7) / 8) 0 ++ bytesBE (BitVec.ofNat 64 l)

/-- Section 5.1.1: the padded message. -/
def pad (m : List UInt8) : List UInt8 := m ++ padding m.length

/-- Section 5.2.1 (and 3.1): four bytes as one word, the first byte the
most significant: the concatenation of their bit strings. -/
def wordOf (b0 b1 b2 b3 : UInt8) : Word :=
  b0.toBitVec ++ b1.toBitVec ++ b2.toBitVec ++ b3.toBitVec

/-- Section 5.2.1: bytes as words, four bytes at a time. A padded message
has a multiple of 64 bytes, so nothing is left over. -/
def words : List UInt8 → List Word
  | b0 :: b1 :: b2 :: b3 :: rest => wordOf b0 b1 b2 b3 :: words rest
  | _ => []

/-- Section 5.2.1: N blocks of 512 bits, each as its 16 words; block i
holds the words 16i to 16i + 15 (M(i+1)_0 … M(i+1)_15 in the standard,
which counts blocks from 1). -/
def parse : Nat → List Word → List (List Word)
  | 0, _ => []
  | n + 1, ws => ws.take 16 :: parse n (ws.drop 16)

/-- Sections 5.2.1 and 6.2.1: a padded message as its N = length / 64
blocks. -/
def blocks (bytes : List UInt8) : List (List Word) := parse (bytes.length / 64) (words bytes)

/-! ## Part 4. Hash computation (section 6.2.2) -/

/-- Step 1, for one t ≥ 16, given W0 … W(t-1) as the list `W` of length t:
W(t) = σ1(W(t-2)) + W(t-7) + σ0(W(t-15)) + W(t-16). (`getD i 0` is the
list's word i, or 0 outside it, which never happens here.) -/
def scheduleNext (W : List Word) : Word :=
  let t := W.length
  smallSigma1 (W.getD (t - 2) 0) + W.getD (t - 7) 0 +
    smallSigma0 (W.getD (t - 15) 0) + W.getD (t - 16) 0

/-- Step 1, one t at a time: W0 … W(t-1) becomes W0 … W(t). -/
def scheduleStep (W : List Word) : List Word := W ++ [scheduleNext W]

/-- Step 1: the message schedule W0 … W63 of a block M of 16 words:
W(t) = M(t) for t ≤ 15, then t = 16 to 63 by `scheduleNext`.
`schedule_message` and `schedule_formula` below restate it in the
standard's form. -/
def schedule (M : List Word) : List Word := Nat.repeat scheduleStep 48 M

/-- The eight working variables a … h (section 2.2.1). -/
structure Vars where
  a : Word
  b : Word
  c : Word
  d : Word
  e : Word
  f : Word
  g : Word
  h : Word

/-- Step 2: a = H0(i-1), b = H1(i-1), …, h = H7(i-1). -/
def start (H : HashValue) : Vars := ⟨H.H0, H.H1, H.H2, H.H3, H.H4, H.H5, H.H6, H.H7⟩

/-- Step 3, the body of the loop for one t, given K(t) and W(t):
T1 = h + Σ1(e) + Ch(e, f, g) + K(t) + W(t); T2 = Σ0(a) + Maj(a, b, c);
h = g; g = f; f = e; e = d + T1; d = c; c = b; b = a; a = T1 + T2. -/
def round (v : Vars) (Kt Wt : Word) : Vars :=
  let T1 := v.h + bigSigma1 v.e + Ch v.e v.f v.g + Kt + Wt
  let T2 := bigSigma0 v.a + Maj v.a v.b v.c
  { h := v.g, g := v.f, f := v.e, e := v.d + T1, d := v.c, c := v.b, b := v.a, a := T1 + T2 }

/-- Steps 2 and 3: the working variables after the rounds t = 0 to n - 1,
starting from H and using the schedule W. -/
def rounds (H : HashValue) (W : List Word) (n : Nat) : Vars :=
  (List.range n).foldl (fun v t => round v (K.getD t 0) (W.getD t 0)) (start H)

/-- Steps 1 to 4 for one block M of 16 words: H(i) from H(i-1):
H0(i) = a + H0(i-1), …, H7(i) = h + H7(i-1). -/
def compress (H : HashValue) (M : List Word) : HashValue :=
  let v := rounds H (schedule M) 64
  ⟨v.a + H.H0, v.b + H.H1, v.c + H.H2, v.d + H.H3,
   v.e + H.H4, v.f + H.H5, v.g + H.H6, v.h + H.H7⟩

/-- "For i = 1 to N": the hash value after the given blocks, from H. -/
def hashBlocks (H : HashValue) (Ms : List (List Word)) : HashValue := Ms.foldl compress H

/-- The message digest H0(N) ‖ H1(N) ‖ … ‖ H7(N), as its 32 bytes. -/
def digest (H : HashValue) : List UInt8 :=
  [H.H0, H.H1, H.H2, H.H3, H.H4, H.H5, H.H6, H.H7].flatMap bytesBE

/-- SHA-256 of a message of whole bytes (sections 6.2.1 and 6.2.2): pad,
parse, hash every block from H(0), and output the digest. -/
def sha256 (m : List UInt8) : List UInt8 := digest (hashBlocks initialHash (blocks (pad m)))

/-! ## Part 5. Checks by the kernel

`decide +kernel` asks Lean's kernel itself to evaluate the statement and
find it true; nothing else is trusted for the answer.

### The constants are what their sections say

Sections 4.2.2 and 5.3.3 give the constants in hexadecimal and say where
they come from; these two theorems check that the hexadecimal values
match that description. -/

/-- n is prime: at least 2, and no d with 2 ≤ d < n divides it. -/
def isPrime (n : Nat) : Bool := 2 ≤ n && (List.range n).all fun d => d < 2 || n % d != 0

/-- The first `count` primes in increasing order, for count ≤ 64 (the 64th
prime is 311). -/
def firstPrimes (count : Nat) : List Nat := ((List.range 312).filter isPrime).take count

/-- `bits` are the first 32 bits of the fractional part of the k-th root
of p, whose whole part is `whole`. Exactly then is r = whole · 2^32 + bits
the whole part of p^(1/k) · 2^32, that is r^k ≤ p · 2^(32k) < (r + 1)^k. -/
def rootBits (k p whole bits : Nat) : Bool :=
  let r := whole * 2 ^ 32 + bits
  bits < 2 ^ 32 && r ^ k ≤ p * 2 ^ (32 * k) && p * 2 ^ (32 * k) < (r + 1) ^ k

/-- The whole part of p^(1/k), counted for a small p. (If it were wrong,
`rootBits` would fail, not pass.) -/
def wholeRoot (k p : Nat) : Nat := ((List.range (p + 1)).filter fun i => i ^ k ≤ p).length - 1

/-- Section 4.2.2: K0 … K63 are the first 32 bits of the fractional parts
of the cube roots of the first 64 primes. -/
theorem K_cube_roots :
    (firstPrimes 64).length = 64 ∧ K.length = 64 ∧
    ((firstPrimes 64).zip K).all (fun (p, k) => rootBits 3 p (wholeRoot 3 p) k.toNat) = true := by
  decide +kernel

/-- Section 5.3.3: H(0) is the first 32 bits of the fractional parts of
the square roots of the first 8 primes. -/
theorem initialHash_square_roots :
    let H := initialHash
    ((firstPrimes 8).zip [H.H0, H.H1, H.H2, H.H3, H.H4, H.H5, H.H6, H.H7]).all
      (fun (p, h) => rootBits 2 p (wholeRoot 2 p) h.toNat) = true := by
  decide +kernel

/-- The worked example of docs/programming/SHA256_SPEC.md: Σ0 of H0(0). -/
theorem bigSigma0_example : bigSigma0 0x6a09e667 = 0xce20b47e := by
  decide +kernel

/-! ### Test vectors

Each theorem has the kernel compute `sha256` of the message and compare
it with the expected digest. No function of the specification computes
an expected digest: the FIPS examples below write it as plain bytes, and
the CAVP vectors keep NIST's hexadecimal text verbatim and read it with
`hex`, a small helper that `sha256` does not use.

The NIST vectors covered, and no others: the FIPS 180-2 examples B.1
("abc") and B.2 (448 bits); and 17 of NIST's CAVP byte-oriented vectors,
16 of the 65 in SHA256ShortMsg.rsp (Len = 0, 8, 16, 24, 32, 64, 128, 248,
256, 384, 432, 440, 448, 456, 504 and 512 bits) and 1 of the 64 in
SHA256LongMsg.rsp (Len = 1304). Not covered: the other CAVP vectors, the
Monte Carlo test and FIPS 180-2 example B.3 (one million 'a'). -/

/-- The UTF-8 bytes of a string; for the ASCII test messages, one byte per
character. -/
def utf8 (s : String) : List UInt8 := s.toUTF8.data.toList

/-- NIST (FIPS 180-2 appendix B.1; the one-block example of FIPS 180-4):
"abc". -/
theorem nist_abc : sha256 (utf8 "abc") =
  [0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
   0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad] := by
  decide +kernel

/-- NIST (FIPS 180-2 appendix B.2; the two-block example of FIPS 180-4):
the 448-bit (56-byte) message. The length no longer fits in the first
block, so the second holds only padding. -/
theorem nist_448 : sha256 (utf8 "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") =
  [0x24, 0x8d, 0x6a, 0x61, 0xd2, 0x06, 0x38, 0xb8, 0xe5, 0xc0, 0x26, 0x93, 0x0c, 0x3e, 0x60, 0x39,
   0xa3, 0x3c, 0xe4, 0x59, 0x64, 0xff, 0x21, 0x67, 0xf6, 0xec, 0xed, 0xd4, 0x19, 0xdb, 0x06, 0xc1] := by
  decide +kernel

/-! NIST's CAVP byte-oriented vectors for SHA-256 (Cryptographic Algorithm
Validation Program, CAVS 11.0, csrc.nist.gov, shabytetestvectors.zip; the
files SHA256ShortMsg.rsp, SHA-256 75e1cb83…283c, and SHA256LongMsg.rsp,
6fac36f3…0974). Each theorem copies one entry's Len, Msg and MD verbatim. -/

/-- The value of a hexadecimal digit 0-9 or a-f, given as its ASCII code,
as NIST's files write them. (Any other character gives a wrong value, so
a typo fails the check.) -/
def hexDigit (c : UInt8) : Nat := if c.toNat ≤ 57 then c.toNat - 48 else c.toNat - 87

/-- Hexadecimal digits, two per byte, as bytes. -/
def hexBytes : List UInt8 → List UInt8
  | hi :: lo :: rest => (hexDigit hi * 16 + hexDigit lo).toUInt8 :: hexBytes rest
  | _ => []

/-- The bytes a hexadecimal string writes. (Its UTF-8 bytes, not
`String.toList`: the kernel reads those far faster.) -/
def hex (s : String) : List UInt8 := hexBytes (utf8 s)

/-- A CAVP message: the first Len bits of Msg. (The entry Len = 0 writes
Msg = 00 for the empty message.) -/
def cavp (len : Nat) (msg : String) : List UInt8 := (hex msg).take (len / 8)

theorem hex_example : hex "00ff1a9c" = [0x00, 0xff, 0x1a, 0x9c] := by
  decide +kernel

theorem cavp_short_0 : sha256 (cavp 0 "00") =
    hex "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" := by
  decide +kernel

theorem cavp_short_8 : sha256 (cavp 8 "d3") =
    hex "28969cdfa74a12c82f3bad960b0b000aca2ac329deea5c2328ebc6f2ba9802c1" := by
  decide +kernel

theorem cavp_short_16 : sha256 (cavp 16 "11af") =
    hex "5ca7133fa735326081558ac312c620eeca9970d1e70a4b95533d956f072d1f98" := by
  decide +kernel

theorem cavp_short_24 : sha256 (cavp 24 "b4190e") =
    hex "dff2e73091f6c05e528896c4c831b9448653dc2ff043528f6769437bc7b975c2" := by
  decide +kernel

theorem cavp_short_32 : sha256 (cavp 32 "74ba2521") =
    hex "b16aa56be3880d18cd41e68384cf1ec8c17680c45a02b1575dc1518923ae8b0e" := by
  decide +kernel

theorem cavp_short_64 : sha256 (cavp 64 "5738c929c4f4ccb6") =
    hex "963bb88f27f512777aab6c8b1a02c70ec0ad651d428f870036e1917120fb48bf" := by
  decide +kernel

theorem cavp_short_128 : sha256 (cavp 128 "0a27847cdc98bd6f62220b046edd762b") =
    hex "80c25ec1600587e7f28b18b1b18e3cdc89928e39cab3bc25e4d4a4c139bcedc4" := by
  decide +kernel

theorem cavp_short_248 : sha256 (cavp 248 "95a765809caf30ada90ad6d61c2b4b30250df0a7ce23b7753c9187f4319ce2") =
    hex "a4139b74b102cf1e2fce229a6cd84c87501f50afa4c80feacf7d8cf5ed94f042" := by
  decide +kernel

theorem cavp_short_256 : sha256 (cavp 256 "09fc1accc230a205e4a208e64a8f204291f581a12756392da4b8c0cf5ef02b95") =
    hex "4f44c1c7fbebb6f9601829f3897bfd650c56fa07844be76489076356ac1886a4" := by
  decide +kernel

theorem cavp_short_384 : sha256 (cavp 384 "4eef5107459bddf8f24fc7656fd4896da8711db50400c0164847f692b886ce8d7f4d67395090b3534efd7b0d298da34b") =
    hex "7c5d14ed83dab875ac25ce7feed6ef837d58e79dc601fb3c1fca48d4464e8b83" := by
  decide +kernel

theorem cavp_short_432 : sha256 (cavp 432 "25362a4b9d74bde6128c4fdc672305900947bc3ada9d9d316ebcf1667ad4363189937251f149c72e064a48608d940b7574b17fefc0df") =
    hex "f8e4ccab6c979229f6066cc0cb0cfa81bb21447c16c68773be7e558e9f9d798d" := by
  decide +kernel

theorem cavp_short_440 : sha256 (cavp 440 "3ebfb06db8c38d5ba037f1363e118550aad94606e26835a01af05078533cc25f2f39573c04b632f62f68c294ab31f2a3e2a1a0d8c2be51") =
    hex "6595a2ef537a69ba8583dfbf7f5bec0ab1f93ce4c8ee1916eff44a93af5749c4" := by
  decide +kernel

theorem cavp_short_448 : sha256 (cavp 448 "2d52447d1244d2ebc28650e7b05654bad35b3a68eedc7f8515306b496d75f3e73385dd1b002625024b81a02f2fd6dffb6e6d561cb7d0bd7a") =
    hex "cfb88d6faf2de3a69d36195acec2e255e2af2b7d933997f348e09f6ce5758360" := by
  decide +kernel

theorem cavp_short_456 : sha256 (cavp 456 "4cace422e4a015a75492b3b3bbfbdf3758eaff4fe504b46a26c90dacc119fa9050f603d2b58b398cad6d6d9fa922a154d9e0bc4389968274b0") =
    hex "4d54b2d284a6794581224e08f675541c8feab6eefa3ac1cfe5da4e03e62f72e4" := by
  decide +kernel

theorem cavp_short_504 : sha256 (cavp 504 "e2f76e97606a872e317439f1a03fcd92e632e5bd4e7cbc4e97f1afc19a16fde92d77cbe546416b51640cddb92af996534dfd81edb17c4424cf1ac4d75aceeb") =
    hex "18041bd4665083001fba8c5411d2d748e8abbfdcdfd9218cb02b68a78e7d4c23" := by
  decide +kernel

theorem cavp_short_512 : sha256 (cavp 512 "5a86b737eaea8ee976a0a24da63e7ed7eefad18a101c1211e2b3650c5187c2a8a650547208251f6d4237e661c7bf4c77f335390394c37fa1a9f9be836ac28509") =
    hex "42e61e174fbb3897d6dd6cef3dd2802fe67b331953b06114a65c772859dfc1aa" := by
  decide +kernel

theorem cavp_long_1304 : sha256 (cavp 1304 "451101250ec6f26652249d59dc974b7361d571a8101cdfd36aba3b5854d3ae086b5fdd4597721b66e3c0dc5d8c606d9657d0e323283a5217d1f53f2f284f57b85c8a61ac8924711f895c5ed90ef17745ed2d728abd22a5f7a13479a462d71b56c19a74a40b655c58edfe0a188ad2cf46cbf30524f65d423c837dd1ff2bf462ac4198007345bb44dbb7b1c861298cdf61982a833afc728fae1eda2f87aa2c9480858bec") =
    hex "3c593aa539fdcdae516cdf2f15000f6634185c88f505b39775fb9ab137a10aa2" := by
  decide +kernel

/-- Not a NIST vector: the 896-bit (112-byte) message of NIST's SHA-384
and SHA-512 examples, with the SHA-256 digest that test-vector lists
publish and Python's `hashlib` (OpenSSL) gives. Two blocks that both hold
message bytes. -/
theorem published_896 : sha256 (utf8 ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmno" ++
    "ijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu")) =
  [0xcf, 0x5b, 0x16, 0xa7, 0x78, 0xaf, 0x83, 0x80, 0x03, 0x6c, 0xe5, 0x9e, 0x7b, 0x04, 0x92, 0x37,
   0x0b, 0x24, 0x9b, 0x11, 0xe8, 0xf0, 0x7a, 0x51, 0xaf, 0xac, 0x45, 0x03, 0x7a, 0xfe, 0xe9, 0xd1] := by
  decide +kernel

/-- Bytes 255, 254, …, 256 - n: a message of n bytes for the padding
boundaries below. For n ≤ 128 every byte is 128 or more, unlike the ASCII
messages above. -/
def countdown (n : Nat) : List UInt8 := (List.range n).map fun i => (255 - i).toUInt8

/-! Padding boundaries, not NIST vectors: digests from Python's `hashlib`
(OpenSSL), an implementation independent of this file. 55 bytes is the
longest message of one block, 56 the shortest of two; 64 is one whole
block; 119 the longest of two blocks, 120 the shortest of three. -/

theorem boundary_55 : sha256 (countdown 55) =
  [0xc7, 0xd0, 0x53, 0xff, 0x9b, 0x2f, 0x82, 0x1d, 0xec, 0x7e, 0x62, 0xcc, 0xc6, 0x9f, 0xcb, 0xb4,
   0xc8, 0x7e, 0x61, 0x60, 0x88, 0x6f, 0x4e, 0x00, 0xc9, 0x77, 0x85, 0xb0, 0xec, 0xbe, 0xca, 0x09] := by
  decide +kernel

theorem boundary_56 : sha256 (countdown 56) =
  [0xad, 0x33, 0x52, 0x98, 0x39, 0x48, 0x19, 0x19, 0xab, 0x44, 0x35, 0xbc, 0x65, 0x3a, 0x1e, 0x85,
   0xb7, 0x2f, 0xe0, 0xc5, 0x85, 0xb8, 0x80, 0x7f, 0xec, 0xb5, 0x47, 0x74, 0xdc, 0x14, 0x10, 0x93] := by
  decide +kernel

theorem boundary_64 : sha256 (countdown 64) =
  [0xbf, 0x86, 0x05, 0x1d, 0x94, 0x1b, 0xc4, 0x96, 0xb3, 0xa7, 0x5d, 0x22, 0x29, 0x96, 0x2c, 0x21,
   0x6e, 0x61, 0x4e, 0x8e, 0x67, 0xb4, 0xb7, 0x3e, 0x29, 0x3a, 0xa6, 0x96, 0x0d, 0xb2, 0x8a, 0xba] := by
  decide +kernel

theorem boundary_119 : sha256 (countdown 119) =
  [0xa3, 0x0e, 0xce, 0x12, 0x04, 0x79, 0xdd, 0xee, 0xb4, 0xe3, 0xc0, 0xaf, 0x22, 0x97, 0x2d, 0x05,
   0x21, 0xce, 0xe9, 0x2f, 0xca, 0x68, 0x7d, 0xdd, 0x17, 0x09, 0xef, 0x17, 0x91, 0xda, 0x2d, 0x55] := by
  decide +kernel

theorem boundary_120 : sha256 (countdown 120) =
  [0x52, 0x99, 0xe3, 0xa1, 0x8d, 0x81, 0x11, 0xcc, 0x5e, 0x7c, 0xd8, 0xe2, 0xe0, 0x1c, 0x9b, 0x45,
   0x65, 0x20, 0x96, 0x4a, 0x7f, 0x73, 0x0e, 0xf5, 0xa9, 0x81, 0x49, 0xfe, 0x56, 0xdc, 0x84, 0xdd] := by
  decide +kernel

/-- A wrong digest is refuted, not merely left unproved: the "abc" digest
with its last bit flipped (0xad becomes 0xac). -/
theorem nist_abc_wrong_refuted : sha256 (utf8 "abc") ≠
  [0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
   0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xac] := by
  decide +kernel

/-! The one-million-'a' vector of FIPS 180-2 appendix B.3 (cdc76e5c …) is
not checked: it has 15,626 blocks, and the kernel needs about 0.5 s and
130 MB per block within one theorem, so about 2 hours and 2 TB
(docs/programming/SHA256_SPEC.md, "What the kernel checks"). -/

/-! ## Part 6. Lemmas for the later stages -/

/-! ### The helper functions as rewrite rules

A Forth cell holds a word as its number `x.toNat`, from 0 to 2^32 - 1
(src/lib/sha256.fs computes on such numbers and masks). These rules turn
each function into operations on those numbers: `>>>`, `<<<`, `|||`,
`&&&` and `^^^` on `Nat`, with `% 2 ^ 32` exactly where a bit can leave
the word. Lean's own `BitVec.toNat_add`, `toNat_xor`, `toNat_and` and
`toNat_or` give the rest; `Nat.and_two_pow_sub_one_eq_mod` turns
`% 2 ^ 32` into a mask `&&& (2 ^ 32 - 1)`. -/

theorem SHR_toNat (n : Nat) (x : Word) : (SHR n x).toNat = x.toNat >>> n := by
  simp [SHR]

theorem ROTR_toNat (n : Nat) (x : Word) :
    (ROTR n x).toNat = (x.toNat >>> n ||| x.toNat <<< (32 - n)) % 2 ^ 32 := by
  have small : x.toNat >>> n < 2 ^ 32 := by
    have := (x >>> n).isLt
    simpa using this
  simp only [ROTR, BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft]
  rw [Nat.or_mod_two_pow, Nat.mod_eq_of_lt small]

/-- ROTR is Lean's own rotation, so Lean's lemmas about `rotateRight` apply. -/
theorem ROTR_eq_rotateRight (h : n < 32) (x : Word) : ROTR n x = x.rotateRight n := by
  simp [ROTR, BitVec.rotateRight, BitVec.rotateRightAux, Nat.mod_eq_of_lt h]

/-- Every bit of the word of 32 ones is 1, checked bit by bit by the
kernel. (Lean's general lemmas about `allOnes` and `~~~` use the axiom
`Classical.choice`; this keeps Ch's lemmas free of it.) -/
theorem allOnes_getLsbD : ∀ i, i < 32 → (BitVec.allOnes 32).getLsbD i = true := by
  decide +kernel

/-- Ch as src/lib/sha256.fs computes it, without a complement:
z ⊕ (x ∧ (y ⊕ z)). Proved bit by bit: the eight cases of three bits. -/
theorem Ch_eq_select (x y z : Word) : Ch x y z = z ^^^ (x &&& (y ^^^ z)) := by
  -- Lean defines the complement ~~~x as allOnes ^^^ x.
  show (x &&& y) ^^^ ((BitVec.allOnes 32 ^^^ x) &&& z) = _
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, allOnes_getLsbD i hi]
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> rfl

/-- Maj as src/lib/sha256.fs computes it: (x ∧ y) ∨ (z ∧ (x ∨ y)). -/
theorem Maj_eq_or (x y z : Word) : Maj x y z = (x &&& y) ||| (z &&& (x ||| y)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [Maj, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or]
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> rfl

theorem Ch_toNat (x y z : Word) :
    (Ch x y z).toNat = z.toNat ^^^ (x.toNat &&& (y.toNat ^^^ z.toNat)) := by
  simp [Ch_eq_select]

theorem Maj_toNat (x y z : Word) :
    (Maj x y z).toNat = (x.toNat &&& y.toNat) ||| (z.toNat &&& (x.toNat ||| y.toNat)) := by
  simp [Maj_eq_or]

theorem bigSigma0_toNat (x : Word) :
    (bigSigma0 x).toNat = (ROTR 2 x).toNat ^^^ (ROTR 13 x).toNat ^^^ (ROTR 22 x).toNat := by
  simp [bigSigma0]

theorem bigSigma1_toNat (x : Word) :
    (bigSigma1 x).toNat = (ROTR 6 x).toNat ^^^ (ROTR 11 x).toNat ^^^ (ROTR 25 x).toNat := by
  simp [bigSigma1]

theorem smallSigma0_toNat (x : Word) :
    (smallSigma0 x).toNat = (ROTR 7 x).toNat ^^^ (ROTR 18 x).toNat ^^^ (SHR 3 x).toNat := by
  simp [smallSigma0]

theorem smallSigma1_toNat (x : Word) :
    (smallSigma1 x).toNat = (ROTR 17 x).toNat ^^^ (ROTR 19 x).toNat ^^^ (SHR 10 x).toNat := by
  simp [smallSigma1]

/-! ### Padding -/

/-- `padZeroBits l` solves the standard's equation l + 1 + k ≡ 448 (mod 512) … -/
theorem padZeroBits_spec (l : Nat) : (l + 1 + padZeroBits l) % 512 = 448 := by
  unfold padZeroBits; omega

/-- … and is its smallest solution k ≥ 0. -/
theorem padZeroBits_least (l k : Nat) (h : (l + 1 + k) % 512 = 448) : padZeroBits l ≤ k := by
  unfold padZeroBits; omega

/-- For a whole number of bytes, k ≡ 7 (mod 8): the bit 1 and k zero bits
are the byte 0x80 and whole zero bytes. -/
theorem padZeroBits_byte (n : Nat) : padZeroBits (8 * n) % 8 = 7 := by
  unfold padZeroBits; omega

theorem length_bytesBE (x : BitVec w) : (bytesBE x).length = w / 8 := by
  simp [bytesBE]

/-- The padding of a message of n bytes: the byte 0x80, the zero bytes,
and the 8 bytes of the length. -/
theorem length_padding (n : Nat) :
    (padding n).length = 1 + (padZeroBits (8 * n) - 7) / 8 + 8 := by
  simp [padding, length_bytesBE]; omega

theorem length_pad (m : List UInt8) : (pad m).length = 64 * ((m.length + 8) / 64 + 1) := by
  simp only [pad, List.length_append, length_padding]
  unfold padZeroBits; omega

/-- The padded length is a multiple of 64 bytes (512 bits). -/
theorem length_pad_mod (m : List UInt8) : (pad m).length % 64 = 0 := by
  rw [length_pad]; omega

/-- Padding adds at least 9 bytes (the byte 0x80 and the length) and at most 72. -/
theorem length_pad_bounds (m : List UInt8) :
    m.length + 9 ≤ (pad m).length ∧ (pad m).length ≤ m.length + 72 := by
  rw [length_pad]; exact ⟨by omega, by omega⟩

/-- The message is a prefix of the padded message. -/
theorem pad_prefix (m : List UInt8) : m <+: pad m := List.prefix_append _ _

/-- The byte after the message is 0x80. -/
theorem pad_after_message (m : List UInt8) : (pad m)[m.length]? = some 0x80 := by
  simp [pad, padding]

/-- The padded message ends with the message's length in bits as 64 bits,
big-endian. -/
theorem pad_suffix (m : List UInt8) : bytesBE (BitVec.ofNat 64 (8 * m.length)) <:+ pad m := by
  simp only [pad, padding]
  exact ⟨m ++ 0x80 :: List.replicate ((padZeroBits (8 * m.length) - 7) / 8) 0, by simp⟩

/-! ### Parsing -/

/-- The number of a word read from four bytes, big-endian:
b0 · 2^24 + b1 · 2^16 + b2 · 2^8 + b3. -/
theorem wordOf_toNat (b0 b1 b2 b3 : UInt8) :
    (wordOf b0 b1 b2 b3).toNat =
      b0.toNat * 2 ^ 24 + b1.toNat * 2 ^ 16 + b2.toNat * 2 ^ 8 + b3.toNat := by
  simp only [wordOf, BitVec.toNat_append, UInt8.toNat]
  -- A shifted number ORed with a smaller one is their sum.
  rw [← Nat.shiftLeft_add_eq_or_of_lt b1.toBitVec.isLt,
    ← Nat.shiftLeft_add_eq_or_of_lt b2.toBitVec.isLt,
    ← Nat.shiftLeft_add_eq_or_of_lt b3.toBitVec.isLt]
  simp only [Nat.shiftLeft_eq]
  omega

theorem length_words : ∀ bytes : List UInt8, (words bytes).length = bytes.length / 4
  | _ :: _ :: _ :: _ :: rest => by simp [words, length_words rest]; omega
  | [] | [_] | [_, _] | [_, _, _] => by simp [words]

theorem length_parse : ∀ (n : Nat) (ws : List Word), (parse n ws).length = n
  | 0, _ => rfl
  | n + 1, ws => by simp [parse, length_parse n]

/-- Every block of `parse n ws` has 16 words when `ws` has 16n of them. -/
theorem length_of_mem_parse :
    ∀ (n : Nat) (ws : List Word), 16 * n ≤ ws.length → ∀ M ∈ parse n ws, M.length = 16
  | 0, _, _, _, h => by simp [parse] at h
  | n + 1, ws, hn, M, h => by
    simp only [parse, List.mem_cons] at h
    rcases h with h | h
    · subst h; simp; omega
    · exact length_of_mem_parse n _ (by simp; omega) M h

/-- A padded message has N = (n + 8) / 64 + 1 blocks, n the message's
length in bytes. -/
theorem length_blocks_pad (m : List UInt8) : (blocks (pad m)).length = (m.length + 8) / 64 + 1 := by
  simp only [blocks, length_parse, length_pad]; omega

/-- Each block of a padded message has 16 words. -/
theorem length_of_mem_blocks_pad (m : List UInt8) :
    ∀ M ∈ blocks (pad m), M.length = 16 := by
  apply length_of_mem_parse
  rw [length_words, length_pad]; omega

/-! ### The message schedule in the standard's form -/

theorem getD_of_prefix {l₁ l₂ : List α} (h : l₁ <+: l₂) (hi : i < l₁.length) (d : α) :
    l₂.getD i d = l₁.getD i d := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem length_scheduleSteps (M : List Word) (k : Nat) :
    (Nat.repeat scheduleStep k M).length = M.length + k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Nat.repeat, scheduleStep, ih]; omega

theorem scheduleSteps_prefix (M : List Word) (k j : Nat) :
    Nat.repeat scheduleStep k M <+: Nat.repeat scheduleStep (k + j) M := by
  induction j with
  | zero => exact List.prefix_refl _
  | succ j ih => exact ih.trans (List.prefix_append _ _)

theorem length_schedule (M : List Word) (hM : M.length = 16) : (schedule M).length = 64 := by
  simp [schedule, length_scheduleSteps, hM]

/-- Step 1, for t ≤ 15: W(t) = M(t). -/
theorem schedule_message (M : List Word) (ht : t < M.length) :
    (schedule M).getD t 0 = M.getD t 0 :=
  getD_of_prefix (scheduleSteps_prefix M 0 48) ht 0

/-- Step 1, for 16 ≤ t ≤ 63:
W(t) = σ1(W(t-2)) + W(t-7) + σ0(W(t-15)) + W(t-16). -/
theorem schedule_formula (M : List Word) (hM : M.length = 16) (h16 : 16 ≤ t) (h64 : t < 64) :
    (schedule M).getD t 0 =
      smallSigma1 ((schedule M).getD (t - 2) 0) + (schedule M).getD (t - 7) 0 +
        smallSigma0 ((schedule M).getD (t - 15) 0) + (schedule M).getD (t - 16) 0 := by
  -- W holds W0 … W(t-1), and one more step appends W(t).
  let W := Nat.repeat scheduleStep (t - 16) M
  have hW : W.length = t := by simp [W, length_scheduleSteps, hM]; omega
  have prefixW : W <+: schedule M := by
    have := scheduleSteps_prefix M (t - 16) (48 - (t - 16))
    rwa [show t - 16 + (48 - (t - 16)) = 48 by omega] at this
  have prefixNext : scheduleStep W <+: schedule M := by
    have := scheduleSteps_prefix M (t - 16 + 1) (47 - (t - 16))
    rwa [show t - 16 + 1 + (47 - (t - 16)) = 48 by omega] at this
  have lengthNext : t < (scheduleStep W).length := by simp [scheduleStep, hW]
  have from_W : ∀ j, j ≤ 16 → 0 < j → (schedule M).getD (t - j) 0 = W.getD (t - j) 0 :=
    fun j _ hj => getD_of_prefix prefixW (by omega) 0
  rw [getD_of_prefix prefixNext lengthNext, from_W 2 (by omega) (by omega),
    from_W 7 (by omega) (by omega), from_W 15 (by omega) (by omega),
    from_W 16 (by omega) (by omega)]
  simp [scheduleStep, scheduleNext, List.getD_eq_getElem?_getD, hW]

/-! ### The compression, one round at a time, and hashing block by block -/

theorem rounds_zero (H : HashValue) (W : List Word) : rounds H W 0 = start H := rfl

/-- One more round: what a counted loop's invariant needs. -/
theorem rounds_succ (H : HashValue) (W : List Word) (t : Nat) :
    rounds H W (t + 1) = round (rounds H W t) (K.getD t 0) (W.getD t 0) := by
  simp [rounds, List.range_succ, List.foldl_append]

theorem hashBlocks_nil (H : HashValue) : hashBlocks H [] = H := rfl

theorem hashBlocks_cons (H : HashValue) (M : List Word) (Ms : List (List Word)) :
    hashBlocks H (M :: Ms) = hashBlocks (compress H M) Ms := rfl

/-- Hashing the blocks of two pieces one after the other, as an
incremental interface (init, update, final) does. -/
theorem hashBlocks_append (H : HashValue) (Ms Ns : List (List Word)) :
    hashBlocks H (Ms ++ Ns) = hashBlocks (hashBlocks H Ms) Ns := by
  simp [hashBlocks, List.foldl_append]

theorem words_append :
    ∀ a b : List UInt8, a.length % 4 = 0 → words (a ++ b) = words a ++ words b
  | _ :: _ :: _ :: _ :: rest, b, h => by
    simp only [List.length_cons] at h
    simp [words, words_append rest b (by omega)]
  | [], _, _ => rfl
  | [_], _, h | [_, _], _, h | [_, _, _], _, h => by simp at h

theorem parse_append : ∀ (n k : Nat) (ws vs : List Word), ws.length = 16 * n →
    parse (n + k) (ws ++ vs) = parse n ws ++ parse k vs
  | 0, _, [], _, _ => by simp [parse]
  | 0, _, _ :: _, _, h => by simp at h
  | n + 1, k, ws, vs, h => by
    rw [show n + 1 + k = n + k + 1 by omega]
    simp only [parse, List.take_append_of_le_length (show 16 ≤ ws.length by omega),
      List.drop_append_of_le_length (show 16 ≤ ws.length by omega)]
    rw [parse_append n k _ _ (by simp; omega)]
    rfl

/-- Parsing a message whose first part is whole blocks gives that part's
blocks, then the rest's. -/
theorem blocks_append (a b : List UInt8) (ha : a.length % 64 = 0) :
    blocks (a ++ b) = blocks a ++ blocks b := by
  unfold blocks
  rw [words_append a b (by omega), List.length_append,
    show (a.length + b.length) / 64 = a.length / 64 + b.length / 64 by omega]
  apply parse_append
  rw [length_words]; omega

/-- SHA-256 of a message a ++ b, where a is whole blocks: hash a's blocks
as they come, then the rest b with the padding for the whole length. This
is the shape of an incremental interface (stage SHA-4). -/
theorem sha256_append_blocks (a b : List UInt8) (ha : a.length % 64 = 0) :
    sha256 (a ++ b) =
      digest (hashBlocks (hashBlocks initialHash (blocks a))
        (blocks (b ++ padding (a.length + b.length)))) := by
  unfold sha256 pad
  rw [List.length_append, List.append_assoc, blocks_append a _ ha, hashBlocks_append]

end Sha256Spec

/-! ## Axiom audit

The axioms of every declaration of this file, whatever its kind or
modifiers (definitions, theorems, private and protected ones, and the
auxiliary declarations Lean makes for them), printed in the words of
`#print axioms`, which computes them the same way (`collectAxioms`).
tests/reference/sha256-spec-check.sh requires each to be within the
owner's allowlist: `propext`, `Classical.choice` and `Quot.sound`. -/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  -- `map₂` holds the declarations of this file, not the imported ones.
  let names := (env.constants.map₂.toList.map (·.1)).toArray.qsort (·.toString < ·.toString)
  IO.println "BEGIN AXIOM AUDIT"
  for name in names do
    let axioms ← collectAxioms name
    if axioms.isEmpty then
      IO.println s!"'{name}' does not depend on any axioms"
    else
      let sorted := axioms.qsort (·.toString < ·.toString)
      IO.println s!"'{name}' depends on axioms: {sorted.toList}"
  IO.println s!"END AXIOM AUDIT ({names.size} declarations)"
