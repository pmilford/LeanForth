\ Unit tests of the shared Nat operation table (src/core/nat-ops.fs; plan
\ S3a, commit C0), called directly as the kernel's reduce_nat
\ (kernel/reduce-nat.fs) and the front end's reduceNat?
\ (front/reduce-nat.fs) call it, by the classes of
\ docs/development/TEST_COVERAGE_REVIEW.md:
\ 1, 3. Every operation by its index with Lean's answers (truncated
\    subtraction, division and remainder by 0, gcd, bitwise operations,
\    shifts, Nat.beq and Nat.ble as the constants Bool.true and
\    Bool.false), results beyond a cell, the names of the fourteen
\    operations and of none, and the constants: each ( node outcome ),
\    the stack as before (T{ }T checks the depth).
\ 2. Malformed input: a helper's failure other than no room (invalid,
\    never ok); an arena too small for the operands; an operand that is
\    no literal leaf (review s3a-decide M1, plan 9.4.8l AW): the first,
\    the second or both, a constant or an application, for each of the
\    fourteen operations and Nat.succ, invalid and -1 with no node made
\    and the cells under the call kept, and lf-nat-lits-by's step not run.
\ 5. Resources, which are never a verdict here (the kernel's count refusal
\    and Meta's threshold are their callers'): a result or an estimate
\    over Lean's 2^30 bits (an exponent of more than a cell, a shift past
\    the limit, a product of bits past a cell) is full with diagnostic 93;
\    a base of 0 or 1 and a shift of 0 compute at once whatever the
\    count; the scratch arena refused by the heap; no room for the
\    constant or the term.
\ 7. Regression pins: the indices of Nat.pow and Nat.shiftLeft.
\ Test-only; nothing here accepts a theorem.
require ../support/alloc-fail.fs
include ../support/heap-watch.fs
include ../support/tester.fs
require ../../src/core/nat-ops.fs
require ../../src/core/name-equal.fs
decimal

: made ( flag -- ) 0= abort" nat-ops test: refused" ;
: roomy ( -- ) 4096 lf-term-capacity! drop 4096 lf-cref-capacity! drop ;
: fresh ( -- )
  lf-name-reset lf-level-reset lf-term-reset lf-cref-reset roomy lf-ssession-begin made ;
fresh
: nlit ( u -- node ) lf-nat-lit ok? made ;
: lits ( a b -- a' b' ) swap nlit swap nlit ;
\ A small result's value, or -1 for a node that is no one-limb literal.
: small-of ( node -- u )
  dup lf-lit-leaf? 0= if drop -1 exit then
  dup lf-lit-small? if lf-lit-cell else drop -1 then ;
: computes ( a b i -- u outcome ) >r lits r> lf-nat-lit-op swap small-of swap ;
: named ( prefix c-addr u -- name ) lf-name-str made ;
: dotted ( c-addr u part-addr part-u -- name ) 2>r 0 -rot named 2r> named ;
: const-name ( node -- name ) lf-term-first@ lf-cref-slot lf-crec-name @ ;
: bool? ( node flag -- flag' )
  >r const-name s" Bool" r> if s" true" else s" false" then dotted lf-name-same? ;

\ ---- 1, 3. Each operation on small operands.
T{ 3 5 0 computes -> 8 outcome-ok }T
T{ 3 5 1 computes -> 0 outcome-ok }T      \ truncated: 3 - 5 = 0
T{ 5 3 1 computes -> 2 outcome-ok }T
T{ 6 7 2 computes -> 42 outcome-ok }T
T{ 2 10 3 computes -> 1024 outcome-ok }T
T{ 0 0 3 computes -> 1 outcome-ok }T      \ 0 ^ 0 = 1
T{ 1071 462 4 computes -> 21 outcome-ok }T
T{ 100 7 5 computes -> 2 outcome-ok }T
T{ 7 0 5 computes -> 7 outcome-ok }T      \ n % 0 = n
T{ 17 5 6 computes -> 3 outcome-ok }T
T{ 7 0 6 computes -> 0 outcome-ok }T      \ n / 0 = 0
T{ 12 10 9 computes -> 8 outcome-ok }T
T{ 12 10 10 computes -> 14 outcome-ok }T
T{ 12 10 11 computes -> 6 outcome-ok }T
T{ 3 4 12 computes -> 48 outcome-ok }T
T{ 48 4 13 computes -> 3 outcome-ok }T
: test-op ( a b i flag -- flag' ) >r >r lits r> lf-nat-lit-op ok? made r> bool? ;
T{ 4 4 7 true test-op 3 4 7 false test-op -> true true }T
T{ 3 5 8 true test-op 5 5 8 true test-op 5 3 8 false test-op -> true true true }T
\ Beyond a cell: 2^64 by pow and by shiftLeft, equal by Nat.beq; its
\ product with itself (three limbs) divided by it again.
: two64 ( -- node ) 2 64 lits 3 lf-nat-lit-op ok? made ;
: same? ( a b -- flag ) 7 lf-nat-lit-op ok? made true bool? ;
T{ two64 lf-lit-small? two64 lf-term-second@ -> false 2 }T
T{ two64 1 nlit 64 nlit 12 lf-nat-lit-op ok? made same? -> true }T
T{ two64 dup 2 lf-nat-lit-op ok? made two64 6 lf-nat-lit-op ok? made two64 same? -> true }T
T{ two64 2 nlit 6 lf-nat-lit-op ok? made 2 nlit 63 nlit 3 lf-nat-lit-op ok? made same? -> true }T

\ ---- 1. core/literals.fs's lf-lit-u> (review s3a-decide B5: the bound
\ of nat-ops.fs's counts, the kernel's count and Meta's threshold): a
\ literal above a cell value, compared unsigned; one of two limbs always.
T{ 0 nlit 0 lf-lit-u> 1 nlit 0 lf-lit-u> 5 nlit 5 lf-lit-u> 6 nlit 5 lf-lit-u>
   -> false true false true }T
T{ -1 nlit -1 lf-lit-u> -1 nlit 1 lf-lit-u> two64 -1 lf-lit-u> two64 0 lf-lit-u>
   -> false true true true }T

\ ---- 1. The names: each operation's index, any other name -1.
: index-of ( c-addr u -- i ) s" Nat" 2swap dotted lf-nat-op ;
T{ s" add" index-of s" sub" index-of s" mul" index-of s" pow" index-of -> 0 1 2 3 }T
T{ s" gcd" index-of s" mod" index-of s" div" index-of s" beq" index-of -> 4 5 6 7 }T
T{ s" ble" index-of s" land" index-of s" lor" index-of s" xor" index-of -> 8 9 10 11 }T
T{ s" shiftLeft" index-of s" shiftRight" index-of -> 12 13 }T
T{ s" succ" index-of s" log2" index-of -> -1 -1 }T
T{ s" Int" s" add" dotted lf-nat-op 0 s" add" named lf-nat-op -> -1 -1 }T
\ Nat.add under another root (Foo.Nat.add) is no operation.
T{ 0 s" Foo" named s" Nat" named s" add" named lf-nat-op -> -1 }T
T{ s" Nat" s" zero" dotted lf-nat-name? 0 s" Nat" named lf-nat-name? -> true false }T
T{ s" Nat" s" zero" dotted lf-nat-zero-name? s" Nat" s" succ" dotted lf-nat-zero-name?
   0 s" zero" named lf-nat-zero-name? s" Int" s" zero" dotted lf-nat-zero-name? -> true false false false }T
\ Nat.succ by its whole name (review s3a-decide B1: one test for the
\ kernel's and the front end's whnf and reduceNat?): Fin.succ (review
\ fe1c-2 L3), a root succ, Nat itself, Nat.zero, Foo.Nat.succ and
\ Nat.succ.x are not; Nat.add.match_1 is not in Nat's namespace.
T{ s" Nat" s" succ" dotted lf-nat-succ-name? s" Fin" s" succ" dotted lf-nat-succ-name?
   0 s" succ" named lf-nat-succ-name? 0 s" Nat" named lf-nat-succ-name? -> true false false false }T
T{ s" Nat" s" zero" dotted lf-nat-succ-name? 0 s" Foo" named s" Nat" named s" succ" named
   lf-nat-succ-name? s" Nat" s" succ" dotted s" x" named lf-nat-succ-name? -> false false false }T
T{ s" Nat" s" add" dotted s" match_1" named lf-nat-name? s" Nat" s" add" dotted lf-nat-name?
   -> false true }T
\ 7. The indices of the operations whose callers' policies differ.
T{ lf-nat-op-pow lf-nat-op-shl s" pow" index-of s" shiftLeft" index-of -> 3 12 3 12 }T

\ ---- 1. The constants (each maker here ends with core/generation-handles.fs's
\ lf-made-term, tested there).
T{ true nop-bool swap true bool? -> outcome-ok true }T
T{ s" zero" s" Nat" lf-nat-in swap const-name s" Nat" s" zero" dotted lf-name-same? -> outcome-ok true }T
T{ 0 s" Nat" lf-nat-named swap const-name 0 s" Nat" named lf-name-same? -> outcome-ok true }T

\ ---- 5. Over Lean's limit: full with diagnostic 93, never a verdict.
: full93? ( node outcome -- flag ) outcome-full = swap -1 = and lf-diag-code@ lf-diag-nat-size = and ;
: over? ( a b i -- flag ) lf-diag-clear >r lits r> lf-nat-lit-op full93? ;
T{ 2 2147483648 3 over? -> true }T                \ 2 ^ 2^31: 2^31 + 1 bits
T{ two64 2 nlit swap lf-diag-clear 3 lf-nat-lit-op full93? -> true }T   \ an exponent of two limbs
T{ 2 1 63 lshift 3 over? -> true }T                \ bits(2) * 2^63 past a cell
T{ 1 1073741824 12 over? -> true }T                \ 1 << 2^30: 2^30 + 1 bits
T{ 1 1073741825 12 over? -> true }T                \ a shift past the limit
T{ 1 nlit two64 lf-diag-clear 12 lf-nat-lit-op full93? -> true }T     \ a shift of two limbs
\ A base of 0 or 1 and a shift of 0 compute at once, whatever the count.
T{ 1 nlit two64 3 lf-nat-lit-op swap small-of -> outcome-ok 1 }T
T{ 0 nlit two64 3 lf-nat-lit-op swap small-of -> outcome-ok 0 }T
T{ 0 nlit two64 12 lf-nat-lit-op swap small-of -> outcome-ok 0 }T
\ The base beyond a cell is no unit; a sized power and shift.
T{ two64 3 nlit 3 lf-nat-lit-op ok? made two64 dup 2 lf-nat-lit-op ok? made two64 2
   lf-nat-lit-op ok? made same? -> true }T
T{ 3 nlit 70 nlit 12 lf-nat-lit-op ok? made 70 nlit 13 lf-nat-lit-op swap small-of -> outcome-ok 3 }T

\ ---- 5. The scratch arena refused by the heap (heap-watch.fs): full with
\ diagnostic 93; then the stores' refusals (alloc-fail.fs) and no room.
: arena-refused? ( a b i -- flag )
  >r lits r> lf-diag-clear 1 heap-refusals ! lf-nat-lit-op 0 heap-refusals ! full93? ;
T{ 3 5 0 arena-refused? 3 5 7 arena-refused? 2 100 3 arena-refused? -> true true true }T
: name-refused ( -- node outcome ) fresh 1 af-arm true nop-bool af-off ;
T{ name-refused nip -> outcome-full }T
: cref-refused ( -- node outcome ) fresh 0 s" Nat" named drop 1 af-arm 0 s" Nat"
   lf-nat-named af-off ;
T{ cref-refused nip -> outcome-full }T
fresh
: crowded ( a b i -- node outcome )
  >r lits lf-term-capacity lf-term-count @ lf-term-capacity! drop
  -rot r> lf-nat-lit-op rot lf-term-capacity! drop ;
T{ 1000 999 0 crowded 1000 999 7 crowded -> -1 outcome-full -1 outcome-full }T
roomy

\ ---- 2. Malformed: an arena too small for the operands (the callers size
\ it from them, so only a direct call reaches this), each operand in
\ turn (b first: 1 cell holds neither, 4 hold 1 and not 2^64 after it);
\ the bits of 0, which pow and shiftLeft never ask (0 goes at once);
\ an operation's failure other than no room is invalid, never ok.
: short? ( a b cells -- flag )
  lf-lit-arena ok? made dup >r ['] big+ swap nop-apply r> lf-lit-arena-free
  outcome-full = swap -1 = and ;
T{ two64 two64 1 short? two64 1 nlit 4 short? -> true true }T
\ nop-apply's answer to the operands' refusal takes the four cells it is
\ given and no more (before plan S3a it dropped one of its caller's too).
T{ 111 222 two64 two64 1 short? -> 111 222 true }T
T{ 0 nlit nop-bits two64 nop-bits -> 0 65 }T
T{ -1 outcome-invalid nop-literal -1 outcome-full lf-diag-clear nop-literal lf-diag-code@
   -> -1 outcome-invalid -1 outcome-full lf-diag-nat-size }T
T{ -1 outcome-invalid nop-truth -> -1 outcome-invalid }T
\ Nat.beq's and Nat.ble's answer after a failed operation (nop-truth,
\ before plan S3a the kernel's lf-rn-truth; review of cleanup-families-2,
\ M1): the failure is the answer, -1 and its outcome, never a Bool
\ constant; on ok the flag picks it.
T{ true outcome-full nop-truth 0 outcome-exhausted nop-truth -> -1 outcome-full -1 outcome-exhausted }T
T{ true outcome-ok nop-truth nip 0 outcome-ok nop-truth nip -> outcome-ok outcome-ok }T

\ ---- 2. An operand that is no literal leaf (review s3a-decide M1, plan
\ 9.4.8l AW): the constant Nat and the application Nat 7, as the first
\ operand, the second or both. Each of the fourteen operations and
\ Nat.succ answers invalid and -1 and makes no node, the cells under the
\ call kept (111); before, they answered ok with a made-up literal.
: k-nat ( -- node ) 0 s" Nat" lf-nat-named ok? made ;
: k-app ( -- node )
  k-nat lf-term-handle 7 nlit lf-term-handle lf-hterm-app lf-made-term ok? made ;
: refused? ( a b i -- flag )
  lf-term-count @ >r lf-nat-lit-op outcome-invalid = swap -1 = and lf-term-count @ r> = and ;
: all-refused? ( a b -- flag ) true 14 0 do >r 2dup i refused? r> and loop nip nip ;
T{ 111 k-nat 3 nlit 0 lf-nat-lit-op -> 111 -1 outcome-invalid }T     \ the first
T{ 111 3 nlit k-app 3 lf-nat-lit-op -> 111 -1 outcome-invalid }T     \ the second (pow)
T{ 111 k-app k-nat 12 lf-nat-lit-op -> 111 -1 outcome-invalid }T     \ both (shiftLeft)
T{ k-nat 3 nlit all-refused? k-app 300 nlit all-refused? -> true true }T
T{ 3 nlit k-nat all-refused? 300 nlit k-app all-refused? -> true true }T
T{ k-nat k-app all-refused? k-app k-app all-refused? -> true true }T
: succ-refused? ( a -- flag )
  lf-term-count @ >r lf-nat-lit-succ outcome-invalid = swap -1 = and lf-term-count @ r> = and ;
T{ 111 k-nat lf-nat-lit-succ -> 111 -1 outcome-invalid }T
T{ k-nat succ-refused? k-app succ-refused? -> true true }T
\ lf-nat-lits-by runs its step only on two literals: ok, the step's
\ answer; else invalid and -1, the step not run.
: ran ( a b i -- node outcome ) drop 2drop 77 outcome-ok ;
T{ 111 3 nlit 4 nlit 9 ' ran lf-nat-lits-by -> 111 77 outcome-ok }T
T{ 111 k-nat 4 nlit 9 ' ran lf-nat-lits-by 3 nlit k-app 9 ' ran lf-nat-lits-by
   -> 111 -1 outcome-invalid -1 outcome-invalid }T

\ ---- 5. The kernel's words on the table (kernel/reduce-nat.fs, whose own
\ tests are tests/core/reduce-nat.fs): the predecessor of a literal of
\ two limbs needs a new literal 1, which a crowded term store refuses.
require ../../src/kernel/reduce-nat.fs
fresh
: crowded-pred ( -- node outcome )
  two64 lf-term-capacity lf-term-count @ lf-term-capacity! drop
  swap lf-reduce-nat-pred rot lf-term-capacity! drop ;
T{ crowded-pred -> -1 outcome-full }T
roomy
\ lf-nat-lit-succ (Nat.succ of a literal, shared by the kernel's
\ lf-reduce-nat-succ and the front end's fold): a + 1, beyond a cell too;
\ a crowded store refuses its literal 1.
T{ 41 nlit lf-nat-lit-succ swap small-of -> outcome-ok 42 }T
T{ two64 lf-nat-lit-succ ok? made two64 1 nlit 0 lf-nat-lit-op ok? made same? -> true }T
fresh
: crowded-succ ( -- node outcome )
  two64 lf-term-capacity lf-term-count @ lf-term-capacity! drop
  swap lf-nat-lit-succ rot lf-term-capacity! drop ;
T{ crowded-succ -> -1 outcome-full }T
roomy
.( nat-ops test: all tests passed) cr
bye
