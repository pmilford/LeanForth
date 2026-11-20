\ Lean's computations on natural-number literals (src/kernel/reduce-nat.fs;
\ plan task 5.2.3; ADR 0014 K7, rules L1-L3), called directly as whnf.fs,
\ defeq.fs and iota.fs call them. Coverage classes of
\ docs/development/TEST_COVERAGE_REVIEW.md:
\ 1, 3. Every binary operation of whnf.fs's list by its index, with
\    Lean's answers (truncated subtraction, division and remainder by 0,
\    gcd, bitwise operations, shifts, Nat.beq and Nat.ble as Bool
\    constants), succ, the predecessor (one limb and several), the
\    constructor form (Nat.zero, Nat.succ n) and the literals' type Nat:
\    each ( node outcome ), the stack as before.
\ 2. An operand that is no literal leaf (review s3a-decide M1; plan
\    9.4.8l AW, the owner's gate of 2026-11-20): invalid and -1 for each
\    operation, the first operand or the second before Lean's count
\    refusal is read, and for Nat.succ, the predecessor (the literal 0
\    too) and the constructor form, never ok and never a verdict, the
\    cells under the call kept (core/nat-ops.fs's lf-nat-lits-by). The
\    callers pass literals only all the same (literals above 0 to the
\    predecessor), which tests/core/defeq.fs (lf-nat-ext, lf-dq-pred?,
\    lf-dq-pred, lf-iota-lit) and tests/front/reduce-nat.fs
\    (lf-meta-nat-value?) pin.
\ 5. Lean's fixed refusals (a count of 2^32 or more: rejected, diagnostic
\    92) and its size limit (a result over 2^30 bits: full, diagnostic
\    93), the shift of 0 by any count; each allocation of an operation
\    refused in turn: full; a crowded term store: full.
\ Big values are checked against each other with Nat.beq, which the
\ library tests (tests/lib/bignum.fs) check against Python's integers.
\ Test-only; nothing here accepts a theorem.
require ../support/alloc-fail.fs
include ../support/tester.fs
require ../../src/kernel/reduce-nat.fs
require ../../src/core/name-equal.fs
decimal

: must ( flag -- ) 0= abort" reduce-nat test: refused" ;
\ Fresh stores and a symbolic session, in which constants can be made;
\ room for every node this file makes (the default is 64 terms).
: roomy ( -- ) 4096 lf-term-capacity! drop 4096 lf-cref-capacity! drop ;
: fresh ( -- )
  lf-name-reset lf-level-reset lf-term-reset lf-cref-reset roomy lf-ssession-begin must ;
fresh
: nat ( u -- node ) lf-reduce-nat-literal ok? must ;
\ Operation i of whnf.fs's list: Nat.add 0, sub 1, mul 2, pow 3, gcd 4,
\ mod 5, div 6, beq 7, ble 8, land 9, lor 10, xor 11, shiftLeft 12,
\ shiftRight 13.
: op ( a b i -- node outcome ) >r swap nat swap nat r> lf-reduce-nat-binary ;
\ A small result's value, or -1 for a node that is no one-limb literal.
: small ( node -- u )
  dup lf-lit-leaf? 0= if drop -1 exit then
  dup lf-lit-small? if lf-lit-cell else drop -1 then ;
: computes ( a b i -- u outcome ) op swap small swap ;

\ The name of a constant node, and names as Lean's (interned here).
: name-of ( node -- name ) lf-term-first@ lf-cref-slot lf-crec-name @ ;
: named ( prefix c-addr u -- name ) lf-name-str must ;
: nat-name ( -- name ) 0 s" Nat" named ;
: names? ( node part-addr part-u -- flag )
  >r >r name-of nat-name r> r> named lf-name-same? ;
: bool? ( node flag -- flag' )
  >r name-of 0 s" Bool" named r> if s" true" else s" false" then named lf-name-same? ;

\ ---------------------------------------------------------------------------
\ 1, 3. Small operands.
T{ 3 5 0 computes -> 8 outcome-ok }T
T{ 3 5 1 computes -> 0 outcome-ok }T      \ truncated: 3 - 5 = 0
T{ 5 3 1 computes -> 2 outcome-ok }T
T{ 6 7 2 computes -> 42 outcome-ok }T
T{ 2 10 3 computes -> 1024 outcome-ok }T
T{ 0 0 3 computes -> 1 outcome-ok }T      \ 0 ^ 0 = 1
T{ 12 18 4 computes -> 6 outcome-ok }T
T{ 0 0 4 computes -> 0 outcome-ok }T
T{ 17 5 5 computes -> 2 outcome-ok }T
T{ 7 0 5 computes -> 7 outcome-ok }T      \ n % 0 = n
T{ 17 5 6 computes -> 3 outcome-ok }T
T{ 7 0 6 computes -> 0 outcome-ok }T      \ n / 0 = 0
T{ 12 10 9 computes -> 8 outcome-ok }T
T{ 12 10 10 computes -> 14 outcome-ok }T
T{ 12 10 11 computes -> 6 outcome-ok }T
T{ 3 4 12 computes -> 48 outcome-ok }T
T{ 48 4 13 computes -> 3 outcome-ok }T
T{ 48 70 13 computes -> 0 outcome-ok }T
\ Nat.beq and Nat.ble give Bool.true or Bool.false.
T{ 3 3 7 op swap true bool? -> outcome-ok true }T
T{ 3 4 7 op swap false bool? -> outcome-ok true }T
T{ 3 5 8 op swap true bool? -> outcome-ok true }T
T{ 5 5 8 op swap true bool? -> outcome-ok true }T
T{ 5 3 8 op swap false bool? -> outcome-ok true }T
\ succ, the predecessor, the constructor form and the type.
T{ 41 nat lf-reduce-nat-succ swap small -> outcome-ok 42 }T
T{ 42 nat lf-reduce-nat-pred swap small -> outcome-ok 41 }T
T{ 0 nat lf-reduce-nat-constructor swap s" zero" names? -> outcome-ok true }T
: succ-form ( node -- arg flag ) dup lf-term-second@ small swap lf-term-first@ s" succ" names? ;
T{ 5 nat lf-reduce-nat-constructor swap succ-form -> outcome-ok 4 true }T
T{ lf-reduce-nat-type swap name-of nat-name lf-name-same? -> outcome-ok true }T

\ Several limbs: 2^64 = 18446744073709551616 by pow, by shiftLeft and by
\ mul, equal by Nat.beq; its predecessor (a subtraction) and successor
\ against 2^64 - 1 and 2^64 + 1 made otherwise; gcd and div on them.
: big ( -- node ) 2 nat 64 nat 3 lf-reduce-nat-binary ok? must ;
: same? ( a b -- flag ) 7 lf-reduce-nat-binary ok? must true bool? ;
T{ big lf-lit-small? -> false }T
T{ big 1 nat 64 nat 12 lf-reduce-nat-binary ok? must same? -> true }T
T{ big 4294967296 nat dup 2 lf-reduce-nat-binary ok? must same? -> true }T
T{ big lf-reduce-nat-pred ok? must big 1 nat 1 lf-reduce-nat-binary ok? must same? -> true }T
T{ big lf-reduce-nat-succ ok? must big 1 nat 0 lf-reduce-nat-binary ok? must same? -> true }T
T{ big lf-reduce-nat-pred ok? must big same? -> false }T
T{ big 6 nat 4 lf-reduce-nat-binary swap small -> outcome-ok 2 }T
T{ big 4294967296 nat 6 lf-reduce-nat-binary ok? must 4294967296 nat same? -> true }T
T{ big lf-reduce-nat-constructor swap lf-term-first@ s" succ" names? -> outcome-ok true }T

\ ---------------------------------------------------------------------------
\ 5. Lean's refusals and its size limit.
: diag ( -- code ) lf-diag-code@ ;
\ Nat.pow with an exponent of 2^32: rejected whatever the base, 0 too.
T{ lf-diag-clear 2 4294967296 3 op diag -> -1 outcome-rejected lf-diag-nat-count }T
T{ lf-diag-clear 0 4294967296 3 op diag -> -1 outcome-rejected lf-diag-nat-count }T
T{ 1 4294967295 3 computes -> 1 outcome-ok }T
\ A result over 2^30 bits: full. 2 ^ 2^31 has 2^31 + 1 bits.
T{ lf-diag-clear 2 2147483648 3 op diag -> -1 outcome-full lf-diag-nat-size }T
\ Nat.shiftLeft: 0 shifted by anything is 0; 1 by 2^32 refused; 1 by
\ 2^30 has 2^30 + 1 bits: full.
T{ 0 4294967296 12 computes -> 0 outcome-ok }T
T{ lf-diag-clear 1 4294967296 12 op diag -> -1 outcome-rejected lf-diag-nat-count }T
T{ lf-diag-clear 1 1073741824 12 op diag -> -1 outcome-full lf-diag-nat-size }T
\ A count of two limbs (2^64) is refused too (get_count_arg through
\ core/literals.fs's lf-lit-u>, review s3a-decide B5).
T{ lf-diag-clear 2 nat big 3 lf-reduce-nat-binary diag -> -1 outcome-rejected lf-diag-nat-count }T
T{ lf-diag-clear 1 nat big 12 lf-reduce-nat-binary diag -> -1 outcome-rejected lf-diag-nat-count }T

\ 5. Each allocation of an operation refused in turn (alloc-fail.fs), its
\ operands made first: full with no node, never ok, the refusal reached
\ each time. Each run starts from fresh stores, so the names the
\ constants need are interned anew and their allocations refused too.
variable the-op     \ ( a b -- node outcome )
variable the-first  \ the first operand's value
1000 the-first !
: operands ( -- a b ) the-first @ nat 999 nat ;
: run-op ( k -- node outcome ) >r fresh operands r> af-arm the-op @ execute ;
: window ( -- n ) 0 run-op 2drop af-seen@ af-off ;
: refused-full? ( k -- flag ) run-op outcome-full = swap -1 = and af-hit 0<> and af-off ;
: each-full? ( xt -- flag )
  the-op ! window dup 0= if drop false exit then
  true swap 1+ 1 ?do i refused-full? and loop ;
: sub-op ( a b -- node outcome ) 1 lf-reduce-nat-binary ;
: beq-op ( a b -- node outcome ) 7 lf-reduce-nat-binary ;
: pow-op ( a b -- node outcome ) 3 lf-reduce-nat-binary ;
: ctor-op ( a b -- node outcome ) drop lf-reduce-nat-constructor ;
: succ-op ( a b -- node outcome ) drop lf-reduce-nat-succ ;
: type-op ( a b -- node outcome ) 2drop lf-reduce-nat-type ;
T{ ' sub-op each-full? ' beq-op each-full? ' pow-op each-full? -> true true true }T
T{ ' ctor-op each-full? ' succ-op each-full? ' type-op each-full? -> true true true }T
0 the-first !
T{ ' ctor-op each-full? -> true }T   \ Nat.zero
1000 the-first !
\ No free term record left: full.
: crowded ( xt -- outcome )
  >r operands lf-term-capacity lf-term-count @ lf-term-capacity! drop
  -rot r> execute nip swap lf-term-capacity! drop ;
T{ ' sub-op crowded ' beq-op crowded ' ctor-op crowded -> outcome-full outcome-full outcome-full }T

\ ---------------------------------------------------------------------------
\ 2. An operand that is no literal leaf (review s3a-decide M1, plan 9.4.8l
\ AW): the constant Nat and the application Nat.succ 4, first, second or
\ both, for each operation, and Nat.succ of either: invalid and -1 with no
\ diagnostic, the cells under the call kept (111). The test comes before
\ the count is read, so pow and shiftLeft by the application, whose fields
\ read as a literal of two limbs or more, are invalid, not rejected (92).
fresh
: k-nat ( -- node ) lf-reduce-nat-type ok? must ;
: k-app ( -- node ) 1 nat drop 2 nat drop 5 nat lf-reduce-nat-constructor ok? must ;
T{ k-app lf-term-second@ 1 > -> true }T
: kernel-refused? ( a b i -- flag )
  lf-diag-clear lf-reduce-nat-binary outcome-invalid = swap -1 = and diag 0= and ;
: each-refused? ( a b -- flag ) true 14 0 do >r 2dup i kernel-refused? r> and loop nip nip ;
T{ 111 3 nat k-app 3 lf-reduce-nat-binary 111 3 nat k-app 12 lf-reduce-nat-binary
   -> 111 -1 outcome-invalid 111 -1 outcome-invalid }T
T{ 111 k-nat 3 nat 0 lf-reduce-nat-binary 111 k-app k-nat 7 lf-reduce-nat-binary
   -> 111 -1 outcome-invalid 111 -1 outcome-invalid }T
T{ k-nat 3 nat each-refused? 3 nat k-app each-refused? k-app k-nat each-refused? -> true true true }T
T{ 111 k-nat lf-reduce-nat-succ 111 k-app lf-reduce-nat-succ
   -> 111 -1 outcome-invalid 111 -1 outcome-invalid }T
\ The first operand no literal and a count Lean refuses (review B1 of
\ AW): invalid, not rejected (92), as the test comes before the count.
T{ k-nat 4294967296 nat 3 kernel-refused? k-app big 3 kernel-refused?
   k-app 4294967296 nat 12 kernel-refused? -> true true true }T
\ The predecessor and the constructor form (review L1 of AW): is_nat_succ
\ gives a predecessor only of a literal above 0 (type_checker.cpp:1029-
\ 1035) and nat_lit_to_constructor asserts a literal (inductive.cpp:
\ 1359-1366), so the constant Nat, the application Nat.succ 4 and, for
\ the predecessor, the literal 0 are invalid and -1, with no diagnostic,
\ no node made and the cells under the call kept (111). Their callers
\ test first (tests/core/defeq.fs pins lf-dq-pred? and lf-iota-lit).
: unary-refused? ( a xt -- flag )
  lf-diag-clear lf-term-count @ >r execute outcome-invalid = swap -1 = and
  diag 0= and lf-term-count @ r> = and ;
T{ 111 k-nat lf-reduce-nat-pred 111 k-app lf-reduce-nat-pred 111 0 nat lf-reduce-nat-pred
   -> 111 -1 outcome-invalid 111 -1 outcome-invalid 111 -1 outcome-invalid }T
T{ 111 k-nat lf-reduce-nat-constructor 111 k-app lf-reduce-nat-constructor
   -> 111 -1 outcome-invalid 111 -1 outcome-invalid }T
T{ k-nat ' lf-reduce-nat-pred unary-refused? k-app ' lf-reduce-nat-pred unary-refused?
   0 nat ' lf-reduce-nat-pred unary-refused? -> true true true }T
T{ k-nat ' lf-reduce-nat-constructor unary-refused? k-app ' lf-reduce-nat-constructor unary-refused?
   -> true true }T
\ Literals still answer as before: the predecessor of 1 is 0, the
\ constructor form of 1 Nat.succ 0, with the cell under the call kept.
T{ 111 1 nat lf-reduce-nat-pred swap small -> 111 outcome-ok 0 }T
T{ 111 1 nat lf-reduce-nat-constructor swap succ-form -> 111 outcome-ok 0 true }T
bye
