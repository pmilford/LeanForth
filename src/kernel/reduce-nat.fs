\ Lean's computations on natural-number literals (plan task 5.2.3; ADR
\ 0014 K7, rules L1-L3; type_checker.cpp at v4.35.0): the operations of
\ reduce_nat (672-703) on literal leaves (core/literals.fs), computed by
\ core/nat-ops.fs (shared with the front end's reduceNat? since plan S3a),
\ with the kernel's refusals; nat_lit_to_constructor for iota
\ (inductive.h), the predecessor of is_def_eq_offset, and the constants
\ they name (Nat, Nat.zero, Nat.succ, Bool.true, Bool.false: no universe
\ arguments, their names interned in this context). whnf.fs decides when
\ reduce_nat applies (the head's name, its arguments' whnf literals or
\ Nat.zero) and calls these words; defeq.fs and iota.fs too.
\
\ Lean's fixed refusals are its verdict: get_count_arg (305-313) refuses
\ Nat.pow with an exponent of 2^32 or more, whatever the base, and
\ Nat.shiftLeft of a nonzero number by 2^32 or more: rejected
\ (diagnostic 92), as Lean's kernel exception rejects the declaration.
\ Lean's size limit, 2^30 bits by default (LEAN_NAT_MAX_SIZE, a
\ setting), and its estimates against it are a resource here: a result
\ over 2^30 bits, an estimate over it for pow and shiftLeft, or no heap
\ for the scratch arena is full (diagnostic 93, core/nat-ops.fs), never
\ a verdict. Every computation runs in a scratch arena on the heap, sized
\ from its operands, and freed before the word returns.
\ An operand that is no literal, and the predecessor of the literal 0,
\ answer invalid with -1 and no diagnostic (owner, 2026-11-20, plan 9.4.8l
\ AW): no caller passes one, as Lean's callers test is_nat_lit_ext first.
\ Untrusted [kernel] until the review gate of AGENTS.md.
\ State: none of its own.

require ../lib/lib.fs
require ../core/literals.fs   \ first: it loads lib/bignum.fs (see there)
require ../core/nat-ops.fs
require ../core/diagnostics.fs
require ../core/generation-handles.fs
require ../core/terms.fs

: lf-rn-site ( -- site ) c" reduce-nat lf-reduce-nat" ;
: lf-rn-refuse ( -- -1 outcome )
  0 0 lf-rn-site lf-diag-nat-count lf-diag-note -1 outcome-rejected ;

\ A literal's type (infer_lit, 315-321), Nat.zero and Nat.succ.
: lf-reduce-nat-type ( -- node outcome ) 0 s" Nat" lf-nat-named ;
: lf-rn-zero ( -- node outcome ) s" zero" s" Nat" lf-nat-in ;
: lf-rn-succ ( -- node outcome ) s" succ" s" Nat" lf-nat-in ;

\ get_count_arg: a count below 2^32, at most lf-rn-count-most (2^32 - 1, or
\ the largest cell where cells are 32 bits; written without a literal
\ wider than 32 bits).
-1 limb-bits 32 - rshift constant lf-rn-count-most
: lf-rn-count? ( lit -- flag ) lf-rn-count-most lf-lit-u> 0= ;
: lf-rn-counted ( a b i -- node outcome )
  over lf-rn-count? if lf-nat-lit-op else drop 2drop lf-rn-refuse then ;
\ Nat.pow (reduce_pow, 633-648) is lf-rn-counted: the exponent's count
\ first; Nat.shiftLeft (650-660): 0 at once, else the shift's count.
: lf-rn-shl ( a b -- node outcome )
  over lf-term-second@ 0= if lf-nat-op-shl lf-nat-lit-op exit then
  lf-nat-op-shl lf-rn-counted ;

\ Lean's policies on literals: pow's count, shiftLeft's 0 and count, else the table.
: lf-rn-binary ( a b i -- node outcome )
  dup lf-nat-op-pow = if lf-rn-counted exit then
  dup lf-nat-op-shl = if drop lf-rn-shl exit then lf-nat-lit-op ;

\ The public words. Binary operation i of core/nat-ops.fs's list on
\ literals a and b, an operand that is no literal invalid before any
\ count is read (as is_nat_lit_ext comes before get_count_arg; whnf.fs
\ passes only literals); Nat.succ of a, invalid for no literal; a literal
\ for Nat.zero (is_nat_lit_ext).
: lf-reduce-nat-binary ( a b i -- node outcome ) ['] lf-rn-binary lf-nat-lits-by ;
: lf-reduce-nat-literal ( u -- node outcome ) lf-nat-lit ;
: lf-reduce-nat-succ ( a -- node outcome ) lf-nat-lit-succ ;
\ The predecessor of a literal above 0 (is_def_eq_offset's is_nat_succ,
\ type_checker.cpp:1029-1035, computes one only for a literal that is not
\ 0); anything else, the literal 0 included, is invalid, never computed
\ on (review L1 of plan 9.4.8l AW; defeq.fs's lf-dq-pred? tests first).
: lf-rn-pred ( a -- node outcome )
  dup lf-lit-small? if lf-lit-cell 1- lf-reduce-nat-literal exit then
  1 lf-reduce-nat-literal ok-then? 0= if nip no-result exit then 1 lf-nat-lit-op ;
: lf-rn-positive? ( a -- flag ) dup lf-lit-leaf? swap lf-term-second@ 0<> and ;
: lf-reduce-nat-pred ( a -- node outcome )
  dup lf-rn-positive? flag>outcome ['] lf-rn-pred ok-apply ;
\ nat_lit_to_constructor (inductive.cpp:1359-1366, which asserts a
\ literal): 0 as Nat.zero, n + 1 as Nat.succ n; anything but a literal
\ invalid, never computed on (iota.fs's lf-iota-lit tests first).
: lf-rn-succ-of ( pred -- node outcome )
  lf-rn-succ ok-then? 0= if nip no-result exit then
  lf-term-handle rot lf-term-handle lf-hterm-app lf-made-term ;
: lf-rn-constructor ( a -- node outcome )
  dup lf-term-second@ 0= if drop lf-rn-zero exit then
  lf-reduce-nat-pred ['] lf-rn-succ-of ok-apply ;
: lf-reduce-nat-constructor ( a -- node outcome ) ['] lf-rn-constructor lf-nat-lit-by ;
