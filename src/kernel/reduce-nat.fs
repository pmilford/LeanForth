\ Lean's computations on natural-number literals (plan task 5.2.3; ADR
\ 0014 K7, rules L1-L3; type_checker.cpp at v4.35.0): the operations of
\ reduce_nat (672-703) on literal leaves (core/literals.fs) with
\ lib/bignum.fs, nat_lit_to_constructor for iota (inductive.h), the
\ predecessor of is_def_eq_offset, and the constants they name (Nat,
\ Nat.zero, Nat.succ, Bool.true, Bool.false: no universe arguments,
\ their names interned in this context). whnf.fs decides when reduce_nat
\ applies (the head's name, its arguments' whnf literals or Nat.zero) and
\ calls these words; defeq.fs and iota.fs too.
\
\ Lean's fixed refusals are its verdict: get_count_arg (305-313) refuses
\ Nat.pow with an exponent of 2^32 or more, whatever the base, and
\ Nat.shiftLeft of a nonzero number by 2^32 or more: rejected
\ (diagnostic 92), as Lean's kernel exception rejects the declaration.
\ Lean's size limit, 2^30 bits by default (LEAN_NAT_MAX_SIZE, a
\ setting), and its estimates against it are a resource here: a result
\ over 2^30 bits, an estimate over it for pow and shiftLeft, or no heap
\ for the scratch arena is full (diagnostic 93), never a verdict.
\ Every computation runs in a scratch arena on the heap, sized from its
\ operands (lf-lit-arena), and freed before the word returns.
\ Untrusted [kernel] until the review gate of AGENTS.md.
\ State: none of its own.

require ../lib/lib.fs
require ../core/literals.fs   \ first: it loads lib/bignum.fs (see there)
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/diagnostics.fs
require ../core/generation-handles.fs
require ../core/literals.fs
require ../core/names.fs
require ../core/terms.fs

: lf-rn-site ( -- site ) c" reduce-nat lf-reduce-nat" ;
: lf-rn-refuse ( -- -1 outcome )
  0 0 lf-rn-site lf-diag-nat-count lf-diag-note -1 outcome-rejected ;
: lf-rn-too-big ( -- -1 outcome )
  0 0 lf-rn-site lf-diag-nat-size lf-diag-note -1 outcome-full ;
: lf-rn-node ( index identity true | false -- node outcome )
  if drop outcome-ok else -1 outcome-full then ;
: lf-rn-handle ( node -- node identity ) dup lf-term-identity 0= if 0 then ;

\ Constants without universe arguments, by name.
: lf-rn-name ( prefix c-addr u -- id outcome ) lf-name-str room-result ;
: lf-rn-const ( id -- node outcome )
  lf-name-generation @ 0 0 lf-cref-new 0= if -1 outcome-full exit then lf-cterm-new lf-rn-node ;
: lf-rn-named ( prefix c-addr u -- node outcome )
  lf-rn-name ok-then? if lf-rn-const else no-result then ;
: lf-rn-in ( part-addr part-u prefix-addr prefix-u -- node outcome )
  0 -rot lf-rn-name ok-then? 0= if >r 2drop r> no-result exit then -rot lf-rn-named ;
\ A literal's type (infer_lit, 315-321), Nat.zero, Nat.succ, and Nat.beq's
\ and Nat.ble's answers.
: lf-reduce-nat-type ( -- node outcome ) 0 s" Nat" lf-rn-named ;
: lf-rn-zero ( -- node outcome ) s" zero" s" Nat" lf-rn-in ;
: lf-rn-succ ( -- node outcome ) s" succ" s" Nat" lf-rn-in ;
: lf-rn-bool ( flag -- node outcome ) if s" true" else s" false" then s" Bool" lf-rn-in ;

\ Operations in a scratch arena: the literals a and b as numbers, op
\ ( x y arena -- z outcome ) on them, the result made a new literal (or,
\ for Nat.beq and Nat.ble, a Bool constant) before the arena is freed.
: lf-rn-operands ( a b arena -- x y outcome )
  tuck lf-lit>big ok-then? 0= if >r 2drop -1 -1 r> exit then
  -rot lf-lit>big ok-then? 0= if >r drop -1 -1 r> exit then swap outcome-ok ;
: lf-rn-apply ( a b op arena -- z outcome )
  swap >r dup >r lf-rn-operands ok-then? 0= if r> r> 2drop >r 2drop -1 r> exit then
  r> r> execute ;
: lf-rn-literal ( z outcome -- node outcome )
  ok-then? 0= if outcome-full = if lf-rn-too-big else -1 outcome-invalid then exit then
  lf-hterm-big lf-rn-node ;
: lf-rn-truth ( flag outcome -- node outcome ) ok-then? if lf-rn-bool else no-result then ;
: lf-rn-in-arena ( a b op cells make -- node outcome )
  >r lf-lit-arena ok-then? 0= if r> drop drop 2drop drop lf-rn-too-big exit then
  dup >r lf-rn-apply r> r> swap >r execute r> lf-lit-arena-free ;
\ Cells for an operation of the sizes of a and b.
: lf-rn-cells ( a b -- a b cells ) over lf-term-second@ over lf-term-second@ + 8 * 64 + ;
: lf-rn-std ( a b op -- node outcome ) >r lf-rn-cells r> swap ['] lf-rn-literal lf-rn-in-arena ;
: lf-rn-test ( a b op -- node outcome ) >r lf-rn-cells r> swap ['] lf-rn-truth lf-rn-in-arena ;
: lf-rn-eq ( x y arena -- flag outcome ) drop big= outcome-ok ;
: lf-rn-le ( x y arena -- flag outcome ) drop big<= outcome-ok ;

\ get_count_arg: a count below 2^32. The bits of a literal, and
\ whether it is 0 or 1.
: lf-rn-count? ( lit -- flag )
  dup lf-lit-small? 0= if drop false exit then
  lf-lit-cell limb-bits 32 > if 32 rshift 0= else drop true then ;
: lf-rn-bits ( lit -- n )
  lf-lit-vector dup 0= if nip exit then 1- tuck cells + @ bit-length swap limb-bits * + ;
: lf-rn-unit? ( lit -- flag ) dup lf-lit-small? if lf-lit-cell 2 u< else drop false then ;
\ Bits estimated for a result, an estimate over the limit being full.
: lf-rn-over? ( bits -- flag ) big-lean-bits u> ;
\ Scratch for a result of at most bits (within the limit): 6 cells per
\ result limb, the operands' limbs twice and 4096 cells. big-pow's peak
\ is its last squaring of x, of m limbs, about half the result's: x, the
\ product (2m), the short factor's copy (2m) and Karatsuba's frames
\ (about 4m, and a few cells per level), so about 9m, 4.5 cells per
\ result limb; shiftLeft needs the result and the operands (review rvCONV
\ M1: 4 cells per limb left a 12,800-bit power full).
: lf-rn-operand-cells ( a b -- a b cells )
  over lf-term-second@ over lf-term-second@ + 2* ;
: lf-rn-sized ( a b op bits -- node outcome )
  limb-bits / 1+ 6 * >r >r lf-rn-operand-cells r> swap r> + 4096 +
  ['] lf-rn-literal lf-rn-in-arena ;
\ Nat.pow (reduce_pow, 633-648): the exponent's count first, then a base
\ of 0 or 1 at once, else the result's bits (at most bits(a) * e).
: lf-rn-pow-bits ( a b -- a b bits ) over lf-rn-bits over lf-lit-cell um* if drop -1 then ;
: lf-rn-pow ( a b -- node outcome )
  dup lf-rn-count? 0= if 2drop lf-rn-refuse exit then
  over lf-rn-unit? if ['] big-pow lf-rn-std exit then
  lf-rn-pow-bits dup lf-rn-over? if drop 2drop lf-rn-too-big exit then
  ['] big-pow swap lf-rn-sized ;
\ Nat.shiftLeft (650-660): 0 at once; else the shift's count, then the
\ result's bits, bits(a) + b.
: lf-rn-shl ( a b -- node outcome )
  over lf-term-second@ 0= if ['] big-lshift lf-rn-std exit then
  dup lf-rn-count? 0= if 2drop lf-rn-refuse exit then
  over lf-rn-bits over lf-lit-cell + dup lf-rn-over? if drop 2drop lf-rn-too-big exit then
  ['] big-lshift swap lf-rn-sized ;

: lf-rn-add ( a b -- node outcome ) ['] big+ lf-rn-std ;
: lf-rn-sub ( a b -- node outcome ) ['] big- lf-rn-std ;
: lf-rn-mul ( a b -- node outcome ) ['] big* lf-rn-std ;
: lf-rn-gcd ( a b -- node outcome ) ['] big-gcd lf-rn-std ;
: lf-rn-mod ( a b -- node outcome ) ['] big-mod lf-rn-std ;
: lf-rn-div ( a b -- node outcome ) ['] big/ lf-rn-std ;
: lf-rn-beq ( a b -- node outcome ) ['] lf-rn-eq lf-rn-test ;
: lf-rn-ble ( a b -- node outcome ) ['] lf-rn-le lf-rn-test ;
: lf-rn-land ( a b -- node outcome ) ['] big-and lf-rn-std ;
: lf-rn-lor ( a b -- node outcome ) ['] big-or lf-rn-std ;
: lf-rn-xor ( a b -- node outcome ) ['] big-xor lf-rn-std ;
: lf-rn-shr ( a b -- node outcome ) ['] big-rshift lf-rn-std ;
\ In the order of whnf.fs's names (lf-whnf-nat-binary).
create lf-rn-binaries
  ' lf-rn-add , ' lf-rn-sub , ' lf-rn-mul , ' lf-rn-pow , ' lf-rn-gcd , ' lf-rn-mod ,
  ' lf-rn-div , ' lf-rn-beq , ' lf-rn-ble , ' lf-rn-land , ' lf-rn-lor , ' lf-rn-xor ,
  ' lf-rn-shl , ' lf-rn-shr ,

\ The public words. Binary operation i of whnf.fs's list on literals a
\ and b; Nat.succ of a; a literal for Nat.zero (is_nat_lit_ext).
: lf-reduce-nat-binary ( a b i -- node outcome ) cells lf-rn-binaries + @ execute ;
: lf-reduce-nat-literal ( u -- node outcome ) lf-hterm-cell lf-rn-node ;
: lf-reduce-nat-succ ( a -- node outcome )
  1 lf-reduce-nat-literal ok-then? 0= if nip no-result exit then lf-rn-add ;
\ The predecessor of a literal above 0 (is_def_eq_offset's is_nat_succ).
: lf-reduce-nat-pred ( a -- node outcome )
  dup lf-lit-small? if lf-lit-cell 1- lf-reduce-nat-literal exit then
  1 lf-reduce-nat-literal ok-then? 0= if nip no-result exit then lf-rn-sub ;
\ nat_lit_to_constructor: 0 as Nat.zero, n + 1 as Nat.succ n.
: lf-rn-succ-of ( pred -- node outcome )
  lf-rn-succ ok-then? 0= if nip no-result exit then
  lf-rn-handle rot lf-rn-handle lf-hterm-app lf-rn-node ;
: lf-reduce-nat-constructor ( a -- node outcome )
  dup lf-term-second@ 0= if drop lf-rn-zero exit then
  lf-reduce-nat-pred ok-then? if lf-rn-succ-of else no-result then ;
