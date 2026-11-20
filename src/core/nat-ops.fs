\ Lean's operations on natural-number literals, shared by the kernel's
\ reduce_nat (kernel/reduce-nat.fs and kernel/whnf.fs; type_checker.cpp
\ at v4.35.0, 672-703) and the front end's reduceNat? (front/reduce-nat.fs;
\ Meta/WHNF.lean:1010-1035), which name the same fourteen binary
\ operations and compute them alike (plan S3a, commit C0: moved here from
\ those two kernel files, the kernel's behaviour unchanged).
\ Public words:
\   lf-nat-name? ( name -- flag )  whether a name is Nat.x, Nat a root name
\   lf-nat-zero-name? ( name -- flag )  whether it is Nat.zero
\   lf-nat-op ( name -- i | -1 )  the index of the operation a name names:
\       Nat.add 0, sub 1, mul 2, pow 3, gcd 4, mod 5, div 6, beq 7, ble 8,
\       land 9, lor 10, xor 11, shiftLeft 12, shiftRight 13; -1 for any
\       other name
\   lf-nat-op-pow lf-nat-op-shl ( -- i )  the indices of Nat.pow and
\       Nat.shiftLeft, whose callers' policies differ
\   lf-nat-lit-op ( a b i -- node outcome )  operation i on the literal
\       leaves a and b (core/literals.fs) with lib/bignum.fs: a new
\       literal, or the constant Bool.true or Bool.false for Nat.beq and
\       Nat.ble; invalid when a or b is no literal
\   lf-nat-lit-succ ( a -- node outcome )  the literal a + 1 (Nat.succ)
\   lf-nat-lit ( u -- node outcome )  the literal of a cell's value
\   lf-nat-lit-bool ( flag -- node outcome )  Bool.true or Bool.false
\   lf-nat-named ( prefix c-addr u -- node outcome )  the constant
\       prefix.c-addr u (prefix a name ID, 0 for the root) with no
\       universe arguments, its name interned in this context
\   lf-nat-in ( part-addr part-u prefix-addr prefix-u -- node outcome )
\       the constant prefix.part, prefix a root name (Nat.zero, Bool.true)
\ Policies stay with the callers: the kernel's refusal of a count of 2^32
\ or more (get_count_arg, 305-313), Meta's exponent threshold (256,
\ Util/SafeExponentiation.lean). Here only resources: Lean's size limit,
\ 2^30 bits by default (LEAN_NAT_MAX_SIZE, a setting), and the estimates
\ against it are a resource: a result over 2^30 bits, an estimate over it
\ for pow (a base of 2 or more) and shiftLeft (a nonzero number), or no
\ heap for the scratch arena is full (diagnostic 93), never a verdict.
\ Every computation runs in a scratch arena on the heap, sized from its
\ operands (lf-lit-arena), and freed before the word returns.
\ Untrusted [kernel] until the review gate of AGENTS.md.
\ State: none of its own; the operation and name tables are constant data.

require ../lib/lib.fs
require ./literals.fs   \ first: it loads lib/bignum.fs (see there)
require ../lib/texts.fs
require ./constant-references.fs
require ./constant-term-boundary.fs
require ./diagnostics.fs
require ./generation-handles.fs
require ./names.fs
require ./terms.fs

: nop-site ( -- site ) c" nat-ops lf-nat-lit-op" ;
: nop-too-big ( -- -1 outcome )
  0 0 nop-site lf-diag-nat-size lf-diag-note -1 outcome-full ;

\ Constants without universe arguments, by name.
: nop-name ( prefix c-addr u -- id outcome ) lf-name-str room-result ;
: nop-const ( id -- node outcome )
  lf-name-generation @ 0 0 lf-cref-new 0= if -1 outcome-full exit then
  lf-cterm-new lf-made-term ;
: lf-nat-named ( prefix c-addr u -- node outcome )
  nop-name ['] nop-const ok-apply ;
: lf-nat-in ( part-addr part-u prefix-addr prefix-u -- node outcome )
  0 -rot nop-name ok-then? 0= if nip nip no-result exit then -rot lf-nat-named ;
: lf-nat-lit-bool ( flag -- node outcome )
  if s" true" else s" false" then s" Bool" lf-nat-in ;
: lf-nat-lit ( u -- node outcome ) lf-hterm-cell lf-made-term ;

\ Operations in a scratch arena: the literals a and b as numbers, op
\ ( x y arena -- z outcome ) on them, the result made a new literal (or,
\ for Nat.beq and Nat.ble, a Bool constant) before the arena is freed.
: nop-operands ( a b arena -- x y outcome )
  tuck lf-lit>big ok-then? 0= if >r 2drop -1 -1 r> exit then
  -rot lf-lit>big ok-then? 0= if >r drop -1 -1 r> exit then swap outcome-ok ;
\ (The operands' failure, -1 and the outcome after ok-then?, is the answer;
\ before the move it dropped one cell of its caller's too many, never run:
\ the callers' arenas always hold the operands.)
: nop-apply ( a b op arena -- z outcome )
  swap >r dup >r nop-operands ok-then? 0= if 2r> 2drop exit then 2r> swap execute ;
: nop-literal ( z outcome -- node outcome )
  ok-then? 0= if outcome-full = if nop-too-big else -1 outcome-invalid then exit then
  lf-hterm-big lf-made-term ;
: nop-truth ( flag outcome -- node outcome )
  ['] lf-nat-lit-bool ok-apply ;
: nop-in-arena ( a b op cells make -- node outcome )
  >r lf-lit-arena ok-then? 0= if r> 2drop 2drop drop nop-too-big exit then
  dup >r nop-apply 2r> >r execute r> lf-lit-arena-free ;
\ Cells for an operation of the sizes of a and b.
: nop-cells ( a b -- a b cells ) over lf-term-second@ over lf-term-second@ + 8 * 64 + ;
\ An operation in an arena of cells for a and b, its result made by make:
\ a number (nop-literal) or a Boolean (nop-truth).
: nop-by ( a b op make -- node outcome ) 2>r nop-cells 2r> rot swap nop-in-arena ;
: nop-std ( a b op -- node outcome ) ['] nop-literal nop-by ;
: nop-test ( a b op -- node outcome ) ['] nop-truth nop-by ;
: nop-eq ( x y arena -- flag outcome ) drop big= outcome-ok ;
: nop-le ( x y arena -- flag outcome ) drop big<= outcome-ok ;

\ The bits of a literal, and whether it is 0 or 1.
: nop-bits ( lit -- n )
  lf-lit-vector dup 0= if nip exit then 1- tuck cells + @ bit-length swap limb-bits * + ;
: nop-unit? ( lit -- flag ) dup lf-lit-small? if lf-lit-cell 2 u< else drop false then ;
\ Bits estimated for a result, an estimate over the limit being full; a
\ count of more than one cell or past the limit is over it at once.
: nop-over? ( bits -- flag ) big-lean-bits u> ;
: nop-count-over? ( lit -- flag )
  dup lf-lit-small? if lf-lit-cell nop-over? else drop true then ;
\ Scratch for a result of at most bits (within the limit): 6 cells per
\ result limb, the operands' limbs twice and 4096 cells. big-pow's peak
\ is its last squaring of x, of m limbs, about half the result's: x, the
\ product (2m), the short factor's copy (2m) and Karatsuba's frames
\ (about 4m, and a few cells per level), so about 9m, 4.5 cells per
\ result limb; shiftLeft needs the result and the operands (review rvCONV
\ M1: 4 cells per limb left a 12,800-bit power full).
: nop-operand-cells ( a b -- a b cells )
  over lf-term-second@ over lf-term-second@ + 2* ;
: nop-sized ( a b op bits -- node outcome )
  limb-bits / 1+ 6 * >r >r nop-operand-cells r> swap r> + 4096 +
  ['] nop-literal nop-in-arena ;
\ Nat.pow (reduce_pow, 633-648): a base of 0 or 1 at once, else the
\ result's bits (at most bits(a) * e), an exponent of more than a cell
\ over the limit.
: nop-pow-bits ( a b -- a b bits )
  over nop-bits over lf-lit-cell um* if drop -1 then ;
: nop-pow ( a b -- node outcome )
  over nop-unit? if ['] big-pow nop-std exit then
  dup lf-lit-small? 0= if 2drop nop-too-big exit then
  nop-pow-bits dup nop-over? if drop 2drop nop-too-big exit then
  ['] big-pow swap nop-sized ;
\ Nat.shiftLeft (650-660): 0 at once; else the result's bits, bits(a) + b.
: nop-shl ( a b -- node outcome )
  over lf-term-second@ 0= if ['] big-lshift nop-std exit then
  dup nop-count-over? if 2drop nop-too-big exit then
  over nop-bits over lf-lit-cell + dup nop-over? if drop 2drop nop-too-big exit then
  ['] big-lshift swap nop-sized ;

: nop-add ( a b -- node outcome ) ['] big+ nop-std ;
: nop-sub ( a b -- node outcome ) ['] big- nop-std ;
: nop-mul ( a b -- node outcome ) ['] big* nop-std ;
: nop-gcd ( a b -- node outcome ) ['] big-gcd nop-std ;
: nop-mod ( a b -- node outcome ) ['] big-mod nop-std ;
: nop-div ( a b -- node outcome ) ['] big/ nop-std ;
: nop-beq ( a b -- node outcome ) ['] nop-eq nop-test ;
: nop-ble ( a b -- node outcome ) ['] nop-le nop-test ;
: nop-land ( a b -- node outcome ) ['] big-and nop-std ;
: nop-lor ( a b -- node outcome ) ['] big-or nop-std ;
: nop-xor ( a b -- node outcome ) ['] big-xor nop-std ;
: nop-shr ( a b -- node outcome ) ['] big-rshift nop-std ;
\ In the order of the name table below.
3 constant lf-nat-op-pow   12 constant lf-nat-op-shl
align here
  ' nop-add , ' nop-sub , ' nop-mul , ' nop-pow , ' nop-gcd , ' nop-mod ,
  ' nop-div , ' nop-beq , ' nop-ble , ' nop-land , ' nop-lor , ' nop-xor ,
  ' nop-shl , ' nop-shr ,
constant nop-ops
: lf-nat-lit-op ( a b i -- node outcome ) cells nop-ops + @ execute ;
: lf-nat-lit-succ ( a -- node outcome )
  1 lf-nat-lit ['] nop-add ok-apply2 ;

\ The names (lib/texts.fs), compared by their components (Lean's name
\ equality), from the last.
texts-begin texts+ add sub mul pow gcd mod div beq ble land lor xor shiftLeft shiftRight
texts-end constant nop-names
: lf-nat-name? ( name -- flag ) lf-name-prefix@ s" Nat" lf-name-top? ;
: lf-nat-zero-name? ( name -- flag )
  dup s" zero" lf-name-str-is? if lf-nat-name? else drop false then ;
\ The index of a name's last component in the table (lib/texts.fs), or -1.
: nop-index ( name -- i | -1 ) ['] lf-name-str-is? nop-names texts-index ;
: lf-nat-op ( name -- i | -1 ) dup lf-nat-name? 0= if drop -1 exit then nop-index ;
