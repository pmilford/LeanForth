\ The front end's reduceNat? (plan S3a, commit C2): Lean 4.35.0's
\ Meta.reduceNat? and withNatValue (src/lean/Lean/Meta/WHNF.lean:976-1035)
\ over core/nat-ops.fs's table, which the kernel's reduce_nat shares.
\ whnf.fs runs them as whnfImp does (1068-1074): after whnfCore and before
\ unfoldDefinition?, each argument put in whnf by a part of its own; any
\ argument without a value leaves the term to unfoldDefinition?.
\ Public words:
\   lf-meta-nat-op? ( e -- a b i true | false )  reduceNat?'s match: e is
\       Nat.succ a (i lf-meta-nat-succ, b 0) or one of the fourteen
\       operations applied to a and b (i its index in core/nat-ops.fs's
\       table), its constant at any universe arguments; else false
\   lf-meta-nat-succ ( -- i )  the index the match gives Nat.succ
\   lf-meta-open? ( e -- flag )  e.hasExprMVar || e.hasFVar
\   lf-meta-nat-guard ( a -- a' flag outcome )  withNatValue's test before
\       whnf: none (false) for an argument with a free variable and no
\       metavariable; else a instantiated, none when it then holds a
\       metavariable or a free variable; true and a' when whnf may give a
\       value; the instantiation's failure passed on (-1 false outcome)
\   lf-meta-nat-value? ( w -- lit flag outcome )  withNatValue's match on
\       the whnf w: a literal is itself, Nat.zero (any universe arguments)
\       the literal 0; anything else none (-1 false); no room for the 0
\       literal: full
\   lf-meta-nat-fold ( v1 v2 i -- e outcome )  the operation on the
\       literals: a raw literal, or Bool.true or Bool.false for Nat.beq and
\       Nat.ble (Lean's toExpr); Nat.succ adds 1 to v1 (v2 unused)
\ Not ported yet: Nat.pow with an exponent above 256 (checkExponent,
\ Util/SafeExponentiation.lean:29: Lean logs a warning and unfolds Nat.pow)
\ answers unsupported (plan S3b), never a value.
\ Untrusted: only the kernel's check of a finished term decides.
\ State: none of its own.

require ../lib/lib.fs
require ../core/literals.fs
require ../core/nat-ops.fs
require ../core/terms.fs
require ../core/constant-term-boundary.fs
require ./mvars.fs
require ./instantiate.fs
require ./meta-spine.fs
require ./meta-env.fs
require ./term-eqv.fs

14 constant lf-meta-nat-succ   \ after core/nat-ops.fs's fourteen operations
256 constant rn-threshold      \ exponentiation.threshold's default

\ ---- The match: Nat.succ of one argument, an operation of two.
: rn-succ ( e -- a b i true | false )
  dup lf-meta-head-name 0= if drop false exit then
  lf-nat-succ-name? if lf-term-second@ 0 lf-meta-nat-succ true else drop false then ;
: rn-args ( e -- a b ) dup lf-term-first@ lf-term-second@ swap lf-term-second@ ;
: rn-binary ( e -- a b i true | false )
  dup lf-meta-head-name 0= if drop false exit then
  lf-nat-op dup 0< if 2drop false exit then >r rn-args r> true ;
: lf-meta-nat-op? ( e -- a b i true | false )
  dup lf-meta-args# dup 1 = if drop rn-succ exit then
  2 = if rn-binary else drop false then ;

\ ---- withNatValue: the test before whnf, then the value of the whnf.
: rn-failed ( outcome -- -1 false outcome ) -1 false rot ;
: lf-meta-open? ( e -- flag ) dup lf-meta-mvar-free? 0= swap lf-meta-has-fvar? or ;
: rn-instantiated ( a -- a' flag outcome )
  lf-instantiate-mvars ok-then? if dup lf-meta-open? 0= outcome-ok else rn-failed then ;
: lf-meta-nat-guard ( a -- a' flag outcome )
  dup lf-meta-mvar-free? 0= if rn-instantiated exit then
  dup lf-meta-has-fvar? 0= outcome-ok ;
: rn-zero? ( w -- flag )
  dup lf-term-const? if lf-const-name lf-nat-zero-name? else drop false then ;
: rn-zero ( -- lit flag outcome )
  0 lf-nat-lit ok-then? if true outcome-ok else rn-failed then ;
: lf-meta-nat-value? ( w -- lit flag outcome )
  dup lf-lit-leaf? if true outcome-ok exit then
  rn-zero? if rn-zero else -1 false outcome-ok then ;

\ ---- The operations (reduceBinNatOp, reduceBinNatPred, reducePow).
: rn-over? ( v -- flag ) rn-threshold lf-lit-u> ;
: rn-power? ( v2 i -- v2 i flag ) dup lf-nat-op-pow = if over rn-over? else false then ;
: lf-meta-nat-fold ( v1 v2 i -- e outcome )
  dup lf-meta-nat-succ = if 2drop lf-nat-lit-succ exit then
  rn-power? if drop 2drop outcome-unsupported no-result exit then lf-nat-lit-op ;
