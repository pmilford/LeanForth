\ Lean 4.35.0's Nat simprocs on literals (simp group 4, pass 2;
\ src/lean/Lean/Meta/Tactic/Simp/BuiltinSimprocs/Nat.lean:28-104), ports
\ for simp/simprocs.fs over front/reduce-nat.fs's operations (core/
\ nat-ops.fs's table: add 0, sub 1, mul 2, pow 3, gcd 4, mod 5, div 6,
\ beq 7, ble 8, land 9, lor 10, xor 11, shiftLeft 12, shiftRight 13).
\ Each operand is read by fromExpr? (getNatValue?, LitValues.lean:37: a
\ raw literal, or OfNat.ofNat T n _ with whnfD T an application of Nat
\ and n a raw literal; an annotation unsupported, mdata not ported);
\ an operand with no value: continue.
\ - reduceUnary (28): Nat.reduceSucc, n + 1; done, no proof (a dsimproc).
\ - reduceBin (33): reduceAdd, reduceMul, reduceSub, reduceDiv,
\   reduceMod, reduceGcd, reduceAnd, reduceXor, reduceOr,
\   reduceShiftLeft, reduceShiftRight: the operation's literal (toExpr:
\   mkNatLit, nat-offset.fs's lf-meta-nat-of-lit); done, no proof.
\ - reducePow (73): the same, an exponent above exponentiation.threshold
\   (256, checkExponent, Util/SafeExponentiation.lean) continue.
\ - reduceBoolPred (46): reduceBEq, reduceBNe: Bool.true or Bool.false.
\ - reduceBinPred (40): reduceLT, reduceGT: evalPropStep
\   (simprocs.fs's lf-simp-eval-prop).
\ Not ported (simprocs.fs's guards): reduceLog2, reducePowMod,
\ reduceDvd and the Diff family. Results beyond core/nat-ops.fs's size
\ limit are full (Lean's own limit is a setting).
\ Untrusted: the kernel checks every proof. State: none of its own.
\ Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../../lib/lib.fs
require ../../../core/terms.fs
require ../../../core/literals.fs
require ../../../core/nat-ops.fs
require ../../reduce-nat.fs
require ../../nat-offset.fs
require ../types.fs
require ../simprocs.fs

\ ---- getNatValue?.
: sn-raw ( a -- lit true | false )
  dup lf-term-tag@ lf-tag-annotation = if lf-unported then
  dup lf-lit-leaf? if true else drop false then ;
: sn-nat-type? ( t -- flag ) lf-whnf-d! lf-meta-head s" Nat" lf-meta-const-named? ;
: sn-of-nat ( a -- lit true | false )
  dup 0 3 lf-meta-nth-arg sn-nat-type?
  if 1 3 lf-meta-nth-arg sn-raw else drop false then ;
: sn-value? ( a -- lit true | false )
  dup 3 s" OfNat.ofNat" lf-meta-app-of? if sn-of-nat else sn-raw then ;
: sn-two ( a b -- v1 v2 true | false )
  swap sn-value? 0= if drop false exit then swap sn-value? if true else drop false then ;

\ ---- The results: a literal as mkNatLit's term, a Bool as it is.
: sn-expr ( node -- e ) dup lf-lit-leaf? if lf-meta-nat-of-lit lf-must then ;
: sn-done ( node -- e h step ) sn-expr lf-simp-none lf-simp-done ;
: sn-folded ( e v1 v2 i -- e' h step ) lf-meta-nat-fold lf-must nip sn-done ;
: sn-bin ( e i -- e' h step )
  over lf-meta-args2 sn-two if rot sn-folded else drop lf-simp-pass then ;
: sn-small? ( lit -- flag ) rn-threshold lf-lit-u> 0= ;   \ reduce-nat.fs's threshold
: sn-pow ( e i -- e' h step )
  drop dup lf-meta-args2 sn-two 0= if lf-simp-pass exit then
  dup sn-small? if lf-nat-op-pow sn-folded else 2drop lf-simp-pass then ;
: sn-succ ( e x -- e' h step )
  drop dup lf-term-second@ sn-value?
  if nip lf-nat-lit-succ lf-must sn-done else lf-simp-pass then ;
: sn-not ( b -- b' ) s" Bool.false" lf-meta-const-named? sp-bool ;
: sn-bne ( e i -- e' h step ) sn-bin dup lf-simp-done = if 2drop sn-not sn-done then ;
\ n < m is m <= n false; n > m is n <= m false.
: sn-ble? ( v1 v2 -- flag )
  8 lf-meta-nat-fold lf-must s" Bool.true" lf-meta-const-named? ;
: sn-lt ( e x -- e' h step )
  drop dup lf-meta-args2 sn-two
  if swap sn-ble? 0= lf-simp-eval-prop else lf-simp-pass then ;
: sn-gt ( e x -- e' h step )
  drop dup lf-meta-args2 sn-two
  if sn-ble? 0= lf-simp-eval-prop else lf-simp-pass then ;

' sn-succ 0 1 false true lf-simproc: Nat.succ Nat.reduceSucc
' sn-bin 0 6 false true lf-simproc: HAdd.hAdd Nat.reduceAdd
' sn-bin 2 6 false true lf-simproc: HMul.hMul Nat.reduceMul
' sn-bin 1 6 false true lf-simproc: HSub.hSub Nat.reduceSub
' sn-bin 6 6 false true lf-simproc: HDiv.hDiv Nat.reduceDiv
' sn-bin 5 6 false true lf-simproc: HMod.hMod Nat.reduceMod
' sn-pow 3 6 false true lf-simproc: HPow.hPow Nat.reducePow
' sn-bin 4 2 false true lf-simproc: Nat.gcd Nat.reduceGcd
' sn-bin 9 6 false true lf-simproc: HAnd.hAnd Nat.reduceAnd
' sn-bin 11 6 false true lf-simproc: HXor.hXor Nat.reduceXor
' sn-bin 10 6 false true lf-simproc: HOr.hOr Nat.reduceOr
' sn-bin 12 6 false true lf-simproc: HShiftLeft.hShiftLeft Nat.reduceShiftLeft
' sn-bin 13 6 false true lf-simproc: HShiftRight.hShiftRight Nat.reduceShiftRight
' sn-lt 0 4 false false lf-simproc: LT.lt Nat.reduceLT
' sn-gt 0 4 false false lf-simproc: GT.gt Nat.reduceGT
' sn-bin 7 4 false true lf-simproc: BEq.beq Nat.reduceBEq
' sn-bne 7 4 false true lf-simproc: bne Nat.reduceBNe

base !   \ the BASE this file was loaded with
