\ The instance check refuses data that differs from the types (plan
\ FE1e3; FE1E §4; src/front/instances.fs): tests/front/bad-keys.elab.ndjson
\ is tests/front/whnf-slice.elab.ndjson with instOfNatNat's last key a
\ literal 0 where Lean has a star, instMulNat recorded as an instance of
\ Add (filed under Mul's root key), instSubNat's Nat key a star, as a
\ no_index annotation the export drops would leave it, Nat.instMod filed
\ under the star root (Mod's later ranks renumbered), instHDiv filed
\ under HDiv with four arguments (an extra star key: the root's
\ declaration right, its arity wrong; HDiv's left-out value renumbered),
\ and the default instance instOfNatNat recorded under Pow (its header's
\ SHA-256 recomputed, so the reader accepts it). lf-inst-check answers
\ invalid with error 113, 112 and 115, and unsupported (unverified) with
\ error 114; lf-default-check invalid with error 116; the other records
\ still check. A root key that is no constant, or another class's, is refused
\ (error 115) by the first query, which refuses the data, and every later
\ one, through each query word. Every T{ }T checks the data stack's depth.
include ../support/tester.fs
\ Every module first: a context member declared after menv-load would
\ move the context under the loaded slice.
require ../../src/front/instances.fs
require ./menv-slice.fs
:noname ( -- c-addr u ) s" tests/front/bad-keys.elab.ndjson" ; is menv-data
require ./whnf-cases.fs

: inst-named ( c-addr u -- i ) menv-name elab-decl-of drop elab-instance-of drop ;
: default-of? ( d j -- flag ) elab-default@ drop nip = ;
: default-named ( c-addr u -- j )
  menv-name elab-decl-of drop elab-default elab-count 0 ?do
    dup i default-of? if drop i unloop exit then loop drop -1 ;
T{ s" instOfNatNat" inst-named lf-inst-check lf-inst-error -> outcome-invalid 113 }T
T{ s" instMulNat" inst-named lf-inst-check lf-inst-error -> outcome-invalid 112 }T
T{ s" instSubNat" inst-named lf-inst-check lf-inst-error -> outcome-unsupported 114 }T
T{ s" instAddNat" inst-named lf-inst-check -> outcome-ok }T
T{ s" instHDiv" inst-named dup it-root-class? swap lf-inst-check lf-inst-error
   -> true outcome-invalid 115 }T
T{ s" instOfNatNat" default-named lf-default-check lf-inst-error -> outcome-invalid 116 }T
T{ s" instHAdd" default-named lf-default-check -> outcome-ok }T
T{ s" instMulNat" inst-named it-root-class? s" Nat.instMod" inst-named it-root-class?
   s" instAddNat" inst-named it-root-class? -> false false true }T
T{ lf-mctx-depth lf-mctx-marks -> 0 0 }T

\ The first query refuses the data, and so does every later one, by each
\ word, the refusal kept (not found again: its code stays when the last
\ error is cleared).
: add-nat ( -- t ) l0 1 s" Add" cn nat app ;
T{ add-nat lf-inst-candidates nip nip lf-inst-error -> outcome-invalid 115 }T
T{ 0 it it-error ! add-nat lf-inst-unify nip nip lf-inst-error -> outcome-invalid 115 }T
T{ 0 it it-error ! s" Add" menv-name elab-decl-of drop lf-default-instances nip nip
   lf-inst-error -> outcome-invalid 115 }T
T{ lf-inst-classes lf-mctx-depth lf-mctx-marks -> outcome-invalid 0 0 }T
\ The pass stops at the first refusal (instHDiv's arity); a record it did
\ not reach is refused by its root key alone (instMulNat under Mul).
T{ s" instMulNat" inst-named it-class-pass lf-inst-error -> outcome-invalid 115 }T
bye
