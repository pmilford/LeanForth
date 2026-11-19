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

\ Each record is checked when first needed (MATHLIB_FRONT.md §3): the
\ first query, of Add's root, whose records are right, answers in full
\ although other roots' are wrong; the second, of Mul's root, meets
\ instMulNat (its class Add): refused (115), the record named
\ (lf-inst-refused-decl), and every later query by each word, the
\ refusal kept (not found again: its code stays when the last error is
\ cleared).
: add-nat ( -- t ) l0 1 s" Add" cn nat app ;
: mul-nat ( -- t ) l0 1 s" Mul" cn nat app ;
: decl-named ( c-addr u -- d ) menv-name elab-decl-of drop ;
: class-defaults ( c-addr u -- n outcome ) decl-named lf-default-instances rot drop ;
T{ add-nat lf-inst-candidates rot drop lf-inst-error lf-inst-refusal -> 3 outcome-ok 0 0 }T
T{ mul-nat lf-inst-candidates nip nip lf-inst-error lf-inst-refusal
   lf-inst-refused-decl s" instMulNat" decl-named =
   -> outcome-invalid 115 115 true }T
T{ 0 it it-error ! add-nat lf-inst-unify nip nip lf-inst-error -> outcome-invalid 115 }T
T{ 0 it it-error ! s" Add" class-defaults nip lf-inst-error -> outcome-invalid 115 }T
T{ lf-inst-classes lf-mctx-depth lf-mctx-marks -> outcome-invalid 0 0 }T
\ The other wrong records, each by the first query that needs it, the
\ tables made anew before each (lf-inst-reset, as a new read): a key
\ difference by its root's query (instOfNatNat, 113), a default
\ instance of another class by that class's default instances (Pow's
\ instOfNatNat, 116, then every query refused); the wide record is no
\ refusal (114: unverified). A record filed under a root no query asks
\ is never found, never refused (MATHLIB_FRONT.md §3, "what is lost"):
\ instHDiv under HDiv of four arguments, Nat.instMod under the star root.
: num ( u -- t ) lf-hterm-cell must drop ;
: ofnat-nat ( -- t ) l0 1 s" OfNat" cn nat app 0 num app ;
: refused-by ( c-addr u -- flag ) decl-named lf-inst-refused-decl = ;
T{ lf-inst-reset ofnat-nat lf-inst-candidates nip nip lf-inst-error s" instOfNatNat" refused-by
   -> outcome-invalid 113 true }T
T{ lf-inst-reset s" Pow" class-defaults nip lf-inst-error s" instOfNatNat" refused-by
   -> outcome-invalid 116 true }T
T{ 0 it it-error ! add-nat lf-inst-candidates nip nip lf-inst-error -> outcome-invalid 116 }T
T{ lf-inst-reset s" HAdd" class-defaults -> 1 outcome-ok }T
T{ l0 1 s" Sub" cn nat app lf-inst-candidates nip nip lf-inst-error lf-inst-refusal
   -> outcome-ok 114 0 }T
T{ l0 l0 l0 3 s" HDiv" cn nat app nat app nat app lf-inst-unify nip nip
   l0 1 s" Mod" cn nat app lf-inst-unify nip nip lf-inst-refusal
   -> outcome-ok outcome-ok 0 }T
\ A record the pass of its root never reached is refused by its root key
\ alone (instMulNat under Mul).
T{ s" instMulNat" inst-named it-class-pass lf-inst-error -> outcome-invalid 115 }T
T{ lf-mctx-depth lf-mctx-marks -> 0 0 }T
bye
