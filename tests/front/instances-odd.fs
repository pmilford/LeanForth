\ Data the instance check accepts but treats apart (plan FE1e3;
\ src/front/instances.fs): tests/front/odd-keys.elab.ndjson is
\ tests/front/whnf-slice.elab.ndjson with the left-out instance
\ Lean.Grind.AddCommMonoid.toAdd (rank 0 under Add, Add's star child)
\ erased, and instSubNat's Nat key a star, as a no_index annotation the
\ export drops would leave it; its header's SHA-256 recomputed. An erased
\ value is in Lean's tree, so getUnify gives it, but never a candidate:
\ Add Nat has two, the other left-out one (rank 1) first. instSubNat's
\ keys are wider than its type's: unverified (error 114), kept as such
\ and still a candidate (a search that tries it answers unsupported, S1
\ §9). Its one difference, instMulNat's Nat key recorded as Add, refuses
\ the data at the first query of Mul's root (error 113), and every
\ later query by each word, until a new read (here a reset of the data).
\ Every T{ }T checks the data stack's depth.
include ../support/tester.fs
\ Every module first: a context member declared after menv-load would
\ move the context under the loaded slice.
require ../../src/front/instances.fs
require ./menv-slice.fs
:noname ( -- c-addr u ) s" tests/front/odd-keys.elab.ndjson" ; is menv-data
require ./whnf-cases.fs

: c1 ( t c-addr u -- t' ) 2>r lf-level-mvar-new made 1 2r> cn swap app ;
: left-rank ( v -- rank ) invert elab-left-out@ drop nip ;
: left-erased? ( v -- flag ) invert elab-left-out@ nip nip elab-erased = ;
: named? ( v c-addr u -- flag ) rot elab-instance@ 2drop elab-decl-name -rot menv-name = ;
: inst-named ( c-addr u -- i ) menv-name elab-decl-of drop elab-instance-of drop ;
lf-defeq-elab lf-defeq-stuck or lf-defeq-flags!
T{ nat s" Add" c1 lf-inst-unify rot @ dup left-erased? swap left-rank -> 3 outcome-ok true 0 }T
T{ nat s" Add" c1 lf-inst-candidates rot @ dup left-erased? swap left-rank
   -> 2 outcome-ok false 1 }T
T{ nat s" Add" c1 lf-inst-candidates 2drop cell+ @ s" instAddNat" named? -> true }T
\ The wide instance: unverified, counted, still the last candidate.
: sub-shape ( -- first-left? last-sub? outcome )
  nat s" Sub" c1 lf-inst-candidates >r 2dup drop @ lf-inst-left-out? -rot 1- cells + @
  s" instSubNat" named? r> ;
T{ sub-shape -> true true outcome-ok }T
T{ s" instSubNat" inst-named lf-inst-verified? lf-inst-unverified# lf-inst-error -> false 1 114 }T
T{ nat s" Sub" c1 lf-inst-candidates nip nip lf-inst-unverified# -> outcome-ok 1 }T
\ A key difference refuses the data, for every later query.
: class-d ( c-addr u -- d ) menv-name elab-decl-of drop ;
T{ nat s" Mul" c1 lf-inst-candidates nip nip lf-inst-error -> outcome-invalid 113 }T
T{ nat s" Add" c1 lf-inst-candidates nip nip lf-inst-error -> outcome-invalid 113 }T
T{ nat s" Sub" c1 lf-inst-unify nip nip lf-inst-error -> outcome-invalid 113 }T
T{ s" HAdd" class-d lf-default-instances nip nip lf-inst-error -> outcome-invalid 113 }T
T{ lf-inst-classes lf-inst-checked# lf-inst-unverified# -> outcome-invalid 2 1 }T
\ A new read, or a reset of the data, forgets the refusal, the trees and
\ the counts (elab-generation).
T{ elab-reset lf-inst-classes lf-inst-checked# lf-inst-unverified# -> outcome-ok 0 0 }T
bye
