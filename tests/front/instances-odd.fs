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
\ later query by each word, until a new read (here a reset of the data,
\ or the tables' generation changed); the 114 the wide record leaves is
\ no refusal, and the counts and lf-inst-verified? read the data as it is
\ (the second re-check's L1 and L2). Every T{ }T checks the data stack's
\ depth.
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
\ The 114 an unverified record leaves is no refusal: an invalid answer
\ with no code of its own after it is the query's alone (s1-synth second
\ re-check, L1); only 112, 113, 115 and 116 refuse the data.
T{ lfa-e-inst-wide it it-error ! outcome-invalid it-refused lf-inst-classes
   -> outcome-invalid outcome-ok }T
T{ lfa-e-inst-class it-refusal? lfa-e-inst-keys it-refusal? lfa-e-inst-root it-refusal?
   lfa-e-default-class it-refusal? -> true true true true }T
T{ lfa-e-inst-wide it-refusal? lfa-e-not-class it-refusal? 0 it-refusal? 117 it-refusal?
   -> false false false false }T
\ A key difference refuses the data, for every later query.
: class-d ( c-addr u -- d ) menv-name elab-decl-of drop ;
T{ nat s" Mul" c1 lf-inst-candidates nip nip lf-inst-error -> outcome-invalid 113 }T
T{ nat s" Add" c1 lf-inst-candidates nip nip lf-inst-error -> outcome-invalid 113 }T
T{ nat s" Sub" c1 lf-inst-unify nip nip lf-inst-error -> outcome-invalid 113 }T
T{ s" HAdd" class-d lf-default-instances nip nip lf-inst-error -> outcome-invalid 113 }T
T{ lf-inst-classes lf-inst-checked# lf-inst-unverified# -> outcome-invalid 2 1 }T
\ A new read, or a reset of the data, forgets the refusal, the trees and
\ the counts (elab-generation): every word reads the data as it is, the
\ counts and lf-inst-verified? too (s1-synth second re-check, L2).
\ Another read is simulated by the tables' generation (it-data), the data
\ kept: each word first, after it, reads the tables of the data as it is.
: add-nat-i ( -- i ) s" instAddNat" inst-named ;
: other-read ( -- ) -1 it it-data ! ;
: add-query ( -- ) nat s" Add" c1 lf-inst-candidates 2drop drop ;
T{ add-nat-i lf-inst-verified? lf-inst-checked# lf-inst-unverified# -> true 2 1 }T
T{ other-read lf-inst-checked# -> 0 }T
T{ add-query add-nat-i lf-inst-verified? other-read add-nat-i lf-inst-verified? -> true false }T
T{ elab-reset lf-inst-checked# lf-inst-unverified# -> 0 0 }T
T{ lf-inst-classes lf-inst-checked# lf-inst-unverified# -> outcome-ok 0 0 }T
bye
