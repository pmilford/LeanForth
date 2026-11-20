\ Unit tests of S2's kabstract and Meta.check (plan S2, branch
\ s2-tactics; src/front/kabstract.fs, src/front/meta-check.fs) over the
\ Init slice, with the variables of tests/front/whnf-cases.fs; run by
\ tests/front/check_s2.py. kabstract: a free-variable pattern abstracted
\ everywhere, under binders too (bound variable k + 1 under k binders); a
\ pattern under a binder matched only where no bound variable is loose
\ (Lean's hasLooseBVars test: fun x => Nat.succ x has no Nat.succ ?n);
\ no occurrence; a let answers unsupported (Lean's order of a let's parts
\ is not ported); no term: invalid. Meta.check: a type correct
\ application, pi and lambda; an argument of the wrong type (invalid,
\ the application kept); a pi whose body is no type; a constant with the
\ wrong number of universe arguments; a let and a smart-unfolding marker
\ (unsupported, in kabstract too); the budget
\ spent (exhausted) and a refused allocation (full), each call after
\ them answering as before; a 10,000-deep target for both walks (class
\ 5). Every T{ }T checks the data stack's depth.
include ../support/tester.fs
include ../support/heap-watch.fs
require ./whnf-cases.fs
require ../../src/front/kabstract.fs
require ../../src/front/meta-check.fs

: eqv ( a b -- flag ) lf-meta-eqv drop ;
: abs= ( e p expected -- flag flag' outcome ) >r lf-meta-kabstract rot r> eqv -rot ;
succ fk app constant sk
nat sk lam constant k-under

\ ---- kabstract.
T{ sk fk succ 0 bv app abs= -> true true outcome-ok }T
T{ k-under sk nat 1 bv lam abs= -> true true outcome-ok }T
T{ k-under fk nat succ 1 bv app lam abs= -> true true outcome-ok }T
T{ nat succ 0 bv app lam succ ?n app lf-meta-kabstract rot drop -> false outcome-ok }T
T{ ?n lf-mvar-value -> false }T
T{ fk sk lf-meta-kabstract rot fk = -> false outcome-ok true }T
T{ nat nat 0 bv 0 bv let lam succ ?n app lf-meta-kabstract
   -> -1 false outcome-unsupported }T
T{ -1 sk lf-meta-kabstract -> -1 false outcome-invalid }T
T{ sk fk succ 0 bv app abs= -> true true outcome-ok }T
\ A smart-unfolding marker (core/annotations.fs, S2 merge B) answers
\ unsupported: Lean visits mdata's term, this walk does not.
: ann ( t -- t' ) lf-annot-match lf-annot drop ;
T{ fs sk ann app sk lf-meta-kabstract -> -1 false outcome-unsupported }T

\ ---- Meta.check, at transparency all.
: chk ( e -- outcome ) lf-tr-all lf-meta-check ;
T{ sk chk nat nat tpi chk nat 0 bv lam chk -> outcome-ok outcome-ok outcome-ok }T
succ nat app constant bad-app
T{ bad-app chk lf-meta-check-bad bad-app = -> outcome-invalid true }T
T{ nat fk tpi chk lf-meta-check-bad -> outcome-invalid -1 }T
T{ l0 1 s" Nat" cn chk -> outcome-invalid }T
T{ nat fk 0 bv let chk -> outcome-unsupported }T
T{ sk ann chk succ sk ann app chk -> outcome-unsupported outcome-unsupported }T
T{ lf-meta-budget 0 lf-meta-budget! sk chk swap lf-meta-budget! sk chk
   -> outcome-exhausted outcome-ok }T
T{ 1 heap-refusals ! nat succ 0 bv app lam chk 0 heap-refusals ! -> outcome-full }T
T{ nat succ 0 bv app lam chk -> outcome-ok }T

\ ---- A 10,000-deep target (S2_INTERFACE.md 9, class 5): Nat.succ applied
\ 10,000 times to Nat.add k k. Both walks keep their work on the heap
\ (kabstract.fs's kab-todo, meta-check.fs's frames), never the host's
\ stacks: kabstract of the pattern Nat.add k k gives the same tower over
\ #0 (one occurrence, at the bottom), Meta.check accepts the tower, and
\ an argument of the wrong type at the bottom (Nat.succ Nat) is found
\ there and named.
: kk ( -- t ) 0 s" Nat.add" cn fk app fk app ;
: tower ( t n -- t' ) 0 ?do succ swap app loop ;
10000 constant deep#
kk deep# tower constant deep-kk
0 bv deep# tower constant deep-bv
succ nat app constant succ-nat
succ-nat deep# tower constant deep-bad
T{ deep-kk kk lf-meta-kabstract rot deep-bv = -> true outcome-ok true }T
T{ deep-kk chk deep-bad chk lf-meta-check-bad succ-nat = -> outcome-ok outcome-invalid true }T
bye
