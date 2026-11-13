\ The shared helpers of the passes that rebuild mixed terms
\ (src/kernel/mixed-rebuild.fs), driven by a pass of this file's own: a
\ copy, which keeps every leaf and rebuilds every binary node with
\ lf-rebuild-binary (mixed-shift, -instantiate, -open and inductive-nested
\ use its pieces with continuations of their own). Coverage classes of
\ docs/development/TEST_COVERAGE_REVIEW.md:
\ 1, 3. A copy is ok, a live node of the same shape; a lambda's body one
\    binder deeper; the audit's fuel; each ( index identity outcome ).
\ 2. An index the store does not hold: invalid; a visit whose result has
\    no identity: invalid, its nodes given back.
\ 5. Every fuel below the least exhausted, the least ok; a binder at the
\    deepest context full (diagnostic binders-full), whatever the fuel;
\    each allocation refused in turn full; every failure gives back what
\    the pass made (the term count as before).
\ Test-only; nothing here accepts a theorem.
require ../support/alloc-fail.fs
include ../support/tester.fs
require ../../src/main.fs
decimal

: must ( flag -- ) 0= abort" mixed-rebuild test: refused" ;
lf-name-reset lf-level-reset lf-term-reset lf-cref-reset lf-lctx-reset
4096 lf-term-capacity! drop
lf-ssession-begin must
: sort-node ( -- node ) 0 lf-term-symbolic-sort must ;
: var ( i -- node ) lf-term-bvar must ;
: binary ( a b tag -- node ) lf-term-binary must ;
\ fun (x : Sort 0) => x x, and Pi (x : Sort 0), Sort 0: 5 and 3 node
\ occurrences.
: lam-node ( -- node ) sort-node 0 var 0 var lf-tag-app binary lf-tag-lam binary ;
: pi-node ( -- node ) sort-node sort-node lf-tag-pi binary ;
: identity ( node -- id ) lf-term-identity must ;

\ The copy: a leaf kept, a binary node rebuilt, a node the store does not
\ hold refused.
: copy-visit ( node frames -- ... frames next )
  over lf-term-valid? lf-rebuild-tag
  dup lf-term-binary-tag? if drop lf-rebuild-binary exit then
  lf-rebuild-no-tag = if lf-rebuild-refuse exit then
  ['] lf-rebuild-keep lf-rebuild-return ;
' copy-visit frames: copier
: copy-in ( root context fuel -- index identity outcome )
  copier frame-budget must copier lf-rebuild-run ;
: copy ( root fuel -- index identity outcome ) 0 swap copy-in ;
\ Same shape: tag and the children's tags.
: shape ( node -- tag t1 t2 )
  dup lf-term-tag@ over lf-term-first@ lf-term-tag@ rot lf-term-second@ lf-term-tag@ ;

\ 1, 3. Copies.
T{ lam-node 100 copy swap 0<> rot drop -> outcome-ok true }T
T{ lam-node 100 copy 2drop shape -> lam-node shape }T
T{ pi-node 100 copy nip nip -> outcome-ok }T
\ A copy needs one unit of fuel per node occurrence: 5 for the lambda.
T{ lam-node 4 copy -> -1 0 outcome-exhausted }T
T{ lam-node 5 copy nip nip -> outcome-ok }T
\ 5. Every fuel below 5 exhausted, the term count as before each time.
: count@ ( -- n ) lf-term-count @ ;
: exhausted-at? ( fuel -- flag )
  lam-node count@ >r swap copy outcome-exhausted = nip nip count@ r> = and ;
: exhausted-below? ( n -- flag ) true swap 0 ?do i exhausted-at? and loop ;
T{ 5 exhausted-below? -> true }T

\ A binder at the deepest context (max-n) cannot be entered: full, with
\ the binders-full diagnostic; the copy of a lambda under that context.
T{ lf-diag-clear lam-node max-n 100 copy-in lf-diag-code@
   -> -1 0 outcome-full lf-diag-binders-full }T
\ One level higher, the lambda's body (an application) is visited at max-n
\ and copied; a lambda in that body cannot be entered: full.
: nested-lam ( -- node ) sort-node lam-node lf-tag-lam binary ;
T{ lam-node max-n 1- 100 copy-in nip nip -> outcome-ok }T
T{ nested-lam max-n 1- 100 copy-in -> -1 0 outcome-full }T
T{ nested-lam max-n 2 - 100 copy-in nip nip -> outcome-ok }T
\ An application there is no binder: its copy goes on.
T{ 0 var 0 var lf-tag-app binary max-n 100 copy-in nip nip -> outcome-ok }T

\ 2. An index the store does not hold: invalid.
T{ count@ 1000 + 100 copy -> -1 0 outcome-invalid }T

\ 5. Each allocation of the copy refused in turn: full, nothing left made.
: refused ( k -- outcome hit? kept? )
  lam-node count@ >r swap af-arm 100 copy nip nip af-hit 0<> af-off count@ r> = ;
: full-at? ( k -- flag ) refused and swap outcome-full = and ;
: window ( -- n ) lam-node 0 af-arm 100 copy 2drop drop af-seen@ af-off ;
: all-full? ( -- flag ) true window 1+ 1 ?do i full-at? and loop ;
T{ window 0> all-full? -> true true }T

\ The audit before allocation (lf-rebuild-audit): ok with the fuel left,
\ exhausted with none.
: audit ( node fuel -- outcome left )
  copier frame-budget must dup identity copier lf-rebuild-audit copier frame-fuel @ ;
\ (on fun (x : #1) => x x, 5 node occurrences); invalid, with no fuel
\ left, for a Sort whose level the store does not hold (this file makes
\ no level: the copies above keep such a leaf unread).
: open-lam ( -- node ) 1 var 0 var 0 var lf-tag-app binary lf-tag-lam binary ;
T{ open-lam 100 audit -> outcome-ok 95 }T
T{ open-lam 2 audit -> outcome-exhausted 0 }T
T{ sort-node 100 audit -> outcome-invalid 0 }T
copier frame-free
bye
