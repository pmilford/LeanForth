\ Unit tests of the front end's memoised (node, depth) rebuild walk
\ (src/front/offset-walk.fs; reuse pass F2 of 2026-11-18) and of the
\ shared rebuild words lf-meta-rebuilt and
\ lf-meta-annot-over, with a walk of the tests' own that puts y for x:
\ leaves, binary nodes rebuilt or kept, a binder's depth, a pair kept by
\ the kind, annotations, a shared node made once (the memo), the walk's
\ own case, a failure's outcome (the first one stays), a run nested in a
\ hook (the record in use put back), full when the heap refuses, then the
\ walk working again; and the term store's room for the rebuild words.
\ instantiate1, abstract and instantiateBetaRevRange, the walk's callers,
\ are tested in tests/front/meta.fs and infer.fs. Every T{ }T checks the
\ data stack's depth. Nothing here checks or accepts a theorem.
include ../support/tester.fs
include ../support/heap-watch.fs
require ../../src/load/front.fs

lf-author-begin lf-mctx-reset lf-lctx-reset 100000 lf-term-capacity! drop
: app ( f a -- t ) lf-term-app 0= abort" app" ;
: lam ( type body -- t ) lf-term-lam 0= abort" lam" ;
: bv ( i -- t ) lf-term-bvar 0= abort" bvar" ;
: fvar ( type -- fvar ) lf-lctx-local ok? 0= abort" fvar" ;
: ann ( t key -- t' ) lf-annot ok? 0= abort" annotation" ;
: parts ( t -- first second ) dup lf-term-first@ swap lf-term-second@ ;
0 lf-term-sort drop constant prop
prop fvar constant x
prop fvar constant y
prop fvar constant z
9 lf-term-bvar drop constant b9

\ The tests' walk: x becomes y; a leaf's visits and the deepest depth
\ seen are counted; z fails the walk (unsupported), a bound variable #9
\ fails it full; a pair is kept when kept-flag is set and the node is z
\ applied to anything.
variable visits   variable deepest   variable kept-flag
: t-kept? ( node depth -- flag )
  drop kept-flag @ if dup lf-term-app? if lf-term-first@ z = exit then then drop false ;
: t-fail ( node -- )
  dup z = if outcome-unsupported ow-fail then b9 = if outcome-full ow-fail then ;
: t-leaf ( node depth -- image )
  deepest @ max deepest ! 1 visits +! dup t-fail dup x = if drop y then ;
' t-kept? ' t-leaf ' false ow-kind constant t-kind
/ow context-record: t-rec
/ow context-record: t-rec2
:noname ( -- ) t-rec ow-free t-rec2 ow-free ; context-teardown
: walk ( t -- t' outcome ) 0 visits ! 0 deepest ! t-kind t-rec ow-run ;
: walk2 ( t -- t' outcome ) t-kind t-rec2 ow-run ;

\ ---- Leaves and binary nodes: rebuilt where a part changes, the same
\ node where none does.
T{ x walk z walk -> y outcome-ok -1 outcome-unsupported }T
T{ prop walk -> prop outcome-ok }T
T{ x z app walk -> -1 outcome-unsupported }T
T{ x prop app walk swap parts -> outcome-ok y prop }T
prop prop app constant pp
T{ pp walk -> pp outcome-ok }T
\ A binder's second part one deeper: the deepest leaf of fun _ => fun _ => x.
: inner2 ( t -- t' ) parts nip parts nip ;
: kept= ( t t' outcome -- flag outcome ) >r = r> ;
T{ prop prop x lam lam walk swap inner2 swap deepest @
   -> y outcome-ok 2 }T
\ A shared node is made once: x x x x has x once, as a leaf at depth 0.
T{ x x app dup app walk nip visits @ -> outcome-ok 1 }T
\ ---- The kind's kept test: z a is its own image, unvisited.
T{ true kept-flag ! z x app dup walk false kept-flag ! kept= visits @
   -> true outcome-ok 0 }T
\ ---- Annotations: over the child's image with the key; kept when the
\ child stays.
T{ x lf-annot-match ann walk swap dup lf-annot? swap parts -> outcome-ok true y lf-annot-match }T
T{ prop lf-annot-match ann dup walk kept= -> true outcome-ok }T
\ ---- Failures: the walk stops with the first one; -1 for the term.
T{ b9 z app walk -> -1 outcome-full }T
T{ z b9 app walk -> -1 outcome-unsupported }T
\ ---- A hook may run another walk with another record: the outer run
\ goes on with its own record (ow-current put back).
: t-nested ( node depth -- image ) drop dup x = if walk2 drop exit then ;
' t-kept? ' t-nested ' false ow-kind constant t-outer
T{ x prop app x app t-outer t-rec ow-run swap parts swap parts
   -> outcome-ok y y prop }T
\ ---- The walk's own case comes first: here every application is y.
: t-own ( node depth -- node depth false | true )
  over lf-term-app? if y ow-done true else false then ;
' t-kept? ' t-leaf ' t-own ow-kind constant t-ownk
T{ x x app x app t-ownk t-rec ow-run -> y outcome-ok }T
\ ---- Full: the first heap request refused (the run's memo); the walk
\ then works again; every refusal in turn gives full or ok, never another
\ answer.
T{ 1 heap-refusals ! x prop app walk heap-refusals @ -> -1 outcome-full 0 }T
T{ x prop app walk nip -> outcome-ok }T
\ A run gives back the blocks of the run before it: none is lost.
T{ x prop app walk 2drop live-blocks @ x prop app walk 2drop live-blocks @ = -> true }T
: deep-x ( n -- t ) x swap 0 ?do prop swap lam loop ;
: refused ( k -- outcome ) 200 deep-x swap heap-refusals ! walk nip 0 heap-refusals ! ;
: ok-or-full? ( outcome -- flag ) dup ok? swap outcome-full = or ;
: refusal-sweep ( -- flag ) true 12 1 do i refused ok-or-full? and loop ;
T{ refusal-sweep 1 refused -> true outcome-full }T
\ Deep terms need no host stack: 20000 binders.
T{ 20000 deep-x walk nip deepest @ -> outcome-ok 20000 }T

\ ---- lf-meta-rebuilt and lf-meta-annot-over: the node
\ itself when its parts stay, else a node of its tag over the new parts;
\ full when the term store has no room.
T{ prop prop pp lf-meta-rebuilt -> pp outcome-ok }T
T{ x prop pp lf-meta-rebuilt swap dup lf-term-app? swap parts -> outcome-ok true x prop }T
prop lf-annot-match ann constant annp
T{ prop annp lf-meta-annot-over -> annp outcome-ok }T
T{ x annp lf-meta-annot-over swap dup lf-annot-child swap lf-annot-key
   -> outcome-ok x lf-annot-match }T
lf-term-capacity constant term-room
T{ lf-term-count @ lf-term-capacity! -> outcome-ok }T
T{ z prop pp lf-meta-rebuilt z annp lf-meta-annot-over -> -1 outcome-full -1 outcome-full }T
T{ prop prop pp lf-meta-rebuilt -> pp outcome-ok }T
T{ term-room lf-term-capacity! -> outcome-ok }T

T{ depth -> 0 }T
cr .( offset-walk.fs: all tests passed) cr
bye
