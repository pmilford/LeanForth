\ Lean's is_geq on universe levels (src/kernel/level-geq.fs; level.cpp
\ 523-544): the cases of is_geq_core that the universe check of an
\ inductive type's fields (tests/core/check-block.fs) never meets, on
\ levels over the parameters u, v and w. Coverage classes of
\ docs/development/TEST_COVERAGE_REVIEW.md:
\ 1, 7. Answers, each Lean's: l2 a max (l1 >= each side, the left one
\    false or the right one), l2 an imax (the same), l1 an imax (its right
\    side >= l2), l1 a max against an imax.
\ 2, 3. Refused input: negative fuel, a level that is not live: false
\    invalid, nothing spent.
\ 5. Fuel: every budget below the least that suffices is exhausted, that
\    budget and the next give the plenty answer; frames the heap cannot
\    grow are full, as is each other allocation refused in turn.
\ 6. Nothing stays allocated: the level store's count is the same after
\    each call.
\ Test-only; nothing here accepts a theorem.
include ../support/tester.fs
include ../support/heap-watch.fs
require ../../src/lib/lib.fs
require ../../src/core/level-scope.fs
require ../../src/core/levels.fs
require ../../src/core/names.fs
require ../../src/kernel/level-geq.fs
decimal

: must ( flag -- ) 0= abort" level-geq: refused" ;
lf-name-reset lf-level-reset lf-lscope-context-reset
: param ( c-addr u -- level )
  0 -rot lf-name-str must dup lf-lscope-context-add must lf-level-param must ;
s" u" param constant u   s" v" param constant v   s" w" param constant w
: l-max ( l1 l2 -- l ) lf-level-max must ;
: imax ( l1 l2 -- l ) lf-level-tag-imax lf-level-binary must ;
: succ ( l -- l' ) lf-level-succ must ;
u v l-max constant uv            \ max u v
u v imax constant iuv          \ imax u v
uv succ constant uv+1          \ succ (max u v), normalized max (u+1) (v+1)
100000 constant plenty
: geq ( l1 l2 -- flag outcome ) plenty lf-level-geq? ;

\ ---------------------------------------------------------------------------
\ 1, 7. l2 a max: l1 >= each side. u >= u but not v; v not >= u (the
\ left side fails first); max (u+1) (v+1) >= both.
T{ u uv geq -> false outcome-ok }T
T{ v uv geq -> false outcome-ok }T
T{ uv+1 uv geq -> true outcome-ok }T
T{ uv uv geq -> true outcome-ok }T
\ l2 an imax: the same, each side; l1 an imax: its right side.
T{ w iuv geq -> false outcome-ok }T
T{ uv iuv geq -> true outcome-ok }T
T{ iuv v geq -> true outcome-ok }T
T{ iuv u geq -> false outcome-ok }T
T{ iuv uv geq -> false outcome-ok }T
T{ iuv iuv geq -> true outcome-ok }T

\ 2, 3. Negative fuel, a level that is not live: refused before any
\ work, false invalid, the fuel left 0.
T{ u uv -1 lf-level-geq? lf-lnorm-fuel @ -> false outcome-invalid 0 }T
T{ u lf-level-count @ 5 + plenty lf-level-geq? -> false outcome-invalid }T
T{ lf-level-count @ 5 + u plenty lf-level-geq? -> false outcome-invalid }T

\ 6. Nothing stays: normalize's new nodes are rolled back.
lf-level-count @ constant levels
T{ uv+1 uv geq 2drop  uv iuv geq 2drop  lf-level-count @ -> levels }T

\ ---------------------------------------------------------------------------
\ 5. Fuel. The least budget that is not exhausted (from 0 up); below it
\ every budget is exhausted (by the search), it and the next give the
\ plenty answer.
2variable pair
: at ( fuel -- flag outcome ) pair 2@ rot lf-level-geq? ;
: short? ( fuel -- flag ) at nip outcome-exhausted = ;
: least ( -- fuel ) 0 begin dup short? over plenty < and while 1+ repeat ;
: same? ( fuel -- flag ) at pair 2@ geq d= ;
: swept? ( l1 l2 -- flag ) pair 2! least dup same? swap 1+ same? and ;
T{ u uv swept? v uv swept? uv+1 uv swept? -> true true true }T
T{ w iuv swept? uv iuv swept? iuv v swept? iuv uv swept? -> true true true true }T
T{ lf-level-count @ -> levels }T

\ Each allocation refused in turn, normalize's frames freed and its
\ arrays trimmed first so that they grow again: full; the first refusal
\ not reached gives the plenty answer. n: the refusals a pair reaches.
: free-arrays ( -- )
  lf-lnorm-frames frame-free lf-lnorm-arg-cells slab-trim drop lf-lnorm-todo-cells slab-trim drop ;
: refused ( k -- flag outcome reached? )
  free-arrays heap-refusals ! pair 2@ geq heap-refusals @ 0= 0 heap-refusals ! ;
: refusal-full? ( k -- flag ) refused swap outcome-full = and nip ;
: refusals ( l1 l2 -- n ) pair 2! 0 begin 1+ dup refused nip nip 0= until 1- ;
: unrefused? ( n -- flag ) 1+ refused 0= -rot pair 2@ geq d= and ;
: refusals-ok? ( l1 l2 -- flag )
  refusals dup unrefused? swap 1+ 1 ?do i refusal-full? and loop ;
T{ uv+1 uv refusals 1 > uv iuv refusals 1 > w iuv refusals 1 > -> true true true }T
T{ uv+1 uv refusals-ok? uv iuv refusals-ok? w iuv refusals-ok? -> true true true }T
T{ 1 refused -> false outcome-full true }T
T{ lf-level-count @ heap-refusals @ -> levels 0 }T
bye
