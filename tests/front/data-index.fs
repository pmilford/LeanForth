\ Unit tests of the ranked-record index (simp group 4, step 2;
\ src/front/data-index.fs) over the Init slice tests/front/whnf-slice.ndjson,
\ with a kind of its own: four values (three records and a left-out one)
\ whose enumeration order is not their rank order, keyed Add Nat, Add ?a
\ and Mul Nat (discr-keys.fs's mkPath). By the classes of
\ docs/development/TEST_COVERAGE_REVIEW.md:
\ 1. outcomes: the roots made, no trie built; a root built at its first
\    query, its entries in rank order (the star child first: getUnify),
\    the checks walking its records in rank order (the left-out value
\    skipped); lf-rix-force building a root without a query, once, and ok
\    for a key no value has; getMatchWithExtra; a gap in a root's ranks
\    invalid; a failed check keeping nothing, the next query building the
\    root anew;
\ 2. interfaces: the status cells (zero, stored, which values have one),
\    lf-rix-left-out?, lf-rix-tree, the kind's table;
\ 3. state: lf-rix-free gives everything back and keeps the kind;
\ 4. resources: each heap request of the roots and a root's build refused
\    in turn: full or the answer, then the answer in full.
\ Every T{ }T checks the data stack's depth.
include ../support/tester.fs
include ../support/heap-watch.fs
require ../../src/front/data-index.fs
require ./whnf-cases.fs

create outs /slab allot   1 cells 1000 outs slab-init drop
create log /slab allot   1 cells 1000 log slab-init drop
: ?lv ( -- level ) lf-level-mvar-new made ;
: ?tv ( level -- t ) lf-level-succ must sort mv-natural lf-mvar-new made ;
: add ( t -- t' ) >r ?lv 1 s" Add" cn r> app ;
: add0 ( t -- t' ) >r l0 1 s" Add" cn r> app ;
: mul0 ( t -- t' ) >r l0 1 s" Mul" cn r> app ;
: keys ( t -- k n ) lf-dt-path made ;
lf-defeq-elab lf-defeq-stuck or lf-defeq-flags!

\ ---- The kind: values 0, 1, -1 (left out) and 2, enumerated so; v0 Add
\ Nat rank 2, v1 Add ?a rank 0, -1 Add Nat rank 1, v2 Mul Nat rank 0.
\ The tree holds v + 100; the checks log each record they see and answer
\ checks-out.
create enum  0 , 1 , -1 , 2 ,
create vranks  1 , 2 , 0 , 0 ,   \ by v + 1
create vkeys 8 cells allot       \ ( k n ) by v + 1
: slot ( v -- addr ) 1+ 2* cells vkeys + ;
nat add0 keys 0 slot 2!   lv1 ?tv add keys 1 slot 2!   nat add0 keys -1 slot 2!
nat mul0 keys 2 slot 2!
variable checks-out   outcome-ok checks-out !   variable entry-out   outcome-ok entry-out !
: t-count ( rix -- n ) drop 4 ;
: t-value ( k rix -- v ) drop cells enum + @ ;
: t-records ( -- n ) 3 ;
: t-keys ( v -- k n ) slot 2@ ;
: t-rank ( v -- rank ) 1+ cells vranks + @ ;
: t-log ( v -- outcome ) log slab-push ;
: t-checks ( rix -- outcome ) ['] t-log swap lf-rix-each dup ok? if drop checks-out @ then ;
: t-entry ( v -- x outcome ) 100 + entry-out @ ;
' t-count ' t-value ' t-records ' t-keys ' t-rank ' t-checks ' t-entry rix-kind, constant t-kind
\ The same, v1 at rank 3: Add's ranks 1, 2, 3, a gap at 0.
: t-rank-gap ( v -- rank ) dup 1 = if drop 3 else t-rank then ;
' t-count ' t-value ' t-records ' t-keys ' t-rank-gap ' t-checks ' t-entry rix-kind, constant gap-kind

create rix /rix allot   rix /rix erase
: fresh ( kind -- ) rix lf-rix-free rix /rix erase rix lf-rix-kind! log slab-clear ;
: unify ( t -- n outcome ) outs slab-clear rix outs lf-rix-unify outs slab-count swap ;
: v@ ( i -- v ) outs slab-at @ ;
: log@ ( i -- v ) log slab-at @ ;
: add-key ( -- k ) nat add0 keys drop ;
: mul-key ( -- k ) nat mul0 keys drop ;
: trie-of ( k -- node ) rix lf-dtree-root drop rix lf-dtree-root-trie ;

\ ---- 1. The roots made, none built; Add Nat's query builds Add's root:
\ v1 (the star child) first, then -1 and v0 in rank order; the checks saw
\ v1 then v0; Mul's root still unbuilt.
t-kind fresh
T{ rix lf-rix-roots rix lf-dtree-roots# add-key trie-of mul-key trie-of
   -> outcome-ok 2 -1 -1 }T
T{ nat add0 unify 0 v@ 1 v@ 2 v@ log slab-count 0 log@ 1 log@ -> 3 outcome-ok 101 99 100 2 1 0 }T
T{ mul-key trie-of add-key trie-of 0< -> -1 false }T
\ lf-rix-force: Mul built without a query (the checks saw v2), once; a
\ key no value has: ok, nothing built.
T{ mul-key rix lf-rix-force log slab-count 2 log@ mul-key rix lf-rix-force log slab-count
   -> outcome-ok 3 2 outcome-ok 3 }T
T{ nat mul0 unify 0 v@ nat add keys drop rix lf-rix-force -> 1 outcome-ok 102 outcome-ok }T
\ getMatchWithExtra: Mul Nat's one value, with no extra argument.
T{ nat mul0 rix outs dup slab-clear lf-rix-match outs slab-count 0 v@ 1 v@ -> outcome-ok 2 102 0 }T
\ A gap in Add's ranks: invalid, nothing of Add's root kept.
gap-kind fresh
T{ rix lf-rix-roots nat add0 unify nip add-key trie-of rix lf-dtree-vals#
   -> outcome-ok outcome-invalid -1 0 }T
\ A failed check (full): nothing kept; the next query builds the root.
t-kind fresh   outcome-full checks-out !
T{ nat add0 unify nip add-key trie-of rix lf-dtree-nodes# -> outcome-full -1 0 }T
outcome-ok checks-out !
T{ nat add0 unify nip add-key trie-of 0< -> outcome-ok false }T
\ An entry refused (full): the same, at the root's first insertion.
t-kind fresh   outcome-full entry-out !
T{ nat add0 unify nip add-key trie-of rix lf-dtree-vals# -> outcome-full -1 0 }T
outcome-ok entry-out !
\ The roots refused (the heap's first request): the queries and
\ lf-rix-force answer full, nothing made.
: roots-refused ( xt -- outcome ) t-kind fresh 1 heap-refusals ! execute 0 heap-refusals ! ;
mul-key constant mul-k   nat add0 constant add-nat
: force-mul ( -- outcome ) mul-k rix lf-rix-force ;
: match-add ( -- outcome ) add-nat rix outs lf-rix-match ;
T{ ' force-mul roots-refused ' match-add roots-refused rix lf-dtree-live?
   -> outcome-full outcome-full false }T
t-kind fresh   rix lf-rix-roots drop

\ ---- 2. Status cells: one per record, zero until stored.
T{ 0 rix lf-rix-status 2 rix lf-rix-status 7 1 rix lf-rix-status-at ! 1 rix lf-rix-status
   -> 0 0 7 }T
T{ 2 rix lf-rix-record? 3 rix lf-rix-record? -1 rix lf-rix-record? -> true false false }T
T{ -1 lf-rix-left-out? 0 lf-rix-left-out? rix lf-rix-tree rix = -> true false true }T

\ ---- 3. Freed: no root, no tree, no cells; the kind kept, so the roots
\ are made again.
T{ rix lf-rix-free rix lf-dtree-live? rix lf-dtree-roots# 0 rix lf-rix-record? -> false 0 false }T
T{ rix lf-rix-roots nat add0 unify nip rix lf-dtree-roots# -> outcome-ok outcome-ok 2 }T

\ ---- 4. Resources: the k-th heap request of the roots and Add's build
\ refused: full or the answer; then in full (three values) until a run
\ meets no refusal.
: refused ( k -- outcome fired? )
  t-kind fresh heap-refusals ! nat add0 unify nip heap-refusals @ 0= 0 heap-refusals ! ;
: in-full? ( -- flag ) nat add0 unify ok? swap 3 = and 0 v@ 101 = and ;
: refusal-ok? ( k -- flag fired? )
  refused swap dup ok? swap outcome-full = or in-full? and swap ;
: refusals-ok? ( -- flag ) true 100 1 do i refusal-ok? -rot and swap 0= if leave then loop ;
T{ refusals-ok? 100 refused nip -> true false }T
rix lf-rix-free
bye
