\ Unit tests of the discrimination tree (plan slice MF2+DT;
\ src/front/discr-tree.fs) over the Init slice tests/front/whnf-slice.ndjson
\ and its elaboration data, its keys made by mkPath (discr-keys.fs) or by
\ hand: a tree not made answers nothing; insertCore with insertVal
\ replacing an equal value in place; getUnify's order (the star child
\ first for a key, every child in insertion order for a star key), a
\ root no value has, a star root (unsupported); roots found by key;
\ a root built by its builder at its first query, once, and nothing kept
\ of a builder's failure, the next query building it anew; each heap
\ request of an insertion refused in turn (full, then in full); a node
\ with 300 children, each found again through the child table across
\ its growth; the throwing faces; free and ready. Every T{ }T checks the
\ data stack's depth.
include ../support/tester.fs
include ../support/heap-watch.fs
require ../../src/front/discr-tree.fs
require ./whnf-cases.fs

create tree /dtree allot   tree /dtree erase
create outs /slab allot   1 cells 100000 outs slab-init drop
: ?lv ( -- level ) lf-level-mvar-new made ;
: ?tv ( level -- t ) lf-level-succ must sort mv-natural lf-mvar-new made ;
: add ( t -- t' ) >r ?lv 1 s" Add" cn r> app ;
: add0 ( t -- t' ) >r l0 1 s" Add" cn r> app ;
: mul0 ( t -- t' ) >r l0 1 s" Mul" cn r> app ;
: keys ( t -- k n ) lf-dt-path made ;
: put ( t v tr -- outcome ) >r >r keys r> r> lf-dtree-insert ;
: unify-in ( t tr -- n outcome ) outs slab-clear outs lf-dtree-unify outs slab-count swap ;
: unify ( t -- n outcome ) tree unify-in ;
: v@ ( i -- v ) outs slab-at @ ;
lf-defeq-elab lf-defeq-stuck or lf-defeq-flags!

\ ---- A tree not made answers nothing and finds no root.
T{ nat add0 unify tree lf-dtree-live? nat add0 keys drop tree lf-dtree-root
   -> 0 outcome-ok false false }T

\ ---- insertCore: Add Nat's keys (Add, Nat) and Add ?a's (Add, star);
\ insertVal replaces an equal value in place: no new node or cell.
T{ nat add0 10 tree put lv1 ?tv add 11 tree put nat add0 12 tree put
   -> outcome-ok outcome-ok outcome-ok }T
T{ tree lf-dtree-live? tree lf-dtree-nodes# tree lf-dtree-vals# tree lf-dtree-roots#
   -> true 3 3 1 }T
T{ nat add0 10 tree put tree lf-dtree-nodes# tree lf-dtree-vals# -> outcome-ok 3 3 }T

\ ---- getUnify: a key visits the star child first, then its own child
\ (Main.lean:597); a star key (a metavariable under isDefEqStuckEx)
\ every child, in insertion order; a root no value has nothing; a star
\ root (a bare metavariable) is unsupported.
T{ nat add0 unify 0 v@ 1 v@ 2 v@ -> 3 outcome-ok 11 10 12 }T
T{ lv1 ?tv add unify 0 v@ 1 v@ 2 v@ -> 3 outcome-ok 10 12 11 }T
T{ nat mul0 unify ?n unify nip -> 0 outcome-ok outcome-unsupported }T
\ The roots: found by their key, the root's key and trie read back.
: add-root ( -- r flag ) nat add0 keys drop tree lf-dtree-root ;
T{ add-root over tree lf-dtree-root-key nat add0 keys drop elab-key= rot tree lf-dtree-root-trie 0<
   -> true true false }T

\ ---- A root built by the builder at its first query, once; nothing of
\ a failure kept (its nodes, cells and trie), the next query building
\ it anew.
create tree2 /dtree allot   tree2 /dtree erase
variable builds   variable failing
: build ( r tr -- outcome )
  2drop 1 builds +! nat mul0 20 tree2 put failing @ if drop outcome-full then ;
: made2 ( -- ) tree2 lf-dtree-free tree2 lf-dtree-ready drop ['] build tree2 lf-dtree-builder! ;
: mul-root ( -- outcome ) nat mul0 keys drop tree2 lf-dtree-root-add nip ;
made2
T{ mul-root 0 tree2 lf-dtree-root-trie tree2 lf-dtree-nodes# -> outcome-ok -1 0 }T
T{ nat mul0 tree2 unify-in 0 v@ nat mul0 tree2 unify-in builds @ -> 1 outcome-ok 20 1 outcome-ok 1 }T
made2 0 builds !  true failing !
T{ mul-root nat mul0 tree2 unify-in -> outcome-ok 0 outcome-full }T
T{ 0 tree2 lf-dtree-root-trie tree2 lf-dtree-nodes# tree2 lf-dtree-vals# -> -1 0 0 }T
false failing !
T{ nat mul0 tree2 unify-in builds @ tree2 lf-dtree-vals# -> 1 outcome-ok 2 1 }T
\ No builder: a root with no trie has no values.
T{ tree2 lf-dtree-free tree2 lf-dtree-ready mul-root nat mul0 tree2 unify-in
   -> outcome-ok outcome-ok 0 outcome-ok }T

\ ---- Resources: each heap request of an insertion into a new tree
\ refused in turn: full or ok, and then the insertion and the query in
\ full, the value once (until a run meets no refusal).
create tree3 /dtree allot   tree3 /dtree erase
: refused ( k -- outcome fired? )
  tree3 lf-dtree-free nat add0 keys rot heap-refusals ! 30 tree3 lf-dtree-insert
  heap-refusals @ 0= 0 heap-refusals ! ;
: in-full? ( -- flag )
  nat add0 30 tree3 put ok? nat add0 tree3 unify-in ok? swap 1 = and and 0 v@ 30 = and ;
: refusal-ok? ( k -- flag fired? )
  refused swap dup ok? swap outcome-full = or in-full? and swap ;
: refusals-ok? ( -- flag ) true 50 1 do i refusal-ok? -rot and swap 0= if leave then loop ;
T{ refusals-ok? 50 refused nip -> true false }T

\ ---- A node with 300 children (Mathlib's classes hold up to 3,594
\ instances under one root): each child found again through the child
\ table, which grew from 16 slots, so inserting them all again adds no
\ node and no cell. The keys are made by hand: Add's root key, then a
\ constant key of its own (a declaration number no slice has).
create tree4 /dtree allot   tree4 /dtree erase
: key-like ( k -- k' ) elab-key-const elab-key-new made dup >r ek swap ek swap /ek move r> ;
: own-key ( i -- k ) elab-key-const elab-key-new made tuck elab-key-ref! ;
: path ( i -- k 2 ) nat add0 keys drop key-like swap 100000 + own-key drop 2 ;
: put4 ( i -- outcome ) dup path rot tree4 lf-dtree-insert ;
: puts ( -- flag ) true 300 0 do i put4 ok? and loop ;
T{ puts tree4 lf-dtree-nodes# tree4 lf-dtree-vals# -> true 301 300 }T
T{ puts tree4 lf-dtree-nodes# tree4 lf-dtree-vals# -> true 301 300 }T

\ ---- The throwing faces: ok runs on; a failure is thrown as its
\ outcome's code (meta-must.fs), here a star root's unsupported.
outs slab-clear
T{ nat add0 keys 13 tree ' lf-dt-insert catch nat add0 tree outs ' lf-dt-get-unify catch
   outs slab-count -> 0 0 4 }T
T{ ?n tree outs ' lf-dt-get-unify catch nip nip nip lf-meta-throw-base outcome-unsupported - = -> true }T

\ ---- Free and ready: nothing kept, made again empty.
T{ tree lf-dtree-free tree lf-dtree-live? tree lf-dtree-ready tree lf-dtree-roots# nat add0 unify
   -> false outcome-ok 0 0 outcome-ok }T
tree lf-dtree-free tree2 lf-dtree-free tree3 lf-dtree-free tree4 lf-dtree-free
T{ lf-mctx-depth lf-mctx-marks -> 0 0 }T
bye
