\ The discrimination tree (plan slice MF2+DT; docs/design/LF_LIBRARIES.md
\ §3 and appendix B, SIMP_DATA.md §5): Lean 4.35.0's DiscrTree
\ (Lean/Meta/DiscrTree/Basic.lean, Main.lean) over the keys of
\ front/elab-keys.fs, each value one cell. The index of the simp and
\ rewriting library, shared by the instance table (front/instances.fs,
\ whose private trie this was, FE1e3) and, from SP1b, simp's lemma sets.
\ LeanForth-specific: Lean's keys, and getUnify's keys made by
\ front/discr-keys.fs. Untrusted: a tree only chooses candidates.
\
\ A tree is a /dtree record the caller owns (in its checker-context
\ record), made by lf-dtree-ready and given back by lf-dtree-free. Its
\ roots are Lean's root map: a key, and the root's trie, or none yet; its
\ tries are nodes (a key, children, values) as Lean's Trie. Children are
\ kept in insertion order, with a hash table by (node, key) to find one
\ and the star child kept apart; Lean keeps them sorted by Key.lt, whose
\ order needs Lean's Name.hash, so a caller that needs Lean's order
\ inserts in Lean's stored order (the instance data's ranks do: FE1E
\ §3.2). Values are cells; insertVal's equality is =.
\ - lf-dtree-ready ( tree -- outcome ): the tree made, empty, once (its
\   roots and child tables on the heap); ok when it is already made.
\ - lf-dtree-free ( tree -- ): everything given back; empty and not made.
\ - lf-dtree-live? ( tree -- flag ): whether it is made.
\ - lf-dtree-insert ( keys n v tree -- outcome ): insertCore
\   (Basic.lean:176): value v under keys k .. k+n-1 (one term in Lean's
\   path order, n at least 1): the root of key k (made when absent), its
\   trie (made when it has none), a child per further key (insertAux),
\   then insertVal: a value = v replaced in place, else v appended. A
\   failure leaves at most nodes without values: no answer changes.
\ - lf-dtree-root-add ( k tree -- r outcome ): root key k declared (the
\   root r, made with no trie when absent), for a tree built root by root.
\ - lf-dtree-root ( k tree -- r true | false ), lf-dtree-roots#
\   ( tree -- n ), lf-dtree-root-key ( r tree -- k ), lf-dtree-root-trie
\   ( r tree -- node ) (-1: none yet); lf-dtree-nodes# and lf-dtree-vals#
\   ( tree -- n ): the nodes and value cells kept.
\ - lf-dtree-builder! ( xt tree -- ): xt ( r tree -- outcome ) builds a
\   root at its first query: run once root r has a new empty trie, it
\   inserts root r's values (and no other root's) by lf-dtree-insert; on
\   a failure every node and value made since is forgotten and r has no
\   trie again, so the next query builds it anew. No builder (0): a root
\   with no trie has no values. The builder may query or fill other
\   trees (the query's tree and output slab are put back after it), not
\   its own tree but by lf-dtree-insert under root r.
\ - lf-dtree-unify ( e tree out -- outcome ): getUnify (Main.lean:567) at
\   the transparency in force (the caller's withReducible): the values
\   whose keys may unify with e appended to the slab out (one cell
\   each), in Lean's order; on a key scope (lf-dt-scoped). The root key
\   is getUnifyKeyArgs' (discr-keys.fs's lf-dt-key); first come the
\   values under the star root (getStarResult, Main.lean:561; built by
\   the builder when it has no trie), then the walk of the key's root; a
\   root no value has adds none; a star root key (e a bare metavariable:
\   Lean folds over every root) is unsupported. Below the root a key is made only where a
\   node has children, as Lean makes it; a star key visits every child,
\   any other the star child, then the child of its key.
\ - lf-dtree-match ( e tree out -- outcome ): getMatch (Main.lean:438-
\   478), the same walk with getMatchKeyArgs' keys (discr-keys.fs's
\   lf-dt-match-key: a metavariable of e is other, so only a star of the
\   tree takes it); lf-dtree-match-extra ( e tree out -- outcome ):
\   getMatchWithExtra (:479-512), two cells a candidate (the value, then
\   its count of extra arguments): e's with 0, then, when e is an
\   application and the tree has a root of e's head with fewer arguments
\   (mayMatchPrefix, a scan of the roots), each prefix's with 1, 2, ...
\   Both on the transparency and settings in force (simp's
\   lf-with-simp-index).
\ - lf-dt-insert ( keys n v tree -- ), lf-dt-get-unify, lf-dt-get-match
\   and lf-dt-get-match-extra ( e tree out -- ): the throwing faces
\   (meta-must.fs's lf-must), for library 2's
\   callers (LF_LIBRARIES appendix B.1).
\ Outcomes: ok; lf-meta-stuck, unsupported, exhausted and invalid from
\ the query's keys (discr-keys.fs) and the builder; unsupported for a
\ star root; full when a slab or table cannot grow. Not reentrant: one
\ query or insertion at a time (the builder runs before the walk, and
\ may insert). State: each tree's record; the record dq (the tree and
\ the slab of the query in progress) in the checker context (ADR 0009).
\ Loads in decimal whatever BASE is, then restores it.
\
\ Example (the instance table's use): a tree in a context record, its
\ roots declared, built at first query by a builder that inserts them.
\   it-dt lf-dtree-ready  ['] build it-dt lf-dtree-builder!
\   k it-dt lf-dtree-root-add  ...  type it-dt out lf-dtree-unify

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/slab.fs
require ../lib/htab.fs
require ../lib/hash32.fs
require ./elab-keys.fs
require ./discr-keys.fs
require ./meta-must.fs

begin-structure /dtnode   \ a trie node; -1 for none
  field: dn-key   field: dn-parent
  field: dn-child   field: dn-last-child   field: dn-sibling   field: dn-star
  field: dn-first   field: dn-last   \ its values: the first and last value cells
end-structure
begin-structure /dtval  field: dv-value  field: dv-next  end-structure
begin-structure /dtroot  field: dr-key  field: dr-trie  end-structure
begin-structure /dtframe  field: df-todo  field: df-node  field: df-skip  end-structure
begin-structure /dtprobe  field: dp-node  field: dp-key  end-structure   \ an edge sought
begin-structure /dtree
  /htab +field dt-roots-index   \ first: its hooks find the tree at its address
  /htab +field dt-edges         \ a node's child by (node, key)
  /slab +field dt-roots   /slab +field dt-nodes   /slab +field dt-vals
  /slab +field dt-stack         \ getUnify's frames
  field: dt-live   field: dt-builder
  field: dt-star-root           \ the star root's number plus one, 0 for none
  /dtprobe +field dt-probe
end-structure
begin-structure /dq  field: dq-tree  field: dq-out
  field: dq-key     \ the key word: lf-dt-key (getUnify) or lf-dt-match-key
  field: dq-extra   \ -1, or the extra arguments written after each value
end-structure
/dq context-record: dq

: dtq ( -- tree ) dq dq-tree @ ;
: dt-use ( tree -- ) dq dq-tree ! ;
: dn@ ( n -- addr ) dtq dt-nodes slab-at ;
: dv@ ( c -- addr ) dtq dt-vals slab-at ;
: dr@ ( r -- addr ) dtq dt-roots slab-at ;
: dtf@ ( i -- addr ) dtq dt-stack slab-at ;
: lf-dtree-live? ( tree -- flag ) dt-live @ ;
: lf-dtree-roots# ( tree -- n ) dt-roots slab-count ;
: lf-dtree-nodes# ( tree -- n ) dt-nodes slab-count ;
: lf-dtree-vals# ( tree -- n ) dt-vals slab-count ;
: lf-dtree-root-key ( r tree -- k ) dt-roots slab-at dr-key @ ;
: lf-dtree-root-trie ( r tree -- node ) dt-roots slab-at dr-trie @ ;
: lf-dtree-builder! ( xt tree -- ) dt-builder ! ;

\ ---- The tables' hooks (lib/htab.fs): roots by key, children by (node,
\ key); keys equal by elab-key=, hashed by elab-key-hash.
: dt-root-rehash ( r htab -- h ) lf-dtree-root-key elab-key-hash ;
: dt-root-same ( r k htab -- flag ) rot swap lf-dtree-root-key elab-key= ;
create dt-root-hooks /htab-hooks allot
' dt-root-rehash ' dt-root-same dt-root-hooks htab-hooks!
: dt-edge-hash ( node k -- h ) elab-key-hash swap hash-step ;
: dt-edge-node ( c htab -- addr ) [ 0 dt-edges ] literal - dt-nodes slab-at ;
\ A node's edge hash, as dt-edge-hash of its parent and key.
: dn-hash ( addr -- h ) dup dn-key @ elab-key-hash swap dn-parent @ hash-step ;
: dt-edge-rehash ( c htab -- h ) dt-edge-node dn-hash ;
: dt-edge-same ( c probe htab -- flag )
  rot swap dt-edge-node over dp-node @ over dn-parent @ = if
  swap dp-key @ swap dn-key @ elab-key= else 2drop false then ;
create dt-edge-hooks /htab-hooks allot
' dt-edge-rehash ' dt-edge-same dt-edge-hooks htab-hooks!

\ ---- Making and freeing a tree.
: dt-slab-init ( unit slab -- outcome ) >r max-n over / r> slab-init ;
: dt-slabs-made ( tree -- outcome )
  >r /dtroot r@ dt-roots dt-slab-init /dtnode r@ dt-nodes dt-slab-init outcome-and
  /dtval r@ dt-vals dt-slab-init outcome-and
  /dtframe r> dt-stack dt-slab-init outcome-and ;
: dt-roots-made ( tree -- outcome ) 4 dt-root-hooks rot dt-roots-index htab-init ;
: dt-edges-made ( tree -- outcome ) 4 dt-edge-hooks rot dt-edges htab-init ;
: lf-dtree-free ( tree -- )
  dup dt-roots-index htab-free dup dt-edges htab-free dup dt-roots slab-free
  dup dt-nodes slab-free dup dt-vals slab-free dup dt-stack slab-free /dtree erase ;
: dt-made ( tree -- outcome )
  dup /dtree erase dup dt-slabs-made ['] dt-roots-made ok-with ['] dt-edges-made ok-with
  dup ok? if drop true swap dt-live ! outcome-ok else swap lf-dtree-free then ;
: lf-dtree-ready ( tree -- outcome )
  dup lf-dtree-live? 0= if dt-made exit then drop outcome-ok ;

\ ---- Nodes and children: a new child is linked last, its edge in the
\ table, and kept as the star child when its key is the star.
: dts ( -- slab ) dtq dt-stack ;
\ A new unit of slab, made by xt ( x addr -- ) from x.
: dt-claimed ( x slab xt -- i outcome )
  >r 1 over slab-claim ok-then? 0= if r> drop nip nip no-result exit then
  tuck swap slab-at rot swap r> execute outcome-ok ;
\ A new record of size bytes at addr: x in its first field, every other
\ cell -1 (none).
: dt-fresh ( x addr size -- ) over swap -1 fill ! ;
: dn-init ( k addr -- ) /dtnode dt-fresh ;
: dt-node-new ( k parent -- n outcome )
  swap dtq dt-nodes ['] dn-init dt-claimed ok-then? 0= if nip no-result exit then
  tuck dn@ dn-parent ! outcome-ok ;
: dt-probe! ( k node -- probe ) dtq dt-probe >r r@ dp-node ! r@ dp-key ! r> ;
: dt-edge-find ( k node -- c true | i false )
  2dup swap dt-edge-hash >r dt-probe! r> dtq dt-edges htab-find ;
: dt-find-child ( k node -- c | -1 )
  dup dn@ dn-child @ 0< if 2drop -1 exit then dt-edge-find 0= if drop -1 then ;
: dt-edge-add ( c -- outcome )
  dtq dt-edges htab-ready dup ok? 0= if nip exit then drop
  dup dn@ dup dn-key @ swap dn-parent @ dt-edge-find if 2drop outcome-invalid exit then
  dtq dt-edges htab-put outcome-ok ;
: dt-append-child ( c n -- )
  dn@ dup dn-child @ 0< if 2dup dn-child ! else 2dup dn-last-child @ dn@ dn-sibling ! then
  dn-last-child ! ;
: dt-star! ( c n -- ) over dn@ dn-key @ elab-key-star? if dn@ dn-star ! else 2drop then ;
: dt-linked ( n c -- c ) tuck swap 2dup dt-star! dt-append-child ;
: dt-child-new ( k n -- c outcome )
  tuck dt-node-new ok-then? 0= if nip no-result exit then
  dup dt-edge-add dup ok? if drop dt-linked outcome-ok else nip nip no-result then ;
: dt-descend ( k n -- c outcome )
  2dup dt-find-child dup 0< 0= if nip nip outcome-ok exit then drop dt-child-new ;

\ ---- Values: insertVal (Basic.lean:125), an equal value replaced in
\ place, else appended after the node's last.
: dt-val-find ( v n -- cell | -1 )
  dn@ dn-first @ begin dup 0< 0= while 2dup dv@ dv-value @ = if nip exit then
  dv@ dv-next @ repeat nip ;
: dv-init ( v addr -- ) /dtval dt-fresh ;
: dt-val-new ( v -- cell outcome ) dtq dt-vals ['] dv-init dt-claimed ;
: dt-append ( v n -- outcome )
  swap dt-val-new ok-then? 0= if nip exit then swap dn@
  dup dn-first @ 0< if 2dup dn-first ! else 2dup dn-last @ dv@ dv-next ! then
  dn-last ! outcome-ok ;
: dt-insert-val ( v n -- outcome )
  2dup dt-val-find dup 0< if drop dt-append else nip dv@ dv-value ! outcome-ok then ;

\ ---- insertAux below a trie node by the keys after the root key.
: dt-keys-rest ( keys n -- end start ) over + swap 1+ ;
: dt-descend-at ( node k start -- node' outcome ) + swap dt-descend ;
: dt-path-from ( keys n node -- node' outcome )
  -rot dt-keys-rest tuck - swap ['] dt-descend-at ok-fold ;
: dt-insert-at ( v keys n node -- outcome )
  dt-path-from ok-then? 0= if nip exit then dt-insert-val ;

\ ---- Roots (Lean's root map, a PersistentHashMap there).
: dt-root-find ( k -- r true | i false ) dup elab-key-hash dtq dt-roots-index htab-find ;
: lf-dtree-root ( k tree -- r true | false )
  dup lf-dtree-live? 0= if 2drop false exit then dt-use dt-root-find dup 0= if nip then ;
: dr-init ( k addr -- ) /dtroot dt-fresh ;
: dt-star-mark ( r -- r )   \ the star root kept apart (getStarResult)
  dup dr@ dr-key @ elab-key-star? if dup 1+ dtq dt-star-root ! then ;
: dt-root-put ( k i -- r outcome )
  >r dtq dt-roots ['] dr-init dt-claimed ok-then? 0= if r> drop no-result exit then
  dt-star-mark dup r> dtq dt-roots-index htab-put outcome-ok ;
: dt-root-add ( k -- r outcome )
  dtq dt-roots-index htab-ready dup ok? 0= if nip no-result exit then drop
  dup dt-root-find if nip outcome-ok else dt-root-put then ;
: dt-trie-new ( r -- outcome )   \ root r's trie: a new empty node
  dup dr@ dr-key @ -1 dt-node-new ok-then? 0= if nip exit then
  swap dr@ dr-trie ! outcome-ok ;
: dt-trie-of ( r -- node outcome )   \ made when it has none
  dup dr@ dr-trie @ dup 0< 0= if nip outcome-ok exit then drop
  dup dt-trie-new ok-then? if dr@ dr-trie @ outcome-ok else no-result then ;
: dt-root-trie ( k -- node outcome )
  dt-root-add ['] dt-trie-of ok-and ;
: dt-insert ( v keys n -- outcome )
  over dt-root-trie ok-then? if dt-insert-at else nip nip nip then ;
: dt-ready-use ( tree -- outcome )
  dup lf-dtree-ready dup ok? if swap dt-use else nip then ;
: lf-dtree-root-add ( k tree -- r outcome )
  dt-ready-use ['] dt-root-add ok-and ok-or-none ;
: lf-dtree-insert ( keys n v tree -- outcome )
  dt-ready-use ok-then? if -rot dt-insert else nip nip then ;

\ ---- A root built at its first query by the builder; nothing of a
\ failure kept: the nodes (their edges taken out) and values since the
\ mark forgotten, the root left with no trie.
: dt-mark ( -- nodes vals ) dtq dt-nodes slab-count dtq dt-vals slab-count ;
: dt-unedge ( n -- )
  dup dn@ dn-parent @ 0< if drop exit then
  dup dn@ dn-hash dtq dt-edges htab-remove drop ;
: dt-back ( nodes vals -- )
  dtq dt-vals slab-cut dup dtq dt-nodes slab-count swap ?do i dt-unedge loop
  dtq dt-nodes slab-cut ;
\ The builder may query or fill other trees: this query's tree, output,
\ key word and extra count are put back after it.
\ The query's key word and extra count kept under r, then put back.
: dt-keep ( r -- k x r ) dq dq-key @ swap dq dq-extra @ swap ;
: dt-put-back ( k x outcome -- outcome ) swap dq dq-extra ! swap dq dq-key ! ;
: dt-saved-run ( r -- outcome ) dq 2@ 2>r dtq dup dt-builder @ execute 2r> dq 2! ;
: dt-build-run ( r -- outcome )
  dup dt-trie-new ok-then? 0= if exit then
  dt-keep dt-saved-run dt-put-back ;
: dt-built ( r -- outcome )
  dt-mark 2>r dup dt-build-run dup ok? if nip 2r> 2drop exit then
  swap -1 swap dr@ dr-trie ! 2r> dt-back ;
: dt-root-ready ( r -- node outcome )   \ its trie, built when it has none
  dup dr@ dr-trie @ dup 0< 0= if nip outcome-ok exit then drop
  dtq dt-builder @ 0= if drop -1 outcome-ok exit then
  dup dt-built ok-then? if dr@ dr-trie @ outcome-ok else no-result then ;

\ ---- getUnify's process (Main.lean:577-605) on the tree's stack of
\ frames (todo, node, skip): skip 0 or more visits a node; skip below 0
\ visits the siblings from node, each with skip (skip invert) plus its
\ arity. A node below 0 has nothing to visit and gets no frame. A frame's
\ visit puts its first new frame in the slot its pop freed (dt-refill:
\ the room is there), any second one on top (dt-push, which may find no
\ room).
: dt-frame! ( todo node skip i -- ) dtf@ df-todo cell-triple! ;
: dt-refill ( todo node skip -- )
  over 0< if drop 2drop exit then dts slab-count dt-frame! 1 dts slab-commit ;
: dt-push ( todo node skip -- outcome )
  over 0< if drop 2drop outcome-ok exit then
  1 dts slab-claim ok-then? 0= if nip nip nip exit then dt-frame! outcome-ok ;
: dt-pop ( -- todo node skip )
  dts slab-last df-todo cell-triple@ dts slab-drop ;
: dt-out ( x -- outcome ) dq dq-out @ slab-push ;
: dt-extra-out ( -- outcome ) dq dq-extra @ dup 0< if drop outcome-ok else dt-out then ;
: dt-value-out ( v -- outcome ) dt-out ['] dt-extra-out ok-and ;
: dt-values-out ( node -- outcome )   \ none for a node below 0
  dup 0< if drop outcome-ok exit then dn@ dn-first @ begin dup 0< 0= while
    dup dv@ dv-value @ dt-value-out dup ok? 0= if nip exit then drop
    dv@ dv-next @ repeat drop outcome-ok ;
: dt-child ( n -- c ) dn@ dn-child @ ;
: dt-visit-skip ( todo node skip -- outcome )
  swap dt-child swap 1- invert dt-refill outcome-ok ;
: dt-key-of ( todo -- rest k args outcome )
  dup lf-dt-rest tuck swap lf-dt-first false rot dq dq-key @ execute ;
\ Lean visits the star child first, then the child of the key: their
\ frames go on in the other order. A star key visits every child.
: dt-on-key ( rest k args node -- outcome )
  >r swap dup elab-key-star? if 2drop r> dt-child -1 dt-refill outcome-ok exit then
  r@ dt-find-child 0 dt-refill r> dn@ dn-star @ 0 dt-push ;
: dt-visit-key ( todo node -- outcome )
  >r dt-key-of ok-then3? if r> dt-on-key else r> drop then ;
\ A node's values when no term is left, else its children by the next
\ term's key (a value's keys are one term: a node has children exactly
\ while terms are left, so the key is made only where Lean makes it).
: dt-visit-zero ( todo node -- outcome )
  over lf-dt-nil = if nip dt-values-out else dt-visit-key then ;
: dt-arity ( s -- n ) dn@ dn-key @ elab-key-arity ;
\ The next sibling's frame goes on first, so that s is visited first.
: dt-siblings ( todo s base -- outcome )
  >r 2dup dn@ dn-sibling @ r@ invert dt-refill dup dt-arity r> + dt-push ;
: dt-frame ( todo node skip -- outcome )
  dup 0< if invert dt-siblings exit then ?dup if dt-visit-skip else dt-visit-zero then ;
: dt-walk ( -- outcome )
  begin dts slab-count while dt-pop dt-frame dup ok? 0= if exit then drop repeat
  outcome-ok ;

\ ---- getUnify.
: dt-walk-from ( list node -- outcome ) 0 dt-push dup ok? if drop dt-walk then ;
\ getStarResult (Main.lean:561): the star root's values come first.
: dt-star-results ( -- outcome )
  dtq dt-star-root @ ?dup 0= if outcome-ok exit then
  1- dt-root-ready ok-then? if dt-values-out then ;
: dt-key-root ( list k -- outcome )
  dt-root-find 0= if 2drop outcome-ok exit then
  dt-root-ready ok-then? if dt-walk-from else nip then ;
: dt-root-key ( e -- k list outcome ) true lf-dt-nil dq dq-key @ execute ;
: dt-run-key ( k list -- outcome )
  over elab-key-star? if 2drop outcome-unsupported exit then
  dt-star-results ok-then? if swap dt-key-root else nip then ;
: dt-unify-run ( e -- outcome ) dt-root-key ok-then2? if dt-run-key then ;
\ A query: its output, key word and extra count set (dt-set), then run
\ on its tree in a key scope.
: dt-set ( out xt extra -- ) dq dq-extra ! dq dq-key ! dq dq-out ! ;
: dt-query ( e tree run -- outcome )
  swap dup dt-use lf-dtree-live? 0= if 2drop outcome-ok exit then
  dts slab-clear lf-dt-scoped ;
: lf-dtree-unify ( e tree out -- outcome )
  ['] lf-dt-key -1 dt-set ['] dt-unify-run dt-query ;

\ ---- getMatch and getMatchWithExtra (Main.lean:438-512): getUnify's walk
\ with getMatchKeyArgs' keys (a metavariable of e is other: a value whose
\ keys have a star there still comes, by the star child).
\ getMatchWithExtra: getMatchCore of e with no extra argument, then, when
\ e is an application whose root key may match a prefix (mayMatchPrefix:
\ the tree has a root of the same head with fewer arguments), of each
\ prefix e.appFn!, (e.appFn!).appFn!, ... with 1, 2, ... (the star root's
\ values again each time).
: dt-tag= ( k1 k2 -- flag ) elab-key-tag swap elab-key-tag = ;
: dt-decl= ( k1 k2 -- flag ) elab-key-decl swap elab-key-decl = ;
: dt-idx= ( k1 k2 -- flag ) elab-key-idx swap elab-key-idx = ;
: dt-like? ( k1 k2 -- flag )   \ the same key but for the arity
  2dup dt-tag= if 2dup dt-decl= if dt-idx= exit then then 2drop false ;
: dt-same-head? ( k r -- flag )   \ root r's key: k's head, fewer arguments
  dtq lf-dtree-root-key 2dup dt-like?
  if elab-key-arity swap elab-key-arity < else 2drop false then ;
: dt-prefix-head? ( k -- flag )
  dup elab-key-tag elab-key-const elab-key-fvar elab-key-proj one-of3? ;
: dt-may-prefix? ( k -- flag )
  dup dt-prefix-head? 0= if drop false exit then
  false dtq lf-dtree-roots# 0 ?do over i dt-same-head? or loop nip ;
: dt-match-at ( e n -- outcome ) dq dq-extra ! dt-unify-run ;
: dt-prefixes ( e -- outcome )
  0 begin over lf-term-app? while 1+ swap lf-term-first@ swap 2dup dt-match-at
    dup ok? 0= if nip nip exit then drop repeat 2drop outcome-ok ;
: dt-first-round ( e -- prefix? outcome )
  dt-root-key ok-then2? 0= if false swap exit then
  over dt-may-prefix? if dt-run-key true else dt-run-key false then swap ;
: dt-extra-run ( e -- outcome )
  0 dq dq-extra ! dup dt-first-round ok-then? 0= if nip exit then
  over lf-term-app? and if dt-prefixes else drop outcome-ok then ;
: lf-dtree-match ( e tree out -- outcome )
  ['] lf-dt-match-key -1 dt-set ['] dt-unify-run dt-query ;
: lf-dtree-match-extra ( e tree out -- outcome )
  ['] lf-dt-match-key 0 dt-set ['] dt-extra-run dt-query ;

\ ---- The throwing faces.
: lf-dt-insert ( keys n v tree -- ) lf-dtree-insert lf-must ;
: lf-dt-get-unify ( e tree out -- ) lf-dtree-unify lf-must ;
: lf-dt-get-match ( e tree out -- ) lf-dtree-match lf-must ;
: lf-dt-get-match-extra ( e tree out -- ) lf-dtree-match-extra lf-must ;

base !   \ the BASE this file was loaded with
