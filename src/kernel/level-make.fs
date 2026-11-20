\ Universe levels as Lean's kernel builds and compares them (ADR 0011,
\ Amendment 1): ports of Lean 4.35.0's level.cpp (commit eb6cafb7) --
\ structural equality (operator==, 125-150), is_not_zero (160-172),
\ is_explicit (54-64), to_offset (67-74), is_one (110), and the
\ simplifying constructors mk_max (81-104) and mk_imax (112-123). Lean's
\ mk_succ (33) is the raw constructor, lf-level-succ. [kernel] code:
\ not through the review gate (AGENTS.md). Untrusted.
\ Preconditions: every level given is a live node whose reachable graph
\ a scope check validated (children earlier, known tags), and the store
\ does not change during a call except by the words here; equal parameter
\ IDs denote equal names and different IDs different names (the name
\ store interns names), as level-compare and the witnesses of level-value
\ assume.
\ State: one record, lf-lmk-state: how many leading nodes have facts,
\ and the level capacity the index of classes was built for; and per
\ node, in columns of the level store, its class (the smallest index of a
\ structurally equal node, so two levels are equal exactly when their
\ classes are), its flags (never zero; has a parameter), the node's
\ identity when they were found, and its place in the index. Members of
\ the checker context (lib/context.fs). Facts are found in index order on
\ demand and kept from call to call: records are only ever given back
\ from the top of the store and made again with new identities, so every
\ public word first gives up the facts of the nodes above the count and
\ of those whose identity changed (lf-lmk-sync), and a caller that rolls
\ the level store back may call lf-lmk-truncate. A write into a node that
\ keeps its index and identity is not seen (only tests do that). The two
\ rule tables of mk_max and mk_imax are shared and read-only.
\ The index of classes: one node of each class is in it, under the hash
\ of its tag and its children's classes (or its parameter's ID), in one
\ chain per bucket of as many buckets as the store's capacity, newest
\ first; a node's class is then found among the few nodes of its bucket,
\ not by comparing it with every earlier node.
\ Bounded work: no fuel; each node's facts are found once while it lives,
\ in expected constant time (the hash spreads the classes; nodes made to
\ collide would share a bucket), and the index is rebuilt in time linear
\ in the facts when the level store grows. Single-threaded within one
\ context.

require ../lib/lib.fs
require ../lib/bytes.fs
require ../core/levels.fs
require ../lib/store-columns.fs

begin-structure /lf-lmkrec
  field: lf-lmkrec-known       \ facts current below this index
  field: lf-lmkrec-built       \ the level capacity the index was built for; 0 none
end-structure
/lf-lmkrec context-record: lf-lmk-state
\ Per node, columns of the level store (lib/store-columns.fs): its class,
\ its flags and its identity when they were found; a class's hash, or -1
\ for a node that is not in the index, and the next class in its bucket
\ + 1, or 0. Per bucket, below the store's capacity, its newest class + 1,
\ or 0.
/slab context-record: lf-lmk-classes
1 cells ' lf-lmk-classes lf-level-columns column-add
/slab context-record: lf-lmk-flag-cells
1 cells ' lf-lmk-flag-cells lf-level-columns column-add
/slab context-record: lf-lmk-stamps
1 cells ' lf-lmk-stamps lf-level-columns column-add
/slab context-record: lf-lmk-keys
1 cells ' lf-lmk-keys lf-level-columns column-add
/slab context-record: lf-lmk-links
1 cells ' lf-lmk-links lf-level-columns column-add
/slab context-record: lf-lmk-heads
1 cells ' lf-lmk-heads lf-level-columns column-add

1 constant lf-lmk-nonzero   \ flag: not zero under any assignment (is_not_zero)
2 constant lf-lmk-param     \ flag: has a parameter (has_param)

: lf-lmk-known ( -- addr ) lf-lmk-state lf-lmkrec-known ;
: lf-lmk-built ( -- addr ) lf-lmk-state lf-lmkrec-built ;
: lf-lmk-class-cell ( index -- addr ) lf-lmk-classes column-at ;
: lf-lmk-flags-cell ( index -- addr ) lf-lmk-flag-cells column-at ;
: lf-lmk-stamp-cell ( index -- addr ) lf-lmk-stamps column-at ;
: lf-lmk-key-cell ( index -- addr ) lf-lmk-keys column-at ;
: lf-lmk-link-cell ( index -- addr ) lf-lmk-links column-at ;
\ Unchecked: facts of a node below lf-lmk-known.
: lf-lmk-class@ ( index -- class ) lf-lmk-class-cell @ ;
: lf-lmk-flags@ ( index -- flags ) lf-lmk-flags-cell @ ;
: lf-lmk-identity ( index -- identity ) lf-levels store-identity @ ;

\ ---------------------------------------------------------------------------
\ The index of classes. A class's bucket is its hash modulo the number of
\ buckets, the heads column's units (as many as the store's capacity once
\ the columns cover it); the heads are rebuilt from the facts when that
\ number has changed since they were built.
: lf-lmk-buckets ( -- n ) lf-lmk-heads slab-capacity ;
: lf-lmk-head ( h -- addr ) lf-lmk-buckets mod lf-lmk-heads column-at ;
: lf-lmk-insert ( index h -- )
  2dup swap lf-lmk-key-cell ! dup lf-lmk-head @ 2 pick lf-lmk-link-cell !
  lf-lmk-head swap 1+ swap ! ;
: lf-lmk-not-class ( index -- ) -1 swap lf-lmk-key-cell ! ;
: lf-lmk-reinsert ( index -- )
  dup lf-lmk-key-cell @ dup 0< if 2drop else lf-lmk-insert then ;
: lf-lmk-rebuild ( -- )
  0 lf-lmk-heads column-at lf-lmk-buckets cells erase
  lf-lmk-known @ 0 ?do i lf-lmk-reinsert loop lf-lmk-buckets lf-lmk-built ! ;
: lf-lmk-index-ready ( -- ) lf-lmk-built @ lf-lmk-buckets <> if lf-lmk-rebuild then ;
\ Take the newest node with facts out of its bucket, whose newest class it
\ is; if it is not (only after a raw write), the index is rebuilt at its
\ next use.
: lf-lmk-unlink ( index -- )
  dup lf-lmk-key-cell @ dup 0< if 2drop exit then lf-lmk-head 2dup @ swap 1+ =
  if swap lf-lmk-link-cell @ swap ! else 2drop 0 lf-lmk-built ! then ;

\ Giving facts up: those of nodes at and above count, after a rollback
\ to count; all of them; and at each public word, those of nodes no longer
\ there or made again since (their identity differs; as records go and
\ come back from the top, the highest node with facts tells).
: lf-lmk-pop ( -- ) -1 lf-lmk-known +! lf-lmk-known @ lf-lmk-unlink ;
: lf-lmk-truncate ( count -- )
  0 max begin lf-lmk-known @ over > while lf-lmk-pop repeat drop ;
: lf-lmk-forget ( -- ) 0 lf-lmk-truncate ;
: lf-lmk-current? ( -- flag )
  lf-lmk-known @ ?dup 0= if true exit then
  1- dup lf-lmk-stamp-cell @ swap lf-lmk-identity = ;
: lf-lmk-sync ( -- )
  lf-level-count @ lf-lmk-truncate begin lf-lmk-current? 0= while lf-lmk-pop repeat ;

\ ---------------------------------------------------------------------------
\ Facts of one node, from its children's. A node with an unknown tag or a
\ child that is not earlier (possible only off the validated graphs) is
\ its own class, never equal to another node, and has no flags.
: lf-lmk-earlier? ( child index -- flag ) 0 swap within ;
: lf-lmk-shape? ( index -- flag )
  dup lf-level-slot node@ rot case
    lf-level-tag-zero of 2drop drop true endof
    lf-level-tag-param of 2drop drop true endof
    lf-level-tag-succ of drop swap lf-lmk-earlier? endof
    dup lf-level-binary-tag? if >r rot tuck lf-lmk-earlier? -rot lf-lmk-earlier? and r>
    else >r 2drop drop false r> then endcase ;
\ Two nodes alike: same tag and the same parameter ID or child classes.
: lf-lmk-firsts ( i j -- f f' ) lf-level-first@ swap lf-level-first@ swap ;
: lf-lmk-seconds ( i j -- s s' ) lf-level-second@ swap lf-level-second@ swap ;
: lf-lmk-classes= ( x y -- flag ) lf-lmk-class@ swap lf-lmk-class@ = ;
: lf-lmk-children= ( i j -- flag )
  2dup lf-lmk-firsts lf-lmk-classes= -rot lf-lmk-seconds lf-lmk-classes= and ;
: lf-lmk-fields= ( i j tag -- flag )
  case lf-level-tag-zero of 2drop true endof
    lf-level-tag-param of lf-lmk-firsts = endof
    lf-level-tag-succ of lf-lmk-firsts lf-lmk-classes= endof
    >r lf-lmk-children= r> endcase ;
: lf-lmk-tags ( i j -- tag tag' ) lf-level-tag@ swap lf-level-tag@ swap ;
: lf-lmk-alike? ( i j -- flag )
  dup lf-lmk-shape? 0= if 2drop false exit then
  2dup lf-lmk-tags over = if lf-lmk-fields= else drop 2drop false then ;
\ A well-shaped node's key: its parameter's ID, or its children's
\ classes (none for zero), hashed with its tag; never negative.
: lf-lmk-child-classes ( index -- a b )
  dup lf-level-first@ lf-lmk-class@ swap lf-level-second@ lf-lmk-class@ ;
: lf-lmk-key ( index -- a b )
  dup lf-level-tag@ case
    lf-level-tag-zero of drop 0 0 endof
    lf-level-tag-param of lf-level-first@ 0 endof
    lf-level-tag-succ of lf-level-first@ lf-lmk-class@ 0 endof
    >r lf-lmk-child-classes r> endcase ;
: lf-lmk-hash ( index -- h )
  dup lf-level-tag@ 1000003 swap fnv-step swap lf-lmk-key >r fnv-step r> fnv-step
  max-n and ;
\ The class of index: an earlier node alike to it, found in its bucket
\ (the index holds one node of each class, the class itself), which it
\ then joins; or index itself, a new class, which goes into the index.
\ Every node of the bucket is compared (lf-lmk-alike?), its hash is not
\ trusted to tell nodes apart.
: lf-lmk-match? ( index h j -- index h j flag ) 2 pick over lf-lmk-alike? ;
: lf-lmk-next ( j -- j' ) lf-lmk-link-cell @ 1- ;
: lf-lmk-find ( index h -- class )
  dup lf-lmk-head @ 1- begin dup 0< 0= while
    lf-lmk-match? if nip nip exit then lf-lmk-next
  repeat 2drop ;
: lf-lmk-new-class ( index h -- index ) over >r lf-lmk-insert r> ;
: lf-lmk-old-class ( index h class -- class ) nip swap lf-lmk-not-class ;
: lf-lmk-class-of ( index -- class )
  lf-lmk-index-ready dup lf-lmk-hash 2dup lf-lmk-find
  dup 3 pick = if drop lf-lmk-new-class else lf-lmk-old-class then ;
\ Flags: zero none; a parameter has one; succ is never zero; max is never
\ zero when either side is not; imax when its right side is not.
: lf-lmk-child-flags ( index -- first second )
  dup lf-level-first@ lf-lmk-flags@ swap lf-level-second@ lf-lmk-flags@ ;
: lf-lmk-imax-flags ( index -- flags )
  lf-lmk-child-flags swap lf-lmk-param and or ;
: lf-lmk-succ-flags ( index -- flags )
  lf-level-first@ lf-lmk-flags@ lf-lmk-param and lf-lmk-nonzero or ;
: lf-lmk-flags-of ( index -- flags )
  dup lf-level-tag@ case
    lf-level-tag-zero of drop 0 endof
    lf-level-tag-param of drop lf-lmk-param endof
    lf-level-tag-succ of lf-lmk-succ-flags endof
    lf-level-tag-max of lf-lmk-child-flags or endof
    >r lf-lmk-imax-flags r> endcase ;
: lf-lmk-facts-of ( index -- class flags )
  dup lf-lmk-shape? if dup lf-lmk-class-of swap lf-lmk-flags-of else dup lf-lmk-not-class 0 then ;
: lf-lmk-compute ( index -- )
  dup >r lf-lmk-facts-of r@ lf-lmk-flags-cell ! r@ lf-lmk-class-cell !
  r@ lf-lmk-identity r> lf-lmk-stamp-cell ! ;
\ Make the facts current up to index (nothing when they already are),
\ one node at a time, so that the count of facts is always exact.
: lf-lmk-upto ( limit -- ) lf-lmk-known @ ?do i lf-lmk-compute 1 lf-lmk-known +! loop ;
: lf-lmk-fill ( index -- ) 1+ dup lf-lmk-known @ > if lf-lmk-upto else drop then ;
: lf-lmk-class ( level -- class ) dup lf-lmk-fill lf-lmk-class@ ;
: lf-lmk-flags ( level -- flags ) dup lf-lmk-fill lf-lmk-flags@ ;

\ ---------------------------------------------------------------------------
\ Lean's level queries. lf-lmk-same? is operator==: structural equality,
\ parameters by ID.
: lf-lmk-same? ( l1 l2 -- flag ) lf-lmk-class swap lf-lmk-class = ;
: lf-lmk-nonzero? ( level -- flag ) lf-lmk-flags lf-lmk-nonzero and 0<> ;
: lf-lmk-param? ( level -- flag ) lf-lmk-flags lf-lmk-param and 0<> ;
: lf-lmk-zero? ( level -- flag ) lf-level-tag@ lf-level-tag-zero = ;
: lf-lmk-succ? ( level -- flag ) lf-level-tag@ lf-level-tag-succ = ;
: lf-lmk-max? ( level -- flag ) lf-level-tag@ lf-level-tag-max = ;
\ to_offset: the level under all its successors, and how many there are.
: lf-lmk-offset ( level -- base k )
  0 begin over lf-lmk-succ? while swap lf-level-first@ swap 1+ repeat ;
: lf-lmk-explicit? ( level -- flag ) lf-lmk-offset drop lf-lmk-zero? ;
\ is_one: succ zero.
: lf-lmk-one? ( level -- flag )
  dup lf-lmk-succ? if lf-level-first@ lf-lmk-zero? else drop false then ;

\ ---------------------------------------------------------------------------
\ mk_max and mk_imax as rule tables, in Lean's order. Each rule gives the
\ choice it makes, or 0 to pass to the next: 1 the first argument, 2 the
\ second, 3 (mk_imax only) mk_max of both. No rule applying is 0: a new
\ raw node.
: lf-lmk-choose ( l1 l2 rules n -- choice )
  cells over + swap ?do 2dup i @ execute ?dup if nip nip unloop exit then
  cell +loop 2drop 0 ;
\ Both explicit (82-83): the deeper, the first on a tie (get_depth of an
\ explicit level is its number of successors).
: lf-lmk-deeper ( l1 l2 -- choice )
  lf-lmk-offset nip swap lf-lmk-offset nip > if 2 else 1 then ;
: lf-lmk-explicit-rule ( l1 l2 -- choice )
  2dup lf-lmk-explicit? swap lf-lmk-explicit? and if lf-lmk-deeper else 2drop 0 then ;
\ Equal (84-85, and imax 119-120): the first.
: lf-lmk-same-rule ( l1 l2 -- choice ) lf-lmk-same? 1 and ;
\ A zero argument (86-89): the other one.
: lf-lmk-zero-rule ( l1 l2 -- choice )
  swap lf-lmk-zero? if drop 2 else lf-lmk-zero? 1 and then ;
\ l2 is a max with l1 as one argument (90-91).
: lf-lmk-in-max? ( l1 l2 -- flag )
  dup lf-lmk-max? 0= if 2drop false exit then
  2dup lf-level-first@ lf-lmk-same? if 2drop true exit then
  lf-level-second@ lf-lmk-same? ;
: lf-lmk-max-rule ( l1 l2 -- choice )
  2dup lf-lmk-in-max? if 2drop 2 else swap lf-lmk-in-max? 1 and then ;
\ The same base under different offsets (95-99): the larger offset.
: lf-lmk-bases ( l1 l2 -- base1 base2 k1 k2 )
  lf-lmk-offset rot lf-lmk-offset 2swap rot swap ;
: lf-lmk-base-rule ( l1 l2 -- choice )
  lf-lmk-bases 2swap lf-lmk-same? if > if 1 else 2 then else 2drop 0 then ;
create lf-lmk-max-rules
  ' lf-lmk-explicit-rule , ' lf-lmk-same-rule , ' lf-lmk-zero-rule ,
  ' lf-lmk-max-rule , ' lf-lmk-base-rule ,
\ mk_imax: a right side never zero gives mk_max (113-114); a zero right
\ side is the result (115-116); so is the right side when the left is zero
\ or one (117-118); equal sides give the left (119-120).
: lf-lmk-nonzero-rule ( l1 l2 -- choice ) nip lf-lmk-nonzero? 3 and ;
: lf-lmk-right-zero-rule ( l1 l2 -- choice ) nip lf-lmk-zero? 2 and ;
: lf-lmk-low-rule ( l1 l2 -- choice ) drop dup lf-lmk-zero? swap lf-lmk-one? or 2 and ;
create lf-lmk-imax-rules
  ' lf-lmk-nonzero-rule , ' lf-lmk-right-zero-rule , ' lf-lmk-low-rule ,
  ' lf-lmk-same-rule ,
: lf-lmk-max-choice ( l1 l2 -- choice ) lf-lmk-max-rules 5 lf-lmk-choose ;
: lf-lmk-imax-choice ( l1 l2 -- choice ) lf-lmk-imax-rules 4 lf-lmk-choose ;

\ The chosen argument; a new raw node can fail (full store or spent
\ serial), recorded by lf-level-add.
: lf-lmk-pick ( l1 l2 choice -- level ) first-or-second ;
: lf-lmk-max ( l1 l2 -- level true | false )
  2dup lf-lmk-max-choice ?dup if lf-lmk-pick true else lf-level-max then ;
: lf-lmk-imax ( l1 l2 -- level true | false )
  2dup lf-lmk-imax-choice case 0 of lf-level-imax endof 3 of lf-lmk-max endof
    >r r@ lf-lmk-pick true r> endcase ;
\ Whether mk_max or mk_imax (tag) of two levels gives anything but a new
\ node of that tag over them.
: lf-lmk-simplifies? ( l1 l2 tag -- flag )
  lf-level-tag-max = if lf-lmk-max-choice else lf-lmk-imax-choice then 0<> ;

\ ---------------------------------------------------------------------------
\ Public words, each on two live levels of a valid store; any other input
\ gives false (or, for equality, false) without reading a node.
: lf-lmk-begin? ( l1 l2 -- l1 l2 flag )
  2dup lf-level-pair-valid? dup if lf-lmk-sync then ;
\ Lean's operator== on two levels.
: lf-level-same? ( l1 l2 -- flag ) lf-lmk-begin? if lf-lmk-same? else 2drop false then ;
\ Lean's mk_max and mk_imax: an argument, or a new node (false when the
\ level store is full or its serial spent).
: lf-level-mk-max ( l1 l2 -- level true | false )
  lf-lmk-begin? if lf-lmk-max else 2drop false then ;
: lf-level-mk-imax ( l1 l2 -- level true | false )
  lf-lmk-begin? if lf-lmk-imax else 2drop false then ;
