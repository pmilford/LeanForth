\ A ranked-record index (simp group 4, step 2; plan
\ .claude/work/briefs/simp-group-4-architect.md sections 1 and 3): a
\ discrimination tree (front/discr-tree.fs) of values that records of the
\ elaboration data describe, each with its keys and its rank, its place
\ in a depth-first walk of its root key's trie in pinned Lean (FE1E §3.2,
\ SIMP_DATA.md §3). Each root is built at its first query, its values
\ inserted in rank order, so that every child list and value list is in
\ Lean's stored order. Moved out of front/instances.fs (FE1e3, MF2),
\ which uses it for the instance table; simp's default set
\ (front/simp/default-set.fs) is its second user. LeanForth-specific:
\ Lean's keys and the data's ranks. Untrusted: an index only chooses
\ candidates.
\
\ An index is a /rix record its user owns (in its checker-context
\ record); its first field is its tree, so its address is the tree's
\ (lf-rix-tree is the identity) and the tree's builder finds it. A kind,
\ a table of seven execution tokens laid once (rix-kind, below), says
\ what its values are:
\   count ( rix -- n ) the values, and value ( k rix -- v ) the k-th, k
\     from 0 (the index given, so that one kind serves several);
\     a value v from 0 up is a record of the user's, one below 0 a value
\     the library's export lacks (left out: lf-rix-left-out?);
\   records ( -- n ) the records, 0 .. n-1, each with a status cell;
\   keys ( v -- k n ) its keys, front/elab-keys.fs's, one term, the first
\     its root key; rank ( v -- rank );
\   checks ( rix -- outcome ) run on a root's values once placed by rank
\     (lf-rix-each walks them), before any is inserted;
\   entry ( v -- x outcome ) the cell the tree holds for v (an instance
\     itself; a simp lemma the theorem record made for it).
\ - lf-rix-kind! ( kind rix -- ): the index's kind, before lf-rix-roots.
\ - lf-rix-roots ( rix -- outcome ): once until lf-rix-free: the tree
\   made with its builder, a zero status cell per record (lib/slab.fs's
\   slab-zeroed) and every value's root key declared, a root with no trie
\   yet; ok, or why not (full), nothing counted as done. An index of kind
\   0 is a plain tree (values inserted by lf-dtree-insert alone): ok.
\ - The builder, at a root's first query (or lf-rix-force): every value
\   whose root key is the root's placed at its rank; their number must
\   fill every rank (the reader refuses two values of one rank; a gap is
\   invalid here); then the kind's checks; then each value's entry
\   inserted in rank order (lf-dtree-insert). A failure keeps nothing of
\   the root (discr-tree.fs's rule): its next query builds it anew.
\ - lf-rix-force ( k rix -- outcome ): root key k's trie built now when it
\   has a root and no trie (a value inserted later goes after the root's
\   data values, as Lean's insertion into a full tree does); ok for a key
\   no value has.
\ - lf-rix-match ( e rix out -- outcome ): getMatchWithExtra
\   (discr-tree.fs's lf-dtree-match-extra) after lf-rix-roots;
\   lf-rix-unify ( e rix out -- outcome ): getUnify (lf-dtree-unify).
\ - lf-rix-each ( xt rix -- outcome ): xt ( v -- outcome ) on each record
\   (not a left-out value) of the root being built, in rank order, while
\   ok: the kind's checks' walk.
\ - lf-rix-status ( v rix -- s ), lf-rix-status-at ( v rix -- a-addr )
\   (valid until lf-rix-free), lf-rix-record? ( v rix -- flag ): record v
\   has a status cell (0 until its user stores one).
\ - lf-rix-left-out? ( v -- flag ); lf-rix-tree ( rix -- tree );
\   lf-rix-free ( rix -- ): everything given back, the roots forgotten,
\   the kind kept.
\ Outcomes: ok; invalid for a gap in a root's ranks; the tree's (its
\ queries' keys, full) and the kind's hooks' otherwise. Not reentrant on
\ one index: the builder places a root's values in the index's one slab.
\ State: each index's record (its tree, its slabs, the root being built,
\ whether its roots are made); none of the module's own.
\ Loads in decimal whatever BASE is, then restores it.
\
\ Example (a kind of the instance table's, front/instances.fs):
\   ' it-count ' it-value-of ' it-records# ' it-keys ' it-rank ' it-checks
\     ' it-entry rix-kind, constant it-kind
\   it-kind it-rix lf-rix-kind!  it-rix lf-rix-roots  ...
\   type it-rix it-out lf-rix-unify

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/slab.fs
require ./elab-keys.fs
require ./discr-tree.fs

begin-structure /rix-kind
  field: rk-count   field: rk-value   field: rk-records   field: rk-keys
  field: rk-rank    field: rk-checks  field: rk-entry
end-structure
\ A kind's table laid at HERE from its seven tokens, in /rix-kind's
\ order (a constant table: no state).
: rix-kind, ( count value records keys rank checks entry -- kind )
  here /rix-kind allot dup >r /rix-kind cell - + r@ swap do i ! -1 cells +loop r> ;
begin-structure /rix
  /dtree +field rix-tree   \ first: the tree's address is the index's
  /slab +field rix-ranked  \ the root being built: its values by rank
  /slab +field rix-status  \ a cell per record
  field: rix-kind          \ its kind's table
  field: rix-root          \ the root key being built
  field: rix-made          \ true once lf-rix-roots has made the roots
end-structure
: lf-rix-tree ( rix -- tree ) ;
: lf-rix-left-out? ( v -- flag ) 0< ;
: lf-rix-kind! ( kind rix -- ) rix-kind ! ;
: lf-rix-free ( rix -- )
  dup lf-dtree-free dup rix-ranked slab-free dup rix-status slab-free
  false swap rix-made ! ;

\ ---- The kind's hooks.
: rk@ ( rix field -- xt ) swap rix-kind @ + @ ;
: rix-values# ( rix -- n ) dup 0 rk-count rk@ execute ;
: rix-value ( k rix -- v ) dup 0 rk-value rk@ execute ;
: rix-records# ( rix -- n ) 0 rk-records rk@ execute ;
: rix-keys ( v rix -- k n ) 0 rk-keys rk@ execute ;
: rix-rank ( v rix -- rank ) 0 rk-rank rk@ execute ;
: rix-checks ( rix -- outcome ) dup 0 rk-checks rk@ execute ;
: rix-entry ( v rix -- x outcome ) 0 rk-entry rk@ execute ;

\ ---- Status cells, one per record.
: lf-rix-status-at ( v rix -- a-addr ) rix-status slab-at ;
: lf-rix-status ( v rix -- s ) lf-rix-status-at @ ;
: lf-rix-record? ( v rix -- flag ) rix-status slab-count index? ;

\ ---- A root's values placed by rank (rix-ranked), counted; their number
\ must be the ranks' (a gap would read as a left-out value, -1).
: rix-ranked@ ( r rix -- v ) rix-ranked slab-at @ ;
: rix-place ( v rix -- outcome ) 2dup rix-rank swap rix-ranked slab-cell-put ;
: rix-under? ( v rix -- flag ) tuck rix-keys drop swap rix-root @ elab-key= ;
: rix-counted ( n outcome -- n' outcome ) dup ok? if swap 1+ swap then ;
: rix-gathered ( n k rix -- n' outcome )
  tuck rix-value swap 2dup rix-under?
  if rix-place rix-counted else 2drop outcome-ok then ;
: rix-gapless ( n outcome rix -- outcome )
  -rot ok-then? if swap rix-ranked slab-count = flag>outcome else nip then ;
: rix-gather ( rix -- outcome )
  dup rix-ranked slab-clear >r 0 r@ rix-values# r@ ['] rix-gathered ok-fold
  r> rix-gapless ;

\ ---- The checks' walk, then the entries inserted in rank order.
: rix-on-rank ( xt rix r -- xt rix outcome )
  over rix-ranked@ dup 0< if drop outcome-ok exit then >r over r> swap execute ;
: lf-rix-each ( xt rix -- outcome )
  dup rix-ranked slab-count ['] rix-on-rank ok-each nip nip ;
: rix-insert-value ( v rix -- outcome )
  2dup rix-keys 2swap >r r@ rix-entry
  ok-then? if r> lf-dtree-insert else r> drop nip nip then ;
: rix-insert-rank ( rix r -- rix outcome ) over rix-ranked@ over rix-insert-value ;
: rix-insert-ranked ( rix -- outcome )
  dup rix-ranked slab-count ['] rix-insert-rank ok-each nip ;
\ The builder (discr-tree.fs's lf-dtree-builder!): the tree is the index;
\ its values gathered, checked, inserted.
: rix-build ( r tree -- outcome )
  tuck lf-dtree-root-key over rix-root !
  dup rix-gather ['] rix-checks ok-with ['] rix-insert-ranked ok-with nip ;

\ ---- The roots: the slabs, the tree with its builder, every value's root.
: rix-slab-ready ( slab -- outcome )
  dup slab-live? if drop outcome-ok exit then 1 cells dup slab-limit-max rot slab-init ;
: rix-slabs-ready ( rix -- outcome )
  dup rix-ranked rix-slab-ready ok-then? if rix-status rix-slab-ready then ;
: rix-tree-ready ( rix -- outcome )
  dup lf-dtree-ready ok-then? if ['] rix-build swap lf-dtree-builder! outcome-ok then ;
: rix-status-ready ( rix -- outcome ) dup rix-records# swap rix-status slab-zeroed ;
: rix-value-root ( rix k -- rix outcome )
  over rix-value over rix-keys drop over lf-dtree-root-add nip ;
: rix-roots-made ( rix -- outcome ) ['] rix-values# ['] rix-value-root ok-each-of ;
: rix-made! ( rix outcome -- outcome ) ok-then? if true swap rix-made ! outcome-ok then ;
: lf-rix-roots ( rix -- outcome )
  dup rix-kind @ 0= over rix-made @ or if drop outcome-ok exit then
  dup dup rix-slabs-ready ['] rix-tree-ready ok-with ['] rix-status-ready ok-with
  ['] rix-roots-made ok-with nip rix-made! ;

\ ---- Queries.
: lf-rix-force ( k rix -- outcome )
  dup lf-rix-roots ok-then? if lf-dtree-force else nip then ;
: lf-rix-match ( e rix out -- outcome )
  over lf-rix-roots ok-then? if lf-dtree-match-extra else nip nip then ;
: lf-rix-unify ( e rix out -- outcome )
  over lf-rix-roots ok-then? if lf-dtree-unify else nip nip then ;

base !   \ the BASE this file was loaded with
