\ Lean's replace memo (replace_fn.cpp 16-40, at the referee commit
\ eb6cafb7: m_cache, a node's result per offset, kept for the rest of one
\ call) as ADR 0016 C4's substitution memo (compact-store plan step S6,
\ plan task 6.5.5): one table per pass kind and context, reused by every
\ call and never allocated per call. [kernel] code: not through the
\ review gate (AGENTS.md).
\
\ An entry is a key -- a node's identity, the offset it was met at, and
\ the call's stamp -- and a value: the result and the result's identity.
\ A pass begins a call with a stamp (lf-rmemo-begin), finds (lf-rmemo@) and
\ keeps (lf-rmemo!) results while it runs, and ends the call
\ (lf-rmemo-end): its entries are taken out again (Algorithm R, as
\ lib/htab.fs removes), so the next call starts as Lean's, with no entry,
\ unless the call was stamped (a stamp other than 0) and succeeded: then
\ its entries stay, for later calls with the same stamp. A stamp names
\ the substitution: a caller stamps only calls whose result for a node and
\ offset the stamp alone fixes (mixed-open.fs: closing a term with the
\ free variables of an inference scope, named by its innermost one; a new
\ binder always makes a new free variable, and identities never repeat).
\ Keys are identities, never indices, and a value is given only while its
\ node still has the identity kept with it: a node discarded since, or an
\ index taken again by another node, is a miss, never a wrong result.
\ Lean keeps only shared nodes' results (is_likely_unshared); the memo
\ keeps every result its pass gives it, which changes the work, never the
\ result: a pass's result for a node and offset is a function of them.
\ The memo costs no fuel (Lean's hash lookups cost no steps either).
\
\ The table and its entries are made when first needed (a context that
\ never substitutes holds no heap block) and freed with the context; a
\ table the heap cannot make or grow keeps nothing more: a miss. Stamped
\ entries are emptied with lf-rmemo-empty (inference does when a job
\ starts) and when a stamped call begins with more than lf-rmemo-cap
\ entries, which bounds the memory (about 60 bytes an entry).
\
\ Interface: /lf-rmemo, lf-rmemo-begin ( stamp memo -- ), lf-rmemo@ ( node
\ offset memo -- result true | false ), lf-rmemo! ( result node offset
\ memo -- ), lf-rmemo-end ( outcome memo -- ), lf-rmemo-empty ( memo -- ),
\ lf-rmemo-release ( memo -- ), lf-rmemo-count ( memo -- n ), and Lean's
\ update rule lf-replace-update ( r1 node r2 -- result outcome ).
\ Example (mixed-open.fs): /lf-rmemo context-record: lf-open-memo, then
\ in a pass 0 lf-open-memo lf-rmemo-begin, node offset lf-open-memo
\ lf-rmemo@ before a visit, result node offset lf-open-memo lf-rmemo!
\ after it, and outcome lf-open-memo lf-rmemo-end when the pass ends.
\ State: none of its own; every word takes a memo record, a member of
\ the checker context that its pass declares. The hooks are shared and
\ read-only.

require ../lib/lib.fs
require ../lib/hash32.fs
require ../lib/htab.fs
require ../lib/slab.fs
require ../core/terms.fs
require ./mixed-rebuild.fs

\ The table comes first, so that its hooks find the memo at its address.
\ The record also holds the entry being found or kept: its key (three
\ cells), then its value (two cells), as an entry holds them.
5 cells constant /lf-rment
begin-structure /lf-rmemo
  /htab +field lf-rmemo-table
  /slab +field lf-rmemo-entries
  /lf-rment +field lf-rmemo-key   \ the entry being found or kept
  field: lf-rmemo-stamp           \ the call's stamp
  field: lf-rmemo-base            \ the entries before the call
end-structure
1 20 lshift constant lf-rmemo-cap

\ Entries and their hashes (a hash is only a hint: lib/htab.fs).
: lf-rment ( n memo -- addr ) lf-rmemo-entries slab-at ;
: lf-rment-hash ( addr -- h )
  0 over @ hash-step over cell+ @ hash-step swap 2 cells + @ hash-step ;
: lf-rmemo-rehash ( n htab -- h ) lf-rment lf-rment-hash ;
: lf-rmemo-same ( n key htab -- flag ) rot swap lf-rment 3 cells tuck compare 0= ;
create lf-rmemo-hooks /htab-hooks allot
' lf-rmemo-rehash ' lf-rmemo-same lf-rmemo-hooks htab-hooks!

\ Making, emptying and freeing. A large table goes back to a small one
\ when emptied, so an emptying costs little whatever a call needed.
1024 constant lf-rmemo-small
: lf-rmemo-live? ( memo -- flag ) lf-rmemo-table htab-live? ;
: lf-rmemo-count ( memo -- n )
  dup lf-rmemo-live? if lf-rmemo-entries slab-count else drop 0 then ;
: lf-rmemo-make ( memo -- )
  dup 4 lf-rmemo-hooks rot lf-rmemo-table htab-init ok? 0= if drop exit then
  /lf-rment dup slab-limit-max rot lf-rmemo-entries slab-init drop ;
: lf-rmemo-release ( memo -- )
  dup lf-rmemo-table htab-free lf-rmemo-entries slab-free ;
: lf-rmemo-small? ( memo -- flag ) lf-rmemo-table htab-slots lf-rmemo-small <= ;
: lf-rmemo-clear ( memo -- ) dup lf-rmemo-table htab-clear lf-rmemo-entries slab-clear ;
: lf-rmemo-empty ( memo -- )
  dup lf-rmemo-live? 0= if drop exit then
  dup lf-rmemo-small? if lf-rmemo-clear exit then
  dup lf-rmemo-release lf-rmemo-make ;

\ A call. Its entries are those from the base on.
: lf-rmemo-crowded? ( stamp memo -- flag ) lf-rmemo-count lf-rmemo-cap > swap 0<> and ;
: lf-rmemo-ready ( stamp memo -- )
  dup lf-rmemo-live? 0= if lf-rmemo-make drop exit then
  tuck lf-rmemo-crowded? if lf-rmemo-empty else drop then ;
: lf-rmemo-begin ( stamp memo -- )
  2dup lf-rmemo-ready tuck lf-rmemo-stamp !
  dup lf-rmemo-count swap lf-rmemo-base ! ;
\ Taking out the entries from the base on, newest first.
: lf-rmemo-forget ( n memo -- )
  2dup lf-rment lf-rment-hash swap lf-rmemo-table htab-remove drop ;
: lf-rmemo-pop ( memo -- )
  dup lf-rmemo-count 1- over lf-rmemo-forget -1 swap lf-rmemo-entries slab-commit ;
: lf-rmemo-above? ( memo -- flag ) dup lf-rmemo-count swap lf-rmemo-base @ > ;
: lf-rmemo-drop ( memo -- ) begin dup lf-rmemo-above? while dup lf-rmemo-pop repeat drop ;
\ The end of a call with its outcome: a stamped call that succeeded keeps
\ its entries; any other call's are taken out.
: lf-rmemo-keeps? ( outcome memo -- flag ) lf-rmemo-stamp @ 0<> swap ok? and ;
: lf-rmemo-end ( outcome memo -- )
  dup lf-rmemo-live? 0= if 2drop exit then
  tuck lf-rmemo-keeps? if drop else lf-rmemo-drop then ;

\ Finding. The key: the node's identity (a node without one has no
\ entry), the offset and the call's stamp.
: lf-rmemo-place ( offset memo -- ) dup lf-rmemo-stamp @ rot rot lf-rmemo-key cell+ 2! ;
: lf-rmemo-key! ( node offset memo -- flag )
  >r swap lf-term-identity 0= if drop r> drop false exit then
  r@ lf-rmemo-key ! r> lf-rmemo-place true ;
: lf-rmemo-find ( memo -- n true | i false )
  dup >r lf-rmemo-key dup lf-rment-hash r> lf-rmemo-table htab-find ;
\ An entry's result while it has the identity kept with it.
: lf-rment-result ( addr -- result true | false )
  3 cells + dup @ swap cell+ @ over lf-term-identity if = else drop false then
  dup 0= if nip then ;
: lf-rmemo@ ( node offset memo -- result true | false )
  dup lf-rmemo-live? 0= if drop 2drop false exit then
  dup >r lf-rmemo-key! 0= if r> drop false exit then
  r@ lf-rmemo-find if r> lf-rment lf-rment-result else r> 2drop false then ;

\ Keeping: the value into the record beside the key (a result without an
\ identity is not kept), then into the entry found, else into a new entry
\ put at the empty slot the find gave (nothing changes the table in
\ between).
: lf-rmemo-value! ( result memo -- flag )
  >r dup lf-term-identity 0= if r> 2drop false exit then
  r@ lf-rmemo-key 4 cells + ! r> lf-rmemo-key 3 cells + ! true ;
: lf-rmemo-update ( memo n -- )
  over lf-rmemo-key 3 cells + swap rot lf-rment 3 cells + 2 cells move ;
: lf-rmemo-copy ( memo n -- ) swap dup lf-rmemo-key -rot lf-rment /lf-rment move ;
: lf-rmemo-add ( i memo -- )
  1 over lf-rmemo-entries slab-claim ok-then? 0= if drop 2drop exit then
  2dup lf-rmemo-copy -rot lf-rmemo-table htab-put ;
: lf-rmemo-put ( memo -- )
  dup lf-rmemo-table htab-ready ok? 0= if drop exit then
  dup lf-rmemo-find if lf-rmemo-update else swap lf-rmemo-add then ;
: lf-rmemo! ( result node offset memo -- )
  dup lf-rmemo-live? 0= if 2drop 2drop exit then
  dup >r lf-rmemo-key! 0= if r> 2drop exit then
  r@ lf-rmemo-value! if r> lf-rmemo-put else r> drop then ;

\ Lean's update_app and update_binding (expr.cpp): the node itself when
\ both children came back unchanged, otherwise a new node of its tag (a
\ full store is full).
: lf-replace-update ( r1 node r2 -- result outcome )
  >r 2dup lf-term-first@ = over lf-term-second@ r@ = and
  if nip r> drop outcome-ok else r> lf-rebuild-build then ;
\ A visit's step (lib/frame.fs) that returns a result the memo gave.
: lf-replace-recall ( node frames result -- result outcome frames 0 )
  rot drop outcome-ok rot 0 ;
\ A visit's step that returns its node unchanged.
: lf-replace-same ( node frames -- node outcome frames 0 ) dup >r lf-rebuild-keep r> 0 ;
