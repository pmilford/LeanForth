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
\ The table is a memo of lib/memo.fs (keys of three cells, values of two,
\ whose check hook gives a value only while its result has the identity
\ kept with it), made when first needed (a context that never substitutes
\ holds no heap block) and freed with the context; a table the heap
\ cannot make or grow keeps nothing more: a miss. Stamped entries are
\ emptied with lf-rmemo-empty (inference does when a job starts) and when
\ a stamped call begins with more than lf-rmemo-cap entries, which bounds
\ the memory (about 50 bytes an entry).
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
\ the checker context that its pass declares.

require ../lib/lib.fs
require ../lib/memo.fs
require ../core/terms.fs
require ./mixed-rebuild.fs

\ The memo, the key being found or kept (built and used by one word), the
\ call's stamp and the entries before the call.
3 constant lf-rmemo-kcells
begin-structure /lf-rmemo
  /memo +field lf-rmemo-table
  lf-rmemo-kcells cells +field lf-rmemo-key
  field: lf-rmemo-stamp
  field: lf-rmemo-base
end-structure
1 20 lshift constant lf-rmemo-cap

\ A kept value, a node and its identity (two cells at a-addr), holds while
\ the node has that identity (also caches.fs's check of its results).
: lf-kept-node? ( a-addr -- flag )
  dup @ lf-term-identity if swap cell+ @ = else drop false then ;

\ Making, emptying and freeing (lib/memo.fs: a large table goes back to a
\ small one when emptied, so an emptying costs little whatever a call
\ needed).
: lf-rmemo-live? ( memo -- flag ) lf-rmemo-table memo-live? ;
: lf-rmemo-count ( memo -- n ) lf-rmemo-table memo-count ;
: lf-rmemo-make ( memo -- )
  lf-rmemo-table >r lf-rmemo-kcells 2 r@ memo-init drop
  ['] lf-kept-node? r> memo-check! ;
: lf-rmemo-release ( memo -- ) lf-rmemo-table memo-free ;
: lf-rmemo-empty ( memo -- ) lf-rmemo-table memo-empty ;

\ A call. Its entries are those from the base on.
: lf-rmemo-crowded? ( stamp memo -- flag ) lf-rmemo-count lf-rmemo-cap > swap 0<> and ;
: lf-rmemo-ready ( stamp memo -- )
  dup lf-rmemo-live? 0= if lf-rmemo-make drop exit then
  tuck lf-rmemo-crowded? if lf-rmemo-empty else drop then ;
: lf-rmemo-begin ( stamp memo -- )
  2dup lf-rmemo-ready tuck lf-rmemo-stamp !
  dup lf-rmemo-count swap lf-rmemo-base ! ;
\ The end of a call with its outcome: a stamped call that succeeded keeps
\ its entries; any other call's are taken out, newest first.
: lf-rmemo-keeps? ( outcome memo -- flag ) lf-rmemo-stamp @ 0<> swap ok? and ;
: lf-rmemo-drop ( memo -- ) dup lf-rmemo-base @ swap lf-rmemo-table memo-cut ;
: lf-rmemo-end ( outcome memo -- )
  dup lf-rmemo-live? 0= if 2drop exit then
  tuck lf-rmemo-keeps? if drop else lf-rmemo-drop then ;

\ Finding. The key: the node's identity (a node without one has no
\ entry), the offset and the call's stamp.
: lf-rmemo-place ( offset memo -- ) dup lf-rmemo-stamp @ rot rot lf-rmemo-key cell+ 2! ;
: lf-rmemo-key! ( node offset memo -- flag )
  >r swap lf-term-identity 0= if drop r> drop false exit then
  r@ lf-rmemo-key ! r> lf-rmemo-place true ;
: lf-rmemo-entry ( memo -- key memo' ) dup lf-rmemo-key swap lf-rmemo-table ;
: lf-rmemo@ ( node offset memo -- result true | false )
  dup >r lf-rmemo-key! 0= if r> drop false exit then
  r> lf-rmemo-entry memo-find dup if @ true then ;

\ Keeping: a result with an identity, into the entry found or a new one.
: lf-rmemo-kept ( result id memo -- )
  lf-rmemo-entry memo-put ok-then? if tuck cell+ ! ! else drop 2drop then ;
: lf-rmemo! ( result node offset memo -- )
  dup >r lf-rmemo-key! 0= if r> 2drop exit then
  dup lf-term-identity if r> lf-rmemo-kept else r> 2drop then ;

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
