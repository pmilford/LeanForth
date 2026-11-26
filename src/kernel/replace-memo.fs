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
\ (lf-rmemo-end). An unstamped call (stamp 0) keeps its entries in a
\ scratch memo of their own, keyed by the call's number in place of the
\ stamp (minus the count of unstamped calls begun), so no other call ever
\ finds them: the next call starts as Lean's, with no entry, as Lean
\ throws its cache away whole. The scratch memo is emptied in one step
\ (memo-empty) when an unstamped call begins with it holding more than
\ lf-rmemo-scratch-most entries, and its numbering begins again (group
\ kernel-speed-3, the prototype's P1; until then every entry was taken
\ out one by one at the call's end). A stamp is >= 0; a negative one is
\ taken as 0, so that it never names a scratch call's number. A stamped
\ call (a stamp above 0) keeps its entries in the main table; one that
\ fails has them taken out again (Algorithm R, as lib/htab.fs removes);
\ one that succeeds keeps them, for later calls with the same stamp. A
\ stamp names
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
\ The table and the scratch memo are memos of lib/memo.fs (keys of three
\ cells, values of two, whose check hook gives a value only while its
\ result has the identity kept with it), made when first needed (a context
\ that never substitutes holds no heap block) and freed with the context;
\ a memo the heap cannot make or grow keeps nothing more: a miss; each of
\ the two is made again, alone, when a call begins with it not live. A
\ call that THROWs (or never ends) leaves its entries: an unstamped call's
\ no later call finds, and the count stops showing them when the next
\ unstamped call begins (lf-rmemo-held!); a stamped call's stay in the
\ table. The passes' recovery after a THROW (lf-open-reset,
\ lf-mixed-rebuild-reset) empties both memos. Stamped entries are
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
\ call's stamp (an unstamped call's number, negative) and the entries
\ before the call; the scratch memo, the unstamped calls numbered since it
\ was last emptied, and its entries before the call in progress.
3 constant lf-rmemo-kcells
begin-structure /lf-rmemo
  /memo +field lf-rmemo-table
  lf-rmemo-kcells cells +field lf-rmemo-key
  field: lf-rmemo-stamp
  field: lf-rmemo-base
  /memo +field lf-rmemo-scratch
  field: lf-rmemo-calls
  field: lf-rmemo-held
end-structure
1 20 lshift constant lf-rmemo-cap
512 constant lf-rmemo-scratch-most

\ A kept value, a node and its identity (two cells at a-addr), holds while
\ the node has that identity (also caches.fs's check of its results).
: lf-kept-node? ( a-addr -- flag )
  dup @ lf-term-identity if swap cell+ @ = else drop false then ;

\ Making, emptying and freeing (lib/memo.fs: a large table goes back to a
\ small one when emptied, so an emptying costs little whatever a call
\ needed).
: lf-rmemo-live? ( memo -- flag )
  dup lf-rmemo-table memo-live? swap lf-rmemo-scratch memo-live? and ;
\ The entries a call may still find: the table's, and the scratch memo's
\ from the start of the unstamped call in progress (or of one that threw).
: lf-rmemo-unheld ( memo -- n ) dup lf-rmemo-scratch memo-count swap lf-rmemo-held @ - ;
: lf-rmemo-count ( memo -- n ) dup lf-rmemo-table memo-count swap lf-rmemo-unheld + ;
\ Each memo of the record, made, emptied or freed by xt ( memo -- ); the
\ scratch memo's numbering begins again whenever it is emptied.
: lf-rmemo-restart ( memo -- ) 0 over lf-rmemo-calls ! 0 swap lf-rmemo-held ! ;
: lf-rmemo-both ( memo xt -- )
  over lf-rmemo-table over execute over lf-rmemo-scratch swap execute lf-rmemo-restart ;
: lf-rmemo-shape ( memo -- )
  >r lf-rmemo-kcells 2 r@ memo-init drop ['] lf-kept-node? r> memo-check! ;
: lf-rmemo-release ( memo -- ) ['] memo-free lf-rmemo-both ;
\ Each memo made again only when it is not live (the heap refused it),
\ the other's entries kept; the scratch memo's numbering begins again
\ when it is made.
: lf-rmemo-mend ( memo' -- flag )
  dup memo-live? if drop false else dup memo-free lf-rmemo-shape true then ;
: lf-rmemo-make ( memo -- )
  dup lf-rmemo-table lf-rmemo-mend drop
  dup lf-rmemo-scratch lf-rmemo-mend if lf-rmemo-restart else drop then ;
: lf-rmemo-empty ( memo -- ) ['] memo-empty lf-rmemo-both ;

\ A call. A stamped call's entries are the table's from the base on; an
\ unstamped call is numbered (its stamp minus its number), after the
\ scratch memo is emptied when it holds more than lf-rmemo-scratch-most
\ entries or the numbers are spent.
: lf-rmemo-crowded? ( stamp memo -- flag ) lf-rmemo-count lf-rmemo-cap > swap 0<> and ;
: lf-rmemo-ready ( stamp memo -- )
  dup lf-rmemo-live? 0= if lf-rmemo-make drop exit then
  tuck lf-rmemo-crowded? if lf-rmemo-empty else drop then ;
: lf-rmemo-stamped ( stamp memo -- )
  tuck lf-rmemo-stamp ! dup lf-rmemo-table memo-count swap lf-rmemo-base ! ;
: lf-rmemo-spent? ( memo -- flag )
  dup lf-rmemo-scratch memo-count lf-rmemo-scratch-most >
  swap lf-rmemo-calls @ max-n = or ;
: lf-rmemo-sweep ( memo -- )
  dup lf-rmemo-spent? if dup lf-rmemo-scratch memo-empty dup lf-rmemo-restart then drop ;
: lf-rmemo-held! ( memo -- ) dup lf-rmemo-scratch memo-count swap lf-rmemo-held ! ;
: lf-rmemo-number ( memo -- )
  1 over lf-rmemo-calls +! dup lf-rmemo-calls @ negate swap lf-rmemo-stamp ! ;
: lf-rmemo-unstamped ( memo -- ) dup lf-rmemo-sweep dup lf-rmemo-held! lf-rmemo-number ;
: lf-rmemo-begin ( stamp memo -- )
  over 0< if nip 0 swap then
  2dup lf-rmemo-ready over if lf-rmemo-stamped else nip lf-rmemo-unstamped then ;
\ The end of a call with its outcome: a stamped call that succeeded keeps
\ its entries; any other stamped call's are taken out, newest first; an
\ unstamped call's are left where no other call finds them; nothing is
\ done when the memo the call keeps in is not live.
: lf-rmemo-scratch? ( memo -- flag ) lf-rmemo-stamp @ 0< ;
\ The memo a call's entries are in: the scratch memo for an unstamped
\ call, else the table, the record's first field.
0 lf-rmemo-table 0<> [if] .( replace-memo.fs: the table comes first) cr abort [then]
: lf-rmemo-in ( memo -- memo' ) dup lf-rmemo-scratch? 0 lf-rmemo-scratch and + ;
: lf-rmemo-keeps? ( outcome memo -- flag ) lf-rmemo-stamp @ 0<> swap ok? and ;
: lf-rmemo-drop ( memo -- ) dup lf-rmemo-base @ swap lf-rmemo-table memo-cut ;
: lf-rmemo-end ( outcome memo -- )
  dup lf-rmemo-in memo-live? 0= if 2drop exit then
  dup lf-rmemo-scratch? if nip lf-rmemo-held! exit then
  tuck lf-rmemo-keeps? if drop else lf-rmemo-drop then ;

\ Finding. The key: the node's identity (a node without one has no
\ entry), the offset and the call's stamp.
: lf-rmemo-place ( offset memo -- ) dup lf-rmemo-stamp @ rot rot lf-rmemo-key cell+ 2! ;
: lf-rmemo-key! ( node offset memo -- flag )
  >r swap lf-term-identity 0= if drop r> drop false exit then
  r@ lf-rmemo-key ! r> lf-rmemo-place true ;
: lf-rmemo-entry ( memo -- key memo' ) dup lf-rmemo-key swap lf-rmemo-in ;
: lf-rmemo@ ( node offset memo -- result true | false )
  dup >r lf-rmemo-key! 0= if r> drop false exit then
  r> lf-rmemo-entry memo-find dup if @ true then ;

\ Keeping: a result with an identity, into the entry found or a new one.
: lf-rmemo-kept ( result id memo -- )
  lf-rmemo-entry memo-put ok-then? if cell-pair! else drop 2drop then ;
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
