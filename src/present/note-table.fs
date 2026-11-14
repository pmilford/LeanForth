\ Labels and notes on proof steps (ADR 0017 §11, plan task 8.1.2): a side
\ table of short texts attached to terms of the term store. A label gives
\ a step a stable ID (label: NAME); a note explains a step and says who
\ wrote it, a person (note" ...") or an AI (ai-note" ..."). Presentation
\ data only: the checker never loads this module, nothing here is part of
\ a term, and no entry can change a verdict. The authoring words
\ (src/author/) fill it; the term printer's Forth mode prints each entry
\ after its term, so labels and notes survive a print and a new run.
\ An entry is stamped with its term's identity, so after a reset of the
\ term store a stale entry reads as dead instead of describing another term.
\ State: one context record, lf-notes (ADR 0009). Each context has its own
\ table; one context is single-threaded.

require ../lib/lib.fs
require ../core/terms.fs

0 constant lf-note-label        \ a step label
1 constant lf-note-person       \ a note written by a person
2 constant lf-note-ai           \ a note written by an AI
64 constant lf-note-capacity
4096 constant lf-note-byte-capacity

begin-structure /lf-pnote
  field: lf-pnote-term       \ term index
  field: lf-pnote-identity   \ that term's identity when recorded
  field: lf-pnote-kind       \ lf-note-label, -person or -ai
  field: lf-pnote-offset     \ text offset in the pool
  field: lf-pnote-length     \ text length
  field: lf-pnote-source     \ source record ID, or -1 for none
end-structure

begin-structure /lf-notes
  field: lf-notes-count      \ entries in use
  field: lf-notes-used       \ pool bytes in use
  lf-note-capacity /lf-pnote * +field lf-notes-entries
  lf-note-byte-capacity +field lf-notes-pool
end-structure
/lf-notes context-record: lf-notes

\ Forget every entry.
: lf-note-reset ( -- ) 0 lf-notes lf-notes-count ! 0 lf-notes lf-notes-used ! ;
\ The number of entries, clamped into range so that a corrupted count can
\ never address outside the table.
: lf-note-count ( -- n ) lf-notes lf-notes-count @ 0 max lf-note-capacity min ;
\ Unchecked: entry i, 0 <= i < lf-note-count.
: lf-note ( i -- entry ) /lf-pnote * lf-notes lf-notes-entries + ;
: lf-note-used ( -- u ) lf-notes lf-notes-used @ 0 max lf-note-byte-capacity min ;

\ An entry is live while its term still has the identity it had when the
\ entry was made.
: lf-note-live? ( i -- flag )
  lf-note dup lf-pnote-term @ lf-term-identity
  if swap lf-pnote-identity @ = else drop false then ;
\ The fields of a live entry i; unchecked otherwise.
: lf-note-term@ ( i -- term ) lf-note lf-pnote-term @ ;
: lf-note-kind@ ( i -- kind ) lf-note lf-pnote-kind @ ;
: lf-note-source@ ( i -- source ) lf-note lf-pnote-source @ ;
: lf-note-text@ ( i -- c-addr u )
  lf-note dup lf-pnote-offset @ lf-notes lf-notes-pool + swap lf-pnote-length @ ;
\ Does live entry i belong to term?
: lf-note-on? ( term i -- flag ) dup lf-note-live? if lf-note-term@ = else 2drop false
  then ;
\ Does term carry any live entry?
: lf-note-on-at? ( term i -- term flag ) over swap lf-note-on? ;
: lf-note-any? ( term -- flag ) lf-note-count ['] lf-note-on-at? any? nip ;

\ Adding an entry: the text is copied into the pool. A dead term or an
\ unknown kind is invalid; a full table or pool is full. Either way
\ nothing changes. The new entry has no source until lf-note-source!.
: lf-note-kind? ( kind -- flag ) lf-note-label lf-note-ai between? ;
: lf-note-room? ( u -- flag )
  lf-note-byte-capacity lf-note-used - upto? lf-note-count lf-note-capacity < and ;
: lf-note-text! ( c-addr u entry -- )
  2dup lf-pnote-length ! lf-note-used over lf-pnote-offset ! drop
  tuck lf-notes lf-notes-pool lf-note-used + swap move lf-notes lf-notes-used +! ;
: lf-note-claim ( term kind -- entry )
  lf-note-count dup 1+ lf-notes lf-notes-count ! lf-note -1 over lf-pnote-source !
  tuck lf-pnote-kind ! over lf-term-identity drop over lf-pnote-identity !
  tuck lf-pnote-term ! ;
: lf-note-args? ( term kind -- flag ) lf-note-kind? swap lf-term-valid? and ;
\ Attach text c-addr u of the given kind to term: the entry's index and ok,
\ or -1 and the failure.
: lf-note-add ( c-addr u kind term -- i outcome )
  2dup swap lf-note-args? 0= if 2drop 2drop -1 outcome-invalid exit then
  2 pick lf-note-room? 0= if 2drop 2drop -1 outcome-full exit then
  lf-note-count >r swap lf-note-claim lf-note-text! r> outcome-ok ;
\ Record entry i's source record ID (an opaque nonnegative number).
: lf-note-source! ( i source -- )
  over 0 lf-note-count within if swap lf-note lf-pnote-source ! else 2drop then ;

\ Move every live entry of term from to term to, which must be live (a
\ rebuilt copy of the same step). Entries of other terms are unchanged.
: lf-note-retarget ( to i -- ) lf-note 2dup lf-pnote-term ! swap lf-term-identity drop
  swap lf-pnote-identity ! ;
: lf-note-move ( from to -- )
  dup lf-term-valid? 0= if 2drop exit then
  lf-note-count 0 ?do over i lf-note-on? if dup i lf-note-retarget then loop 2drop ;

\ Is there a live label with this text among the entries from index from
\ onwards? Labels must be unique within one declaration.
: lf-note-label-at? ( c-addr u i -- c-addr u flag )
  dup lf-note-live? 0= if drop false exit then
  dup lf-note-kind@ lf-note-label <> if drop false exit then
  lf-note-text@ 2over compare 0= ;
: lf-note-label-from? ( c-addr u from k -- c-addr u from flag )
  over + swap >r lf-note-label-at? r> swap ;
: lf-note-label? ( c-addr u from -- flag )
  0 max lf-note-count over - ['] lf-note-label-from? any? nip nip nip ;
