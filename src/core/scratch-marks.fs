\ Marks of a check's scratch (compact-store plan step S1; ADR 0016 C3 and
\ C9 step 3). A check makes temporary terms, levels and constant
\ references -- its scratch -- above its input, and gives them back when
\ a step fails or no longer needs them. A scratch mark records where the
\ term, level and constant-reference stores stand, as one store mark of
\ each (lib/store.fs); a rollback to it gives back everything made since
\ in all three, and with the terms the local context's entries whose free
\ variables went with them (local-context.fs: entries are made in node
\ order, so they are the newest). The mark is joint: no family is rolled
\ back by hand or alone, as one tier mark will cover them all once they
\ share a tier (C3; plan steps S3 and S4). Identities never rewind.
\
\ LIFO. Marks are given back newest first. A rollback checks every
\ family's mark before it changes anything and refuses, with invalid and
\ nothing changed, a mark that is no longer valid for its store: of
\ another store or generation, above the count, or stale because a
\ rollback to an older mark went below it and records were made again
\ (store-mark-valid?). A mark held in a record is LIFO by construction (one
\ owner, used once), not by a check: store marks cannot tell apart two
\ marks taken at the same position, so giving back the older and then the
\ younger one acts as a rollback to that position and gives back what was
\ made in between (tests/core/mixed-infer.fs). A refusal is never ok.
\
\ Two ways to hold a mark. A pass with a record of its own keeps a
\ /lf-scratch record in it (lf-scratch-mark, lf-scratch-rollback). A pass
\ that can hold only a number across its work -- a frame cell, the return
\ stack -- puts the mark on the mark stack and holds its number, which
\ never repeats (lf-scratch-push). The stack is strictly LIFO: only the
\ newest mark can be given back (lf-scratch-back) or let go keeping what
\ was made since (lf-scratch-drop), so a mark used out of order is refused
\ even where the stores could not tell. Either use takes the mark off the
\ stack, refused or not. Number 0, the number of a failed push, is never
\ on the stack.
\
\ A step may keep the levels and references it made while giving back its
\ terms: an inference step whose result is a Sort level the step made
\ (mixed-infer.fs). lf-scratch-discard and lf-scratch-cut roll back only
\ the terms and the local context, checking every family's mark all the
\ same. Once levels share the terms' tier (plan step S4), such a step must
\ make its level again after the rollback or keep its terms.
\
\ Outcomes: ok, invalid (a store's count or a mark not valid; a stack mark
\ that is not the newest), full (the mark stack cannot grow, or its
\ numbers are spent). Untrusted; part of the checker's [kernel] path, not
\ yet through the review gate.
\ State: the mark stack, a growable array lf-scratch-stack, and its record
\ lf-scratch-state (depth and last number), members of the checker context
\ (lib/context.fs), where the stores are too. Single-threaded within one
\ context; a mark means something only in its own context. A THROW out of
\ a pass leaves its stack marks behind, as it leaves the pass's frames
\ busy: later marks stack above them, LIFO, and lf-scratch-reset empties
\ the stack for code that catches the THROW and holds no mark of its own.
\ Example:
\   create m /lf-scratch allot
\   m lf-scratch-mark drop    \ ok
\   ( make terms, levels and references )
\   m lf-scratch-rollback     \ ok: the three stores stand as they stood

require ../lib/lib.fs
require ./terms.fs
require ./levels.fs
require ./constant-references.fs
require ./local-context.fs

\ The families a mark covers, in the order of its parts: the term, level
\ and constant-reference stores.
3 constant lf-scratch-families
create lf-scratch-stores ' lf-terms , ' lf-levels , ' lf-crefs ,
begin-structure /lf-scratch
  lf-scratch-families /store-mark * +field lf-scratch-parts
end-structure
: lf-scratch-store ( k -- store ) cells lf-scratch-stores + @ execute ;
: lf-scratch-part ( scratch k -- mark ) /store-mark * swap lf-scratch-parts + ;
: lf-scratch-pair ( scratch k -- mark store ) tuck lf-scratch-part swap lf-scratch-store ;

\ Mark every family: ok; or invalid when a store's count is not valid,
\ the record then refused by every rollback.
: lf-scratch-refused ( scratch -- outcome ) /lf-scratch erase outcome-invalid ;
: lf-scratch-mark-one ( scratch k -- scratch outcome )
  over swap lf-scratch-pair store-mark ;
: lf-scratch-mark ( scratch -- outcome )
  lf-scratch-families ['] lf-scratch-mark-one ok-each
  ok? if drop outcome-ok else lf-scratch-refused then ;
\ Whether every family's mark is valid now (a rollback would accept it).
: lf-scratch-valid-at? ( scratch k -- scratch flag )
  over swap lf-scratch-pair store-mark-valid? ;
: lf-scratch-valid? ( scratch -- flag )
  lf-scratch-families ['] lf-scratch-valid-at? all? nip ;
\ The term count marked: the terms below it are older than the mark.
: lf-scratch-terms ( scratch -- n ) 0 lf-scratch-part lf-term-mark-end ;

\ Family k back to its part of a valid mark (store-rollback cannot refuse
\ it then), and the local context's entries above the terms marked. The
\ terms go back through lf-term-rollback, which also takes their entries
\ out of the hash-consing table (terms.fs).
: lf-scratch-level-back ( mark -- outcome ) lf-level-rollback ;
: lf-scratch-cref-back ( mark -- outcome ) lf-cref-rollback ;
create lf-scratch-backs
  ' lf-term-rollback , ' lf-scratch-level-back , ' lf-scratch-cref-back ,
: lf-scratch-back-to ( scratch k -- )
  tuck lf-scratch-part swap cells lf-scratch-backs + @ execute drop ;
: lf-scratch-lctx ( scratch -- ) lf-scratch-terms lf-lctx-drop ;
\ Give back everything made since the mark: ok, or invalid with nothing
\ changed for a mark that is not valid.
: lf-scratch-rollback ( scratch -- outcome )
  dup lf-scratch-valid? 0= if drop outcome-invalid exit then
  lf-scratch-families 0 do dup i lf-scratch-back-to loop lf-scratch-lctx outcome-ok ;
\ Give back the terms made since the mark, and their local-context
\ entries, keeping the levels and references: the same outcomes.
: lf-scratch-discard ( scratch -- outcome )
  dup lf-scratch-valid? 0= if drop outcome-invalid exit then
  dup 0 lf-scratch-back-to lf-scratch-lctx outcome-ok ;
\ The first failure of two outcomes: a later step's outcome counts only
\ when the earlier one was ok (outcome.fs's outcome-and, named for the
\ scratch release that follows a step).
: lf-scratch-settled ( outcome outcome' -- outcome ) outcome-and ;

\ The mark stack: entry k (from 0, the oldest) holds a mark and its number.
begin-structure /lf-scratch-entry
  field: lf-sentry-number
  /lf-scratch +field lf-sentry-marks
end-structure
begin-structure /lf-sstate
  field: lf-sstate-depth     \ marks on the stack
  field: lf-sstate-number    \ the last number given; 0 before the first
end-structure
/lf-scratch-entry context-slab: lf-scratch-stack
/lf-sstate context-record: lf-scratch-state
: lf-scratch-depth ( -- addr ) lf-scratch-state lf-sstate-depth ;
: lf-scratch-number ( -- addr ) lf-scratch-state lf-sstate-number ;
\ Entry k's address, valid until the stack next grows (lf-scratch-push).
: lf-scratch-entry ( k -- entry ) lf-scratch-stack slab-at ;
: lf-scratch-newest ( -- entry ) lf-scratch-depth @ 1- lf-scratch-entry ;
\ The marks on the stack and the room it has (for a full stack's record).
: lf-scratch-size ( -- depth room ) lf-scratch-depth @ lf-scratch-stack slab-capacity ;
\ Empty the stack: every mark on it is refused from then on.
: lf-scratch-reset ( -- ) 0 lf-scratch-depth ! ;

\ Push a mark of every family: its number and ok; or 0 and full when the
\ stack cannot grow or the numbers are spent, or invalid when a store's
\ count is not valid (nothing pushed).
: lf-scratch-room ( -- outcome )
  lf-scratch-number @ max-n = if outcome-full exit then
  lf-scratch-depth @ 1+ lf-scratch-stack slab-hold ;
: lf-scratch-numbered ( entry -- mark )
  lf-scratch-number 1 over +! @ tuck swap lf-sentry-number ! 1 lf-scratch-depth +! ;
: lf-scratch-placed ( -- mark outcome )
  lf-scratch-depth @ lf-scratch-entry dup lf-sentry-marks lf-scratch-mark
  dup ok? if drop lf-scratch-numbered outcome-ok else nip 0 swap then ;
: lf-scratch-push ( -- mark outcome )
  lf-scratch-room dup ok? if drop lf-scratch-placed else 0 swap then ;

\ Whether mark is the newest mark on the stack.
: lf-scratch-top? ( mark -- flag )
  lf-scratch-depth @ 0> if lf-scratch-newest lf-sentry-number @ = else drop false then ;
\ Take the newest mark off the stack, after xt ( scratch -- outcome ) ran
\ on it: xt's outcome; or invalid, nothing run or taken off, for a mark
\ that is not the newest.
: lf-scratch-using ( mark xt -- outcome )
  swap lf-scratch-top? 0= if drop outcome-invalid exit then
  lf-scratch-newest lf-sentry-marks swap execute -1 lf-scratch-depth +! ;
\ Let the newest mark go, keeping what was made since.
: lf-scratch-drop ( mark -- outcome ) ['] drop-ok lf-scratch-using ;
\ Give back everything made since the newest mark (lf-scratch-rollback),
\ or only its terms (lf-scratch-discard), and let it go.
: lf-scratch-back ( mark -- outcome ) ['] lf-scratch-rollback lf-scratch-using ;
: lf-scratch-cut ( mark -- outcome ) ['] lf-scratch-discard lf-scratch-using ;
