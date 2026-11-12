\ The memory limit of one check (check --memory-per-check; ADR 0014
\ Amendment 8). A check's scratch -- the term nodes, levels and constant
\ references it makes above the input, its local context and the entries
\ of its result caches, all given back or emptied when it ends -- may
\ hold at most a set number of bytes; a check that would pass it stops
\ full (ADR 0008), as when the heap refuses, never accepted. The limit is
\ LeanForth's own resource bound, like fuel, never a Lean verdict. It
\ exists so that one large check cannot take the memory that the other
\ workers of a parallel check (--jobs) share in one process.
\
\ Bytes are counted per record, not read from the heap, so that the
\ count is the same in every context and run, whatever an earlier check
\ grew: a record counts the bytes below, upper bounds on a 64-bit host
\ of its record, identity, side columns and hash-table slots
\ (tests/core/check-declaration.fs checks them against the stores). The
\ heap holds more, as stores grow by doubling and the walks' stacks and
\ memos are not counted: about 1.3-1.4 times the count, measured (ADR
\ 0014 Amendment 8).
\ The stores make and give back records in the hot paths, so the meter
\ never sums on each record. Each new record is charged against a credit
\ (lf-meter-charge); only when the credit runs out does the meter read the
\ check's whole scratch (lf-meter-used, a DEFER that
\ kernel/check-declaration.fs sets) and either refuse the record, or set
\ the credit to the bytes left below the limit. A record charged whose
\ node turns out shared costs only an earlier reading, never a refusal:
\ every refusal comes from a reading. Once a reading refuses, every later
\ charge of the same check is refused too (lf-meter-passed?).
\
\ Use: lf-meter-limit! sets the context's setting (0, a new context's: no
\ limit); the check calls lf-meter-start when it begins and lf-meter-stop
\ when it has ended, so the feed and every other use of the stores
\ outside a check is never refused. Untrusted; part of the checker's
\ [kernel] path, not yet through the review gate.
\ State: one record, lf-meter (the setting; while a check runs its limit,
\ credit, whether it passed the limit and the bytes it then asked for),
\ a member of the checker context (lib/context.fs); the reading
\ lf-meter-used is a DEFER set once while loading.
\ Example:
\   4000 20 lshift lf-meter-limit!   \ every later check: at most 4000 MB
\   lf-meter-start  lf-meter-term? drop  lf-meter-stop

require ../lib/lib.fs

begin-structure /lf-meter
  field: lf-meter-setting   \ bytes each check's scratch may hold; 0: no limit
  field: lf-meter-limit     \ the running check's limit; 0 outside a check
  field: lf-meter-credit    \ bytes that may be charged before the next reading
  field: lf-meter-passed    \ true once a reading of this check refused
  field: lf-meter-asked     \ the bytes that reading found, with the charge
end-structure
/lf-meter context-record: lf-meter

\ Bytes each record counts (see the header).
12 cells constant lf-meter-term-bytes    \ a term node
22 cells constant lf-meter-level-bytes   \ a level
8 cells constant lf-meter-cref-bytes     \ a constant reference, plus
2 cells constant lf-meter-arg-bytes      \ each of its universe arguments
8 cells constant lf-meter-entry-bytes    \ a cache entry
6 cells constant lf-meter-local-bytes    \ a local-context entry

\ The check's scratch now, in bytes; 0 until the checker sets it.
defer lf-meter-used ( -- u )
:noname ( -- 0 ) 0 ; is lf-meter-used

: lf-meter-limit! ( bytes -- ) lf-meter lf-meter-setting ! ;
: lf-meter-limit@ ( -- bytes ) lf-meter lf-meter-setting @ ;
: lf-meter-passed? ( -- flag ) lf-meter lf-meter-passed @ ;
: lf-meter-asked@ ( -- bytes ) lf-meter lf-meter-asked @ ;

\ A check begins: its limit is the setting, nothing charged, so that the
\ first charge reads. When it has ended: no limit until the next begins.
: lf-meter-run ( limit -- )
  lf-meter tuck lf-meter-limit ! 0 over lf-meter-credit ! 0 over lf-meter-passed !
  0 swap lf-meter-asked ! ;
: lf-meter-start ( -- ) lf-meter-limit@ lf-meter-run ;
: lf-meter-stop ( -- ) 0 lf-meter-run ;

\ A reading for a charge of u bytes: refused once passed; with no limit,
\ credit for any check; else room when the scratch and u fit the limit,
\ the credit then what is left.
: lf-meter-boundless ( u -- true ) drop max-n lf-meter lf-meter-credit ! true ;
: lf-meter-refuse ( bytes -- false )
  lf-meter tuck lf-meter-asked ! true swap lf-meter-passed ! false ;
: lf-meter-room ( bytes limit -- flag )
  2dup u> if drop lf-meter-refuse exit then swap - lf-meter lf-meter-credit ! true ;
: lf-meter-read ( u -- flag )
  lf-meter-passed? if drop false exit then
  lf-meter lf-meter-limit @ ?dup 0= if lf-meter-boundless exit then
  >r lf-meter-used + r> lf-meter-room ;
\ Charge u bytes for a record about to be made: true when it may be.
: lf-meter-charge ( u -- flag )
  lf-meter lf-meter-credit 2dup @ swap - dup 0< if 2drop lf-meter-read exit then
  swap ! drop true ;
: lf-meter-term? ( -- flag ) lf-meter-term-bytes lf-meter-charge ;
: lf-meter-level? ( -- flag ) lf-meter-level-bytes lf-meter-charge ;
: lf-meter-entry? ( -- flag ) lf-meter-entry-bytes lf-meter-charge ;
\ A reference with n universe arguments.
: lf-meter-cref? ( n -- flag )
  lf-meter-arg-bytes * lf-meter-cref-bytes + lf-meter-charge ;
