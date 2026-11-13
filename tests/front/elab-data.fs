\ Unit tests of src/front/elab-data.fs (plan row FE1d), the words around
\ the reader; tests/front/test_elab_data.py runs every damaged file
\ through the command line. Here: the slice's data read against the init
\ slice's stage, every kind of record read back by number and by
\ declaration; the synthetic eliminators found by kind and type; a
\ refused read keeps nothing (every table empty, nothing loaded), a later
\ read works again and replaces the earlier one; a missing file, a call
\ during a read and a sealed stage refused; every allocation that fails
\ gives full or ok, never anything else, and leaks no heap block; the
\ reader and its JSON view give back their blocks after every read.
\ Loaded under HEX: loading must not depend on BASE, and must leave BASE
\ as it found it.
include ../support/tester.fs
include ../support/heap-watch.fs
hex require ../../src/front/elab-data.fs base @ decimal constant base-after-load

T{ base-after-load elab-kinds elab-instance-reducible -> 16 4 4 }T
create lib /stage allot
create sealed /stage allot
create zero-sha 32 allot  zero-sha 32 erase
: slice ( -- c-addr u ) s" tests/author/init-slice.ndjson" ;
: good ( -- c-addr u ) s" tests/front/init-slice.elab.ndjson" ;
: elims ( -- c-addr u ) s" tests/front/eliminators.elab.ndjson" ;
: digest ( -- sha ) lib stage-manifest manifest-digest ;
T{ 12 lib stage-init slice lib stage-read -> outcome-ok outcome-ok }T

\ Declarations of the slice by name, looked up in its tier.
: part ( n c-addr u -- n' ) lib stage-tier name-seek-str drop ;
: decl ( n -- d ) lib stage-find drop ;
: top ( c-addr u -- d ) 0 -rot part decl ;
: nat ( c-addr u -- d ) 0 s" Nat" part -rot part decl ;
: why? ( c-addr u -- flag ) elab-error-why compare 0= ;
: counts ( -- n1 n2 n3 n4 ) elab-kinds 0 do i elab-count loop ;

\ The slice's data: three instances, two default instances, eighteen
\ reducibility statuses, no eliminator; nothing failed.
T{ good lib digest elab-read elab-loaded? counts -> outcome-ok true 3 2 18 0 }T
T{ elab-error-line s" none" why? -> 0 true }T
T{ 0 elab-instance@ -> s" instAddNat" top s" Add" top 1000 }T
T{ 2 elab-instance@ -> s" instOfNatNat" top s" OfNat" top 1000 }T
T{ 0 elab-instance-order nip 1 elab-instance-order swap @ -> 0 1 1 }T
T{ s" instHAdd" top elab-instance-of s" Nat" top elab-instance-of -> 1 true false }T
T{ 0 elab-default@ -> s" HAdd" top s" instHAdd" top 1000 }T
T{ 1 elab-default@ -> s" OfNat" top s" instOfNatNat" top 100 }T
T{ s" instAddNat" top elab-status s" Id" top elab-status s" outParam" top elab-status
   -> elab-instance-reducible elab-implicit-reducible elab-reducible }T
T{ s" Nat" top elab-status s" succ" nat elab-status -> elab-semireducible elab-semireducible }T
T{ s" Nat" top elab-induction elab-eliminator-for -> false }T

\ The synthetic eliminators (test_elab_data.py writes them): one per
\ kind and type list; a key of two types is found by neither of them alone.
T{ elims lib digest elab-read counts -> outcome-ok 3 2 18 4 }T
T{ s" Nat" top elab-induction elab-eliminator-for -> 0 true }T
T{ 0 elab-eliminator@ -> elab-induction s" rec" nat }T
T{ s" Nat" top elab-cases elab-eliminator-for over elab-eliminator@ -> 1 true elab-cases
   s" casesOn" nat }T
T{ s" And" top elab-induction elab-eliminator-for s" And" top elab-cases elab-eliminator-for
   -> 2 true false }T
T{ 3 elab-eliminator-types nip 3 elab-eliminator-types drop 1 cells + @ -> 2 s" Nat" top }T
T{ s" Eq" top elab-induction elab-eliminator-for -> false }T

\ A refused read keeps nothing; the next read works and replaces it.
: empty? ( -- flag )
  elab-loaded? 0= counts + + + 0= and s" instAddNat" top elab-status 0= and
  s" instAddNat" top elab-instance-of 0= and s" Nat" top elab-induction elab-eliminator-for 0=
  and ;
T{ elims lib zero-sha elab-read empty? elab-error-line s" elaboration data of another export"
   why? elab-error-code -> outcome-invalid true 1 true 9 }T
T{ good lib digest elab-read counts elab-error-code -> outcome-ok 3 2 18 0 0 }T
\ Refused after its last line: none of the records it read stays.
T{ s" tests/front/cut-off.elab.ndjson" lib digest elab-read empty? elab-error-line
   s" records differ in number from the header" why? elab-error-code
   -> outcome-invalid true 27 true 20 }T
\ Every code has its text, the first and the last as documented.
T{ 0 ed-message s" none" compare 1 ed-message s" file missing or unreadable" compare
   25 ed-message s" a read in progress" compare -> 0 0 0 }T
T{ elims lib digest elab-read good lib digest elab-read counts -> outcome-ok outcome-ok 3 2 18 0 }T
T{ elab-reset empty? -> true }T
T{ s" tests/front/no-such.ndjson" lib digest elab-read elab-error-line
   s" file missing or unreadable" why? empty? -> outcome-invalid 0 true true }T

\ A read while one is in progress is refused and changes nothing loaded.
T{ good lib digest elab-read -> outcome-ok }T
T{ true elab elab-reading ! good lib digest elab-read s" a read in progress" why?
   false elab elab-reading ! counts -> outcome-invalid true 3 2 18 0 }T

\ A sealed stage: its names cannot be looked up; refused, nothing kept.
T{ 12 sealed stage-init slice sealed stage-load -> outcome-ok outcome-ok }T
T{ good sealed sealed stage-manifest manifest-digest elab-read empty?
   -> outcome-invalid true }T
T{ s" the library's stage is sealed: its names cannot be looked up" why? -> true }T

\ Resources: the k-th allocation refused, for every k until a read needs
\ none: full or ok, never another outcome, and no block kept but the
\ data's; then the next read is ok.
: blocks ( -- n ) live-blocks @ ;
: refused-read ( k -- outcome ) heap-refusals ! elims lib digest elab-read 0 heap-refusals ! ;
: full-or-ok? ( outcome -- flag ) dup ok? swap outcome-full = or ;
: refusals ( -- flag )
  true 40 1 do elab-reset i refused-read full-or-ok? and loop ;
T{ elab-reset ed-slabs-clear refusals -> true }T
T{ elims lib digest elab-read counts -> outcome-ok 3 2 18 4 }T

\ The reader and the view give their blocks back after every read, ok or
\ not; the data's slabs and table keep theirs until the context goes.
T{ blocks good lib digest elab-read drop blocks = -> true }T
T{ blocks elims lib zero-sha elab-read drop blocks = -> true }T
T{ lib stage-free sealed stage-free -> }T
bye
