\ Unit tests of src/front/simp-data.fs (plan FE9, slice SD-a of
\ docs/design/TACTIC_SIMP.md) and of the format-4 parts of
\ src/front/elab-data.fs it rests on: the fixtures of tests/front/simp-data/
\ (tests/front/test_simp_data.py writes them) read against the simp slice's
\ export: the good file's congruence lemmas by function in rank order, their
\ hypotheses, priorities and ranks, the defeq tag; the slice's own data
\ from the writer; a format-3.2 file answering unsupported, never "none";
\ every damaged file refused with its outcome, line and code, nothing kept;
\ every heap allocation of a read refused in turn (tests/support/
\ meta-sweeps.fs: full or the same answer, never another); the context's
\ memo and slabs given back when it is freed. Loaded under HEX: loading
\ must not depend on BASE, and must leave BASE as it found it.
include ../support/tester.fs
include ../support/heap-watch.fs
include ../support/meta-sweeps.fs
hex require ../../src/front/simp-data.fs base @ decimal constant base-after-load
T{ base-after-load simp-congr-kind elab-kinds-most elab-tag-defeq -> 16 11 16 8 }T

create lib /stage allot
: digest ( -- sha ) lib stage-manifest manifest-digest ;
T{ 12 lib stage-init s" tests/front/simp-slice.ndjson" lib stage-read -> outcome-ok outcome-ok }T
: part ( n c-addr u -- n' ) lib stage-tier name-seek-str drop ;
: top ( c-addr u -- d ) 0 -rot part lib stage-find drop ;
: nat ( c-addr u -- d ) 0 s" Nat" part -rot part lib stage-find drop ;
: fx ( c-addr u -- outcome ) lib digest elab-read ;
: good ( -- outcome ) s" tests/front/simp-data/good.elab.ndjson" fx ;

\ Before any read: no simp data, so unsupported, never "none".
T{ simp-data? s" ite" top simp-congr-lemmas s" add_zero" nat simp-defeq?
   -> false 0 0 outcome-unsupported false outcome-unsupported }T

\ The good file: ite's two lemmas in rank order, dite's one, none for a
\ function without; the defeq tag of Nat.add_zero alone.
T{ good simp-data? simp-congr-count simp-congr-kind elab-count simp-defeq-count
   -> outcome-ok true 3 3 1 }T
T{ s" ite" top simp-congr-lemmas -> 1 2 outcome-ok }T
T{ 1 simp-congr@ 1 simp-congr-rank 1 simp-congr-fun -> s" ite_congr" top 1000 0 s" ite" top }T
T{ 2 simp-congr@ 2 simp-congr-rank -> s" add_zero" nat 500 1 }T
T{ s" dite" top simp-congr-lemmas 0 simp-congr@ -> 0 1 outcome-ok s" dite_congr" top 1000 }T
T{ s" add_zero" nat simp-congr-lemmas -> 0 0 outcome-ok }T
: hyps@ ( c -- h0 .. hn-1 n ) simp-congr-hyps dup >r cells bounds ?do i @ 1 cells +loop r> ;
T{ 0 hyps@ 2 hyps@ -> 9 10 11 3 0 1 }T
T{ s" add_zero" nat simp-defeq? s" ite_congr" top simp-defeq? s" ite" top simp-defeq?
   -> true outcome-ok false outcome-ok false outcome-ok }T

\ The slice's own data from the writer: dite_congr and ite_congr, one
\ defeq tag (Nat.add_zero; Nat.zero_add is proved by induction).
T{ s" tests/front/simp-slice.elab.ndjson" fx simp-congr-count simp-defeq-count
   -> outcome-ok 2 1 }T
T{ s" ite" top simp-congr-lemmas swap simp-congr@ drop s" zero_add" nat simp-defeq?
   -> 1 outcome-ok s" ite_congr" top false outcome-ok }T

\ Format 3.2: read, but no simp data: unsupported.
T{ s" tests/front/simp-data/plain32.elab.ndjson" fx simp-data? s" ite" top simp-congr-lemmas
   -> outcome-ok false 0 0 outcome-unsupported }T

\ Every damaged file refused: outcome, line, code; nothing kept.
: refused ( c-addr u -- outcome line code kept )
  fx elab-error-line elab-error-code simp-congr-count simp-defeq-count + ;
create fx-buf 128 allot
: fx+ ( u c-addr n -- u' ) >r over fx-buf + r@ move r> + ;
: fixture ( "name" -- c-addr u )
  0 s" tests/front/simp-data/" fx+ parse-name fx+ s" .elab.ndjson" fx+ fx-buf swap ;
T{ fixture v3-congr refused -> outcome-invalid 2 11 0 }T
T{ fixture v32-defeq refused -> outcome-invalid 2 10 0 }T
T{ fixture v5 refused -> outcome-unsupported 1 7 0 }T
T{ fixture v41 refused -> outcome-unsupported 1 7 0 }T
T{ fixture unknown-kind refused -> outcome-invalid 6 11 0 }T
T{ fixture no-hyps refused -> outcome-invalid 2 10 0 }T
T{ fixture rank-text refused -> outcome-invalid 2 10 0 }T
T{ fixture priority-big refused -> outcome-unsupported 2 19 0 }T
T{ fixture name-unknown refused -> outcome-invalid 2 12 0 }T
T{ fixture name-def refused -> outcome-invalid 2 14 0 }T
T{ fixture fun-unknown refused -> outcome-invalid 2 12 0 }T
T{ fixture twice refused -> outcome-invalid 4 47 0 }T
T{ fixture order-swap refused -> outcome-invalid 3 48 0 }T
T{ fixture order-gap refused -> outcome-invalid 4 48 0 }T
T{ fixture order-split refused -> outcome-invalid 4 48 0 }T
T{ fixture order-again refused -> outcome-invalid 4 48 0 }T
T{ fixture hyps-beyond refused -> outcome-invalid 4 37 0 }T
T{ fixture hyps-down refused -> outcome-invalid 2 37 0 }T
T{ fixture defeq-def refused -> outcome-invalid 6 14 0 }T
T{ fixture defeq-twice refused -> outcome-invalid 6 29 0 }T
T{ fixture count-missing refused -> outcome-invalid 1 10 0 }T
T{ fixture count-wrong refused -> outcome-invalid 5 20 0 }T
\ After a refusal, simp-data? is false and the next read works again.
T{ simp-data? good simp-congr-count -> false outcome-ok 3 }T

\ The heap: every allocation of a read of the good file refused in turn
\ (the kind's slabs and memo given back before each run, so that each
\ first claim allocates): full or the same three lemmas, never another.
: anew ( -- ) simp-congrs sweep-slab-anew elab-orders sweep-slab-anew sd-index memo-free ;
' anew sweep-slabs-xt !
: read-good ( e -- x outcome ) drop good simp-congr-count swap ;
T{ 0 ' read-good heap-sweep swap 0> -> 0 true }T
' noop sweep-slabs-xt !
\ A context's memo and slabs go with it: no heap block kept.
: in-fresh ( -- ) context-new throw dup context-use good drop context-main context-use
  context-free throw ;
T{ live-blocks @ in-fresh live-blocks @ = -> true }T
T{ elab-reset simp-congr-count simp-data? -> 0 false }T
T{ lib stage-free -> }T
