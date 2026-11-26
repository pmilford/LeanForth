\ Unit tests of src/front/simp-data.fs (plan FE9, slices SD-a and SD-b of
\ docs/design/TACTIC_SIMP.md) and of the format-4 and 4.1 parts of
\ src/front/elab-data.fs it rests on: the fixtures of tests/front/simp-data/
\ (tests/front/test_simp_data.py writes them) read against the simp slice's
\ export: the good file's congruence lemmas by function in rank order, their
\ hypotheses, priorities and ranks, the defeq tag; the slice's own data
\ from the writer (a run of two lemmas of one function, ForM.forM's,
\ plan task SD-b.8); format 4.1's realized congruence theorems by
\ function, their argument kinds; a format-3.2 file answering
\ unsupported, never "none";
\ every damaged file refused with its outcome, line and code, nothing kept;
\ every heap allocation of a read refused in turn (tests/support/
\ meta-sweeps.fs: full or the same answer, never another); the context's
\ memo and slabs given back when it is freed. Loaded under HEX: loading
\ must not depend on BASE, and must leave BASE as it found it.
include ../support/tester.fs
include ../support/heap-watch.fs
include ../support/meta-sweeps.fs
hex require ../../src/front/simp-data.fs base @ decimal constant base-after-load
require ../../src/front/simp-set-data.fs   \ format 4.1's other kinds, which the slice's data holds
T{ base-after-load simp-congr-kind simp-realized-kind elab-kinds-most elab-tag-defeq
   -> 16 11 12 24 8 }T

create lib /stage allot
: digest ( -- sha ) lib stage-manifest manifest-digest ;
T{ 12 lib stage-init s" tests/front/simp-slice.ndjson" lib stage-read -> outcome-ok outcome-ok }T
: part ( n c-addr u -- n' ) lib stage-tier name-seek-str drop ;
: top ( c-addr u -- d ) 0 -rot part lib stage-find drop ;
: nat ( c-addr u -- d ) 0 s" Nat" part -rot part lib stage-find drop ;
: fx ( c-addr u -- outcome ) lib digest elab-read ;
: good ( -- outcome ) s" tests/front/simp-data/good.elab.ndjson" fx ;
: hsub ( -- d ) 0 s" HSub" part s" hSub" part lib stage-find drop ;

\ Before any read: no simp data, so unsupported, never "none".
T{ simp-data? s" ite" top simp-congr-lemmas s" add_zero" nat simp-defeq?
   -> false 0 0 outcome-unsupported false outcome-unsupported }T

\ The good file: ite's, dite's and HSub.hSub's lemmas, none for a
\ function without; the defeq tag of Nat.add_zero alone.
T{ good simp-data? simp-congr-count simp-congr-kind elab-count simp-defeq-count
   -> outcome-ok true 3 3 1 }T
T{ s" ite" top simp-congr-lemmas -> 1 1 outcome-ok }T
T{ 1 simp-congr@ 1 simp-congr-rank 1 simp-congr-fun -> s" ite_congr" top 1000 0 s" ite" top }T
T{ hsub simp-congr-lemmas 2 simp-congr@ 2 simp-congr-fun
   -> 2 1 outcome-ok s" succ_sub_succ_eq_sub" nat 1000 hsub }T
T{ s" dite" top simp-congr-lemmas 0 simp-congr@ -> 0 1 outcome-ok s" dite_congr" top 1000 }T
T{ s" add_zero" nat simp-congr-lemmas -> 0 0 outcome-ok }T
: hyps@ ( c -- h0 .. hn-1 n ) simp-congr-hyps dup >r cells bounds ?do i @ 1 cells +loop r> ;
T{ 0 hyps@ 2 hyps@ -> 9 10 11 3 0 }T
T{ s" add_zero" nat simp-defeq? s" ite_congr" top simp-defeq? s" ite" top simp-defeq?
   -> true outcome-ok false outcome-ok false outcome-ok }T
\ sd-falls?: a rank's priority is at most the one before it, an equal one
\ too (re-check of simp-sd-a, D); record 2 made rank 1 of record 1's run by hand.
: prio ( c p -- flag ) over sdc sdc-priority ! sd-falls? ;
T{ 1 2 sdc sdc-rank ! 2 1000 prio 2 1001 prio 2 999 prio 2 0 prio -> true false true true }T

\ The slice's own data from the writer (format 4.1): dite_congr,
\ ite_congr, ForM.forM's two and the five lemmas of the functions simp
\ slice SL1a-1's roots brought in, 33 defeq tags (Nat.add_zero's;
\ Nat.zero_add is proved by induction), five realized theorems.
T{ s" tests/front/simp-slice.elab.ndjson" fx simp-congr-count simp-defeq-count
   simp-realized-count -> outcome-ok 9 33 5 }T
\ A run of two (plan task SD-b.8): ForM.forM's lemmas in Lean's order,
\ Vector.forM_congr (rank 0) then Array.forM_congr (rank 1).
: two ( c-addr u c-addr u -- d ) 2swap 0 -rot part -rot part lib stage-find drop ;
T{ s" ForM" s" forM" two simp-congr-lemmas rot dup simp-congr-rank swap simp-congr@ drop
   -> 2 outcome-ok 0 s" Vector" s" forM_congr" two }T
T{ s" ForM" s" forM" two simp-congr-lemmas drop + 1- dup simp-congr-rank swap simp-congr@
   -> 1 s" Array" s" forM_congr" two 1000 }T
: dec ( -- d ) s" Decidable" s" decide" two ;
: real-kinds ( f -- k0 .. kn-1 n ) simp-realized drop drop simp-realized-kinds
  dup >r cells bounds ?do i @ 1 cells +loop r> ;
T{ dec simp-realized rot simp-realized@ elab-decl-name
   -> true outcome-ok 0 s" Decidable" part s" decide" part s" congr_simp" part }T
T{ dec real-kinds s" ite" top real-kinds -> 1 3 2 0 1 3 1 1 5 }T
T{ s" add_zero" nat simp-realized -> 0 false outcome-ok }T
T{ s" ite" top simp-congr-lemmas rot simp-congr@ drop s" zero_add" nat simp-defeq?
   -> 1 outcome-ok s" ite_congr" top false outcome-ok }T

\ The relation a conclusion of n arguments may be: Eq, Iff, else none (-2).
: named ( c-addr u -- name ) 0 -rot lib stage-tier name-seek-str drop ;
T{ 3 sd-relation-name 2 sd-relation-name 4 sd-relation-name -> s" Eq" named s" Iff" named -2 }T

\ Formats 3, 3.1 and 3.2: read, but no simp data: both questions unsupported.
: older ( c-addr u -- outcome flag c n outcome flag outcome )
  fx simp-data? s" ite" top simp-congr-lemmas s" add_zero" nat simp-defeq? ;
T{ s" tests/front/simp-data/plain32.elab.ndjson" older
   -> outcome-ok false 0 0 outcome-unsupported false outcome-unsupported }T
T{ s" tests/front/simp-data/plain31.elab.ndjson" older
   -> outcome-ok false 0 0 outcome-unsupported false outcome-unsupported }T
T{ s" tests/front/simp-data/plain3.elab.ndjson" older
   -> outcome-ok false 0 0 outcome-unsupported false outcome-unsupported }T

\ Every damaged file refused: outcome, line, code; nothing kept.
: refused ( c-addr u -- outcome line code kept )
  fx elab-error-line elab-error-code simp-congr-count simp-defeq-count + simp-realized-count + ;
create fx-buf 128 allot
: fx+ ( u c-addr n -- u' ) >r over fx-buf + r@ move r> + ;
: fixture ( "name" -- c-addr u )
  0 s" tests/front/simp-data/" fx+ parse-name fx+ s" .elab.ndjson" fx+ fx-buf swap ;
T{ fixture v3-congr refused -> outcome-invalid 2 11 0 }T
T{ fixture v32-defeq refused -> outcome-invalid 2 10 0 }T
T{ fixture v5 refused -> outcome-unsupported 1 7 0 }T
T{ fixture v41-uncounted refused -> outcome-invalid 1 10 0 }T
T{ fixture v4-realized refused -> outcome-invalid 6 11 0 }T
T{ fixture real-other refused -> outcome-invalid 6 37 0 }T
T{ fixture real-kind refused -> outcome-invalid 6 10 0 }T
T{ fixture real-kinds-big refused -> outcome-invalid 6 10 0 }T
T{ fixture real-kinds-text refused -> outcome-invalid 6 10 0 }T
T{ fixture real-twice refused -> outcome-invalid 8 49 0 }T
\ A @[congr] lemma's name for a realized theorem: not fun's congr_simp
\ (37, not 47); fewer kinds than ite's five leading binders (37), more
\ accepted (Lean counts them through a reducing telescope).
T{ fixture real-congr-name refused -> outcome-invalid 6 37 0 }T
T{ fixture real-kinds-short refused -> outcome-invalid 6 37 0 }T
T{ fixture real-kinds-long refused -> outcome-ok 0 0 5 }T
T{ fixture real-def refused -> outcome-invalid 6 14 0 }T
T{ fixture real-unknown refused -> outcome-invalid 6 12 0 }T
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
T{ fixture fun-other refused -> outcome-invalid 2 37 0 }T
T{ fixture fun-swapped refused -> outcome-invalid 2 37 0 }T
T{ fixture not-eq refused -> outcome-invalid 4 37 0 }T
T{ fixture ite_eq_left refused -> outcome-invalid 4 37 0 }T
T{ fixture iff_self refused -> outcome-invalid 4 37 0 }T
T{ fixture prio-rising refused -> outcome-invalid 4 48 0 }T
T{ fixture prio-equal refused -> outcome-invalid 4 37 0 }T
T{ fixture defeq-def refused -> outcome-invalid 6 14 0 }T
T{ fixture defeq-twice refused -> outcome-invalid 6 29 0 }T
T{ fixture tag-unknown refused -> outcome-invalid 6 10 0 }T
T{ fixture count-missing refused -> outcome-invalid 1 10 0 }T
T{ fixture count-wrong refused -> outcome-invalid 5 20 0 }T

\ Format 4.1's default simp set (simp group 4, front/simp-set-data.fs):
\ the slice's own data from the writer (194 lemmas kept, 4,203 left out,
\ 2 definitions to unfold, 207 simprocs); a good file of one record of
\ each kind, its questions answered; each damaged copy refused at its
\ line with its code, nothing kept; 4.1 data without the set: no
\ default set (simp answers unsupported).
: set-kept ( -- n )
  simp-lemma-count simp-proc-count + true simp-lemmas# + false simp-lemmas# + ;
: set-refused ( c-addr u -- outcome line code kept ) fx elab-error-line elab-error-code set-kept ;
T{ s" tests/front/simp-slice.elab.ndjson" set-refused simp-default? simp-lemma-count
   true simp-lemmas# false simp-lemmas# simp-proc-count
   -> outcome-ok 0 0 4798 true 194 4397 0 207 }T
T{ fixture set41 set-refused simp-default? -> outcome-ok 0 0 4 true }T
T{ 0 simp-lemma-rank 0 simp-lemma-prio 0 simp-lemma-rfl? 0 simp-lemma-perm? 0 simp-lemma-keys nip
   -> 33 1000 true false 7 }T
T{ 0 simp-lemma-proof s" add_zero" nat = 0 true simp-lemma-value 1 true simp-lemma-value
   -> true 0 -1 }T
T{ -1 simp-lemma-rank -1 simp-lemma-prio -1 simp-lemma-keys nip false simp-lemmas# -> 0 1000 2 0 }T
T{ s" Eq" s" ndrec" two simp-unfold? s" add_zero" nat simp-unfold? -> true false }T
T{ false simp-procs# true simp-procs# 0 false simp-proc-value dup simp-proc-dsimproc? swap
   simp-proc-rank 0 simp-proc-keys nip -> 1 0 true 0 2 }T
T{ fixture good41 set-refused simp-default? -> outcome-ok 0 0 0 false }T
T{ fixture set-twice set-refused -> outcome-invalid 13 52 0 }T
T{ fixture set-other set-refused -> outcome-invalid 8 52 0 }T
T{ fixture set-procs set-refused -> outcome-invalid 8 52 0 }T
T{ fixture set-name-long set-refused -> outcome-invalid 8 52 0 }T
T{ fixture lemma-set set-refused -> outcome-invalid 9 52 0 }T
T{ fixture lemma-rfl set-refused -> outcome-invalid 9 50 0 }T
T{ fixture lemma-proof-def set-refused -> outcome-invalid 9 14 0 }T
T{ fixture lemma-unknown set-refused -> outcome-invalid 9 12 0 }T
T{ fixture lemma-keys-cut set-refused -> outcome-invalid 9 30 0 }T
T{ fixture lemma-bool set-refused -> outcome-invalid 9 10 0 }T
T{ fixture lemma-inv set-refused -> outcome-invalid 9 10 0 }T
T{ fixture left-known set-refused -> outcome-invalid 10 51 0 }T
T{ fixture left-reason set-refused -> outcome-invalid 10 10 0 }T
T{ fixture left-name set-refused -> outcome-invalid 10 10 0 }T
T{ fixture unfold-unknown set-refused -> outcome-invalid 11 12 0 }T
T{ fixture proc-name set-refused -> outcome-invalid 12 10 0 }T
T{ fixture proc-keys-cut set-refused -> outcome-invalid 12 30 0 }T
T{ fixture v4-lemma set-refused -> outcome-invalid 6 11 0 }T
T{ fixture set41-uncounted set-refused -> outcome-invalid 1 10 0 }T
\ After a refusal, simp-data? is false and the next read works again.
T{ simp-data? good simp-congr-count -> false outcome-ok 3 }T
\ Format 4 has no realized records: unsupported, never "none"; 4.1 has.
T{ dec simp-realized -> 0 false outcome-unsupported }T
: good41 ( -- outcome ) s" tests/front/simp-data/good41.elab.ndjson" fx ;
T{ good41 simp-realized-count dec simp-realized rot drop -> outcome-ok 2 true outcome-ok }T
\ A later read of an older format forgets 4.1: unsupported again.
T{ s" tests/front/simp-data/plain32.elab.ndjson" fx dec simp-realized rot drop
   -> outcome-ok false outcome-unsupported }T

\ The heap: every allocation of a read of the good file refused in turn
\ (the kind's slabs and memo given back before each run, so that each
\ first claim allocates): full or the same three lemmas, never another.
\ (Format 4.1's default simp set, front/simp-set-data.fs, below.)
: anew ( -- )
  simp-congrs sweep-slab-anew simp-reals sweep-slab-anew elab-orders sweep-slab-anew
  sd-index memo-free ;
' anew sweep-slabs-xt !
: read-good ( e -- x outcome ) drop good41 simp-congr-count simp-realized-count + swap ;
T{ 0 ' read-good heap-sweep swap 0> -> 0 true }T
\ The same for the default set's records: full or the same four values.
: set-anew ( -- )
  anew ss-lemmas sweep-slab-anew ss-lefts sweep-slab-anew ss-procs sweep-slab-anew
  ss-unfolds sweep-slab-anew ss-sets sweep-slab-anew ss-pre sweep-slab-anew
  ss-post sweep-slab-anew ss-proc-pre sweep-slab-anew ss-proc-post sweep-slab-anew ;
' set-anew sweep-slabs-xt !
: read-set ( e -- x outcome ) drop s" tests/front/simp-data/set41.elab.ndjson" fx set-kept swap ;
T{ 0 ' read-set heap-sweep swap 0> -> 0 true }T
' noop sweep-slabs-xt !
\ A context's memo and slabs go with it: no heap block kept.
: in-fresh ( -- ) context-new throw dup context-use good drop context-main context-use
  context-free throw ;
T{ live-blocks @ in-fresh live-blocks @ = -> true }T
T{ elab-reset simp-congr-count simp-data? -> 0 false }T
T{ lib stage-free -> }T
\ After context-new the registry of kinds is sealed: a kind added now
\ aborts, the registry unchanged (tests/front/elab-kinds.fs, which never
\ makes a context, tests the others).
: add-kind ( c-addr u -- ior )
  0 ['] noop 2swap ['] elab-add-kind catch dup if nip nip nip nip else nip then ;
T{ context-sealed? s" late" add-kind s" late" ed-kind-index -> true -2 false }T
