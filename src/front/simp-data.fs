\ Simp's elaboration data (plan row FE9, slice SD-a of
\ docs/design/TACTIC_SIMP.md; docs/design/SIMP_DATA.md section 3;
\ docs/programming/ELABORATION_DATA.md, "Format 4"): the congr records of
\ format 4, Lean's @[congr] lemmas (congrExtension,
\ Meta/Tactic/Simp/SimpCongrTheorems.lean), read as a kind of its own of
\ front/elab-data.fs's reader (elab-add-kind), and the two questions simp
\ asks of the data: which congruence lemmas a function has, in the order
\ Lean tries them, and whether a theorem carries Lean's defeq tag (read by
\ elab-data.fs). Untrusted and fail-closed like the rest of the data: a
\ lemma named here is only tried, and its use checked by the kernel; a
\ refused record refuses the whole file (elab-error gives its line and
\ code), so no answer below comes from a bad record.
\
\ A congr record: name, the lemma (a theorem, named by one record at
\ most: error 47); fun, the function (any declaration); hyps, its
\ hypotheses' places among the lemma's binders (increasing, each below
\ the number of the leading Pi binders of its type: error 37); priority;
\ rank, its place in its function's list. One function's records are one
\ run of lines ranked 0, 1, 2, ... in file order, as the writer sorts
\ them (error 48 otherwise). Members, names and numbers are checked as
\ elab-data.fs checks them (errors 10-14, 19, 22 for no room).
\
\ simp-data? ( -- flag ): the data read is of format 4, so the answers
\ below are Lean's; when it is not (no data, or an older format)
\ simp-congr-lemmas and simp-defeq? answer unsupported, never "none".
\ simp-congr-lemmas ( f -- c n outcome ): the congruence lemmas of
\ function declaration f, records c .. c+n-1 in the order Lean tries them
\ (n = 0: none); simp-congr@ ( c -- thm priority ), simp-congr-fun ( c --
\ f ), simp-congr-rank ( c -- rank ), simp-congr-hyps ( c -- addr n ) (the
\ places, cells), simp-congr-count ( -- n ). simp-defeq? ( d -- flag
\ outcome ): declaration d has Lean's defeq tag; simp-defeq-count ( -- n ).
\ Unchecked: c below simp-congr-count. simp-congr-kind is the kind's
\ number for elab-count.
\
\ Example (the simp slice's export read but not sealed, as
\ tests/front/simp-data.fs does; ite's one lemma, ite_congr):
\   s" tests/front/simp-slice.elab.ndjson" lib digest elab-read .   \ 0
\   s" ite" top simp-congr-lemmas . . simp-congr@ . s" ite_congr" top = .
\   \ prints 0 0 1 1000 -1
\
\ State: a context memo, sd-index, of a function's run (its first record
\ and length, under the key f 0) and of each lemma's record (key d 1), and
\ a context slab of the records (their places a span of elab-data.fs's
\ elab-orders); emptied by every
\ reset of the data (the kind's clear), freed with the context.
\ Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/memo.fs
require ./elab-data.fs

begin-structure /simp-congr
  field: sdc-decl   field: sdc-priority   \ a pair: simp-congr@
  field: sdc-fun   field: sdc-rank
  field: sdc-hyps   field: sdc-hyps#   \ its hypotheses' places: a span of elab-orders
end-structure
/memo context-record: sd-index
/simp-congr context-slab: simp-congrs
:noname ( -- ) sd-index memo-free ; context-teardown
0 constant sd-fun-role   1 constant sd-lemma-role

: sdc ( c -- addr ) simp-congrs slab-at ;
: sd-clear ( -- ) simp-congrs slab-clear sd-index memo-clear ;
: sd-ready ( -- outcome )
  sd-index memo-live? if outcome-ok else 2 2 sd-index memo-init then ;
: sd-order-bad ( -- outcome ) elab-e-congr-order elab-refuse ;

\ ---- A function's run: its first record and its length.
: sd-run ( f -- a-addr | 0 ) sd-fun-role sd-index memo-at ;
: sd-run@ ( a-addr -- first n ) dup @ swap cell+ @ ;
\ Rank r of record c continues the run: c follows its last record, r its length.
: sd-continues? ( c r a-addr -- flag ) sd-run@ rot over = >r + = r> and ;
: sd-extend ( c r a-addr -- outcome )
  dup >r sd-continues? r> swap if cell+ 1 swap +! outcome-ok else drop sd-order-bad then ;
\ Rank 0 opens the function's run, unless it has one.
: sd-open ( c f -- outcome )
  dup sd-run if 2drop sd-order-bad exit then
  sd-fun-role sd-index memo-claim elab-roomed
  ok-then? if 1 over cell+ ! ! outcome-ok else nip then ;
: sd-place ( c r f -- outcome )
  over if sd-run ?dup if sd-extend else 2drop sd-order-bad then else nip sd-open then ;

\ ---- The record's steps ( value c -- outcome ), in turn while ok.
: sdc-ready ( value c -- outcome ) 2drop sd-ready elab-roomed ;
: sd-new-lemma ( d -- d outcome )
  dup sd-lemma-role sd-index memo-at
  if elab-e-congr-twice elab-refuse else outcome-ok then ;
: sd-lemma ( index -- d outcome )
  elab-decl dup ok? if drop kind-thm elab-of-kind then dup ok? if drop sd-new-lemma then ;
: sdc-name! ( value c -- outcome )
  sdc swap c" name" elab-member sd-lemma ['] sdc-decl elab-put ;
: sdc-fun! ( value c -- outcome )
  sdc swap c" fun" elab-member elab-decl ['] sdc-fun elab-put ;
: sdc-priority! ( value c -- outcome )
  sdc swap c" priority" elab-member elab-u32 ['] sdc-priority elab-put ;
: sdc-hyps! ( value c -- outcome ) sdc sdc-hyps swap c" hyps" elab-member elab-numbers ;
: simp-congr-hyps ( c -- addr n ) sdc sdc-hyps elab-span@ ;
\ Increasing places, each below the lemma's leading binders.
: sd-hyp-next ( limit prev h -- limit h flag ) tuck < >r 2dup > r> and ;
: sd-hyps-fit? ( limit addr n -- flag )
  -1 -rot cells bounds ?do
    i @ sd-hyp-next 0= if 2drop false unloop exit then
  1 cells +loop 2drop true ;
: sdc-fit ( value c -- outcome )
  nip dup sdc sdc-decl @ elab-type-pis swap simp-congr-hyps sd-hyps-fit?
  if outcome-ok else elab-e-unfit elab-refuse then ;
: sdc-rank! ( value c -- outcome )
  sdc swap c" rank" elab-member elab-u32 ['] sdc-rank elab-put ;
: sdc-run@ ( c -- c r f ) dup sdc dup sdc-rank @ swap sdc-fun @ ;
: sdc-order ( value c -- outcome ) nip sdc-run@ sd-place ;
: sdc-index ( value c -- outcome )
  nip dup sdc sdc-decl @ sd-lemma-role sd-index memo! elab-roomed ;
create sdc-members
  s" fun" counted, s" hyps" counted, s" name" counted, s" priority" counted,
  s" rank" counted, 0 0 counted,
create sdc-form  sdc-members , ' simp-congrs ,
  ' sdc-ready , ' sdc-name! , ' sdc-fun! , ' sdc-priority! , ' sdc-hyps! , ' sdc-fit ,
  ' sdc-rank! , ' sdc-order , ' sdc-index , 0 ,
: sd-on-congr ( value -- outcome ) sdc-form elab-on-form ;
create sd-congr-key  s" congr" counted,
create sd-congr-form  sd-congr-key , ' sd-on-congr , ' sd-clear ,
sd-congr-form elab-add-kind constant simp-congr-kind

\ ---- The questions.
: simp-data? ( -- flag ) elab-format4? ;
: simp-congr-lemmas ( f -- c n outcome )
  simp-data? 0= if drop 0 0 outcome-unsupported exit then
  sd-run ?dup if sd-run@ else 0 0 then outcome-ok ;
: simp-congr@ ( c -- thm priority ) sdc cell-pair@ ;
: simp-congr-fun ( c -- f ) sdc sdc-fun @ ;
: simp-congr-rank ( c -- rank ) sdc sdc-rank @ ;
: simp-congr-count ( -- n ) simp-congrs slab-count ;
: simp-defeq? ( d -- flag outcome )
  simp-data? 0= if drop false outcome-unsupported exit then
  elab-tag-defeq elab-tagged? outcome-ok ;
: simp-defeq-count ( -- n ) elab-tag-defeq elab-tag-count ;

base !   \ the BASE this file was loaded with
