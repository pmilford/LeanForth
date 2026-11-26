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
\ most: error 47); fun, the function, the constant both sides of the
\ lemma's conclusion (an Eq or an Iff) call with as many arguments
\ (error 37); hyps, its
\ hypotheses' places among the lemma's binders (increasing, each below
\ the number of the leading Pi binders of its type: error 37); priority;
\ rank, its place in its function's list. One function's records are one
\ run of lines ranked 0, 1, 2, ... in file order, as the writer sorts
\ them, their priorities falling (error 48 otherwise). Members, names
\ and numbers are checked as elab-data.fs checks them (errors 10-14, 19,
\ 22 for no room).
\
\ A realized record (format 4.1, slice SD-b; scripts/export_simp.lean):
\ name, a theorem f.congr_simp Lean realized in the library
\ (Meta/CongrTheorems.lean:405-446); fun, f (error 37 when name is not
\ f's congr_simp; one record a function at most, error 47); kind, the
\ text congr_simp; arg_kinds, the kinds congrKindsExt holds for it
\ (numbers 0-3: congr-thms.fs's lf-ck-fixed, -eq, -cast, -subsingleton;
\ another number error 10). simp-realized ( f -- r flag outcome ): f's
\ record r and true, or false (Lean would realize the theorem in the
\ user's file: no record), unsupported for data older than 4.1;
\ simp-realized@ ( r -- thm ), simp-realized-kinds ( r -- addr n ) (the
\ kinds, cells), simp-realized-count ( -- n ).
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
\ and length, under the key f 0), of each lemma's record (key d 1) and of
\ a function's realized record (key f 2), and the context slabs of the
\ records (their places and kinds spans of elab-data.fs's elab-orders);
\ emptied by every
\ reset of the data (the kind's clear), freed with the context.
\ Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/memo.fs
require ../lib/find.fs
require ./elab-data.fs

begin-structure /simp-congr
  field: sdc-decl   field: sdc-priority   \ a pair: simp-congr@
  field: sdc-fun   field: sdc-rank
  field: sdc-hyps   field: sdc-hyps#   \ its hypotheses' places: a span of elab-orders
end-structure
/memo context-record: sd-index
/simp-congr context-slab: simp-congrs
:noname ( -- ) sd-index memo-free ; context-teardown
0 constant sd-fun-role   1 constant sd-lemma-role   2 constant sd-real-role

: sdc ( c -- addr ) simp-congrs slab-at ;
: sd-clear ( -- ) simp-congrs slab-clear sd-index memo-clear ;
: sd-ready ( -- outcome )
  sd-index memo-live? if outcome-ok else 2 2 sd-index memo-init then ;
: sd-order-bad ( -- outcome ) elab-e-congr-order elab-refuse ;

\ ---- A function's run: its first record and its length.
: sd-run ( f -- a-addr | 0 ) sd-fun-role sd-index memo-at ;
: sd-run@ ( a-addr -- first n ) dup @ swap cell+ @ ;
\ Rank r of record c continues the run: c follows its last record, r its length.
\ The record and rank that continue the run.
: sd-next ( a-addr -- c r ) sd-run@ tuck + swap ;
: sd-continues? ( c r a-addr -- flag ) sd-next d= ;
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
: sd-theorem ( index -- d outcome ) elab-decl dup ok? if drop kind-thm elab-of-kind then ;
: sd-lemma ( index -- d outcome ) sd-theorem dup ok? if drop sd-new-lemma then ;
\ A record's member read into its field at a-addr: its lemma (a theorem
\ named once), its function (a declaration).
: sd-at! ( a-addr x outcome -- outcome ) ['] noop elab-put ;
: sd-name! ( value a-addr -- outcome ) swap c" name" elab-member sd-lemma sd-at! ;
: sd-fun! ( value a-addr -- outcome ) swap c" fun" elab-member elab-decl sd-at! ;
: sdc-name! ( value c -- outcome ) sdc sdc-decl sd-name! ;
: sdc-fun! ( value c -- outcome ) sdc sdc-fun sd-fun! ;
: sdc-priority! ( value c -- outcome )
  sdc swap c" priority" elab-member elab-u32 ['] sdc-priority elab-put ;
: sdc-hyps! ( value c -- outcome ) sdc sdc-hyps swap c" hyps" elab-member elab-numbers ;
: simp-congr-hyps ( c -- addr n ) sdc sdc-hyps elab-span@ ;
\ Increasing places, each below the lemma's leading binders (elab-data.fs's
\ ed-below?, review of SD-a finding 10, plan task SD-b.7).
: sd-hyp-next ( prev h -- h flag ) tuck < ;
: sd-increasing? ( addr n -- flag )
  -1 -rot cells bounds ?do
    i @ sd-hyp-next 0= if drop false unloop exit then
  1 cells +loop drop true ;
: sd-hyps-fit? ( limit c -- flag )
  sdc sdc-hyps tuck swap ed-below? if elab-span@ sd-increasing? else drop false then ;
: sd-fit ( flag -- outcome ) if outcome-ok else elab-e-unfit elab-refuse then ;
: sdc-fit ( value c -- outcome )
  nip dup sdc sdc-decl @ elab-type-pis swap sd-hyps-fit? sd-fit ;
\ Lean's funName (mkSimpCongrTheorem, SimpCongrTheorems.lean): the
\ lemma's conclusion, past its written Pis, is Eq _ lhs rhs or Iff lhs
\ rhs (Expr.eqOrIff?), lhs and rhs call one constant with as many
\ arguments, and fun is that constant (error 37 otherwise). Lean's check
\ of the hypotheses' shape is not repeated: the kernel checks each use
\ of a lemma.
: sd-a@ ( e -- u ) elab-tier expr-a@ ;   \ an application's function, a constant's name
: sd-const? ( e -- flag ) elab-tier expr-tag@ tag-const = ;
\ e's call: the constant at the head of its spine and its number of
\ arguments; -1 -1 when the head is not a constant.
: sd-call ( e -- name n )
  elab-tier expr-app-spine over sd-const? if swap sd-a@ swap else 2drop -1 -1 then ;
: sd-named ( c-addr u -- name ) 0 -rot elab-tier name-seek-str drop ;   \ -1: absent
\ The relation a call of n arguments may be: Eq with 3, Iff with 2; else -2.
: sd-relation-name ( n -- name )
  dup 3 = if drop s" Eq" sd-named exit then 2 = if s" Iff" sd-named else -2 then ;
: sd-relation? ( e -- flag ) sd-call sd-relation-name = ;
\ A relation's sides: its last argument and the one before.
: sd-rhs ( e -- rhs ) elab-tier expr-b@ ;
: sd-lhs ( e -- lhs ) sd-a@ sd-rhs ;
: sd-sides ( e -- lhs rhs ) dup sd-lhs swap sd-rhs ;
\ The constant both sides call with as many arguments; else -1.
: sd-same-call ( e -- name )
  sd-sides sd-call 2>r sd-call 2dup 2r> d= if drop else 2drop -1 then ;
: sd-lhs-fun ( e -- name ) dup sd-relation? if sd-same-call exit then drop -1 ;
: sd-conclusion ( d -- e ) elab-type@ elab-tier expr-pi-end ;
: sdc-lhs-fun ( c -- name ) sdc sdc-decl @ sd-conclusion sd-lhs-fun ;
: sdc-head ( value c -- outcome )
  nip dup sdc-lhs-fun swap sdc sdc-fun @ elab-decl-name = sd-fit ;
: sdc-rank! ( value c -- outcome )
  sdc swap c" rank" elab-member elab-u32 ['] sdc-rank elab-put ;
: sdc-run@ ( c -- c r f ) dup sdc dup sdc-rank @ swap sdc-fun @ ;
: sdc-order ( value c -- outcome ) nip sdc-run@ sd-place ;
\ Priorities fall along a run, as Lean's insert keeps each list
\ (SimpCongrTheorems.lean): rank r's at most rank r-1's, record c-1.
: sd-priority@ ( c -- p ) sdc sdc-priority @ ;
: sd-falls? ( c -- flag )
  dup sdc sdc-rank @ 0= if drop true exit then
  dup 1- sd-priority@ swap sd-priority@ u< 0= ;
: sdc-falls ( value c -- outcome ) nip sd-falls? if outcome-ok else sd-order-bad then ;
: sdc-index ( value c -- outcome )
  nip dup sdc sdc-decl @ sd-lemma-role sd-index memo! elab-roomed ;
\ The run's order (error 48) comes before the head (error 37): a record
\ out of place is refused for its place, whatever its lemma.
\ Each form is one table: its members' names follow its steps.
create sdc-form  0 , ' simp-congrs ,
  ' sdc-ready , ' sdc-name! , ' sdc-fun! , ' sdc-priority! , ' sdc-hyps! , ' sdc-fit ,
  ' sdc-rank! , ' sdc-order , ' sdc-falls , ' sdc-head , ' sdc-index , 0 ,
sdc-form elab-keys-here
  s" fun" counted, s" hyps" counted, s" name" counted, s" priority" counted,
  s" rank" counted, 0 0 counted,
sdc-form ' sd-clear s" congr" elab-add-kind constant simp-congr-kind

\ ---- Realized congruence theorems (format 4.1).
begin-structure /simp-real
  field: sdr-decl   field: sdr-fun
  field: sdr-kinds   field: sdr-kinds#   \ the argument kinds: a span of elab-orders
end-structure
/simp-real context-slab: simp-reals
: sdr ( r -- addr ) simp-reals slab-at ;
\ A realized theorem's name: a theorem; that it is fun's (sdr-fit) says the rest.
: sdr-name! ( value r -- outcome )
  sdr sdr-decl swap c" name" elab-member sd-theorem sd-at! ;
: sdr-fun! ( value r -- outcome ) sdr sdr-fun sd-fun! ;
: sdr-kind ( value r -- outcome )
  drop c" kind" elab-member s" congr_simp" elab-text= 0= if elab-malformed exit then
  outcome-ok ;
: sdr-kinds! ( value r -- outcome )
  sdr sdr-kinds swap c" arg_kinds" elab-member elab-numbers ;
: simp-realized-kinds ( r -- addr n ) sdr sdr-kinds elab-span@ ;
: sd-kind? ( n -- flag ) 4 u< ;   \ congr-thms.fs's four kinds, 0-3
: sd-bad-kind? ( addr i -- addr flag ) over swap cells + @ sd-kind? 0= ;
: sdr-kinds-ok ( value r -- outcome )
  nip simp-realized-kinds ['] sd-bad-kind? find-index
  if drop elab-malformed else outcome-ok then ;
\ A kind for each of fun's leading binders at least (Lean counts them
\ through a reducing telescope, so more may come): else error 37.
: sdr-arity ( value r -- outcome )
  nip dup sdr sdr-fun @ elab-type-pis swap simp-realized-kinds nip > 0= sd-fit ;
\ name is fun's congr_simp (Lean's reserved name, CongrTheorems.lean:399).
: sd-congr-simp-of ( f -- name )
  elab-decl-name s" congr_simp" elab-tier name-seek-str drop ;
: sdr-fit ( value r -- outcome )
  nip sdr dup sdr-fun @ sd-congr-simp-of swap sdr-decl @ elab-decl-name = sd-fit ;
: sdr-index ( value r -- outcome )
  nip dup sdr sdr-fun @ sd-real-role 2dup sd-index memo-at
  if 2drop drop elab-e-real-twice elab-refuse exit then sd-index memo! elab-roomed ;
: sdr-clear ( -- ) simp-reals slab-clear ;
create sdr-form  0 , ' simp-reals ,
  ' sdc-ready , ' sdr-name! , ' sdr-fun! , ' sdr-kind , ' sdr-kinds! , ' sdr-kinds-ok ,
  ' sdr-arity , ' sdr-fit , ' sdr-index , 0 ,
sdr-form elab-keys-here
  s" arg_kinds" counted, s" fun" counted, s" kind" counted, s" name" counted, 0 0 counted,
sdr-form ' sdr-clear s" realized" elab-add-kind41 constant simp-realized-kind

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
: simp-realized ( f -- r flag outcome )
  elab-format41? 0= if drop 0 false outcome-unsupported exit then
  sd-real-role sd-index memo@ if true else 0 false then outcome-ok ;
: simp-realized@ ( r -- thm ) sdr sdr-decl @ ;
: simp-realized-count ( -- n ) simp-reals slab-count ;

base !   \ the BASE this file was loaded with
