\ A library declaration decoded for the front end (plan S1;
\ docs/design/S1_INTERFACE.md §1): while a LeanForth text runs, the Meta
\ layer sees the library as Lean's getConstInfo does, through
\ front/meta-env.fs's run mode, from the importer stage that holds it
\ (import/stage.fs; read, not sealed). A declaration is decoded from the
\ stage's tier into the run's stores the first time it is asked for and
\ kept for the run (memoized): its kind, name, universe parameters, type,
\ value, reducibility hint, and its inductive data laid out as
\ core/input.fs lays out the input's (lf-ity-*, lf-ict-*, lf-irc-*), so
\ that whnf.fs and defeq.fs read either alike. Names cross by content, as
\ cli/check-lf.fs's lfc-name does: a tier name becomes the run's name of
\ the same parts (lf-name-str, lf-name-num) and a run name is sought in
\ the tier part by part, adding none there.
\
\ Trust ([import], S1 §1): only the stage's read-only words are used
\ (stage-tier, stage-decls, stage-find, staged-*@, the tier's readers;
\ tests/front/test_front_imports.py holds front/ to that list). What is
\ decoded is scratch of the run: it never enters lfa-declarations, so no
\ text writes it as a record, and lfc-empty empties it (with the stores)
\ before the stage is sealed. The kernel reads the library itself, so a
\ wrong decode changes only what the front end elaborates.
\
\ How: expressions and levels are decoded by bottom-up walks
\ (dag-walk.fs) whose memo is kept for the run, so a shared node is made
\ once; a binder gets its name and kind in the presentation table only
\ when its node has none yet (present/binder-table.fs). Every memo is
\ stamped with the term, level and name stores' generations and forgotten
\ when any of them was reset since (a new text's run). An mdata
\ expression (Lean's exporter writes none unless asked) and a string
\ literal (plan S5) answer unsupported. Not after a scratch rollback
\ below a decoded node (core/scratch-marks.fs): the hand-over, the only
\ front-end rollback, decodes nothing.
\
\ Words: lf-libdec-stage! ( stage -- ) binds the library (0: none) and
\ forgets every decoded record; lf-libdec-reset ( -- ) forgets them and
\ the library; lf-libdec-stage ( -- stage ) the library bound;
\ lf-libdec-count ( -- n ) the library's declarations when it was bound
\ (the stage's count then: one that grows later adds none);
\ lf-libdec-find ( name -- d outcome ) the newest declaration of a run
\ name, invalid when none; lf-libdec-decl ( d -- r outcome ) declaration
\ d decoded (memoized), invalid beyond the library or for a kind with
\ none (an inductive block); lf-libdec-kind lf-libdec-dname
\ lf-libdec-type lf-libdec-value ( r -- x ) (value -1: none),
\ lf-libdec-hint ( r -- hint height ), lf-libdec-params ( r -- addr n ),
\ lf-libdec-data ( r -- addr|0 ) of a record; lf-libdec-run-name
\ ( n -- name outcome ) a tier name's run name; lf-tier-kinds ( e tier
\ slab -- outcome ) the binder kinds (0-3, Lean's BinderInfo) of e's
\ leading Pi binders, read from the tier's tags (S1 §4); lf-libdec-kinds
\ ( d slab -- outcome ) those of library declaration d's type, none and
\ invalid for d beyond the library. Outcomes: ok; invalid as above;
\ unsupported as above; full when a store, a slab or the heap refuses (a
\ refused declaration is given back whole, and a walk that stops forgets
\ its nodes under way, so that the next decode starts again).
\ State: one context record, lbd (the stage, its count when bound, the
\ stamps, the memo and the two walks), and the slabs lbd-records, lbd-parts, lbd-pairs and
\ lbd-data, members of the checker context (ADR 0009); every record's
\ parameters and data are heap blocks of their own, so their addresses
\ hold for the run. Untrusted front-end code. Loads in decimal whatever
\ BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/slab.fs
require ../lib/bytes.fs
require ../core/names.fs
require ../core/levels.fs
require ../core/terms.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/let-terms.fs
require ../core/literals.fs
require ../core/projections.fs
require ../core/input.fs
require ../present/binder-table.fs
require ../import/stage.fs
require ./dag-walk.fs

begin-structure /lbd
  field: lbd-stage        \ the library's stage, or 0
  field: lbd-count        \ its declarations when bound: the memo's size
  field: lbd-terms-gen    \ the stores' generations the memos are for
  field: lbd-levels-gen
  field: lbd-names-gen
  field: lbd-memo         \ heap: per declaration of the stage, its record + 1
  /dw +field lbd-xwalk    \ expressions; its memo kept for the run
  /dw +field lbd-lwalk    \ levels; likewise
end-structure
/lbd context-record: lbd
begin-structure /lbr
  field: lbr-decl         \ the stage's declaration it decodes
  field: lbr-kind         \ lf-kind-* (core/input.fs)
  field: lbr-name         \ the run's name
  field: lbr-type
  field: lbr-value        \ a term, or -1
  field: lbr-hint
  field: lbr-height
  field: lbr-params       \ heap: the universe parameters' run names
  field: lbr-params#
  field: lbr-data         \ heap: inductive data as core/input.fs's, or 0
end-structure
/lbr context-slab: lbd-records
1 cells context-slab: lbd-parts    \ a name's parts, the last first
2 cells context-slab: lbd-pairs    \ a constant's universe arguments
1 cells context-slab: lbd-data     \ a declaration's inductive data, being made

: lbd-stage@ ( -- stage ) lbd lbd-stage @ ;
: lbd-tier ( -- tier ) lbd-stage@ stage-tier ;
: lbd-tuples ( -- cons ) lbd-tier tier-tuples ;
: lf-libdec-stage ( -- stage ) lbd-stage@ ;
: lf-libdec-count ( -- n ) lbd lbd-count @ ;
: lbd-in? ( d -- flag ) lf-libdec-count u< ;
: lbd-push ( x slab -- outcome )
  1 over slab-claim ok-then? if swap slab-at ! outcome-ok else nip nip then ;
: lbd-pop ( slab -- x ) dup slab-count 1- over slab-at @ -1 rot slab-commit ;
: lbd-made ( x true | false -- x outcome ) if outcome-ok else -1 outcome-full then ;

\ ---- Forgetting: every record's blocks, the memo, the walks' tables;
\ then the stores' generations they are for.
: lbr@ ( r -- addr ) lbd-records slab-at ;
: lbd-free-record ( r -- ) lbr@ dup lbr-params heap-release lbr-data heap-release ;
: lbd-free-records ( -- )
  lbd-records slab-count 0 ?do i lbd-free-record loop lbd-records slab-clear ;
: lbd-gens ( -- t l n ) lf-term-generation @ lf-level-generation @ lf-name-generation @ ;
: lbd-stamp! ( -- ) lbd-gens lbd lbd-names-gen ! lbd lbd-levels-gen ! lbd lbd-terms-gen !
  ;
: lbd-stale? ( -- flag )
  lbd-gens lbd lbd-names-gen @ <> swap lbd lbd-levels-gen @ <> or
  swap lbd lbd-terms-gen @ <> or ;
: lbd-forget ( -- )
  lbd-free-records lbd lbd-memo heap-release
  lbd lbd-xwalk dw-free lbd lbd-lwalk dw-free lbd-stamp! ;
' lbd-forget context-teardown
: lbd-current ( -- ) lbd-stale? if lbd-forget then ;
: lf-libdec-reset ( -- ) lbd-forget 0 lbd lbd-stage ! 0 lbd lbd-count ! ;
: lbd-decls ( stage -- n ) dup if stage-decls then ;
: lf-libdec-stage! ( stage -- )
  lf-libdec-reset dup lbd-decls lbd lbd-count ! lbd lbd-stage ! ;

\ ---- Names. A run name sought in the tier part by part, root first
\ (-1: the tier has none; full when the tier has no room for the
\ candidate it compares); a tier name made in the run's store.
: lbd-parts! ( n xt -- outcome )
  >r lbd-parts slab-clear begin dup while
    dup lbd-parts lbd-push ok-then? 0= if r> drop exit then r@ execute
  repeat r> 2drop outcome-ok ;
: lbd-tier-prefix ( n -- n' ) lbd-tier name-prefix@ ;
: lbd-num? ( id -- flag ) lf-name-tag@ lf-name-tag-num = ;
: lbd-seek ( n id -- n' outcome )
  dup lbd-num? if lf-name-payload lbd-tier name-seek-num exit then
  lf-name-text lbd-tier name-seek-str ;
: lbd-sought ( -- n outcome )
  0 begin lbd-parts slab-count over 0< 0= and while
    lbd-parts lbd-pop lbd-seek ok-then? 0= if no-result exit then
  repeat outcome-ok ;
: lbd-tier-name ( id -- n outcome )
  ['] lf-name-prefix@ lbd-parts! dup ok? if drop lbd-sought else no-result then ;
: lbd-num-name? ( n -- flag ) lbd-tier name-tag@ tag-name-num = ;
: lbd-run-part ( id n -- id' true | false )
  dup lbd-num-name? if lbd-tier name-number@ lf-name-num else lbd-tier name-text@
    lf-name-str then ;
: lbd-run-parts ( -- id outcome )
  0 begin lbd-parts slab-count while
    lbd-parts lbd-pop lbd-run-part 0= if -1 outcome-full exit then
  repeat outcome-ok ;
: lf-libdec-run-name ( n -- name outcome )
  ['] lbd-tier-prefix lbd-parts! dup ok? if drop lbd-run-parts else no-result then ;
: lbd-staged ( n -- d outcome )
  dup 0< if drop -1 outcome-invalid exit then
  lbd-stage@ stage-find if outcome-ok else -1 outcome-invalid then ;
: lf-libdec-find ( name -- d outcome )
  lbd-stage@ 0= if drop -1 outcome-invalid exit then
  lbd-tier-name ok-then? if lbd-staged else no-result then ;

\ ---- The walks kept for the run (dag-walk.fs): their tables made at the
\ first use, for every node the tier holds; a walk that stops erases the
\ memo (its nodes under way would read as a cycle), a done node is read.
: lbd-refuse ( x outcome walk -- image ) over ok? if 2drop else dw-refuse drop -1 then ;
: lbd-tables ( n walk -- outcome )
  dup dw-memo @ if 2drop outcome-ok exit then
  tuck dw-size ! dup dw-tables if dw-memo-erase outcome-ok else dw-free outcome-full then
    ;
: lbd-start ( walk -- walk ) outcome-ok over dw-outcome ! 0 over dw-top ! ;
: lbd-clean ( outcome walk -- outcome ) over ok? if drop else dw-memo-erase then ;
: lbd-go ( root walk -- image outcome ) lbd-start tuck dw-go rot lbd-clean ;
: lbd-walk ( root walk -- image outcome )
  2dup dw-done? if dw-image outcome-ok else lbd-go then ;

\ ---- Levels: zero is the store's 0, a parameter its run name's.
: lbd-lwalk@ ( -- walk ) lbd lbd-lwalk ;
: lbd-ltag ( l -- tag ) lbd-tier level-tag@ ;
: lbd-la ( l -- l' ) lbd-tier level-a@ ;
: lbd-lb ( l -- l' ) lbd-tier level-b@ ;
: lbd-a? ( l walk -- child true | false ) swap lbd-la swap dw-want ;
: lbd-b? ( l walk -- child true | false ) swap lbd-lb swap dw-want ;
: lbd-ab? ( l walk -- child true | false ) 2dup lbd-a? if nip nip true else lbd-b? then ;
: lbd-max-tag? ( tag -- flag ) dup tag-level-max = swap tag-level-imax = or ;
: lbd-l-pending ( l walk -- child true | false )
  over lbd-ltag dup tag-level-succ = if drop lbd-a? exit then
  lbd-max-tag? if lbd-ab? else 2drop false then ;
: lbd-limg ( l -- index ) lbd-lwalk@ dw-image ;
: lbd-two ( l -- left right ) dup lbd-la lbd-limg swap lbd-lb lbd-limg ;
: lbd-param ( l -- index outcome )
  lbd-tier level-name@ lf-libdec-run-name ok-then? if lf-level-param lbd-made else
    no-result then ;
: lbd-succ ( l -- index outcome ) lbd-la lbd-limg lf-level-succ lbd-made ;
: lbd-max ( l -- index outcome ) lbd-two lf-level-max lbd-made ;
: lbd-imax ( l -- index outcome ) lbd-two lf-level-imax lbd-made ;
: lbd-l-make ( l -- index outcome )
  dup lbd-ltag case
    tag-level-zero of drop 0 outcome-ok endof  tag-level-succ of lbd-succ endof
    tag-level-max of lbd-max endof  tag-level-imax of lbd-imax endof
    tag-level-param of lbd-param endof  nip outcome-invalid no-result rot endcase ;
: lbd-l-build ( l walk -- index ) >r lbd-l-make r> lbd-refuse ;
: lbd-levels# ( -- n ) lbd-tier tier-levels cons-numbers ;
: lbd-level ( l -- index outcome )
  lbd-levels# lbd-lwalk@ lbd-tables ok-then? if lbd-lwalk@ lbd-walk else no-result then ;

\ ---- Expressions: children first (an application's and a binder's two,
\ a letE's type, value and body, a projection's structure).
: lbd-xwalk@ ( -- walk ) lbd lbd-xwalk ;
: lbd-tag ( e -- tag ) lbd-tier expr-tag@ ;
: lbd-ea ( e -- e' ) lbd-tier expr-a@ ;
: lbd-eb ( e -- e' ) lbd-tier expr-b@ ;
: lbd-ebody ( e -- e' ) lbd-tier expr-body@ ;
: lbd-x? ( e walk xt -- child true | false ) rot swap execute swap dw-want ;
: lbd-xa? ( e walk -- child true | false ) ['] lbd-ea lbd-x? ;
: lbd-xb? ( e walk -- child true | false ) ['] lbd-eb lbd-x? ;
: lbd-xab? ( e walk -- child true | false ) 2dup lbd-xa? if nip nip true else lbd-xb? then
  ;
: lbd-xabc? ( e walk -- child true | false )
  2dup lbd-xab? if nip nip true else ['] lbd-ebody lbd-x? then ;
: lbd-pair-tag? ( tag -- flag ) dup tag-app = swap binder-tag? or ;
: lbd-x-pending ( e walk -- child true | false )
  over lbd-tag dup lbd-pair-tag? if drop lbd-xab? exit then
  dup let-tag? if drop lbd-xabc? exit then tag-proj = if lbd-xa? else 2drop false then ;
: lbd-img ( e -- term ) lbd-xwalk@ dw-image ;
: lbd-app ( e -- term outcome ) dup lbd-ea lbd-img swap lbd-eb lbd-img lf-term-app
  lbd-made ;
: lbd-bvar ( e -- term outcome ) lbd-ea lf-term-bvar lbd-made ;
: lbd-sort ( e -- term outcome )
  lbd-ea lbd-level ok-then? if lf-term-symbolic-sort lbd-made else no-result then ;
: lbd-nat ( e -- term outcome )
  lbd-ea lbd-tier tier-texts text@ lf-hterm-decimal if drop outcome-ok else -1
    outcome-full then ;
\ A constant: its universe arguments as level pairs (index, identity),
\ then its reference and its term.
: lbd-pair, ( index -- outcome )
  dup lf-level-identity 0= if drop outcome-full exit then swap
  1 lbd-pairs slab-claim ok-then? if lbd-pairs slab-at 2! outcome-ok else nip nip then ;
: lbd-arg ( t i -- outcome ) swap lbd-tuples tuple-item lbd-level ok-then? if lbd-pair,
  then ;
: lbd-args ( t -- outcome )
  lbd-pairs slab-clear outcome-ok over lbd-tuples tuple-length 0 ?do
    drop dup i lbd-arg dup ok? 0= if nip unloop exit then
  loop nip ;
: lbd-cterm ( name -- term outcome )
  lf-name-generation @ 0 lbd-pairs slab-at lbd-pairs slab-count lf-cref-new
  if lf-cterm-new if drop outcome-ok exit then then -1 outcome-full ;
: lbd-const ( e -- term outcome )
  dup lbd-eb lbd-args ok-then? 0= if no-result exit then
  lbd-ea lf-libdec-run-name ok-then? if lbd-cterm else no-result then ;
: lbd-proj ( e -- term outcome )
  dup lbd-tier expr-payload@ lf-libdec-run-name ok-then? 0= if nip no-result exit then
  over lbd-eb rot lbd-ea lbd-img -rot lf-proj-of ;
\ A binder, named as the tier names it when its node has no name yet.
: lbd-node ( e tag -- term true | false )
  >r dup lbd-ea lbd-img swap lbd-eb lbd-img r> tag-pi < if lf-term-lam else lf-term-pi
    then ;
: lbd-unnamed? ( term -- flag ) lf-pres-binder@ if 2drop false else true then ;
: lbd-label ( term name kind -- outcome )
  rot dup lbd-unnamed? if -rot lf-pres-binder! else drop 2drop outcome-ok then ;
: lbd-named ( term e kind -- term outcome )
  >r lbd-tier expr-payload@ lf-libdec-run-name ok-then? 0= if r> drop exit then
  over swap r> lbd-label ;
: lbd-binder ( e tag -- term outcome )
  2dup lbd-node 0= if 2drop -1 outcome-full exit then -rot tag-lam - 3 and lbd-named ;
\ A letE: the let of its value and the lambda of its type and body
\ (core/let-terms.fs), with its nonDep flag.
: lbd-let-lam ( e -- lam true | false ) dup lbd-ea lbd-img swap lbd-ebody lbd-img
  lf-term-lam ;
: lbd-let-named ( e -- lam outcome )
  dup lbd-let-lam if swap 0 lbd-named else drop -1 outcome-full then ;
: lbd-let ( e tag -- term outcome )
  tag-let-nondep = >r dup lbd-let-named ok-then? 0= if nip r> drop no-result exit then
  swap lbd-eb lbd-img swap r> lf-let-make lbd-made ;
: lbd-plain ( e tag -- term outcome )
  case tag-app of lbd-app endof  tag-bvar of lbd-bvar endof  tag-sort of lbd-sort endof
    tag-const of lbd-const endof  tag-proj of lbd-proj endof  tag-nat of lbd-nat endof
    nip outcome-unsupported no-result rot endcase ;
: lbd-x-make ( e -- term outcome )
  dup lbd-tag dup binder-tag? if lbd-binder exit then
  dup let-tag? if lbd-let exit then lbd-plain ;
: lbd-x-build ( e walk -- term ) >r lbd-x-make r> lbd-refuse ;
: lbd-exprs# ( -- n ) lbd-tier tier-exprs cons-numbers ;
: lbd-term ( e -- term outcome )
  lbd-exprs# lbd-xwalk@ lbd-tables ok-then? if lbd-xwalk@ lbd-walk else no-result then ;
:noname ( -- )
  ['] lbd-l-pending lbd-lwalk@ dw-pending ! ['] lbd-l-build lbd-lwalk@ dw-build !
  ['] lbd-x-pending lbd-xwalk@ dw-pending ! ['] lbd-x-build lbd-xwalk@ dw-build ! ;
    context-setup

\ ---- Binder kinds (S1 §4): e's leading Pi binders, from the tier's tags.
: lbd-pi-in? ( e tier -- flag ) expr-tag@ tag-pi tag-let within ;
: lbd-kind+ ( e tier slab -- e tier outcome ) >r 2dup expr-tag@ tag-pi - r> lbd-push ;
: lf-tier-kinds ( e tier slab -- outcome )
  dup slab-clear >r begin 2dup lbd-pi-in? while
    r@ lbd-kind+ ok-then? 0= if nip r> drop exit then tuck expr-b@ swap
  repeat 2drop r> drop outcome-ok ;
: lf-libdec-kinds ( d slab -- outcome )
  over lbd-in? 0= if slab-clear drop outcome-invalid exit then
  >r lbd-stage@ staged-type@ lbd-tier r> lf-tier-kinds ;

\ ---- A declaration's record, filled step by step ( r -- outcome ): the
\ steps read the stage's declaration the record names (lbr-decl).
create lbd-kinds   \ per staged kind from kind-axiom on; 0: none (a block)
  lf-kind-axiom , lf-kind-definition , lf-kind-theorem , lf-kind-opaque ,
  lf-kind-quotient , 0 , lf-kind-inductive , lf-kind-constructor , lf-kind-recursor ,
here lbd-kinds - 1 cells / constant lbd-kinds#
kind-recursor kind-axiom - 1+ lbd-kinds# <>
[if] .( lib-decode.fs: lbd-kinds needs one entry per staged kind) cr abort [then]
: lbd-d ( r -- d ) lbr@ lbr-decl @ ;
: lbd-staged-kind ( r -- kind ) lbd-d lbd-stage@ staged-kind@ ;
: lbd-kind-of ( r -- kind )
  lbd-staged-kind kind-axiom - dup 0 lbd-kinds# within if cells lbd-kinds + @ else
    drop 0 then ;
: lbd-s-kind ( r -- outcome )
  dup lbd-kind-of dup 0= if 2drop outcome-invalid exit then
  swap lbr@ lbr-kind ! outcome-ok ;
: lbd-s-name ( r -- outcome )
  dup lbd-d lbd-stage@ staged-name@ lf-libdec-run-name ok-then? if swap lbr@ lbr-name !
    outcome-ok else nip then ;
\ The universe parameters: a heap block of their run names.
: lbd-block ( n field -- outcome )
  swap cells 1 max allocate if 2drop outcome-full else swap ! outcome-ok then ;
: lbd-params-t ( d -- t n )
  lbd-stage@ staged-params@ dup none? if drop 0 0 else dup lbd-tuples tuple-length then ;
: lbd-param, ( t i addr -- outcome )
  >r tuck swap lbd-tuples tuple-item lf-libdec-run-name
  ok-then? if swap cells r> + ! outcome-ok else nip r> drop then ;
: lbd-params-fill ( t n addr -- outcome )
  swap outcome-ok swap 0 ?do drop 2dup i swap lbd-param, dup ok? 0= if leave then loop nip
    nip ;
: lbd-s-params ( r -- outcome )
  dup lbd-d lbd-params-t rot lbr@ 2dup lbr-params# ! lbr-params
  2dup lbd-block ok-then? if @ lbd-params-fill else nip nip then ;
\ The type, and the value of a definition, theorem or opaque declaration.
: lbd-term! ( e r xt -- outcome )
  >r swap lbd-term ok-then? if swap lbr@ r> execute ! outcome-ok else nip r> drop then ;
: lbd-s-type ( r -- outcome )
  dup lbd-d lbd-stage@ staged-type@ swap ['] lbr-type lbd-term! ;
: lbd-valued? ( r -- flag )
  lbr@ lbr-kind @ dup lf-kind-definition = over lf-kind-theorem = or swap lf-kind-opaque =
    or ;
: lbd-s-value ( r -- outcome )
  dup lbd-valued? if dup lbd-d lbd-stage@ staged-value@ swap ['] lbr-value lbd-term! else
    drop outcome-ok then ;
\ A definition's hints, its height when they are regular (else opaque, 0).
: lbd-def? ( r -- flag ) lbr@ lbr-kind @ lf-kind-definition = ;
: lbd-hints ( r -- hints ) lbd-d lbd-stage@ staged-hints@ ;
: lbd-height ( r -- ) dup lbd-d lbd-stage@ staged-hint@ swap lbr@ lbr-height ! ;
: lbd-hint! ( r -- )
  dup lbd-hints 2dup swap lbr@ lbr-hint ! lf-hint-regular = if lbd-height else drop then ;
: lbd-s-hint ( r -- outcome ) dup lbd-def? if lbd-hint! else drop then outcome-ok ;
\ Inductive data, as the feed lays it out (import/feed.fs), names as run
\ names: a type [params indices nested flags] all ctors; a constructor
\ [induct cidx params fields]; a recursor [params indices motives minors k]
\ all rules (count, then constructor, fields and right side of each). One
\ step ( r -- outcome ) per item, chained with ok-with.
: lbd-d, ( x -- outcome ) lbd-data lbd-push ;
: lbd-item ( r k -- u ) swap lbd-d lbd-stage@ staged-item ;
: lbd-n, ( r k -- outcome ) lbd-item lbd-d, ;
: lbd-name, ( n -- outcome ) lf-libdec-run-name ok-then? if lbd-d, then ;
: lbd-list, ( t -- outcome )
  dup lbd-tuples tuple-length dup lbd-d, ok-then? 0= if nip exit then
  0 ?do i over lbd-tuples tuple-item lbd-name, dup ok? 0= if nip unloop exit then drop
    loop
  drop outcome-ok ;
: lbd-names, ( r k -- outcome ) lbd-item lbd-list, ;
: lbd-rhs, ( e -- outcome ) lbd-term ok-then? if lbd-d, then ;
: lbd-rule-x ( u j -- outcome )
  /rule-items mod case rule-ctor-item of lbd-name, endof rule-rhs-item of lbd-rhs, endof
    drop lbd-d, 0 endcase ;
: lbd-rule-item ( t j -- outcome ) tuck swap lbd-tuples tuple-item swap lbd-rule-x ;
: lbd-rules ( t -- outcome )
  dup lbd-tuples tuple-length dup /rule-items mod if 2drop outcome-invalid exit then
  dup /rule-items / lbd-d, ok-then? 0= if nip exit then
  0 ?do dup i lbd-rule-item dup ok? 0= if nip unloop exit then drop loop drop outcome-ok ;
: lbd-flags ( d -- flags )
  dup lbd-stage@ staged-rec? lf-ity-rec-bit and swap lbd-stage@ staged-reflexive?
    lf-ity-reflexive-bit and or ;
: lbd-k ( d -- flag ) lbd-stage@ staged-k? ;
: lbd-t-params ( r -- outcome ) more-type-params lbd-n, ;
: lbd-t-indices ( r -- outcome ) more-type-indices lbd-n, ;
: lbd-t-nested ( r -- outcome ) more-type-nested lbd-n, ;
: lbd-t-flags ( r -- outcome ) lbd-d lbd-flags lbd-d, ;
: lbd-t-all ( r -- outcome ) more-type-all lbd-names, ;
: lbd-t-ctors ( r -- outcome ) more-type-ctors lbd-names, ;
: lbd-type-data ( r -- outcome )
  outcome-ok ['] lbd-t-params ok-with ['] lbd-t-indices ok-with ['] lbd-t-nested ok-with
  ['] lbd-t-flags ok-with ['] lbd-t-all ok-with ['] lbd-t-ctors ok-with nip ;
: lbd-c-induct ( r -- outcome ) more-ctor-induct lbd-item lbd-name, ;
: lbd-c-cidx ( r -- outcome ) more-ctor-cidx lbd-n, ;
: lbd-c-params ( r -- outcome ) more-ctor-params lbd-n, ;
: lbd-c-fields ( r -- outcome ) more-ctor-fields lbd-n, ;
: lbd-ctor-data ( r -- outcome )
  outcome-ok ['] lbd-c-induct ok-with ['] lbd-c-cidx ok-with ['] lbd-c-params ok-with
  ['] lbd-c-fields ok-with nip ;
: lbd-r-params ( r -- outcome ) more-rec-params lbd-n, ;
: lbd-r-indices ( r -- outcome ) more-rec-indices lbd-n, ;
: lbd-r-motives ( r -- outcome ) more-rec-motives lbd-n, ;
: lbd-r-minors ( r -- outcome ) more-rec-minors lbd-n, ;
: lbd-r-k ( r -- outcome ) lbd-d lbd-k lbd-d, ;
: lbd-r-all ( r -- outcome ) more-rec-all lbd-names, ;
: lbd-r-rules ( r -- outcome ) more-rec-rules lbd-item lbd-rules ;
: lbd-rec-data ( r -- outcome )
  outcome-ok ['] lbd-r-params ok-with ['] lbd-r-indices ok-with ['] lbd-r-motives ok-with
  ['] lbd-r-minors ok-with ['] lbd-r-k ok-with ['] lbd-r-all ok-with
  ['] lbd-r-rules ok-with nip ;
: lbd-kind-data ( r kind -- outcome )
  case kind-type of lbd-type-data endof  kind-ctor of lbd-ctor-data endof
    kind-recursor of lbd-rec-data endof  nip outcome-ok swap endcase ;
: lbd-keep ( r -- outcome )
  lbd-data slab-count dup 0= if 2drop outcome-ok exit then
  over lbr@ lbr-data lbd-block ok-then? 0= if exit then
  lbr@ lbr-data @ 0 lbd-data slab-at swap lbd-data slab-count cells move outcome-ok ;
: lbd-s-data ( r -- outcome )
  lbd-data slab-clear dup dup lbd-staged-kind lbd-kind-data ok-then? if lbd-keep then ;
create lbd-steps   \ ( r -- outcome ) each, in order (outcome-steps); 0 ends them
  ' lbd-s-kind , ' lbd-s-name , ' lbd-s-params , ' lbd-s-type , ' lbd-s-value ,
  ' lbd-s-hint , ' lbd-s-data , 0 ,
: lbd-fill ( r -- outcome ) lbd-steps outcome-steps ;

\ ---- Records: claimed blank, kept in the memo when filled, else given
\ back with their blocks.
: lbd-blank ( d addr -- ) dup /lbr erase -1 over lbr-value ! lbr-decl ! ;
: lbd-new ( d -- r outcome )
  1 lbd-records slab-claim ok-then? 0= if nip no-result exit then
  tuck lbr@ lbd-blank outcome-ok ;
: lbd-memo@ ( d -- addr ) cells lbd lbd-memo @ + ;
: lbd-remember ( r -- ) dup 1+ swap lbd-d lbd-memo@ ! ;
: lbd-memo-ready ( -- outcome )
  lbd lbd-memo @ if outcome-ok exit then
  lf-libdec-count cells 1 max dup allocate if 2drop outcome-full exit then
  tuck swap erase lbd lbd-memo ! outcome-ok ;
: lbd-giveback ( r -- ) lbd-free-record -1 lbd-records slab-commit ;
: lbd-decode ( d -- r outcome )
  lbd-new ok-then? 0= if no-result exit then
  dup lbd-fill dup ok? if drop dup lbd-remember outcome-ok exit then
  swap lbd-giveback no-result ;
: lbd-known ( d -- r true | false ) lbd-memo@ @ +1>number ;
: lf-libdec-decl ( d -- r outcome )
  lbd-current dup lbd-in? 0= if drop -1 outcome-invalid exit then
  lbd-memo-ready ok-then? 0= if no-result exit then
  dup lbd-known if nip outcome-ok else lbd-decode then ;
: lf-libdec-kind ( r -- kind ) lbr@ lbr-kind @ ;
: lf-libdec-dname ( r -- name ) lbr@ lbr-name @ ;
: lf-libdec-type ( r -- term ) lbr@ lbr-type @ ;
: lf-libdec-value ( r -- term ) lbr@ lbr-value @ ;
: lf-libdec-hint ( r -- hint height ) lbr@ dup lbr-hint @ swap lbr-height @ ;
: lf-libdec-params ( r -- addr n ) lbr@ dup lbr-params @ swap lbr-params# @ ;
: lf-libdec-data ( r -- addr|0 ) lbr@ lbr-data @ ;

base !   \ the BASE this file was loaded with
