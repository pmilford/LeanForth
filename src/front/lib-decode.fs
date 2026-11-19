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
require ../core/annotations.fs
require ../import/stage.fs
require ./dag-walk.fs
require ./elab-data.fs

\ Sources of nodes. Two families are decoded by the same walks: the
\ stage's tier (a library declaration's type, value and rules) and
\ front/elab-data.fs's smart-unfolding bodies (below). A source is a walk
\ record (dag-walk.fs; first, so that a source is its walk) and the words
\ that read one of its nodes as the tier holds it: its tier tag (tag-*,
\ tag-level-*) and its children in the tier's order (an application's
\ function and argument, a binder's type and body, a let's type, value
\ and body, a projection's or an mdata's term). A level source has the
\ words up to lbs-param.
begin-structure /lbs
  /dw +field lbs-walk  \ first: a source's address is its walk's
  field: lbs-tag       \ ( x -- tag ) its tier tag
  field: lbs-child     \ ( x i -- x' ) its children (i 0 1 2), in the tier's order
  field: lbs-count     \ ( -- n ) the source's nodes: the walk's size
  field: lbs-param     \ levels ( l -- index outcome ): a universe parameter
  field: lbs-levels    \ terms ( -- src ): the source of their levels
  field: lbs-name      \ ( e -- name outcome ) a constant's or projection's run name
  field: lbs-field     \ ( e -- i ) a projection's field
  field: lbs-arg#      \ ( e -- n ) a constant's universe arguments
  field: lbs-arg       \ ( e i -- l ) its i-th, i < n
  field: lbs-text      \ ( e -- c-addr u ) a natural literal's digits
  field: lbs-label     \ ( term e -- term outcome ) a binder's name, if any
  field: lbs-mdata     \ ( e -- term outcome ) an mdata node's term
end-structure
: src-tag ( x src -- tag ) lbs-tag @ execute ;
: src-child ( x i src -- x' ) lbs-child @ execute ;
: src-a ( x src -- x' ) 0 swap src-child ;
: src-b ( x src -- x' ) 1 swap src-child ;
: src-c ( x src -- x' ) 2 swap src-child ;
: src-count ( src -- n ) lbs-count @ execute ;
: src-param ( l src -- index outcome ) lbs-param @ execute ;
: src-name ( e src -- name outcome ) lbs-name @ execute ;
: src-field ( e src -- i ) lbs-field @ execute ;
: src-arg# ( e src -- n ) lbs-arg# @ execute ;
: src-arg ( e i src -- l ) lbs-arg @ execute ;
: src-text ( e src -- c-addr u ) lbs-text @ execute ;
: src-label ( term e src -- term outcome ) lbs-label @ execute ;
: src-mdata ( e src -- term outcome ) lbs-mdata @ execute ;
begin-structure /lbd
  field: lbd-stage        \ the library's stage, or 0
  field: lbd-count        \ its declarations when bound: the memo's size
  field: lbd-terms-gen    \ the stores' generations the memos are for
  field: lbd-levels-gen
  field: lbd-names-gen
  field: lbd-memo         \ heap: per declaration of the stage, its record + 1
  /lbs +field lbd-xwalk    \ expressions; its memo kept for the run
  /lbs +field lbd-lwalk    \ levels; likewise
  /lbs +field lbd-sxwalk   \ smart-unfolding bodies' nodes; likewise
  /lbs +field lbd-slwalk   \ and their levels
  field: lbd-data-gen     \ the elaboration data's generation they are for
  field: lbd-snames       \ the body's definition's universe parameters
  field: lbd-snames#
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
  lbd-free-records lbd lbd-memo heap-release lbd lbd-xwalk dw-free lbd lbd-lwalk dw-free
  lbd lbd-sxwalk dw-free lbd lbd-slwalk dw-free lbd-stamp! ;
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
    dup lbd-parts slab-push ok-then? 0= if r> drop exit then r@ execute
  repeat r> 2drop outcome-ok ;
: lbd-tier-prefix ( n -- n' ) lbd-tier name-prefix@ ;
: lbd-num? ( id -- flag ) lf-name-tag@ lf-name-tag-num = ;
: lbd-seek ( n id -- n' outcome )
  dup lbd-num? if lf-name-payload lbd-tier name-seek-num exit then
  lf-name-text lbd-tier name-seek-str ;
: lbd-sought ( -- n outcome )
  0 begin lbd-parts slab-count over 0< 0= and while
    lbd-parts slab-pop lbd-seek ok-then? 0= if no-result exit then
  repeat outcome-ok ;
: lbd-tier-name ( id -- n outcome )
  ['] lf-name-prefix@ lbd-parts! dup ok? if drop lbd-sought else no-result then ;
: lbd-num-name? ( n -- flag ) lbd-tier name-tag@ tag-name-num = ;
: lbd-run-part ( id n -- id' true | false )
  dup lbd-num-name? if lbd-tier name-number@ lf-name-num else lbd-tier name-text@
    lf-name-str then ;
: lbd-run-parts ( -- id outcome )
  0 begin lbd-parts slab-count while
    lbd-parts slab-pop lbd-run-part 0= if -1 outcome-full exit then
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
: lbd-refuse ( walk x outcome -- image )
  dup ok? if drop nip else nip swap dw-refuse -1 then ;
: lbd-tables ( n walk -- outcome )
  dup dw-memo @ if 2drop outcome-ok exit then
  tuck dw-size ! dup dw-tables if dw-memo-erase outcome-ok else dw-free outcome-full then
    ;
: lbd-start ( walk -- walk ) outcome-ok over dw-outcome ! 0 over dw-top ! ;
: lbd-clean ( outcome walk -- outcome ) over ok? if drop else dw-memo-erase then ;
: lbd-go ( root walk -- image outcome ) lbd-start tuck dw-go rot lbd-clean ;
: lbd-walk ( root walk -- image outcome )
  2dup dw-done? if dw-image outcome-ok else lbd-go then ;
\ A walk over the n nodes of its family, its tables made at the first.
: lbd-kept ( root n walk -- image outcome )
  tuck lbd-tables ok-then? if lbd-walk else nip no-result then ;

\ ---- One walk over either source: the images of x's children, made
\ (dw-done?) before x is built; the pending tests, x's first child not
\ made yet among a, a b, a b c.
: src-a-img ( x src -- image ) tuck src-a swap dw-image ;
: src-b-img ( x src -- image ) tuck src-b swap dw-image ;
: src-c-img ( x src -- image ) tuck src-c swap dw-image ;
: src-ab-img ( x src -- a b ) 2dup src-b-img >r src-a-img r> ;
: src-ac-img ( x src -- a c ) 2dup src-c-img >r src-a-img r> ;
: lbd-a? ( x src -- child true | false ) tuck src-a swap dw-want ;
: lbd-ab? ( x src -- child true | false ) 2dup src-a -rot tuck src-b swap dw-want2 ;
: lbd-abc? ( x src -- child true | false )
  2dup lbd-ab? if nip nip true else tuck src-c swap dw-want then ;
\ A source's image of node x, the walk's tables made at the first use.
: lbd-run ( x src -- image outcome ) dup src-count swap lbd-kept ;

\ Levels: zero is the store's 0, a parameter what the source says.
: lbd-max-tag? ( tag -- flag ) dup tag-level-max = swap tag-level-imax = or ;
: lbd-l-pending ( l src -- child true | false )
  2dup src-tag dup tag-level-succ = if drop lbd-a? exit then
  lbd-max-tag? if lbd-ab? else 2drop false then ;
: lbd-succ ( l src -- index outcome ) src-a-img lf-level-succ lbd-made ;
: lbd-max ( l src -- index outcome ) src-ab-img lf-level-max lbd-made ;
: lbd-imax ( l src -- index outcome ) src-ab-img lf-level-imax lbd-made ;
: lbd-l-make ( l src -- index outcome )
  2dup src-tag case
    tag-level-zero of 2drop 0 outcome-ok endof  tag-level-succ of lbd-succ endof
    tag-level-max of lbd-max endof  tag-level-imax of lbd-imax endof
    tag-level-param of src-param endof  drop 2drop outcome-invalid no-result 0 endcase ;
: lbd-l-build ( l src -- index ) tuck lbd-l-make lbd-refuse ;
\ Level l of an expression source's levels.
: src-level ( l src -- index outcome ) lbs-levels @ execute lbd-run ;

\ Expressions: children first.
: lbd-pair-tag? ( tag -- flag ) dup tag-app = swap binder-tag? or ;
: lbd-one-tag? ( tag -- flag ) dup tag-proj = swap tag-mdata = or ;
: lbd-x-pending ( e src -- child true | false )
  2dup src-tag dup lbd-pair-tag? if drop lbd-ab? exit then
  dup let-tag? if drop lbd-abc? exit then lbd-one-tag? if lbd-a? else 2drop false then ;
: lbd-app ( e src -- term outcome ) src-ab-img lf-term-app lbd-made ;
: lbd-bvar ( e src -- term outcome ) src-a lf-term-bvar lbd-made ;
: lbd-sort ( e src -- term outcome )
  tuck src-a swap src-level ok-then? if lf-term-symbolic-sort lbd-made else no-result
  then ;
: lbd-nat ( e src -- term outcome )
  src-text lf-hterm-decimal if drop outcome-ok else -1 outcome-full then ;
\ A constant: its universe arguments as level pairs (index, identity),
\ then its reference and its term.
: lbd-pair, ( index -- outcome )
  dup lf-level-identity 0= if drop outcome-full exit then swap lbd-pairs slab-2push ;
: lbd-arg ( e src i -- outcome )
  swap dup >r src-arg r> src-level ok-then? if lbd-pair, then ;
: lbd-args ( e src -- outcome )
  lbd-pairs slab-clear 2dup src-arg# 0 ?do
    2dup i lbd-arg dup ok? 0= if nip nip unloop exit then drop
  loop 2drop outcome-ok ;
: lbd-cterm ( name -- term outcome )
  lf-name-generation @ 0 lbd-pairs slab-at lbd-pairs slab-count lf-cref-new
  if lf-cterm-new if drop outcome-ok exit then then -1 outcome-full ;
: lbd-const ( e src -- term outcome )
  2dup lbd-args dup ok? 0= if nip nip no-result exit then drop
  src-name ok-then? if lbd-cterm else no-result then ;
\ A projection: its structure's image and field, then its name.
: src-proj ( e src -- image i ) 2dup src-field >r src-a-img r> ;
: lbd-proj ( e src -- term outcome )
  2dup src-proj 2swap src-name ok-then? if swap lf-proj-of else nip nip no-result then ;
\ A binder: lam below tag-pi, named as the source names it.
: lbd-node ( e src tag -- term true | false )
  tag-pi < if src-ab-img lf-term-lam else src-ab-img lf-term-pi then ;
: lbd-binder ( e src tag -- term outcome )
  >r 2dup r> lbd-node if -rot src-label else 2drop -1 outcome-full then ;
\ A letE: the let of its value and the lambda of its type and body
\ (core/let-terms.fs), with its nonDep flag.
: lbd-let-lam ( e src -- lam true | false ) src-ac-img lf-term-lam ;
: lbd-let-named ( e src -- lam outcome )
  2dup lbd-let-lam if -rot src-label else 2drop -1 outcome-full then ;
: lbd-let ( e src tag -- term outcome )
  tag-let-nondep = >r 2dup lbd-let-named ok-then?
  if -rot src-b-img swap r> lf-let-make lbd-made else nip nip r> drop no-result then ;
\ Any other tag (a string literal, plan S5; a free variable) answers
\ unsupported.
: lbd-plain ( e src tag -- term outcome )
  case tag-app of lbd-app endof  tag-bvar of lbd-bvar endof  tag-sort of lbd-sort endof
    tag-const of lbd-const endof  tag-proj of lbd-proj endof  tag-nat of lbd-nat endof
    tag-mdata of src-mdata endof  drop 2drop outcome-unsupported no-result 0 endcase ;
: lbd-x-make ( e src -- term outcome )
  2dup src-tag dup binder-tag? if lbd-binder exit then
  dup let-tag? if lbd-let exit then lbd-plain ;
: lbd-x-build ( e src -- term ) tuck lbd-x-make lbd-refuse ;
\ A source's walk words: a level source's; a term source's, with the
\ word that gives the source of its levels (a context's records move as
\ it grows: a source keeps no address).
: lbd-level-walk ( src -- src )
  ['] lbd-l-pending over dw-pending ! ['] lbd-l-build over dw-build ! ;
: lbd-term-walk ( xt src -- src )
  tuck lbs-levels ! ['] lbd-x-pending over dw-pending ! ['] lbd-x-build over dw-build ! ;

\ ---- The tier's source: a library declaration's levels and expressions.
: lbd-lsrc ( -- src ) lbd lbd-lwalk ;
: lbd-xsrc ( -- src ) lbd lbd-xwalk ;
: lbd-ltag ( l -- tag ) lbd-tier level-tag@ ;
: lbd-lchild ( l i -- l' ) lbd-tier swap if level-b@ else level-a@ then ;
: lbd-levels# ( -- n ) lbd-tier tier-levels cons-numbers ;
: lbd-param ( l -- index outcome )
  lbd-tier level-name@ lf-libdec-run-name ok-then? if lf-level-param lbd-made else
    no-result then ;
: lbd-level ( l -- index outcome ) lbd-lsrc lbd-run ;
: lbd-tag ( e -- tag ) lbd-tier expr-tag@ ;
: lbd-ea ( e -- e' ) lbd-tier expr-a@ ;
: lbd-eb ( e -- e' ) lbd-tier expr-b@ ;
: lbd-echild ( e i -- e' )
  lbd-tier swap case 0 of expr-a@ endof 1 of expr-b@ endof drop expr-body@ 0 endcase ;
: lbd-exprs# ( -- n ) lbd-tier tier-exprs cons-numbers ;
\ A constant's name is its a, a projection's its payload.
: lbd-ename ( e -- name outcome )
  dup lbd-tag tag-proj = if lbd-tier expr-payload@ else lbd-ea then lf-libdec-run-name ;
: lbd-earg# ( e -- n ) lbd-eb lbd-tuples tuple-length ;
: lbd-earg ( e i -- l ) swap lbd-eb lbd-tuples tuple-item ;
: lbd-etext ( e -- c-addr u ) lbd-ea lbd-tier tier-texts text@ ;
\ A binder named as the tier names it when its node has no name yet, its
\ kind the tag's offset (Lean's BinderInfo; a let's lambda: 0).
: lbd-unnamed? ( term -- flag ) lf-pres-binder@ if 2drop false else true then ;
: lbd-label ( term name kind -- outcome )
  rot dup lbd-unnamed? if -rot lf-pres-binder! else drop 2drop outcome-ok then ;
: lbd-kind ( e -- kind ) lbd-tag dup binder-tag? if tag-lam - 3 and else drop 0 then ;
: lbd-named ( term e -- term outcome )
  dup lbd-kind >r lbd-tier expr-payload@ lf-libdec-run-name
  ok-then? 0= if r> drop exit then over swap r> lbd-label ;
\ An mdata expression (Lean's exporter writes none unless asked).
: lbd-no-mdata ( e -- -1 outcome ) drop outcome-unsupported no-result ;
: lbd-term ( e -- term outcome ) lbd-xsrc lbd-run ;
: lbd-tier-levels ( -- )
  lbd-lsrc lbd-level-walk ['] lbd-ltag over lbs-tag ! ['] lbd-lchild over lbs-child !
  ['] lbd-levels# over lbs-count ! ['] lbd-param swap lbs-param ! ;
: lbd-tier-walk ( -- src )
  ['] lbd-lsrc lbd-xsrc lbd-term-walk ['] lbd-tag over lbs-tag !
  ['] lbd-echild over lbs-child ! ['] lbd-exprs# over lbs-count ! ;
: lbd-tier-terms ( -- )
  lbd-tier-walk ['] lbd-ename over lbs-name ! ['] lbd-eb over lbs-field !
  ['] lbd-earg# over lbs-arg# ! ['] lbd-earg over lbs-arg ! ['] lbd-etext over lbs-text !
  ['] lbd-named over lbs-label ! ['] lbd-no-mdata swap lbs-mdata ! ;
' lbd-tier-levels context-setup
' lbd-tier-terms context-setup

\ ---- Smart-unfolding bodies (S2 merge B; docs/design/S2_INTERFACE.md
\ §3): a sunfold record's value, from front/elab-data.fs's nodes and
\ levels (numbered across records), decoded into the run's stores by the
\ same walks over sources of their own, kept as the library's, forgotten
\ with them and when the data is read again. A universe parameter k is
\ the definition's k-th (the names given), a constant the run's name of
\ its declaration (the stage's own outside a text's run), a sunfoldMatch
\ or sunfoldMatchAlt entry an annotation (core/annotations.fs), a
\ borrowed mark its term (the compiler's, never read by Meta).
\ Unsupported: a string literal (plan S5), a constant or structure the
\ library lacks, a body holding an inert node (format 3.1: metadata not
\ carried, MATHLIB_FRONT.md O1). Binders get no presentation names (a
\ body is shown only in messages).
: lbd-slsrc ( -- src ) lbd lbd-slwalk ;
: lbd-sxsrc ( -- src ) lbd lbd-sxwalk ;
: lbd-sun-forget ( -- )
  lbd-sxsrc dw-free lbd-slsrc dw-free elab-generation lbd lbd-data-gen ! ;
: lbd-sun-current ( -- )
  lbd-current elab-generation lbd lbd-data-gen @ <> if lbd-sun-forget then ;
\ Levels: their kinds are the tier's tags.
elab-level-zero tag-level-zero <> elab-level-succ tag-level-succ <> or
elab-level-max tag-level-max <> or elab-level-imax tag-level-imax <> or
elab-level-param tag-level-param <> or
[if] .( lib-decode.fs: elab-level-* differ from tier tags tag-level-*) cr abort [then]
: lbd-sname@ ( k -- name ) cells lbd lbd-snames @ + @ ;
: lbd-sparam ( l -- index outcome )
  elab-level-a dup lbd lbd-snames# @ u< 0= if drop outcome-invalid no-result exit then
  lbd-sname@ lf-level-param lbd-made ;
: lbd-slevels# ( -- n ) elab-levels slab-count ;
: lbd-slchild ( l i -- l' ) if elab-level-b else elab-level-a then ;
\ Nodes (elab-node-bvar .. elab-node-have, which the reader checks): a
\ node's tier tag, and its children from a (an application's), from b (a
\ binder's type and body, a let's type, value and body) or from c (a
\ projection's or an mdata's term).
: lbd-ntag-low ( kind -- tag )
  case elab-node-bvar of tag-bvar endof  elab-node-sort of tag-sort endof
    elab-node-app of tag-app endof  elab-node-lam of tag-lam endof
    elab-node-forall of tag-pi endof  drop tag-let 0 endcase ;
: lbd-ntag-high ( kind -- tag )
  case elab-node-lit of tag-nat endof  elab-node-str of tag-str endof
    elab-node-proj of tag-proj endof  elab-node-mdata of tag-mdata endof
    elab-node-const of tag-const endof  drop tag-let-nondep 0 endcase ;
: lbd-ntag ( n -- tag )
  elab-node-kind dup elab-node-lit < if lbd-ntag-low else lbd-ntag-high then ;
1 elab-node-lam lshift 1 elab-node-forall lshift or 1 elab-node-let lshift or
  1 elab-node-have lshift or constant lbd-b-kinds
1 elab-node-proj lshift 1 elab-node-mdata lshift or constant lbd-c-kinds
: lbd-kind-in? ( kind mask -- flag ) swap 1 swap lshift and 0<> ;
: lbd-nfirst ( n -- k )
  elab-node-kind dup lbd-b-kinds lbd-kind-in? 1 and
  swap lbd-c-kinds lbd-kind-in? 2 and or ;
: lbd-nfield ( n k -- x )
  case 0 of elab-node-a endof  1 of elab-node-b endof  2 of elab-node-c endof
    drop elab-node-d 0 endcase ;
: lbd-nchild ( n i -- x ) over lbd-nfirst + lbd-nfield ;
: lbd-snodes# ( -- n ) elab-nodes slab-count ;
\ A declaration's name in the run (lf-libdec-run-name in a text's run).
: lbd-sdecl ( d' -- name outcome )
  elab-decl-name lbd-stage@ if lf-libdec-run-name else outcome-ok then ;
: lbd-sknown ( n -- name outcome )
  elab-node-a dup 0< if drop outcome-unsupported no-result else lbd-sdecl then ;
: lbd-narg# ( n -- k ) elab-node-levels nip ;
: lbd-narg ( n i -- l ) swap elab-node-levels drop swap cells + @ ;
: lbd-ntext ( n -- c-addr u ) elab-node-a elab-key-text ;
: lbd-anonymous ( term n -- term outcome ) drop outcome-ok ;
: lbd-s-key ( kind -- key )
  elab-sunfold-match = if lf-annot-match else lf-annot-match-alt then ;
\ An inert node is refused here too, never read as an annotation.
: lbd-nmdata ( n -- term outcome )
  dup elab-node-a elab-inert = if drop outcome-unsupported no-result exit then
  dup elab-node-c lbd-sxsrc dw-image swap elab-node-a
  dup elab-borrowed = if drop outcome-ok else lbd-s-key lf-annot then ;
: lbd-snode ( n -- term outcome ) lbd-sxsrc lbd-run ;
: lbd-elab-levels ( -- )
  lbd-slsrc lbd-level-walk ['] elab-level-kind over lbs-tag !
  ['] lbd-slchild over lbs-child ! ['] lbd-slevels# over lbs-count !
  ['] lbd-sparam swap lbs-param ! ;
: lbd-elab-walk ( -- src )
  ['] lbd-slsrc lbd-sxsrc lbd-term-walk ['] lbd-snodes# over lbs-count !
  ['] lbd-nchild over lbs-child ! ['] lbd-ntag over lbs-tag !
  ['] lbd-sknown over lbs-name ! ;
: lbd-elab-terms ( -- )
  lbd-elab-walk ['] elab-node-b over lbs-field !
  ['] lbd-narg# over lbs-arg# ! ['] lbd-narg over lbs-arg ! ['] lbd-ntext over lbs-text !
  ['] lbd-anonymous over lbs-label ! ['] lbd-nmdata swap lbs-mdata ! ;
' lbd-elab-levels context-setup
' lbd-elab-terms context-setup
\ The body of sunfold record s, for a definition whose universe
\ parameters are the n names at addr.
: lf-libdec-sunfold ( s addr n -- body outcome )
  lbd lbd-snames# ! lbd lbd-snames ! lbd-sun-current
  dup elab-sunfold-usable? 0= if drop outcome-unsupported no-result exit then
  elab-sunfold-value lbd-snode ;

\ ---- Binder kinds (S1 §4): e's leading Pi binders, from the tier's tags.
: lbd-kind+ ( e tier slab -- e tier outcome ) >r 2dup expr-tag@ tag-pi - r> slab-push ;
: lf-tier-kinds ( e tier slab -- outcome )
  dup slab-clear >r begin 2dup expr-pi? while
    r@ lbd-kind+ ok-then? 0= if nip r> drop exit then tuck expr-b@ swap
  repeat 2drop r> drop outcome-ok ;
: lf-libdec-kinds ( d slab -- outcome )
  over lbd-in? 0= if slab-clear drop outcome-invalid exit then
  >r lbd-stage@ staged-type@ lbd-tier r> lf-tier-kinds ;
\ The domain of library declaration d's binder k (from 0, compact-exprs.fs's
\ expr-domain), whose kinds lf-tier-kinds reads: an eliminator's
\ alternative's fields (S2_INTERFACE 4); false when d's type has no
\ binder k or d is beyond the library.
: lf-libdec-domain ( d k -- e tier true | false )
  swap dup lbd-in? 0= if 2drop false exit then
  lbd-stage@ staged-type@ lbd-tier rot expr-domain dup if lbd-tier swap then ;

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
\ step ( r -- outcome ) per item, the first run, the rest chained with
\ ok-with.
: lbd-d, ( x -- outcome ) lbd-data slab-push ;
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
  dup lbd-t-params ['] lbd-t-indices ok-with ['] lbd-t-nested ok-with
  ['] lbd-t-flags ok-with ['] lbd-t-all ok-with ['] lbd-t-ctors ok-with nip ;
: lbd-c-induct ( r -- outcome ) more-ctor-induct lbd-item lbd-name, ;
: lbd-c-cidx ( r -- outcome ) more-ctor-cidx lbd-n, ;
: lbd-c-params ( r -- outcome ) more-ctor-params lbd-n, ;
: lbd-c-fields ( r -- outcome ) more-ctor-fields lbd-n, ;
: lbd-ctor-data ( r -- outcome )
  dup lbd-c-induct ['] lbd-c-cidx ok-with ['] lbd-c-params ok-with
  ['] lbd-c-fields ok-with nip ;
: lbd-r-params ( r -- outcome ) more-rec-params lbd-n, ;
: lbd-r-indices ( r -- outcome ) more-rec-indices lbd-n, ;
: lbd-r-motives ( r -- outcome ) more-rec-motives lbd-n, ;
: lbd-r-minors ( r -- outcome ) more-rec-minors lbd-n, ;
: lbd-r-k ( r -- outcome ) lbd-d lbd-k lbd-d, ;
: lbd-r-all ( r -- outcome ) more-rec-all lbd-names, ;
: lbd-r-rules ( r -- outcome ) more-rec-rules lbd-item lbd-rules ;
: lbd-rec-data ( r -- outcome )
  dup lbd-r-params ['] lbd-r-indices ok-with ['] lbd-r-motives ok-with
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
: lbd-giveback ( r -- ) lbd-free-record lbd-records slab-drop ;
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
