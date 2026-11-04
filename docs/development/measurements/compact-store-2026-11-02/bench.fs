\ Prototype (ADR 0016, measurement code): what one node build and one
\ instantiate step cost in Gforth, over a loaded input tier. Not a module of
\ src/. A scratch tier is added after the input: scratch nodes are appended
\ to the same arena (numbers from the input count up) and found through a
\ table of (node + 1, epoch) pairs, emptied by advancing the epoch. A build
\ probes the input table only when every child is an input node (ADR 0016
\ C3), then the scratch table, and appends on a miss: one probe sequence
\ per table. instantiate replaces bound variable `off` by a closed node,
\ lowers the larger ones, skips sub-terms whose loose range shows they are
\ untouched, and memoises (node, offset) in one reusable table emptied by
\ an epoch.
require ./main.fs

variable ic          \ input count: nodes below it are the input tier
variable sepoch      \ scratch epoch, also the memo's; slots of epoch 0 are empty
variable mfill  variable sfill   \ memo entries and scratch nodes this epoch
0 sepoch !
: sealed ( -- ) e-count ic ! 1 sepoch +! 0 mfill ! 0 sfill ! ;
: scratch? ( n -- flag ) ic @ u< 0= ;
: scratch-reset ( -- ) ic @ 4 * exprs arena-used ! 1 sepoch +! 0 mfill ! 0 sfill ! ;

\ The scratch table: 2^20 pairs (node + 1, epoch).
arena: stab  20 constant sbits  1 sbits lshift 1- constant smask
: stab-init ( -- ) 1 sbits lshift 2* dup stab arena-init stab arena-used !
  stab arena-base @ 1 sbits lshift 2* u32s erase ;
: s-node@ ( slot -- u ) 2* stab arena@ ;
: s-epoch@ ( slot -- u ) 2* 1+ stab arena@ ;
: s-claim ( id slot -- ) swap 1+ over 2* stab arena! sepoch @ swap 2* 1+ stab arena! ;
variable s-compared
: scratch-find ( h -- id true | slot false )
  smask and begin dup s-epoch@ sepoch @ = while
    1 s-compared +! dup s-node@ 1- dup ek= if nip true exit then drop 1+ smask and
  repeat false ;

\ Counters.
variable builds  variable input-hits  variable scratch-hits  variable made
variable input-probes  variable probe-skips
: counters-clear ( -- )
  0 builds ! 0 input-hits ! 0 scratch-hits ! 0 made ! 0 input-probes !
  0 probe-skips ! 0 s-compared ! ;
\ Whether a child of the node in ek is a scratch node (by kind).
: ek-tag ( -- tag ) 0 ek@ $1F and ;
: kids-scratch? ( -- flag )
  ek-tag dup t-app t-let within if drop 1 ek@ scratch? 2 ek@ scratch? or exit then
  dup let? if drop 1 ek@ scratch? 2 ek@ scratch? or 3 ek@ scratch? or exit then
  t-proj = if 1 ek@ scratch? else false then ;
: ek-hash ( -- h ) 0 ek@ 1 ek@ 2 ek@ 3 ek@ key4-hash ;
: in-input ( h -- id true | h false )
  kids-scratch? if 1 probe-skips +! false exit then
  1 input-probes +! dup expr-find if nip 1 input-hits +! true else drop false then ;
: build ( head a b c data -- id )
  ek! 1 builds +! ek-hash in-input if exit then
  scratch-find if 1 scratch-hits +! exit then
  1 sfill +! sfill @ smask 4 / 3 * > abort" scratch table full"
  expr-new tuck swap s-claim 1 made +! ;
\ Builders that compute the data word as load.fs does.
: mk-app ( f a -- id ) t-app -rot 0 2 pick e-data@ 2 pick e-data@ false data2 build ;
: mk-binder ( head t b -- id ) 0 2 pick e-data@ 2 pick e-data@ true data2 build ;
: mk-bvar ( i -- id ) t-bvar over 0 0 4 roll 1+ 0 0 >data build ;

\ The memo: 2^18 slots of (node + 1, offset, result, epoch).
arena: memo  18 constant mbits  1 mbits lshift 1- constant mmask
: memo-init ( -- ) 1 mbits lshift 4 * dup memo arena-init memo arena-used !
  memo arena-base @ 1 mbits lshift 4 * u32s erase ;
: m@ ( slot field -- u ) swap 4 * + memo arena@ ;
: m! ( u slot field -- ) swap 4 * + memo arena! ;
: memo-hash ( n off -- slot ) swap fmix h+ mmask and ;
variable memo-hits
: memo-live? ( slot -- flag ) 3 m@ sepoch @ = ;
: memo-key? ( n off slot -- flag ) tuck 1 m@ = -rot 0 m@ swap 1+ = and ;
: memo-find ( n off -- result true | false )
  2dup memo-hash begin dup memo-live? while
    3dup memo-key? if nip nip 2 m@ 1 memo-hits +! true exit then 1+ mmask and
  repeat drop 2drop false ;
: memo-put ( n off result -- )
  1 mfill +! mfill @ mmask 4 / 3 * > abort" memo full"
  >r 2dup memo-hash begin dup memo-live? while 1+ mmask and repeat
  r> over 2 m! tuck 1 m! swap 1+ over 0 m! sepoch @ swap 3 m! ;

\ instantiate (n, off): n with bound variable off replaced by inst-value.
variable inst-value  variable steps  variable skips
: untouched? ( n off -- flag ) swap e-data@ d-range u< 0= ;
: inst-bvar ( n off -- n' )
  swap e-a@ 2dup = if 2drop inst-value @ exit then nip 1- mk-bvar ;
defer inst ( n off -- n' )
: inst-app ( n off -- n' ) over e-a@ over inst >r swap e-b@ swap inst r> swap mk-app ;
: inst-binder ( n off -- n' )
  over e-a@ over inst >r over e-b@ swap 1+ inst >r e-head@ r> r> swap mk-binder ;
: inst-let ( n off -- n' )
  over e-a@ over inst >r over e-b@ over inst >r over 1+ e-a@ swap 1+ inst
  >r e-head@ r> r> r> swap rot ( head t v b ) 3dup let-data build ;
: inst-proj ( n off -- n' )
  over e-a@ swap inst >r dup e-head@ r> rot e-b@ 0 2 pick e-data@ dup d-range
  over d-flags rot d-depth 1+ >data build ;
: inst-node ( n off -- n' )
  over e-tag@ dup t-bvar = if drop inst-bvar exit then
  dup t-app = if drop inst-app exit then
  dup t-lam t-let within if drop inst-binder exit then
  dup let? if drop inst-let exit then
  t-proj = if inst-proj exit then
  drop ;   \ no other kind has loose bound variables
: inst-real ( n off -- n' )
  2dup untouched? if 1 skips +! drop exit then
  2dup memo-find if nip nip exit then
  1 steps +! 2dup inst-node >r r@ memo-put r> ;
' inst-real is inst

\ Benchmarks.
: closed-node ( -- n ) ic @ 0 ?do i e-tag@ t-sort = if i unloop exit then loop 0 ;
: lam? ( n -- flag ) e-tag@ t-lam t-forall within ;
: app? ( n -- flag ) e-tag@ t-app = ;
: .count ( n c-addr u -- ) type ." =" 0 .r ."  " ;
: .builds ( -- )
  builds @ s" builds" .count input-probes @ s" input-probes" .count
  probe-skips @ s" input-probes-skipped" .count input-hits @ s" found-in-input" .count
  scratch-hits @ s" found-in-scratch" .count made @ s" new-nodes" .count
  s-compared @ s" scratch-slots-compared" .count cr ;
\ Time per item of a loop, in nanoseconds.
: .per ( us n c-addr u -- ) type ."  ns each=" swap 1000 * swap 1 max / 0 .r cr ;
\ Every input lambda's body instantiated with a closed node, as beta
\ reduction does; the scratch tier and the memo are emptied after each.
variable bodies  variable bad
\ A sanity check of each result: its loose range is at most the body's
\ minus one (the variable replaced is gone, the others moved down).
: range-ok? ( body result -- flag ) e-data@ d-range swap e-data@ d-range lower u> 0= ;
: inst-body ( n -- )
  scratch-reset e-b@ dup 0 inst range-ok? 0= if 1 bad +! then 1 bodies +! ;
: .inst ( us -- )
  ." instantiate: lambda bodies=" bodies @ 0 .r ."  range-check-failures=" bad @ 0 .r ."  steps=" steps @ 0 .r
  ."  skipped=" skips @ 0 .r ."  memo-hits=" memo-hits @ 0 .r cr ."   " .builds
  dup steps @ s"   time per step" .per dup made @ s"   time per new node" .per
  ."   seconds " .secs cr ;
: bench-inst ( -- )
  sealed stab-init memo-init counters-clear 0 steps ! 0 skips ! 0 memo-hits !
  0 bodies ! 0 bad ! closed-node inst-value ! start
  ic @ 0 ?do i lam? if i inst-body then loop now t0 @ - .inst scratch-reset ;
\ Building application nodes, three ways, over every input application
\ app(f, a): app(a, f), whose children are input nodes (input probe, then
\ scratch probe; mostly new); app(previous result, f), whose first child is
\ a scratch node (scratch probe only; always new); app(f, a) again (found
\ in the input). The scratch tier is emptied every 2^18 new nodes.
variable prev  variable since
: maybe-reset ( -- )
  made @ since @ - $40000 < 0= if scratch-reset made @ since ! 0 prev ! then ;
: swapped ( n -- ) dup e-b@ swap e-a@ mk-app drop maybe-reset ;
: chained ( n -- )
  prev @ ?dup 0= if dup then swap e-a@ mk-app prev ! maybe-reset ;
: again ( n -- ) dup e-a@ swap e-b@ mk-app drop ;
: .build ( us c-addr u -- ) type .builds builds @ s"   time per build" .per ;
: build-loop ( xt -- us )
  sealed counters-clear 0 since ! 0 prev ! start
  ic @ 0 ?do i app? if i over execute then loop drop now t0 @ - scratch-reset ;
: bench-build ( -- )
  stab-init
  ['] swapped build-loop s" build, children in the input: " .build
  ['] chained build-loop s" build, a scratch child: " .build
  ['] again build-loop s" build, an existing input node: " .build ;
: bench ( c-addr u -- ) phase-load bench-build bench-inst ;
