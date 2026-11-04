\ Lean's level normalisation and level equality (ADR 0011, Amendment 1):
\ ports of Lean 4.35.0's level.cpp (commit eb6cafb7) -- normalize
\ (454-516) with push_max_args (420-427), mk_max of a list (429-444) and
\ mk_succ (446-452), is_norm_lt (395-418) and is_equivalent (518-521) --
\ and of Lean's name order for parameters (name.cpp 191-220; strings by
\ lean_string_lt, object.cpp 2210-2215: bytes, then length), on the
\ simplifying constructors of level-make. [kernel] code: experimental,
\ not through the review gate. Untrusted.
\ Lean's normalize is incomplete on purpose: an imax normalizes to
\ mk_imax of its normalized sides, and a max that mk_imax makes there is
\ not sorted again. So two levels with equal values for every assignment
\ can be different here, exactly as for Lean (docs/project/BEYOND_LEAN.md,
\ BL-1).
\ Preconditions: those of level-make (validated graphs, parameter IDs
\ that are interned names).
\ State: one record, lf-lnorm-state: normalize's frames (lib/frame.fs),
\ the first failure of the call, the fuel left, the argument stack of the
\ max case (its top and cells), a mark of the level store before the
\ call, a merge's cursors, and per level of the input the normal form
\ found. A member of the checker context (lib/context.fs).
\ The normal forms are new nodes of the level store, given back when the
\ call ends; the facts
\ of level-make are truncated with them. Single-threaded within one
\ context.
\ Depth (plan task 6.2.0): normalize keeps a level's pending work on
\ its frames, an explicit stack that grows with the depth of the level
\ graph; push_max_args keeps the maxes still to flatten on a growable
\ array; is_norm_lt and the name order loop. So no depth is limited by
\ the host's stacks or a constant: a stack the heap cannot grow is full.

require ../lib/lib.fs
require ../lib/slab.fs
require ../lib/store-columns.fs
require ../core/diagnostics.fs
require ../core/levels.fs
require ../core/names.fs
require ../core/name-equal.fs
require ./level-make.fs

128 constant lf-lnorm-capacity   \ the argument stack's first room, in cells

begin-structure /lf-lnrec
  /frames +field lf-lnrec-frames                    \ normalize's visits (fuel unused)
  field: lf-lnrec-status                            \ the first failure; ok while none
  field: lf-lnrec-fuel                              \ fuel left
  field: lf-lnrec-top                               \ argument cells in use
  /store-mark +field lf-lnrec-mark                  \ the level store before the call
  field: lf-lnrec-i                                 \ a merge: the next of the left run,
  field: lf-lnrec-j                                 \ the next of the right run,
  field: lf-lnrec-k                                 \ the next scratch cell,
  field: lf-lnrec-mid                               \ the right run's start,
  field: lf-lnrec-hi                                \ and its end;
  field: lf-lnrec-width                             \ a pass's run width,
  field: lf-lnrec-to                                \ and the arguments' end
end-structure
/lf-lnrec context-record: lf-lnorm-state
\ The max case's argument stack: a growable array with no fixed limit
\ (plan task 6.2.0; a max of a thousand parameters flattens to a thousand
\ arguments); one the heap cannot grow is full.
1 cells context-slab: lf-lnorm-arg-cells
\ push_max_args's maxes still to flatten (no fixed limit).
1 cells context-slab: lf-lnorm-todo-cells
\ Per level, a column of the level store (lib/store-columns.fs): its
\ normal form + 1, or 0.
/slab context-record: lf-lnorm-memo-column
1 cells ' lf-lnorm-memo-column lf-level-columns column-add

: lf-lnorm-status ( -- addr ) lf-lnorm-state lf-lnrec-status ;
\ Fuel left after lf-level-equivalent; level-compare continues with it.
: lf-lnorm-fuel ( -- addr ) lf-lnorm-state lf-lnrec-fuel ;
: lf-lnorm-top ( -- addr ) lf-lnorm-state lf-lnrec-top ;
: lf-lnorm-arg ( i -- addr ) cells lf-lnorm-arg-cells slab-base + ;
: lf-lnorm-memo ( level -- addr ) lf-lnorm-memo-column column-at ;
: lf-lnorm-clear ( -- ) lf-lnorm-memo-column column-erase ;
: lf-lnorm-site ( -- site ) c" level-normalize lf-level-equivalent" ;
: lf-lnorm-frames ( -- frames ) lf-lnorm-state lf-lnrec-frames ;

\ ---------------------------------------------------------------------------
\ The first failure wins; once there is one, every step does nothing and
\ gives some level (the result is then discarded).
: lf-lnorm-ok? ( -- flag ) lf-lnorm-status @ ok? ;
: lf-lnorm-fail ( outcome -- ) lf-lnorm-ok? if lf-lnorm-status ! else drop then ;
\ One unit of fuel for each level normalized, max argument pushed and
\ pair of arguments ordered; none left is exhausted.
: lf-lnorm-dry ( -- )
  lf-lnorm-ok? if lf-lnorm-fuel @ lf-lnorm-site lf-diag-exhausted then
  outcome-exhausted lf-lnorm-fail ;
: lf-lnorm-spend ( -- )
  lf-lnorm-fuel @ 0> if -1 lf-lnorm-fuel +! else lf-lnorm-dry then ;
\ Room on a growable stack or array the heap would not grow: full,
\ recorded with the cells in use, the capacity and code (the frames' or a
\ work stack's).
: lf-lnorm-no-room ( used capacity code -- )
  lf-lnorm-ok? if lf-lnorm-site swap lf-diag-note else drop 2drop then
  outcome-full lf-lnorm-fail ;
\ New nodes: a full store or spent serial (recorded by lf-level-add) is full.
: lf-lnorm-made ( level true | false -- level )
  if exit then outcome-full lf-lnorm-fail 0 ;
: lf-lnorm-succ ( level -- level' ) lf-lnorm-ok? if lf-level-succ lf-lnorm-made then ;
: lf-lnorm-succs ( level k -- level' ) 0 ?do lf-lnorm-succ loop ;
: lf-lnorm-max ( l1 l2 -- level )
  lf-lnorm-ok? if lf-lmk-max lf-lnorm-made else drop then ;
: lf-lnorm-imax ( l1 l2 -- level )
  lf-lnorm-ok? if lf-lmk-imax lf-lnorm-made else drop then ;

\ ---------------------------------------------------------------------------
\ Lean's name order: -1, 0 or 1. Unchecked: both names passed
\ lf-lnorm-name-ok?, so every prefix chain ends at the anonymous name.
: lf-lnorm-sign ( n -- -1|0|1 ) dup 0> 1 and swap 0< or ;
: lf-lnorm-depth ( id -- n )
  0 swap begin dup while lf-name-prefix@ swap 1+ swap repeat drop ;
: lf-lnorm-up ( id n -- id' ) 0 ?do lf-name-prefix@ loop ;
\ One component each (203-215): a string after a number; strings by bytes
\ and then length (Forth's COMPARE), numbers by value.
: lf-lnorm-str? ( id -- flag ) lf-name-tag@ lf-name-tag-str = ;
: lf-lnorm-limb ( a b -- n )
  2dup lf-name-tags= 0= if drop lf-lnorm-str? 1 and 2* 1- exit then
  over lf-lnorm-str? if lf-name-text rot lf-name-text 2swap compare exit then
  lf-name-payload swap lf-name-payload swap - lf-lnorm-sign ;
\ Two names of the same depth: their prefixes first, then the last parts,
\ that is the first differing component from the root. Walked from the
\ last components up to the first equal prefix, keeping the order of the
\ highest pair that differs.
: lf-lnorm-kept ( n a b -- n' a b ) 2dup lf-lnorm-limb ?dup if >r rot drop r> -rot then ;
: lf-lnorm-level-cmp ( a b -- n )
  0 -rot begin 2dup <> while lf-lnorm-kept lf-name-prefixes repeat 2drop ;
\ Any two names (216-219): the shorter name's depth decides first, then a
\ prefix comes before its extensions.
: lf-lnorm-depths ( a b -- da db ) lf-lnorm-depth swap lf-lnorm-depth swap ;
: lf-lnorm-trimmed ( a b da db -- a' b' )
  2dup min tuck - >r - rot swap lf-lnorm-up swap r> lf-lnorm-up ;
: lf-lnorm-name-cmp ( a b -- n )
  2dup lf-lnorm-depths 2dup - lf-lnorm-sign >r lf-lnorm-trimmed lf-lnorm-level-cmp
  ?dup if r> drop else r> then ;
\ A name whose every component is valid and well formed, in either mode
\ of the name store (lf-name-part-ok?).
: lf-lnorm-limb-ok? ( id -- flag )
  dup lf-name-valid? if lf-name-part-ok? else drop false then ;
: lf-lnorm-name-ok? ( id -- flag )
  begin dup while dup lf-lnorm-limb-ok? 0= if drop false exit then lf-name-prefix@ repeat
  drop true ;

\ ---------------------------------------------------------------------------
\ is_norm_lt: by base (the level under its successors), then offset.
\ Different bases: by kind (level.h 30: zero, succ, max, imax, param, as
\ LeanForth's tags), parameters by name, max and imax by their left sides,
\ or by their right sides when the left ones are equal. Lean recurses on
\ the sides; its last call is in tail position, so this loops.
: lf-lnorm-lefts ( a b -- a' b' ) lf-level-first@ swap lf-level-first@ swap ;
: lf-lnorm-rights ( a b -- a' b' ) lf-level-second@ swap lf-level-second@ swap ;
: lf-lnorm-sides ( ba bb -- a' b' )
  2dup lf-lnorm-lefts lf-lmk-same? if lf-lnorm-rights else lf-lnorm-lefts then ;
\ Two different parameters need their names: an ID that is not a valid
\ name leaves the comparison undecided (unknown).
: lf-lnorm-named? ( a b -- flag ) lf-lnorm-name-ok? swap lf-lnorm-name-ok? and ;
: lf-lnorm-unnamed ( a b -- false ) 2drop outcome-unknown lf-lnorm-fail false ;
: lf-lnorm-names< ( ba bb -- flag )
  lf-lnorm-lefts 2dup lf-lnorm-named? if lf-lnorm-name-cmp 0< else lf-lnorm-unnamed then ;
\ One step: the answer and true, or the next pair and false.
: lf-lnorm-bases< ( ba bb -- flag true | a' b' false )
  2dup lf-lmk-tags 2dup <> if < nip nip true exit then 2drop
  dup lf-level-tag@ lf-level-tag-param = if lf-lnorm-names< true else lf-lnorm-sides false then ;
: lf-lnorm-lt-step ( a b -- flag true | a' b' false )
  2dup = if 2drop false true exit then
  lf-lmk-offset rot lf-lmk-offset rot 2>r swap
  2dup lf-lmk-same? if 2drop 2r> < true else 2r> 2drop lf-lnorm-bases< then ;
: lf-lnorm-lt ( a b -- flag ) begin lf-lnorm-lt-step until ;

\ The argument stack. A push the heap cannot make room for is full.
: lf-lnorm-crowded ( level -- )
  drop lf-lnorm-ok? if lf-lnorm-top @ lf-lnorm-arg-cells slab-capacity lf-lnorm-site
    lf-diag-work-stack-full lf-diag-note then outcome-full lf-lnorm-fail ;
: lf-lnorm-room? ( n -- flag ) 1+ lf-lnorm-arg-cells slab-hold ok? ;
: lf-lnorm-push ( level -- )
  lf-lnorm-top @ dup lf-lnorm-room?
  if lf-lnorm-arg ! 1 lf-lnorm-top +! else drop lf-lnorm-crowded then ;
\ push_max_args: the arguments of nested maxes, left to right, each level
\ visited spending one unit of fuel. The maxes still to flatten wait on a
\ growable array, the right side below the left; one the heap cannot grow
\ is full.
: lf-lnorm-todo ( -- slab ) lf-lnorm-todo-cells ;
: lf-lnorm-todo-push ( level n -- n' )
  dup 1+ lf-lnorm-todo slab-hold ok?
  if tuck cells lf-lnorm-todo slab-base + ! 1+
  else nip dup lf-lnorm-todo slab-capacity lf-diag-work-stack-full lf-lnorm-no-room then ;
: lf-lnorm-todo-pop ( n -- level n' ) 1- dup cells lf-lnorm-todo slab-base + @ swap ;
: lf-lnorm-push-one ( n level -- n' )
  lf-lnorm-ok? 0= if drop exit then lf-lnorm-spend
  dup lf-lmk-max? if dup lf-level-second@ rot lf-lnorm-todo-push
    swap lf-level-first@ swap lf-lnorm-todo-push
  else lf-lnorm-push then ;
: lf-lnorm-push-args ( level -- )
  0 lf-lnorm-todo-push begin dup while lf-lnorm-todo-pop swap lf-lnorm-push-one repeat drop ;

\ Sorting arguments from..to-1 in place by is_norm_lt (insertion sort;
\ only structurally equal arguments tie, so the order is std::sort's).
: lf-lnorm-swap ( addr addr' -- ) 2dup @ swap @ rot ! swap ! ;
: lf-lnorm-before? ( i -- flag )
  lf-lnorm-spend lf-lnorm-ok? 0= if drop false exit then
  dup lf-lnorm-arg @ swap 1- lf-lnorm-arg @ lf-lnorm-lt ;
: lf-lnorm-sink ( from i -- )
  begin 2dup < while dup lf-lnorm-before? while
    dup lf-lnorm-arg over 1- lf-lnorm-arg lf-lnorm-swap 1-
  repeat then 2drop ;
: lf-lnorm-insertion ( from to -- )
  2dup < if over 1+ ?do dup i lf-lnorm-sink loop drop else 2drop then ;
\ Long lists (plan task 6.2.0; a max of a thousand parameters) are merge
\ sorted, bottom up, through scratch cells above the stack's top, so that
\ sorting costs n log n comparisons, not n*n/2; each comparison costs one
\ unit of fuel, as in the insertion sort, which lists of at most
\ lf-lnorm-short arguments keep (so their fuel is as before). A merge
\ takes the right run's argument first only when it is strictly less, so
\ equal arguments keep their order; only structurally equal arguments
\ tie, so the result is the insertion sort's.
32 constant lf-lnorm-short
: lf-lnorm-i ( -- addr ) lf-lnorm-state lf-lnrec-i ;
: lf-lnorm-j ( -- addr ) lf-lnorm-state lf-lnrec-j ;
: lf-lnorm-k ( -- addr ) lf-lnorm-state lf-lnrec-k ;
: lf-lnorm-mid ( -- addr ) lf-lnorm-state lf-lnrec-mid ;
: lf-lnorm-hi ( -- addr ) lf-lnorm-state lf-lnrec-hi ;
: lf-lnorm-width ( -- addr ) lf-lnorm-state lf-lnrec-width ;
: lf-lnorm-to ( -- addr ) lf-lnorm-state lf-lnrec-to ;
: lf-lnorm-take ( cursor -- )
  dup @ lf-lnorm-arg @ lf-lnorm-k @ lf-lnorm-arg ! 1 swap +! 1 lf-lnorm-k +! ;
: lf-lnorm-right-first? ( -- flag )
  lf-lnorm-spend lf-lnorm-ok? 0= if false exit then
  lf-lnorm-j @ lf-lnorm-arg @ lf-lnorm-i @ lf-lnorm-arg @ lf-lnorm-lt ;
: lf-lnorm-both? ( -- flag ) lf-lnorm-i @ lf-lnorm-mid @ < lf-lnorm-j @ lf-lnorm-hi @ < and ;
: lf-lnorm-merged ( -- )
  begin lf-lnorm-both? while
    lf-lnorm-right-first? if lf-lnorm-j else lf-lnorm-i then lf-lnorm-take repeat
  begin lf-lnorm-i @ lf-lnorm-mid @ < while lf-lnorm-i lf-lnorm-take repeat
  begin lf-lnorm-j @ lf-lnorm-hi @ < while lf-lnorm-j lf-lnorm-take repeat ;
\ Merge lo..mid-1 and mid..hi-1 through the scratch at scratch, then copy
\ the result back to lo.
: lf-lnorm-merge ( lo mid hi scratch -- )
  dup lf-lnorm-k ! >r lf-lnorm-hi ! dup lf-lnorm-j ! lf-lnorm-mid ! dup lf-lnorm-i !
  lf-lnorm-merged r> lf-lnorm-arg swap dup lf-lnorm-arg swap lf-lnorm-hi @ swap - cells move ;
: lf-lnorm-run ( lo -- )
  dup lf-lnorm-width @ + lf-lnorm-to @ min over lf-lnorm-width @ 2* + lf-lnorm-to @ min
  lf-lnorm-to @ lf-lnorm-merge ;
: lf-lnorm-pass ( from -- )
  begin dup lf-lnorm-to @ < while dup lf-lnorm-run lf-lnorm-width @ 2* + repeat drop ;
: lf-lnorm-widen ( -- ) lf-lnorm-width @ 2* lf-lnorm-width ! ;
: lf-lnorm-scratch? ( from to -- flag ) dup rot - + lf-lnorm-arg-cells slab-hold ok? ;
: lf-lnorm-merge-sort ( from to -- )
  2dup lf-lnorm-scratch? 0= if drop lf-lnorm-arg @ lf-lnorm-crowded exit then
  lf-lnorm-to ! 1 lf-lnorm-width !
  begin lf-lnorm-to @ over - lf-lnorm-width @ > while dup lf-lnorm-pass lf-lnorm-widen repeat
  drop ;
: lf-lnorm-sort ( from to -- )
  2dup swap - lf-lnorm-short > if lf-lnorm-merge-sort else lf-lnorm-insertion then ;

\ Dropping explicit arguments (476-494): all but the largest, and that
\ one too when a later argument's offset is at least its own.
: lf-lnorm-explicit-at? ( i -- flag ) lf-lnorm-arg @ lf-lmk-explicit? ;
: lf-lnorm-offset-at ( i -- k ) lf-lnorm-arg @ lf-lmk-offset nip ;
: lf-lnorm-last-explicit ( from to -- i )
  swap begin 2dup 1+ > while dup 1+ lf-lnorm-explicit-at? while 1+ repeat then nip ;
: lf-lnorm-covered? ( i to k -- flag )
  rot 1+ rot swap ?do dup i lf-lnorm-offset-at > 0= if drop true unloop exit then loop
  drop false ;
: lf-lnorm-first-kept ( from to -- i )
  over lf-lnorm-explicit-at? 0= if drop exit then
  tuck lf-lnorm-last-explicit dup rot over lf-lnorm-offset-at lf-lnorm-covered?
  if 1+ then ;
\ Keeping each base once, with its largest offset (495-510): the kept
\ arguments are moved down to from..end-1.
: lf-lnorm-base ( level -- base ) lf-lmk-offset drop ;
: lf-lnorm-same-base? ( a b -- flag ) lf-lnorm-base swap lf-lnorm-base lf-lmk-same? ;
: lf-lnorm-above? ( a b -- flag ) lf-lmk-offset nip swap lf-lmk-offset nip > ;
: lf-lnorm-last ( w -- addr ) 1- lf-lnorm-arg ;
: lf-lnorm-keep ( w level -- w' )
  over lf-lnorm-last @ over lf-lnorm-same-base? 0= if over lf-lnorm-arg ! 1+ exit then
  over lf-lnorm-last @ over lf-lnorm-above? if over lf-lnorm-last ! else drop then ;
: lf-lnorm-dedup ( from to -- end )
  2dup lf-lnorm-first-kept >r over r@ lf-lnorm-arg @ swap lf-lnorm-arg !
  swap 1+ swap r> 1+ ?do i lf-lnorm-arg @ lf-lnorm-keep loop ;
\ Each kept argument under the max's successors (511-512), then mk_max
\ folded from the right (429-444).
: lf-lnorm-lift ( from end k -- )
  -rot swap ?do i lf-lnorm-arg @ over lf-lnorm-succs i lf-lnorm-arg ! loop drop ;
: lf-lnorm-fold ( from end -- level )
  1- dup lf-lnorm-arg @ -rot 2dup <
  if 1- do i lf-lnorm-arg @ swap lf-lnorm-max -1 +loop else 2drop then ;

\ ---------------------------------------------------------------------------
\ normalize, once per level of the input (the normal forms of a call are
\ remembered, so a shared graph is not normalized twice). A level's visit
\ is a chain of steps on the frames ( ... frames -- ... frames next ) that
\ ends with its normal form ( level' frames 0 ); lf-lnorm-call asks for the
\ visit of a level, continuing with cont ( level' frames -- ... ). A visit
\ the frames cannot hold (the heap refuses) is full and gives 0. The
\ frames' own fuel is not used: the call's fuel is spent as before.
: lf-lnorm-call ( level frames cont -- ... frames next )
  frame-need 2 pick frame-room?
  if over frame-visitor @ frame-open
  else >r nip 0 swap dup frame-used @ over frame-capacity @ lf-diag-frame-limit
    lf-lnorm-no-room r> then ;
\ imax (463-467): mk_imax of the normalized sides, not normalized again;
\ the level and its offset wait while the left side is normalized, then
\ the left side's normal form too.
: lf-lnorm-imax-done ( l2 frames -- level frames 0 )
  >r r@ frame-restore swap lf-lnorm-imax r@ frame-restore drop r@ frame-restore
  lf-lnorm-succs r> 0 ;
: lf-lnorm-imax-left ( l1 frames -- r frames next )
  >r r@ frame-save 1 r@ frame-pick lf-level-second@ r> ['] lf-lnorm-imax-done lf-lnorm-call ;
: lf-lnorm-imax-case ( r k frames -- r' frames next )
  >r r@ frame-save dup r@ frame-save lf-level-first@ r> ['] lf-lnorm-imax-left lf-lnorm-call ;
\ max (468-514): the arguments, each normalized and flattened again,
\ pushed above the max's own arguments; the stack is given back after.
\ The old top, the offset, the end of the max's own arguments and the
\ next of them wait while each is normalized.
: lf-lnorm-combine ( from to k -- level )
  >r 2dup lf-lnorm-sort over swap lf-lnorm-dedup 2dup r> lf-lnorm-lift lf-lnorm-fold ;
: lf-lnorm-max-done ( frames -- level frames 0 )
  >r r@ frame-restore lf-lnorm-top @ r@ frame-restore lf-lnorm-ok?
  if lf-lnorm-combine else drop 2drop 0 then r@ frame-restore lf-lnorm-top ! r> 0 ;
defer lf-lnorm-flatten ( i frames -- ... frames next )
: lf-lnorm-flattened ( level' frames -- i frames next )
  >r lf-lnorm-push-args r@ frame-restore 1+ r> ['] lf-lnorm-flatten ;
: lf-lnorm-next-arg ( i frames -- ... frames next )
  0 over frame-pick 2 pick > 0= if nip lf-lnorm-max-done exit then
  2dup frame-save swap lf-lnorm-arg @ swap ['] lf-lnorm-flattened lf-lnorm-call ;
' lf-lnorm-next-arg is lf-lnorm-flatten
: lf-lnorm-max-case ( r k frames -- ... frames next )
  >r lf-lnorm-top @ r@ frame-save r@ frame-save lf-lnorm-top @ swap lf-lnorm-push-args
  lf-lnorm-top @ r@ frame-save r> lf-lnorm-next-arg ;
\ Zero and parameters, under any successors, are their own normal form.
: lf-lnorm-compute ( level frames -- ... frames next )
  >r dup lf-lmk-offset over lf-level-tag@ case
    lf-level-tag-imax of rot drop r> lf-lnorm-imax-case endof
    lf-level-tag-max of rot drop r> lf-lnorm-max-case endof
    >r 2drop r> r> swap 0 swap endcase ;
\ A visit: a level already normalized gives its normal form; else one
\ unit of fuel, then the normal form, remembered by the step it keeps for
\ the visit's end.
: lf-lnorm-remember ( level level' -- level' ) tuck 1+ swap lf-lnorm-memo ! ;
: lf-lnorm-remembered ( level' frames -- level' frames 0 )
  >r r@ frame-restore swap lf-lnorm-remember r> 0 ;
: lf-lnorm-visit-step ( level frames -- ... frames next )
  lf-lnorm-ok? 0= if nip 0 swap 0 exit then
  over lf-lnorm-memo @ ?dup if rot drop 1- swap 0 exit then
  lf-lnorm-spend 2dup frame-save ['] lf-lnorm-remembered over frame-save lf-lnorm-compute ;
\ Normalize one level to the end, as a loop of its own on the frames from
\ what they hold (level-geq.fs calls it from its steps).
: lf-lnorm-walk ( level -- level' )
  lf-lnorm-frames dup frame-used @ >r ['] frame-return lf-lnorm-call r> frame-loop drop ;

\ ---------------------------------------------------------------------------
\ is_equivalent: structurally equal, or so after normalize (left first).
: lf-lnorm-decide ( l1 l2 -- flag )
  2dup lf-lmk-same? if 2drop true exit then
  swap lf-lnorm-walk swap lf-lnorm-walk lf-lmk-same? ;
\ A call: the store marked first, given back last (a refused rollback is
\ invalid), the facts of level-make cut back with it.
: lf-lnorm-store-mark ( -- addr ) lf-lnorm-state lf-lnrec-mark ;
: lf-lnorm-begin ( fuel -- outcome )
  lf-lnorm-fuel ! outcome-ok lf-lnorm-status ! 0 lf-lnorm-top ! lf-lnorm-frames frame-reset
  max-n lf-lnorm-frames frame-fuel ! lf-lnorm-clear
  lf-lmk-sync lf-lnorm-store-mark lf-levels store-mark ;
: lf-lnorm-end ( -- )
  lf-lnorm-store-mark lf-levels store-rollback lf-lnorm-fail
  lf-level-count @ lf-lmk-truncate ;
: lf-lnorm-result ( flag -- flag outcome )
  lf-lnorm-status @ dup ok? 0= if nip false swap then ;
: lf-lnorm-usable? ( l1 l2 fuel -- flag ) 0< 0= -rot lf-level-pair-valid? and ;

\ Whether Lean's is_equivalent holds for two live levels whose graphs a
\ scope check validated, with fuel: (flag ok) when decided; (false
\ unknown) when two different parameters must be ordered and one's ID is
\ not a valid name of the name store (never in a declaration's check,
\ whose parameters are names); (false exhausted) when the fuel runs out;
\ (false full) when the level store is full, or the heap cannot grow
\ the argument stack or the frames; (false invalid) for negative
\ fuel, an invalid level or a refused rollback. lf-lnorm-fuel is the fuel
\ left (0 after invalid input). Nothing stays allocated.
: lf-lnorm-refused ( l1 l2 -- false outcome )
  2drop 0 lf-lnorm-fuel ! false outcome-invalid ;
: lf-level-equivalent ( l1 l2 fuel -- flag outcome )
  >r 2dup r@ lf-lnorm-usable? 0= if r> drop lf-lnorm-refused exit then
  r> lf-lnorm-begin ok? 0= if lf-lnorm-refused exit then
  lf-lnorm-decide lf-lnorm-end lf-lnorm-result ;

\ ---------------------------------------------------------------------------
\ The frames, set up in every context and freed with it. Host stacks: a
\ call holds a constant number of cells whatever the levels' depth -- its
\ entry words, the loop, one step and the words it calls (the sort, the
\ name order, level-make's constructors), and level-geq.fs's loop around
\ normalize's; lf-lnorm-return-cells and lf-lnorm-data-cells bound that
\ generously for mixed-infer.fs and the job pool (context-need).
: lf-lnorm-setup ( -- ) ['] lf-lnorm-visit-step lf-lnorm-frames frame-init ;
' lf-lnorm-setup context-setup
: lf-lnorm-release ( -- ) lf-lnorm-frames frame-free ;
' lf-lnorm-release context-teardown
256 constant lf-lnorm-return-cells
256 constant lf-lnorm-data-cells
lf-lnorm-data-cells lf-lnorm-return-cells context-need
