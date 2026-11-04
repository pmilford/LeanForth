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
\ State: one record, lf-lnorm-state: the first failure of the call, the
\ fuel left, the argument stack of the max case (its top and cells), a
\ mark of the level store before the call, and per level the normal form
\ found (or, while checking names, whether the level is reached). A
\ member of the checker context (lib/context.fs). The normal forms are
\ new nodes of the level store, given back when the call ends; the facts
\ of level-make are truncated with them. Single-threaded within one
\ context.
\ Stack use: normalize, push_max_args, is_norm_lt and the name order
\ recurse on the host stacks once per level of a graph (children are
\ earlier nodes, at most lf-level-capacity deep), a few cells each.

require ../lib/lib.fs
require ../core/diagnostics.fs
require ../core/levels.fs
require ../core/names.fs
require ../core/name-equal.fs
require ./level-make.fs

128 constant lf-lnorm-capacity   \ cells of the max case's argument stack

begin-structure /lf-lnrec
  field: lf-lnrec-status                            \ the first failure; ok while none
  field: lf-lnrec-fuel                              \ fuel left
  field: lf-lnrec-top                               \ argument cells in use
  /store-mark +field lf-lnrec-mark                  \ the level store before the call
  lf-lnorm-capacity cells +field lf-lnrec-args
  lf-level-capacity cells +field lf-lnrec-memo      \ normal form + 1, or 0
end-structure
/lf-lnrec context-record: lf-lnorm-state

: lf-lnorm-status ( -- addr ) lf-lnorm-state lf-lnrec-status ;
\ Fuel left after lf-level-equivalent; level-compare continues with it.
: lf-lnorm-fuel ( -- addr ) lf-lnorm-state lf-lnrec-fuel ;
: lf-lnorm-top ( -- addr ) lf-lnorm-state lf-lnrec-top ;
: lf-lnorm-arg ( i -- addr ) cells lf-lnorm-state lf-lnrec-args + ;
: lf-lnorm-memo ( level -- addr ) cells lf-lnorm-state lf-lnrec-memo + ;
: lf-lnorm-clear ( -- ) 0 lf-lnorm-memo lf-level-capacity cells erase ;
: lf-lnorm-site ( -- site ) c" level-normalize lf-level-equivalent" ;

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
\ New nodes: a full store or spent serial (recorded by lf-level-add) is full.
: lf-lnorm-made ( level true | false -- level ) if exit then outcome-full lf-lnorm-fail 0 ;
: lf-lnorm-succ ( level -- level' ) lf-lnorm-ok? if lf-level-succ lf-lnorm-made then ;
: lf-lnorm-succs ( level k -- level' ) 0 ?do lf-lnorm-succ loop ;
: lf-lnorm-max ( l1 l2 -- level ) lf-lnorm-ok? if lf-lmk-max lf-lnorm-made else drop then ;
: lf-lnorm-imax ( l1 l2 -- level ) lf-lnorm-ok? if lf-lmk-imax lf-lnorm-made else drop then ;

\ ---------------------------------------------------------------------------
\ Lean's name order: -1, 0 or 1. Unchecked: both names passed
\ lf-lnorm-name-ok?, so every prefix is an earlier valid entry.
: lf-lnorm-sign ( n -- -1|0|1 ) dup 0> 1 and swap 0< or ;
: lf-lnorm-depth ( id -- n ) 0 swap begin dup while lf-name-prefix@ swap 1+ swap repeat drop ;
: lf-lnorm-up ( id n -- id' ) 0 ?do lf-name-prefix@ loop ;
\ One component each (203-215): a string after a number; strings by bytes
\ and then length (Forth's COMPARE), numbers by value.
: lf-lnorm-str? ( id -- flag ) lf-name-tag@ lf-name-tag-str = ;
: lf-lnorm-limb ( a b -- n )
  2dup lf-name-tags= 0= if drop lf-lnorm-str? 1 and 2* 1- exit then
  over lf-lnorm-str? if lf-name-text rot lf-name-text 2swap compare exit then
  lf-name-payload swap lf-name-payload swap - lf-lnorm-sign ;
\ Two names of the same depth: their prefixes first, then the last parts.
: lf-lnorm-level-cmp ( a b -- n )
  2dup = if 2drop 0 exit then
  2dup lf-name-prefixes recurse ?dup if nip nip exit then lf-lnorm-limb ;
\ Any two names (216-219): the shorter name's depth decides first, then a
\ prefix comes before its extensions.
: lf-lnorm-depths ( a b -- da db ) lf-lnorm-depth swap lf-lnorm-depth swap ;
: lf-lnorm-trimmed ( a b da db -- a' b' )
  2dup min tuck - >r - rot swap lf-lnorm-up swap r> lf-lnorm-up ;
: lf-lnorm-name-cmp ( a b -- n )
  2dup lf-lnorm-depths 2dup - lf-lnorm-sign >r lf-lnorm-trimmed lf-lnorm-level-cmp
  ?dup if r> drop else r> then ;
\ A name whose every component is a valid entry.
: lf-lnorm-limb-ok? ( id -- flag ) dup lf-name-valid? if lf-name-entry-ok? else drop false then ;
: lf-lnorm-name-ok? ( id -- flag )
  begin dup while dup lf-lnorm-limb-ok? 0= if drop false exit then lf-name-prefix@ repeat
  drop true ;

\ ---------------------------------------------------------------------------
\ is_norm_lt: by base (the level under its successors), then offset.
\ Different bases: by kind (level.h 30: zero, succ, max, imax, param, as
\ LeanForth's tags), parameters by name, max and imax by their left sides,
\ or by their right sides when the left ones are equal.
defer lf-lnorm-less ( a b -- flag )
: lf-lnorm-lefts ( a b -- a' b' ) lf-level-first@ swap lf-level-first@ swap ;
: lf-lnorm-rights ( a b -- a' b' ) lf-level-second@ swap lf-level-second@ swap ;
: lf-lnorm-sides< ( ba bb -- flag )
  2dup lf-lnorm-lefts lf-lmk-same? if lf-lnorm-rights else lf-lnorm-lefts then lf-lnorm-less ;
: lf-lnorm-names< ( ba bb -- flag ) lf-lnorm-lefts lf-lnorm-name-cmp 0< ;
: lf-lnorm-bases< ( ba bb -- flag )
  2dup lf-lmk-tags 2dup <> if < nip nip exit then 2drop
  dup lf-level-tag@ lf-level-tag-param = if lf-lnorm-names< else lf-lnorm-sides< then ;
: lf-lnorm-lt ( a b -- flag )
  2dup = if 2drop false exit then
  lf-lmk-offset rot lf-lmk-offset rot 2>r swap
  2dup lf-lmk-same? if 2drop 2r> < else 2r> 2drop lf-lnorm-bases< then ;
' lf-lnorm-lt is lf-lnorm-less

\ ---------------------------------------------------------------------------
\ The argument stack. A push beyond its capacity is full.
: lf-lnorm-crowded ( level -- )
  drop lf-lnorm-ok? if lf-lnorm-top @ lf-lnorm-capacity lf-lnorm-site
    lf-diag-work-stack-full lf-diag-note then outcome-full lf-lnorm-fail ;
: lf-lnorm-push ( level -- )
  lf-lnorm-top @ dup lf-lnorm-capacity <
  if lf-lnorm-arg ! 1 lf-lnorm-top +! else drop lf-lnorm-crowded then ;
\ push_max_args: the arguments of nested maxes, left to right.
: lf-lnorm-push-args ( level -- )
  lf-lnorm-ok? 0= if drop exit then lf-lnorm-spend
  dup lf-lmk-max? if dup lf-level-first@ recurse lf-level-second@ recurse
  else lf-lnorm-push then ;

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
: lf-lnorm-sort ( from to -- )
  2dup < if over 1+ ?do dup i lf-lnorm-sink loop drop else 2drop then ;

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
\ remembered, so a shared graph is not normalized twice).
defer lf-lnorm-walk ( level -- level' )
\ imax (463-467): mk_imax of the normalized sides, not normalized again.
: lf-lnorm-imax-case ( r k -- level )
  >r dup lf-level-first@ lf-lnorm-walk swap lf-level-second@ lf-lnorm-walk
  lf-lnorm-imax r> lf-lnorm-succs ;
\ max (468-514): the arguments, each normalized and flattened again,
\ pushed above the max's own arguments; the stack is given back after.
: lf-lnorm-flatten ( from to -- ) swap ?do i lf-lnorm-arg @ lf-lnorm-walk lf-lnorm-push-args loop ;
: lf-lnorm-args ( r -- from to )
  lf-lnorm-top @ swap lf-lnorm-push-args lf-lnorm-top @ 2dup lf-lnorm-flatten
  nip lf-lnorm-top @ ;
: lf-lnorm-combine ( from to k -- level )
  >r 2dup lf-lnorm-sort over swap lf-lnorm-dedup 2dup r> lf-lnorm-lift lf-lnorm-fold ;
: lf-lnorm-max-case ( r k -- level )
  lf-lnorm-top @ >r >r lf-lnorm-args r>
  lf-lnorm-ok? if lf-lnorm-combine else drop 2drop 0 then r> lf-lnorm-top ! ;
\ Zero and parameters, under any successors, are their own normal form.
: lf-lnorm-compute ( level -- level' )
  dup lf-lmk-offset over lf-level-tag@ case
    lf-level-tag-imax of rot drop lf-lnorm-imax-case endof
    lf-level-tag-max of rot drop lf-lnorm-max-case endof
    >r 2drop r> endcase ;
: lf-lnorm-visit ( level -- level' )
  lf-lnorm-ok? 0= if drop 0 exit then
  dup lf-lnorm-memo @ ?dup if nip 1- exit then
  lf-lnorm-spend dup lf-lnorm-compute tuck 1+ swap lf-lnorm-memo ! ;
' lf-lnorm-visit is lf-lnorm-walk

\ ---------------------------------------------------------------------------
\ Every parameter reached from two roots is a valid name (the order needs
\ names); the reached marks use the memo cells and are cleared after.
: lf-lnorm-reached ( level -- ) true swap lf-lnorm-memo ! ;
: lf-lnorm-reach ( level -- )
  dup lf-level-tag@ dup lf-level-binary-tag?
  if drop dup lf-level-first@ lf-lnorm-reached lf-level-second@ lf-lnorm-reached exit then
  lf-level-tag-succ = if lf-level-first@ lf-lnorm-reached else drop then ;
: lf-lnorm-param-ok? ( level -- flag )
  dup lf-level-tag@ lf-level-tag-param = if lf-level-first@ lf-lnorm-name-ok? else drop true then ;
: lf-lnorm-seen-ok? ( level -- flag )
  dup lf-lnorm-memo @ 0= if drop true exit then dup lf-lnorm-reach lf-lnorm-param-ok? ;
: lf-lnorm-names? ( l1 l2 -- flag )
  2dup lf-lnorm-reached lf-lnorm-reached max 0 swap
  do i lf-lnorm-seen-ok? 0= if unloop false exit then -1 +loop true ;

\ ---------------------------------------------------------------------------
\ is_equivalent: structurally equal, or so after normalize (left first).
\ Names that cannot be ordered leave it undecided (unknown).
: lf-lnorm-normals ( l1 l2 -- flag )
  swap lf-lnorm-walk swap lf-lnorm-walk lf-lmk-same? ;
: lf-lnorm-unnamed ( l1 l2 -- false ) 2drop outcome-unknown lf-lnorm-fail false ;
: lf-lnorm-decide ( l1 l2 -- flag )
  2dup lf-lmk-same? if 2drop true exit then
  2dup lf-lnorm-names? lf-lnorm-clear if lf-lnorm-normals else lf-lnorm-unnamed then ;
\ A call: the store marked first, given back last (a refused rollback is
\ invalid), the facts of level-make cut back with it.
: lf-lnorm-store-mark ( -- addr ) lf-lnorm-state lf-lnrec-mark ;
: lf-lnorm-begin ( fuel -- outcome )
  lf-lnorm-fuel ! outcome-ok lf-lnorm-status ! 0 lf-lnorm-top ! lf-lnorm-clear
  lf-lmk-forget lf-lnorm-store-mark lf-levels store-mark ;
: lf-lnorm-end ( -- )
  lf-lnorm-store-mark lf-levels store-rollback lf-lnorm-fail
  lf-level-count @ lf-lmk-truncate ;
: lf-lnorm-result ( flag -- flag outcome )
  lf-lnorm-status @ dup ok? 0= if nip false swap then ;
: lf-lnorm-usable? ( l1 l2 fuel -- flag ) 0< 0= -rot lf-level-pair-valid? and ;

\ Whether Lean's is_equivalent holds for two live levels whose graphs a
\ scope check validated, with fuel: (flag ok) when decided; (false
\ unknown) for a parameter whose name is not a valid entry of the name
\ store; (false exhausted) when the fuel runs out; (false full) when the
\ level store or the argument stack is full; (false invalid) for negative
\ fuel, an invalid level or a refused rollback. lf-lnorm-fuel is the fuel
\ left (0 after invalid input). Nothing stays allocated.
: lf-lnorm-refused ( l1 l2 -- false outcome ) 2drop 0 lf-lnorm-fuel ! false outcome-invalid ;
: lf-level-equivalent ( l1 l2 fuel -- flag outcome )
  >r 2dup r@ lf-lnorm-usable? 0= if r> drop lf-lnorm-refused exit then
  r> lf-lnorm-begin ok? 0= if lf-lnorm-refused exit then
  lf-lnorm-decide lf-lnorm-end lf-lnorm-result ;
