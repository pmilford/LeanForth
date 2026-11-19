\ Level equality and Lean's cheap level simplifications for the front end
\ (plan FE1c; ADR 0021 D6), ports of Lean 4.35.0's Lean/Level.lean:
\ - lf-meta-level= ( a b -- flag outcome ): Level.beq, structural
\   equality (two records of the same tag and parts, compared part by
\   part: the store may hold equal levels twice when it does not share);
\ - lf-meta-never-zero? ( level -- flag outcome ): Level.isNeverZero, a
\   successor reached through either side of a max or the second of an
\   imax;
\ - lf-meta-max ( u v -- w outcome ): mkLevelMax' (mkLevelMaxCore's
\   rules in Lean's order: u == v, a zero side, one side subsuming the
\   other -- an explicit level below the other's offset, or an argument
\   of the other's max -- the same base with the larger offset; else a
\   new max), and lm-simp-max ( u v d -- w outcome ), simpLevelMax',
\   which gives d where mkLevelMax' would make a new node;
\ - lf-meta-imax ( u v -- w outcome ): mkLevelIMax' (v never zero: the
\   max; v zero or u zero: v; u == v: u; else a new imax), and
\   lm-simp-imax, simpLevelIMax'.
\ Equality and isNeverZero keep their pending pairs on a heap stack, so
\ no level's depth needs the host's stacks (plan task 6.2.0).
\ Outcomes: ok; full when the store or the heap has no room. Untrusted.
\ State: the slab ls-pairs, a member of the checker context (ADR 0009);
\ one comparison at a time (none of these words runs inside another).

require ../lib/lib.fs
require ../core/levels.fs

\ Shapes, shared with level-defeq.fs and level-normalize.fs: Lean's
\ getLevelOffset and getOffset, the base under the successors and their
\ number; Lean's == on two leaves, one node or a record of the same fields.
: ld-succ? ( level -- flag ) lf-level-tag@ lf-level-tag-succ = ;
: ld-param? ( level -- flag ) lf-level-tag@ lf-level-tag-param = ;
: ld-pred ( level -- level' ) lf-level-first@ ;
: ld-offset ( level -- base k ) 0 begin over ld-succ? while 1+ swap ld-pred swap repeat ;
: ld-base ( level -- base ) ld-offset drop ;
: ld-record ( level -- addr u ) lf-level-slot /node ;
: ld-same? ( a b -- flag )
  2dup = if 2drop true exit then >r ld-record r> ld-record compare 0= ;

2 cells context-slab: ls-pairs
: ls-push ( a b -- outcome ) ls-pairs slab-2push ;
: ls-pop ( -- a b ) ls-pairs slab-2pop ;
: ls-more? ( -- flag ) ls-pairs slab-count 0> ;
: ls-start ( a b -- outcome ) ls-pairs slab-clear ls-push ;
: ls-tag ( level -- tag ) lf-level-tag@ ;
: ls-zero? ( level -- flag ) ls-tag lf-level-tag-zero = ;
: ls-succ? ( level -- flag ) ls-tag lf-level-tag-succ = ;
: ls-max? ( level -- flag ) ls-tag lf-level-tag-max = ;
: ls-leaf? ( level -- flag ) dup ls-succ? swap ls-tag lf-level-binary-tag? or 0= ;

\ Equality: a pair is equal when it is one node, or its tags agree and
\ so do its fields (a leaf) or its parts (pushed).
: ls-firsts ( a b -- outcome ) lf-level-first@ swap lf-level-first@ swap ls-push ;
: ls-parts ( a b -- same? outcome )
  2dup ls-firsts dup ok? 0= if nip nip false swap exit then
  drop dup ls-succ? if 2drop true outcome-ok exit then
  lf-level-second@ swap lf-level-second@ ls-push true swap ;
: ls-step ( a b -- same? outcome )
  2dup = if 2drop true outcome-ok exit then
  over ls-tag over ls-tag <> if 2drop false outcome-ok exit then
  over ls-leaf? if ld-same? outcome-ok else ls-parts then ;
\ The pairs compared off ls-pairs by slab.fs's slab-2all? (term-eqv.fs's
\ by the same word): until none is left (true), a pair differs (false)
\ or a step fails (false and its outcome).
: lf-meta-level= ( a b -- flag outcome )
  ls-start dup ok? if drop ls-pairs ['] ls-step slab-2all? else false swap then ;

\ isNeverZero: a successor reached through max's sides or imax's second.
: ls-push1 ( level -- outcome ) 0 ls-push ;
: ls-never-max ( level -- false outcome )
  dup lf-level-first@ ls-push1 dup ok? 0= if nip false swap exit then
  drop lf-level-second@ ls-push1 false swap ;
: ls-never-imax ( level -- false outcome ) lf-level-second@ ls-push1 false swap ;
: ls-never-step ( level -- found? outcome )
  dup ls-tag case lf-level-tag-succ of drop true outcome-ok endof
    lf-level-tag-max of ls-never-max endof  lf-level-tag-imax of ls-never-imax endof
    >r drop false outcome-ok r> endcase ;
: ls-never-round ( -- found? outcome ) ls-pop drop ls-never-step ;
: ls-never-run ( -- flag outcome )
  begin ls-more? while ls-never-round dup ok? 0= if nip false swap exit then
  drop if true outcome-ok exit then repeat false outcome-ok ;
: lf-meta-never-zero? ( level -- flag outcome )
  0 ls-start dup ok? if drop ls-never-run else false swap then ;

\ mkLevelMaxCore's rules give a code: the next rule, u, v, or an outcome
\ that ends it (plus lm-ends); mkLevelIMaxCore's may ask for the max.
0 constant lm-next
1 constant lm-u
2 constant lm-v
3 constant lm-max
8 constant lm-ends
: lm-when ( flag outcome code -- code' )
  swap dup ok? if drop and else nip nip lm-ends + then ;
: lm-same ( u v -- u v code ) 2dup lf-meta-level= lm-u lm-when ;
: lm-offset ( level -- k ) ld-offset nip ;
: ls-explicit? ( level -- flag ) ld-base ls-zero? ;
: lm-above? ( u v -- flag )
  dup ls-explicit? if lm-offset swap lm-offset <= else 2drop false then ;
: lm-arg= ( u v part -- u v code )
  >r 2dup swap r> execute swap lf-meta-level= lm-u lm-when ;
: lm-in-max ( u v -- u v code )
  over ls-max? 0= if lm-next exit then
  ['] lf-level-first@ lm-arg= ?dup if exit then ['] lf-level-second@ lm-arg= ;
\ subsumes u v: take u; subsumes v u: take v.
: lm-subsumes ( u v -- u v code ) 2dup lm-above? if lm-u else lm-in-max then ;
\ (lm-subsumes gives u, the next rule or an end; u becomes v.)
: lm-flip ( code -- code' ) dup lm-u = if drop lm-v then ;
: lm-subsumed ( u v -- u v code ) swap lm-subsumes lm-flip >r swap r> ;
: lm-higher ( u v -- code ) lm-offset swap lm-offset <= if lm-u else lm-v then ;
: lm-bases ( u v -- u v code )
  2dup ld-base swap ld-base lf-meta-level= dup ok? 0= if nip lm-ends + exit then
  drop if 2dup lm-higher else lm-next then ;
: lm-rules ( u v -- u v code )
  lm-same ?dup if exit then over ls-zero? lm-v and ?dup if exit then
  dup ls-zero? lm-u and ?dup if exit then lm-subsumes ?dup if exit then
  lm-subsumed ?dup if exit then lm-bases ;
: lm-take ( u v code -- w outcome )
  dup lm-ends < if lm-u = if drop else nip then outcome-ok exit then
  lm-ends - nip nip -1 swap ;
: lf-meta-max ( u v -- w outcome )
  lm-rules ?dup if lm-take else lf-level-max room-result then ;
: lm-simp-max ( u v d -- w outcome )
  >r lm-rules ?dup if r> drop lm-take else 2drop r> outcome-ok then ;

\ mkLevelIMaxCore's rules.
: li-rules ( u v -- u v code )
  dup lf-meta-never-zero? lm-max lm-when ?dup if exit then
  dup ls-zero? lm-v and ?dup if exit then
  over ls-zero? lm-v and ?dup if exit then lm-same ;
: li-take ( u v code -- w outcome )
  dup lm-max = if drop lf-meta-max else lm-take then ;
: lf-meta-imax ( u v -- w outcome )
  li-rules ?dup if li-take else lf-level-imax room-result then ;
: lm-simp-imax ( u v d -- w outcome )
  >r li-rules ?dup if r> drop li-take else 2drop r> outcome-ok then ;
