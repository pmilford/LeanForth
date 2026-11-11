\ Universe levels as Lean's kernel builds and compares them (ADR 0011,
\ Amendment 1): mk_max and mk_imax rule by rule (level-make), Lean's name
\ order, is_equivalent with its incomplete normalize (level-normalize) and
\ the comparison around it (level-compare); fuel, room and malformed
\ input; then random levels against an independent model of Lean's
\ constructors and structural equality, written from level.cpp without
\ sharing code with the modules, and against the witness assignments of
\ level-value (equivalent levels have equal values). The pinned-Lean
\ comparison of the same functions is tests/core/level-kernel-differential.py
\ (make check). Test-only; no theorem is checked.
include ../support/tester.fs
include ../support/checks.fs
require ../../src/lib/lib.fs
require ../../src/core/level-scope.fs
require ../../src/core/levels.fs
require ../../src/core/names.fs
require ../../src/kernel/level-make.fs
require ../../src/kernel/level-normalize.fs
require ../../src/kernel/level-compare.fs
require ../../src/kernel/level-value.fs
require ../support/store-faults.fs
decimal

\ The rule rows below need equal levels as distinct nodes (one, one'; u,
\ u'): hash-consing is off (one switch with the terms, compact-store plan
\ step S4; tests/core/levels.fs).
false lf-term-sharing!
: must ( flag -- ) 0= abort" level-compare test: refused" ;
: intern ( c-addr u -- id ) 0 -rot lf-name-str must ;
: param ( id -- level ) lf-level-param must ;
: succ ( level -- level' ) lf-level-succ must ;
: max-of ( a b -- level ) lf-level-max must ;
: imax-of ( a b -- level ) lf-level-imax must ;
: tag@ ( level -- tag ) lf-level-read must 2drop ;

\ A session with the parameters u, v and w (interned names) in context.
variable u-id variable v-id variable w-id
: session ( -- )
  lf-name-reset lf-level-reset lf-lscope-context-reset
  s" u" intern u-id ! s" v" intern v-id ! s" w" intern w-id !
  u-id @ lf-lscope-context-add must v-id @ lf-lscope-context-add must
  w-id @ lf-lscope-context-add must ;

\ ---------------------------------------------------------------------------
\ Lean's name order (name.cpp 191-220): by components from the root, a
\ string after a number, strings by bytes then length, numbers by value,
\ a prefix before its extensions.
session
: nm ( c-addr u -- id ) intern ;
: num ( prefix n -- id ) lf-name-num must ;
: str ( prefix c-addr u -- id ) lf-name-str must ;
s" a" nm constant n-a   s" b" nm constant n-b   s" aa" nm constant n-aa
s" B" nm constant n-cap
n-a 1 num constant n-a.1   n-a 2 num constant n-a.2   n-a 10 num constant n-a.10
n-a s" b" str constant n-a.b   n-a.1 s" x" str constant n-a.1.x
: cmp ( a b -- n ) lf-lnorm-name-cmp ;
T{ n-a n-a cmp n-a n-b cmp n-b n-a cmp -> 0 -1 1 }T
T{ n-a n-aa cmp n-b n-aa cmp n-cap n-a cmp -> -1 1 -1 }T
T{ n-a.2 n-a.10 cmp n-a.1 n-a.b cmp n-a.b n-a.1 cmp -> -1 -1 1 }T
T{ n-a n-a.b cmp n-a.b n-a cmp n-a.1.x n-a.2 cmp -> -1 1 -1 }T
T{ n-b n-a.b cmp n-a.10 n-aa cmp -> 1 -1 }T
T{ 0 s" u" lf-name-str must lf-lnorm-name-ok? 99 lf-lnorm-name-ok? -> true false }T

\ ---------------------------------------------------------------------------
\ mk_max and mk_imax (level.cpp 81-104, 112-123), one rule at a time. The
\ result is an argument (its index) or a new node right after the store's
\ last one.
session
u-id @ param constant u   v-id @ param constant v   w-id @ param constant w
0 succ constant one   one succ constant two   0 succ constant one'
u succ constant u+1   u+1 succ constant u+2   v succ constant v+1
u v max-of constant max-uv   u param constant u'
: next-node ( -- index ) lf-level-count @ ;
: new? ( level tag a b -- flag ) 2>r swap lf-level-read must 2r> d= -rot = and ;
\ Both explicit: the deeper; equal depth, the first.
T{ one two lf-level-mk-max must two one lf-level-mk-max must -> two two }T
T{ one one' lf-level-mk-max must one' one lf-level-mk-max must -> one one' }T
\ Equal: the first. A zero argument: the other.
T{ u u' lf-level-mk-max must u' u lf-level-mk-max must -> u u' }T
T{ 0 u lf-level-mk-max must u 0 lf-level-mk-max must -> u u }T
\ One argument of the other, a max: that max.
T{ u max-uv lf-level-mk-max must v max-uv lf-level-mk-max must -> max-uv max-uv }T
T{ max-uv v lf-level-mk-max must max-uv u lf-level-mk-max must -> max-uv max-uv }T
\ The same base: the larger offset.
T{ u+1 u lf-level-mk-max must u u+2 lf-level-mk-max must -> u+1 u+2 }T
\ Nothing applies: a new max, even for an explicit level and a parameter.
next-node constant n1
T{ u v lf-level-mk-max must -> n1 }T
T{ n1 lf-level-tag-max u v new? -> true }T
next-node constant n2
T{ one u+1 lf-level-mk-max must dup lf-level-tag-max one u+1 new? -> n2 true }T
\ mk_imax: a right side never zero gives mk_max; a zero right side is
\ zero; a left side zero or one gives the right side; equal sides the left.
T{ u v+1 lf-level-mk-imax must dup lf-level-tag-max u v+1 new? -> next-node 1- true }T
T{ u+1 u lf-level-mk-imax must -> next-node 1- }T
T{ next-node 1- lf-level-tag-imax u+1 u new? -> true }T
v one max-of constant max-v1
T{ u max-v1 lf-level-mk-imax must dup lf-level-tag-max u max-v1 new? -> next-node 1- true }T
T{ u 0 lf-level-mk-imax must 0 u lf-level-mk-imax must one u lf-level-mk-imax must
  -> 0 u u }T
T{ u u' lf-level-mk-imax must -> u }T
T{ two u lf-level-mk-imax must -> next-node 1- }T
T{ next-node 1- lf-level-tag-imax two u new? -> true }T
\ imax 1 (u+1) becomes max 1 (u+1); u+1 already covers it only after
\ normalize, which mk_max does not do.
T{ one u+1 lf-level-mk-imax must dup lf-level-tag-max one u+1 new? -> next-node 1- true }T
\ lf-level-same? is structural, parameters by ID; invalid levels are false.
T{ u u' lf-level-same? u v lf-level-same? one one' lf-level-same? -> true false true }T
T{ u -1 lf-level-same? u 99 lf-level-mk-max -> false false }T
\ A full store: a new node is refused; an argument is still given.
: fill-levels ( -- ) begin lf-level-count @ lf-level-capacity < while 0 succ drop repeat ;
\ Levels made by a test are given back through a mark of the level store
\ (lib/store.fs), never by setting its count.
create level-mark /store-mark allot
: levels-marked ( -- ) level-mark lf-levels store-mark ok? 0= abort" level mark" ;
: levels-back ( -- ) level-mark lf-levels store-rollback ok? 0= abort" level rollback" ;
levels-marked
fill-levels
T{ u v lf-level-mk-max -> false }T
T{ u 0 lf-level-mk-imax -> 0 true }T
levels-back

\ ---------------------------------------------------------------------------
\ is_equivalent (518-521) through level-compare: ok for Lean's true,
\ unknown for Lean's false, which lf-level-inequivalent? reports as apart.
session
u-id @ param constant lu   v-id @ param constant lv
0 succ constant lone
lu succ constant su   lv succ constant sv
: cmp100 ( a b -- status ) 100 lf-level-compare ;
: apart ( a b -- flag status ) 100 lf-level-inequivalent? ;
\ The table of tests/reference/level-compare-table.lean, with names.
T{ lu lu cmp100 su lu succ cmp100 lu lv cmp100 -> outcome-ok outcome-ok outcome-unknown }T
T{ lu lu 0 max-of cmp100 lone lone 0 max-of cmp100 0 lone cmp100
  -> outcome-ok outcome-ok outcome-unknown }T
T{ lu 0 imax-of 0 cmp100 lu lv max-of lv lu max-of cmp100 lu 0 lu max-of cmp100
  -> outcome-ok outcome-ok outcome-ok }T
T{ lu 0 max-of succ su cmp100 su 0 imax-of 0 cmp100 0 lu 0 max-of max-of lu cmp100
  -> outcome-ok outcome-ok outcome-ok }T
T{ lu 0 max-of succ lv max-of su lv max-of cmp100
  lu 0 max-of succ lv imax-of su lv imax-of cmp100 0 lu imax-of 0 cmp100
  -> outcome-ok outcome-ok outcome-unknown }T
\ Levels here: lu, lv the parameters u, v; su, sv their successors; lone
\ the level 1. Lean's incompleteness, kept: imax 1 (u+1) against
\ max 1 (u+1); the
\ order of names after an imax (T1 against T2 of the review); a zero that
\ only normalize removes from inside a max.
lone su imax-of constant i1u   lone su max-of constant m1u
T{ i1u m1u apart -> true outcome-ok }T
T{ i1u m1u cmp100 lf-lcmp-apart @ -> outcome-unknown true }T
T{ sv su imax-of sv su max-of apart su sv imax-of sv su max-of apart
  -> true outcome-ok false outcome-ok }T
T{ 0 i1u max-of succ i1u succ apart -> true outcome-ok }T
T{ i1u su apart m1u su apart -> true outcome-ok false outcome-ok }T
\ Equal levels are never apart; neither are levels Lean equates.
T{ su su apart lu lv max-of lv lu max-of apart -> false outcome-ok false outcome-ok }T
\ Explicit levels compare by value (normalize gives their value).
T{ lone 0 max-of lone 0 imax-of max-of lone cmp100 0 succ succ lone lone max-of succ cmp100
  -> outcome-ok outcome-ok }T
\ Nothing stays allocated, and the facts of level-make follow the store.
lf-level-count @ constant count-before
T{ i1u m1u cmp100 lf-level-count @ -> outcome-unknown count-before }T

\ Two different parameters whose IDs are not names cannot be ordered:
\ unknown, not apart. One parameter alone needs no order.
lf-level-count @ constant opaque-base
77 lf-lscope-context-add must 78 lf-lscope-context-add must
77 param constant p   78 param constant q
T{ p q max-of q p max-of apart -> false outcome-unknown }T
T{ p p 0 max-of cmp100 p q cmp100 -> outcome-ok outcome-unknown }T

\ Fuel: the scope checks of both roots, then one unit per level
\ normalized, max argument pushed and pair ordered; structural equality
\ is free. Every budget gives the full answer or exhausted, never ok
\ early, and no node stays allocated.
lu lv max-of lv lu max-of 2constant swapped
lf-level-count @ constant budget-base
: budget ( a b fuel -- )
  lf-level-compare dup outcome-ok <> over outcome-exhausted <> and abort" budget outcome"
  outcome-exhausted = lf-lcmp-fuel @ 0<> and abort" exhausted keeps fuel"
  lf-level-count @ budget-base <> abort" budget allocation" ;
: budgets ( a b -- ) 60 0 do 2dup i budget loop 2drop ;
swapped budgets
: needed ( a b -- n ) 0 begin >r 2dup r@ lf-level-compare ok? 0= while r> 1+ repeat
  2drop r> ;
\ max u v against max v u: two scope checks of three visits; normalizing
\ max u v takes 9 (the level, three pushes of its arguments, u and v
\ normalized and pushed, one ordering), max v u 7 (u and v remembered).
T{ swapped needed -> 22 }T
T{ swapped 30 lf-level-compare lf-lcmp-fuel @ -> outcome-ok 8 }T
\ Stamps (plan task 6.5.5): a call's memo of normal forms erases nothing,
\ it takes a new stamp; only when the stamps run out is the column erased
\ and they restart at 1, so no earlier call's normal form counts as this
\ call's. Every level holds stamp 1 and itself as its normal form, as an
\ earlier call could leave it, and the stamps run out: the comparison
\ still spends what it did above.
: stale-forms ( -- )
  1 lf-lnorm-stamp ! lf-level-count @ 0 ?do i 1+ i lf-lnorm-memo! loop
  max-n lf-lnorm-stamp ! ;
stale-forms
T{ swapped 30 lf-level-compare lf-lcmp-fuel @ lf-lnorm-stamp @ -> outcome-ok 8 1 }T
T{ lu lu 20 lf-level-compare lf-lcmp-fuel @ -> outcome-ok 18 }T
\ Undecided keeps the fuel only in keeping mode; failures leave none.
T{ lu lv 20 lf-level-compare lf-lcmp-fuel @ -> outcome-unknown 0 }T
T{ lu lv 20 lf-level-compare-keeping lf-lcmp-fuel @ -> outcome-unknown 16 }T
T{ lu lv 3 lf-level-compare-keeping lf-lcmp-fuel @ -> outcome-exhausted 0 }T
\ Room: the store full, normalize cannot build its forms: full, and the
\ store is back.
levels-marked
fill-levels
T{ i1u m1u 100 lf-level-compare -> outcome-full }T
T{ i1u m1u 100 lf-level-inequivalent? -> false outcome-full }T
T{ lf-level-count @ -> lf-level-capacity }T
levels-back
\ Invalid input: negative fuel, a level outside the store, a corrupted
\ node, a parameter outside the context.
T{ lu lv -1 lf-level-compare lf-lcmp-fuel @ -> outcome-invalid 0 }T
T{ -1 lu 100 lf-level-compare 99 lu 100 lf-level-compare -> outcome-invalid outcome-invalid }T
T{ lu lu -1 lf-level-equivalent lu 99 100 lf-level-equivalent
  -> false outcome-invalid false outcome-invalid }T
lu lf-level-tag@ constant saved-tag
99 lu level-tag!
T{ lu lv 100 lf-level-compare lv lu 100 lf-level-compare -> outcome-invalid outcome-invalid }T
saved-tag lu level-tag!
lf-lscope-context-reset
T{ lu lu 100 lf-level-compare -> outcome-invalid }T
T{ lu lu 20 ' lf-level-compare rs-checked -> outcome-invalid }T

\ ---------------------------------------------------------------------------
\ Random levels against an independent model. Levels are built from zero,
\ u, v, w, succ, max and imax over earlier levels, each with at most
\ tree-limit nodes as a tree, so the model's plain recursion stays small.
variable level-seed
: level-rnd ( n -- u ) level-seed @ 1103515245 * 12345 + dup level-seed ! 16 rshift 32767 and swap mod ;
create sizes lf-level-capacity cells allot
: size ( level -- n ) cells sizes + @ ;
: size! ( n level -- ) cells sizes + ! ;
24 constant tree-limit
variable pool    \ levels to pick from: those built so far
: pick-level ( -- level ) pool @ level-rnd ;
: small2 ( -- a b true | false )
  pick-level pick-level 2dup size swap size + tree-limit < dup 0= if nip nip then ;
: grow ( -- )
  6 level-rnd case
    0 of pick-level dup size tree-limit < if succ drop else drop then endof
    1 of small2 if max-of drop then endof
    2 of small2 if imax-of drop then endof
    3 of u-id @ param drop endof
    4 of v-id @ param drop endof
    >r small2 if imax-of drop then r> endcase ;
: sized ( level -- n )
  lf-level-read must rot case
    lf-level-tag-succ of drop size 1+ endof
    lf-level-tag-max of size swap size + 1+ endof
    lf-level-tag-imax of size swap size + 1+ endof
    >r 2drop 1 r> endcase ;
: grown ( -- ) lf-level-count @ 1- dup sized swap size! ;
: random-store ( limit -- )
  session u-id @ param drop v-id @ param drop w-id @ param drop
  lf-level-count @ 0 do i sized i size! loop
  begin lf-level-count @ dup pool ! over < while grow grown repeat drop ;

\ The model, from level.cpp: operator== (125-150), get_depth, is_explicit,
\ to_offset, is_not_zero, is_one, and the choices of mk_max and mk_imax.
: kids ( level -- first second ) lf-level-read must rot drop ;
: m-same? ( a b -- flag )
  2dup tag@ swap tag@ <> if 2drop false exit then
  over tag@ case
    lf-level-tag-zero of 2drop true endof
    lf-level-tag-param of kids drop swap kids drop = endof
    lf-level-tag-succ of kids drop swap kids drop recurse endof
    drop 2dup kids drop swap kids drop recurse >r kids nip swap kids nip recurse r> and 0
  endcase ;
: m-depth ( level -- n )
  dup tag@ case
    lf-level-tag-zero of drop 0 endof
    lf-level-tag-param of drop 0 endof
    lf-level-tag-succ of kids drop recurse 1+ endof
    drop kids recurse swap recurse max 1+ 0 endcase ;
: m-explicit? ( level -- flag )
  begin dup tag@ lf-level-tag-succ = while kids drop repeat tag@ lf-level-tag-zero = ;
: m-offset ( level -- base k )
  0 begin over tag@ lf-level-tag-succ = while swap kids drop swap 1+ repeat ;
: m-nonzero? ( level -- flag )
  dup tag@ case
    lf-level-tag-succ of drop true endof
    lf-level-tag-max of kids recurse swap recurse or endof
    lf-level-tag-imax of kids nip recurse endof
    nip false swap endcase ;
: m-zero? ( level -- flag ) tag@ lf-level-tag-zero = ;
: m-one? ( level -- flag )
  dup tag@ lf-level-tag-succ = if kids drop m-zero? else drop false then ;
: m-arg-of? ( a b -- flag )   \ b is a max with a as an argument
  dup tag@ lf-level-tag-max <> if 2drop false exit then
  kids >r over m-same? swap r> m-same? or ;
\ 0 new node, 1 first, 2 second (3 for mk_imax: mk_max).
: m-max ( a b -- choice )
  2dup m-explicit? swap m-explicit? and
  if m-depth swap m-depth swap >= if 1 else 2 then exit then
  2dup m-same? if 2drop 1 exit then
  over m-zero? if 2drop 2 exit then
  dup m-zero? if 2drop 1 exit then
  2dup m-arg-of? if 2drop 2 exit then
  2dup swap m-arg-of? if 2drop 1 exit then
  m-offset rot m-offset 2swap rot 2swap ( kb ka ba bb )
  m-same? if < if 1 else 2 then else 2drop 0 then ;
: m-imax ( a b -- choice )
  dup m-nonzero? if 2drop 3 exit then
  dup m-zero? if 2drop 2 exit then
  over dup m-zero? swap m-one? or if 2drop 2 exit then
  m-same? if 1 else 0 then ;
\ Whether result is what the choice says: the first or the second
\ argument (1, 2), or a new node of the tag over them (0).
: as-chosen ( result tag a b choice -- flag )
  case 1 of drop nip = endof 2 of nip nip = endof 0 of new? endof
    >r 2drop 2drop false r> endcase ;
create hits 4 cells allot
: hit ( choice -- ) cells hits + 1 swap +! ;
variable checks
: check-max ( a b -- )
  2dup m-max dup hit >r 2dup lf-level-mk-max must lf-level-tag-max 2swap r>
  as-chosen 0= abort" mk_max differs from the model" ;
\ mk_imax's expected tag and choice: mk_max's for choice 3.
: imax-expectation ( a b -- tag choice )
  2dup m-imax dup 3 = if drop m-max lf-level-tag-max swap
  else nip nip lf-level-tag-imax swap then ;
: check-imax ( a b -- )
  2dup m-imax hit 2dup imax-expectation 2>r 2dup lf-level-mk-imax must -rot
  2r> >r -rot r> as-chosen 0= abort" mk_imax differs from the model" ;
: check-same ( a b -- )
  2dup lf-level-same? -rot m-same? <> abort" operator== differs from the model" ;
: round ( n -- )
  level-seed ! lf-level-capacity 8 - random-store levels-marked
  200 0 do pick-level pick-level 2dup check-same 2dup check-max check-imax
    levels-back 3 checks +! loop ;
hits 4 cells erase 0 checks !
: rounds ( -- ) 30 0 do i 7 * 1+ round loop ;
rounds
\ Every choice of the model is reached.
T{ hits @ 0> hits cell+ @ 0> hits 2 cells + @ 0> hits 3 cells + @ 0> -> true true true true }T
.( constructor checks against the model: ) checks @ . cr

\ Equivalent levels have equal values under every witness assignment
\ (each step of Lean's normalize keeps the value), equivalence is
\ symmetric, and structurally equal levels are equivalent.
: witness-value ( level w -- n ) 100000 swap lf-level-value-witness ok? must ;
: values= ( a b w -- flag ) tuck witness-value >r witness-value r> = ;
: witnesses= ( a b -- flag )
  2dup -1 values= >r 2dup 0 values= >r 2dup u-id @ values= >r 2dup v-id @ values= >r
  w-id @ values= r> and r> and r> and r> and ;
variable eqs  variable crowded
: equivalent? ( a b -- flag true | false )
  100000 lf-level-equivalent dup outcome-full = if 2drop 1 crowded +! false exit then
  ok? must true ;
: check-equivalent ( a b -- )
  2dup equivalent? 0= if 2drop exit then >r
  2dup swap equivalent? 0= if r> drop 2drop exit then r@ <> abort" not symmetric"
  2dup m-same? r@ 0= and abort" equal but not equivalent"
  r> if witnesses= 0= abort" equivalent with different values" 1 eqs +! else 2drop then ;
: equivalence-round ( n -- )
  level-seed ! lf-level-capacity 2/ random-store
  300 0 do pick-level pick-level check-equivalent loop ;
0 eqs ! 0 crowded !
: equivalence-rounds ( -- ) 20 0 do i 13 * 5 + equivalence-round loop ;
equivalence-rounds
T{ eqs @ 100 > crowded @ 100 < -> true true }T
.( equivalent pairs checked against the witnesses: ) eqs @ .
.( ; pairs that filled the store: ) crowded @ . cr

\ Level-make's facts are kept from call to call, found through the index
\ of classes, and given up from the top (the review's finding M2: refilled
\ from nothing at every call they cost n*n/2 node comparisons, 22 s for
\ one call above 16,000 levels). At a raised capacity, one comparison at
\ the top of 3,001 levels finds the facts of all of them; the next finds
\ none again. Records rolled back and made again with other nodes (new
\ identities) get new facts: a parameter where a successor was is a new
\ class, and equal again to a parameter made after it.
\ First, at the default capacity: nodes that share a bucket of the index
\ are told apart by comparing them. Parameters whose IDs differ only from
\ bit 20 up share a bucket (with a power of two of buckets, the bucket
\ depends on the low bits alone), and are still different classes, each
\ equal to itself made again.
lf-level-reset
: own-classes? ( n -- flag ) true swap 1+ 1 ?do i lf-lmk-class@ i = and loop ;
: far-param ( k -- level ) 20 lshift 1+ lf-level-param must ;
: far-params ( n -- ) 0 ?do i 1+ far-param drop loop ;
: bucket-of ( index -- b ) lf-lmk-hash lf-lmk-buckets mod ;
10 far-params
T{ 10 1 lf-level-same? 10 own-classes? 1 bucket-of 10 bucket-of = -> false true true }T
T{ 1 far-param 1 lf-level-same? -> true }T
T{ 16384 lf-level-capacity! -> outcome-ok }T
lf-level-reset
: succs ( level n -- top ) 0 ?do lf-level-succ must loop ;
\ The level store is marked at count 1000, on the way up the chain, and
\ given back to it after.
0 999 succs levels-marked 2001 succs constant tall
T{ tall tall lf-level-same? lf-lmk-known @ -> true 3001 }T
T{ tall 0 lf-level-same? lf-lmk-known @ -> false 3001 }T
T{ 0 1000 succs drop lf-level-count @ -> 4001 }T
T{ tall 1000 succs 0 4000 succs lf-level-same? lf-lmk-known @ -> true 9001 }T
T{ level-mark mark-count @ -> 1000 }T
levels-back
u-id @ lf-level-param must constant u1
u-id @ lf-level-param must constant u2
T{ u1 u2 lf-level-same? u1 999 lf-level-same? lf-lmk-known @ -> true false 1002 }T
T{ 999 lf-lmk-class@ u1 lf-lmk-class@ u2 lf-lmk-class@ -> 999 1000 1000 }T
\ Many classes at a raised capacity: 2,000 different parameters are
\ 2,000 classes.
lf-level-reset
: params ( n -- ) 0 ?do i 1+ lf-level-param must drop loop ;
2000 params
T{ 2000 2000 lf-level-same? 2000 own-classes? -> true true }T
T{ 1234 lf-level-param must 1234 lf-level-same? -> true }T
\ Long argument lists are merge sorted (plan task 6.2.0): a max of 40
\ parameters nested one way equals the same max nested the other way, and
\ differs from one with a parameter changed.
lf-level-reset
: nparam ( i -- level ) 0 swap lf-name-num must lf-level-param must ;
: up-chain ( n -- level ) 1 nparam swap 1+ 2 ?do i nparam lf-level-max must loop ;
: down-chain ( n -- level ) 1 nparam swap 1+ 2 ?do i nparam swap lf-level-max must loop ;
T{ 40 up-chain 40 down-chain 100000 lf-level-equivalent -> true outcome-ok }T
T{ 40 up-chain 39 down-chain 41 nparam lf-level-max must 100000 lf-level-equivalent
   -> false outcome-ok }T
\ The scope checks' memo (compact-store plan step S4): off (outside a
\ check), each comparison walks both roots; on, a root found in scope is
\ not walked again while its identity and the parameter context's
\ generation hold, so it costs no fuel; a change of the context, or the
\ index given back and made again, walks it again.
session
u-id @ param succ constant mu+1   u-id @ param succ constant m1
: cmp-fuel ( -- fuel ) mu+1 m1 30 lf-level-compare drop lf-lcmp-fuel @ ;
T{ cmp-fuel cmp-fuel -> 26 26 }T
lf-memo-on lf-audit-memo!
T{ cmp-fuel cmp-fuel -> 26 30 }T
99 lf-lscope-context-add must
T{ cmp-fuel cmp-fuel -> 26 30 }T
\ A parameter context whose count is corrupted is never trusted from the
\ memo: the kept roots are walked again, and the walk refuses them
\ (review rvS4 L1).
lf-lscope-context-count @ constant ctx-count
lf-lscope-ids slab-capacity 1+ lf-lscope-context-count !
T{ mu+1 m1 30 lf-level-compare ok? -> false }T
ctx-count lf-lscope-context-count !
T{ cmp-fuel -> 30 }T
create memo-mark /store-mark allot
: memo-pair ( -- a b ) u-id @ param succ u-id @ param succ ;
: pair-fuel ( a b -- fuel ) 30 lf-level-compare drop lf-lcmp-fuel @ ;
memo-mark lf-levels store-mark drop
T{ memo-pair 2dup pair-fuel -rot pair-fuel -> 26 30 }T
memo-mark lf-level-rollback drop
T{ memo-pair pair-fuel -> 26 }T
lf-memo-off lf-audit-memo!
T{ cmp-fuel -> 26 }T
lf-memo-auto lf-audit-memo!
lf-level-reset
T{ lf-level-default lf-level-capacity! -> outcome-ok }T
bye
