\ Test support for the checked environment (src/kernel/environment.fs,
\ env-publish.fs): names, synthetic inputs, a synthetic check, and digests.
\ Test-only.
\
\ The synthetic check does with the environment what check-declaration
\ (plan task 2.2.3) will do, without any typing: an audit step with its
\ planned audit outcome, N2 on its own name, one lookup per name it uses
\ (each recorded as a dependency), then its planned verdict. Each step that
\ succeeds charges one unit of the declaration's fuel; out of fuel is
\ exhausted. syn-pause runs after each step; the interleaving tests make it
\ task-yield. A plan per declaration is shared, read-only data; the fuel
\ left is in a context record, so jobs keep their own.
\
\ Digests (FNV-style mixing of cells, compared only within one run): one
\ per slot (0 for a slot that is not final), of the dependency pool, and
\ of the input region below the input marks, including the name bytes.
\
\ Defining lf-env-fault-hooks first compiles the publisher's test-only
\ fault-injection hook, lf-env-before-final.

: lf-env-fault-hooks ( -- ) ;
require ../../src/kernel/env-publish.fs

\ ---------------------------------------------------------------------------
\ The world an input refers to: names, and two terms for every type and
\ value root (the environment never looks inside them). world builds it
\ in the current context; the input is per context in v0 (input.fs), so
\ every context that checks builds the same world, from a fresh start,
\ and gets the same IDs and indices, which world-again verifies.
: sub ( prefix c-addr u -- id ) lf-name-str 0= abort" intern" ;
: intern ( c-addr u -- id ) 0 -rot sub ;
: sort-term ( n -- index ) lf-term-sort 0= abort" term" ;
: letters ( -- c-addr u ) s" ABCDEFGHIJKLMNPQRSTXYZuvw" ;
32 constant most-names
create name-ids most-names cells allot
create ids-before most-names cells allot
: name-at ( k -- addr ) cells name-ids + ;
: letter ( k -- id ) letters drop + 1 intern ;
: world-names ( -- )
  letters nip 0 ?do i letter i name-at ! loop
  s" Nat" intern dup 25 name-at ! s" add" sub 26 name-at ! ;
0 constant t-type
1 constant t-value
: world ( -- )
  world-names 0 sort-term t-type <> 1 sort-term t-value <> or abort" world: terms" ;
: world-again ( -- )
  name-ids ids-before most-names cells move world
  name-ids most-names cells ids-before over compare abort" world: names" ;
: name: ( k "name" -- ) create , does> @ name-at @ ;
0 name: n.A    1 name: n.B    2 name: n.C    3 name: n.D    4 name: n.E
5 name: n.F    6 name: n.G    7 name: n.H    8 name: n.I    9 name: n.J
10 name: n.K   11 name: n.L   12 name: n.M   13 name: n.N   14 name: n.P
15 name: n.Q   16 name: n.R   17 name: n.S   18 name: n.T   19 name: n.X
20 name: n.Y   21 name: n.Z   22 name: n.u   23 name: n.v   24 name: n.w
25 name: n.Nat 26 name: n.Nat.add
world

\ ---------------------------------------------------------------------------
\ Plans and the input builder.
lf-input-capacity constant decls
4 constant most-uses
begin-structure /plan
  field: plan-audit       \ the audit step's outcome; ok goes on
  field: plan-verdict     \ the outcome once every step succeeded
  field: plan-fuel        \ fuel for the whole check
  field: plan-count       \ names used
  most-uses cells +field plan-uses
end-structure
\ One plan per declaration, and one more for an attempt to add to a full
\ input.
create plans decls 1+ /plan * allot
: plan ( i -- addr ) /plan * plans + ;
variable building
: the-plan ( -- addr ) building @ plan ;

create buf /lf-idecl allot
: decl ( name kind -- )
  buf /lf-idecl erase buf lf-idecl-kind ! buf lf-idecl-name !
  t-type buf lf-idecl-type ! t-value buf lf-idecl-value !
  lf-input-count building ! the-plan /plan erase 1000 the-plan plan-fuel ! ;
: no-value ( -- ) -1 buf lf-idecl-value ! ;
create buf-params 4096 cells allot
: param ( name -- )
  buf-params buf lf-idecl-params ! buf-params buf lf-idecl-arity @ cells + !
  1 buf lf-idecl-arity +! ;
: uses ( name -- ) the-plan dup plan-count @ cells swap plan-uses + ! 1 the-plan plan-count +! ;
: audit ( outcome -- ) the-plan plan-audit ! ;
: verdict ( outcome -- ) the-plan plan-verdict ! ;
: fuel ( n i -- ) plan plan-fuel ! ;
: add ( -- ) buf lf-input-add ok? 0= abort" add" drop ;
: def ( name -- ) lf-kind-definition decl ;
: thm ( name -- ) lf-kind-theorem decl ;
: ends ( -- ) lf-input-end ok? 0= abort" end" ;

\ The main input: 27 declarations reaching every outcome and every naming
\ rule. The expected verdicts follow it.
: main-input-1 ( -- )
  n.A def n.u param add                         \ 0  ok
  n.B thm n.A uses add                          \ 1  ok, uses 0
  n.C def n.Z uses add                          \ 2  rejected: Z is unknown (N1)
  n.D def outcome-unknown verdict add          \ 3  unknown
  n.E thm n.D uses add                          \ 4  unknown: D undecided (K5)
  n.F lf-kind-axiom decl no-value outcome-unsupported audit add  \ 5 unsupported (U1)
  n.G def n.F uses add                          \ 6  unsupported: F unsupported (K5)
  n.A def add                                  \ 7  rejected: A accepted (N2)
  n.C def n.A uses n.B uses add                  \ 8  ok: C was rejected, no conflict
  n.H def n.H uses add ;                        \ 9  rejected: self reference (N1)
: main-input-2 ( -- )
  n.I def n.J uses add                          \ 10 rejected: forward reference (N1)
  n.J def n.u param n.v param add                \ 11 ok
  n.D def add                                  \ 12 unknown: D undecided (N2, K5)
  n.K def outcome-exhausted verdict add        \ 13 exhausted
  n.L def n.K uses add                          \ 14 unknown: K exhausted (K5)
  n.M def outcome-invalid verdict add          \ 15 invalid
  n.N def outcome-full verdict add             \ 16 full
  n.P def n.N uses n.M uses add                  \ 17 unknown (K5)
  n.Q def outcome-rejected verdict add         \ 18 rejected
  n.R def n.Q uses add ;                        \ 19 rejected: Q rejected (N1)
: main-input-3 ( -- )
  n.F def add                                  \ 20 unsupported: F unsupported (N2, K5)
  n.Nat.add def add                            \ 21 ok
  n.S thm n.Nat uses add                        \ 22 rejected: Nat is not Nat.add (N1)
  n.T thm n.v param n.u param n.Nat.add uses n.J uses n.B uses add   \ 23 ok, uses 1 11 21
  n.X def add                                  \ 24 ok
  n.X def outcome-unsupported audit add        \ 25 unsupported (audit before N2)
  n.Y def n.X uses add ;                        \ 26 ok: the accepted X wins, uses 24
: main-input ( -- ) lf-input-reset main-input-1 main-input-2 main-input-3 ends ;
27 constant main-count
create main-expected
  outcome-ok , outcome-ok , outcome-rejected , outcome-unknown , outcome-unknown ,
  outcome-unsupported , outcome-unsupported , outcome-rejected , outcome-ok ,
  outcome-rejected , outcome-rejected , outcome-ok , outcome-unknown ,
  outcome-exhausted , outcome-unknown , outcome-invalid , outcome-full ,
  outcome-unknown , outcome-rejected , outcome-rejected , outcome-unsupported ,
  outcome-ok , outcome-rejected , outcome-ok , outcome-ok , outcome-unsupported ,
  outcome-ok ,
: expected@ ( i -- outcome ) cells main-expected + @ ;

\ ---------------------------------------------------------------------------
\ The synthetic check, run in the current context.
begin-structure /syn
  field: syn-fuel
end-structure
/syn context-record: syn
: syn-still ( -- ) ;
defer syn-pause
' syn-still is syn-pause

: me ( -- i ) lf-env-cand lf-cand-decl @ ;
: my-plan ( -- addr ) me plan ;
: spend ( -- outcome )
  syn syn-fuel @ 0> if -1 syn syn-fuel +! outcome-ok else outcome-exhausted then ;
\ Go on after a step: spend fuel and pause; or finish with the failure.
: step ( outcome -- flag )
  dup ok? if drop spend then dup ok? if drop syn-pause true else lf-env-finish false then ;
: use@ ( k -- name ) cells my-plan plan-uses + @ ;
: use-step ( k -- flag ) use@ lf-env-resolve nip step ;
: syn-uses ( -- flag )
  my-plan plan-count @ 0 ?do i use-step 0= if false unloop exit then loop true ;
\ The check allocates a scratch term in its context's term store, as a
\ real check would, which the driver must roll back.
: make-scratch ( -- ) 0 lf-term-sort if drop then ;
: syn-check ( -- )
  make-scratch my-plan plan-fuel @ syn syn-fuel !
  my-plan plan-audit @ step 0= if exit then
  lf-env-own-name step 0= if exit then
  syn-uses if my-plan plan-verdict @ lf-env-finish then ;

\ ---------------------------------------------------------------------------
\ Making and running environments.
: fresh-env ( deps -- ) lf-env-new ok? 0= abort" env" lf-env-use ok? 0= abort" use" ;
: env-free ( -- ) lf-env lf-env-free ok? 0= abort" free" ;
\ Results are read in a view of the whole environment.
: verdicts-match? ( n -- flag )
  lf-env-view drop true swap 0 ?do i lf-env-outcome i expected@ = and loop ;
\ A maker for lf-env-run (G-P6): a new, idle context holding the same
\ world and the main input; the current context stays selected.
: main-maker ( -- context ior )
  context-new ?dup if exit then
  lf-context @ over context-use world-again main-input context-use 0 ;

\ ---------------------------------------------------------------------------
\ Digests.
: digest-mix ( h x -- h' ) xor 16777619 um* drop ;
: digest-cells ( h addr n -- h' ) 0 ?do dup @ rot swap digest-mix swap cell+ loop drop ;
: digest-bytes ( h addr n -- h' ) 0 ?do dup c@ rot swap digest-mix swap char+ loop drop ;
: width-cells ( store -- n ) store-width @ 1 cells / ;
: recs-digest ( h count store -- h' ) tuck width-cells * swap store-records swap digest-cells ;
: ids-digest ( h count store -- h' ) store-identities swap digest-cells ;
\ A store's records and identities below count.
: store-digest ( h count store -- h' ) 2dup 2>r recs-digest 2r> ids-digest ;
: input-digest ( -- h )
  0 lf-input-stores# 0 ?do i lf-input-mark mark-count @ i lf-input-store store-digest loop
  lf-name-bytes lf-input-bytes @ digest-bytes
  lf-input-state /lf-inrec 1 cells / digest-cells ;
: slot@ ( d -- slot ) lf-env lf-env-slot ;
: slot-digest ( d -- h )
  slot@ dup lf-slot-final? if 0 swap /lf-slot 1 cells / digest-cells else drop 0 then ;
: pool ( -- store ) lf-env lf-env-pool ;
: pool-count ( -- n ) pool store-count @ ;
: pool-digest ( -- h ) 0 pool-count pool store-digest pool-count digest-mix ;
\ The environment byte for byte: the pool, and every final slot.
: env-digest ( -- h )
  pool-digest lf-env lf-env-length 0 ?do i slot-digest digest-mix loop ;
\ The environment's content, independent of the order of publication:
\ each final slot with its dependencies by value instead of their place
\ in the pool, which depends on the order in which slots were published.
: cells-between ( from to -- addr n ) over - 1 cells / ;
: head-digest ( h slot -- h' ) dup lf-slot-deps cells-between digest-cells ;
: tail-digest ( h slot -- h' ) dup lf-slot-count swap lf-slot-looks cells-between digest-cells ;
: end-digest ( h slot -- h' ) dup lf-slot-looked swap /lf-slot + cells-between digest-cells ;
: deps-digest ( h slot -- h' )
  dup lf-slot-deps @ swap lf-slot-count @ over + swap ?do i pool store-slot @ digest-mix loop ;
\ Its lookups (environment.fs, "Lookups") by value too, from the lookup pool.
: looks-digest ( h slot -- h' )
  dup lf-slot-looked @ 0 ?do
    i over lf-slot-look >r >r swap r> digest-mix r> digest-mix swap
  loop drop ;
: slot-content ( d -- h )
  slot@ dup lf-slot-final? 0= if drop 0 exit then
  0 over head-digest over tail-digest over end-digest over deps-digest swap looks-digest ;
: env-content ( -- h ) 0 lf-env lf-env-length 0 ?do i slot-content digest-mix loop ;

\ ---------------------------------------------------------------------------
\ Steps checked against ADR 0012 test row 2: whatever the outcome, only
\ slot i changes and the input region is unchanged; after a failure the
\ slot holds only its state, outcome and lookups and the pool is
\ unchanged; after an acceptance the pool grew by exactly the slot's
\ dependencies, which are its candidate's; either way the lookup pool grew
\ by exactly the slot's lookups, two records each.
create slot-digests decls cells allot
variable pool-before   variable input-before   variable pool-count-before
variable looks-count-before
variable step-failures  0 step-failures !
: bad ( -- ) 1 step-failures +! ;
: check-that ( flag -- ) 0= if bad then ;
: slots# ( -- n ) lf-env lf-env-length ;
: before@ ( d -- h ) cells slot-digests + @ ;
: looks-count ( -- n ) lf-env lf-env-looks store-count @ ;
: snap ( -- )
  slots# 0 ?do i slot-digest i cells slot-digests + ! loop
  pool-digest pool-before ! input-digest input-before ! pool-count pool-count-before !
  looks-count looks-count-before ! ;
: changed ( -- n ) 0 slots# 0 ?do i slot-digest i before@ <> - loop ;
\ The record up to its lookups.
: slot-tail ( d -- addr n )
  slot@ dup lf-slot-decl tuck swap - 0 lf-slot-looks swap - 1 cells / ;
: after-fail ( i -- )
  dup slot-tail cells-zero? check-that slot@ lf-slot-final? check-that
  pool-digest pool-before @ = check-that ;
: after-accept ( i -- )
  slot@ dup lf-slot-count @ pool-count-before @ + pool-count = check-that
  lf-slot-deps @ pool-count-before @ = check-that ;
: after-looks ( i -- )
  slot@ dup lf-slot-looked @ 2* looks-count-before @ + looks-count = check-that
  dup lf-slot-looked @ if lf-slot-looks @ looks-count-before @ = check-that else drop then ;
: scratch-gone? ( -- flag ) lf-term-count @ 0 lf-input-mark mark-count @ = ;
: after-step ( i outcome -- )
  changed 1 = check-that input-digest input-before @ = check-that
  scratch-gone? check-that over after-looks ok? if after-accept else after-fail then ;
\ Run step i with xt and check it: the outcome.
: checked-step ( xt i -- outcome )
  snap tuck lf-env-step 0= check-that tuck after-step ;
: checked-run ( xt n -- ) 0 ?do dup i checked-step drop loop drop ;
