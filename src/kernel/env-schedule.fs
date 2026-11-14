\ The parallel scheduler of the checked environment (ADR 0012 E7, G-P1 to
\ G-P7; ADR 0009, order of work 4; plan tasks 7.1.1, 7.2.1 in part,
\ 7.3.1): every declaration of the input checked as a job of the job
\ pool (lib/task.fs) in one of several worker contexts, each reading the
\ same input, the driving context's, in place (import/feed.fs's
\ lf-feed-shared; ADR 0016 S8: each worker keeps only its levels,
\ scratch, caches, memos and marks, and must have the same fingerprint), and
\ published by the single publisher, lf-env-hand-over-job
\ (env-publish.fs), in the driving task, outside every job (G-P1). The
\ verdicts and the environment are the serial run's (lf-env-run), however
\ many workers run and in whatever order their checks end (G-P4):
\ - Readiness (G-P5). Before any check, each declaration gets a
\   readiness set: the slots of every earlier declaration named by a
\   name its check may look up -- a constant or a projection's structure
\   in its type, value and recursor rules, a name in its inductive data,
\   its own name and its block's members' names, and the names the
\   checker looks up itself (lf-sch-builtins: literals, quotients,
\   Nat's reductions, the axiom allowlist) -- and of every earlier type
\   whose generated recursor may hold such a name (environment.fs,
\   lf-env-type-name). These are the slots lf-env-ready? asks about. A
\   declaration is handed out when every slot of its set is final; then
\   lf-env-ready? is asked for each of its names, and a refusal (a fault
\   of the plan, counted in lf-sched-unready) defers it until every slot
\   below it is final.
\ - In time. A check that still finds a slot below its declaration not
\   final (environment.fs, lf-env-early?: a name met only after unfolding
\   a definition, of which the input holds a later declaration too) is
\   never handed over: its scratch is rolled back and it runs again once
\   every slot below it is final (lf-sched-reruns). So no check depends on
\   a slot that is not final (G-P7).
\ - Independence. Each check begins in a context rolled back to the
\   input's marks, with empty caches and memos (check-declaration.fs; the
\   level scope memo lasts one check too, level-compare.fs), and so its
\   verdict, diagnostic and fuel do not depend on which checks its worker
\   ran before.
\ - Stops (G-P6). The serial run stops at the first declaration whose
\   check throws or whose publication fails. Here such a declaration
\   lowers lf-sched-stop; nothing after the stop is handed out, every
\   declaration before it is still checked, and the caller shows only the
\   serial run's part. A worker context in which a check threw is freed
\   and replaced from the maker.
\ - Blocks (ADR 0015 B5). A block's members after its first are published
\   with it and not checked again; one its first left open is checked
\   alone, once every slot below it is final, as the serial run checks it.
\ Verdicts are read from the slots afterwards, in file order, so printing
\ needs no order of its own.
\
\ Interface, in the driving task outside jobs, the environment current
\ and valid over the driving context's input:
\ - lf-sched-init ( -- outcome ): frees an earlier run's workers and
\   blocks and starts empty; ok, or invalid for a slab shape refused
\   (never with the shapes here);
\ - lf-sched-plan ( -- outcome ): the readiness sets of the current
\   context's input; ok, or full (no heap), or invalid (a corrupted
\   name or term read, or a list that is not live);
\ - lf-sched-add ( context -- outcome ): a worker, an idle context holding
\   the same input with its check's budget set (the scheduler frees it);
\   ok, or full (invalid for a list that is not live) when its lists
\   cannot grow, and then nothing is added and the context is not taken;
\ - lf-sched-run ( check keep maker -- ): every declaration, check ( -- )
\   the check word, keep ( outcome d -- ) run in the worker's context
\   after each hand-over and rollback (as cli/check-run.fs keeps a
\   serial step), maker ( -- context ior ) a replacement worker, made in
\   the driving context and given back with that context current; the
\   pool runs one worker per context, and is stopped at the end;
\ - lf-sched-tick! ( xt -- ): after lf-sched-init, xt ( -- ) is run in the
\   driving task after each job is settled (a report that does not change
\   the run: progress lines, results written as they become final); 0, the
\   default, none. lf-sched-final ( -- n ): every slot below n is final and
\   n is not beyond the stop (what a tick may report);
\ - lf-sched-pre! ( xt -- ): after lf-sched-init, xt ( d -- n ) is asked
\   in the driving task, the driving context current, when d is about to
\   be handed out (the carry pass's decision on readiness, plan step
\   6.2.5c4): 0, hand it out; 1, xt published d (with its block's
\   members) itself, so it is done; 2, d waits until every slot below it
\   is final and is asked again (a 2 then counts as 0); 3, the run stops
\   at d, as the serial run stops at a failure there; an xt of 0, the
\   default, asks nothing;
\ - lf-sched-stop ( -- d ): the declaration at which the serial run would
\   have stopped, or the input's count; lf-sched-broken? ( -- flag ): the
\   run could not go on (a job refused, no worker left), so its verdicts
\   are incomplete, and lf-sched-cause ( -- n ) why (0 not said, 1 no worker
\   left, 2 a job refused, 3 waiting failed); lf-sched-reached ( -- n ): every slot below it final;
\   lf-sched-checked? ( d -- flag ): d was handed over (checked itself);
\ - lf-sched-reruns, lf-sched-unready, lf-sched-forced, lf-sched-renewed,
\   lf-sched-launched, lf-sched-edges ( -- n ): counts for reports and
\   tests (unready and forced are 0 unless the plan is wrong);
\ - lf-sched-host-ok ( -- flag ): whether this host may run workers at once:
\   threads only on x86-64, whose stores become visible in program order
\   (ADR 0009, Amendment 2; no memory barriers are used); cooperative and
\   serial hosts always may;
\ - lf-sched-pool-start ( -- ior ): size and start the pool before the run,
\   so that a refusal (no threads) leaves the run to the serial one;
\ - lf-sched-workers ( -- n ): the workers added;
\ - lf-sched-free ( -- ): the worker contexts and every block freed.
\ Planted faults, for tests only: a test that defines lf-sched-fault-hooks
\ before this file loads gets lf-sched-faults, a variable of bits
\ (lf-fault-hasty: every declaration is ready at once; lf-fault-trusting:
\ no readiness test at hand-out; lf-fault-careless: a check that began too
\ early is handed over; lf-fault-unordered: a check's facts kept at its
\ place in the order checks ended, not at its declaration), each of which
\ a guard above or the comparison with the serial run must catch.
\
\ [kernel] [runtime] code: not through the review gate (AGENTS.md).
\ Memory: per declaration about 8 cells; per readiness slot 2 cells; per
\ term number 4 bytes (the walk's stamps), all freed by lf-sched-free.
\ The ready queues are priority queues (lib/pqueue.fs), lowest declaration
\ first.
\ State: one shared record, lf-sched, with its slabs, written only by the
\ driving task outside jobs (the workers' contexts are its members' only
\ link to the jobs). LeanForth-specific.

require ../lib/lib.fs
require ../lib/slab.fs
require ../lib/u32.fs
require ../lib/task.fs
require ../lib/sort.fs
require ../lib/pqueue.fs
require ../core/terms.fs
require ../core/input.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/projections.fs
require ../core/statement-match.fs
require ./environment.fs
require ./env-publish.fs

\ A declaration's state, in the low bits of its state cell, with two flags.
0 constant lf-sch-waiting   \ a lone declaration or a block's first, waiting
1 constant lf-sch-queued    \ in the ready heap
2 constant lf-sch-running   \ its check runs as a job
3 constant lf-sch-done      \ handed over, or the run stopped there
4 constant lf-sch-later     \ waits until every slot below it is final
5 constant lf-sch-trailing  \ a block's member after its first
15 constant lf-sch-mask
16 constant lf-sch-checked  \ flag: handed over, so checked itself
32 constant lf-sch-noted    \ flag: its slot was seen final

begin-structure /lf-sched
  field: lf-sch-count       \ declarations of the input
  field: lf-sch-check       \ the check ( -- )
  field: lf-sch-keep        \ ( outcome d -- ), in the worker's context
  field: lf-sch-maker       \ ( -- context ior ): a replacement worker
  field: lf-sch-home-ctx    \ the driving context
  field: lf-sch-stop-at     \ where the serial run would stop, or the count
  field: lf-sch-broken      \ true once the run cannot go on
  field: lf-sch-cause       \ why: 0 unknown, 1 no worker left, 2 job refused, 3 wait failed
  field: lf-sch-frontier    \ every slot below it is final
  field: lf-sch-running#    \ jobs running
  field: lf-sch-stamp       \ the plan's stamp: one per declaration planned
  field: lf-sch-launched#   \ checks handed out as jobs
  field: lf-sch-reruns#     \ checks run again: they began too early
  field: lf-sch-unready#    \ hand-outs lf-env-ready? refused
  field: lf-sch-forced#     \ handed out only because nothing else could run
  field: lf-sch-renewed#    \ workers replaced after a THROW
  field: lf-sch-handed#     \ checks handed over so far
  field: lf-sch-tick        \ ( -- ) run in the driving task after each settled job, or 0
  field: lf-sch-pre         \ ( d -- n ) asked before d is handed out, or 0
  /slab +field lf-sch-ctxs     \ per worker: its context, 0 once lost
  /slab +field lf-sch-jobs     \ per worker: its job, or 0
  /slab +field lf-sch-ats      \ per worker: the declaration its job checks
  /slab +field lf-sch-states   \ per declaration: state and flags
  /slab +field lf-sch-waits    \ per declaration: slots of its set not final yet
  /slab +field lf-sch-froms    \ per declaration: its set's start in lf-sch-deps
  /slab +field lf-sch-deps     \ the readiness sets, slot numbers
  /slab +field lf-sch-nfroms   \ per declaration: its names' start in lf-sch-names
  /slab +field lf-sch-names    \ the names each set came from
  /slab +field lf-sch-rfroms   \ per slot: its dependents' start in lf-sch-rdeps
  /slab +field lf-sch-rdeps    \ the declarations whose sets hold each slot
  /pqueue +field lf-sch-ready  \ declarations ready, lowest first
  /pqueue +field lf-sch-laters \ waiting for every slot below them, lowest first
  /slab +field lf-sch-named    \ per name: stamp of the last set that took it
  /slab +field lf-sch-dseen    \ per slot: stamp of the last set that took it
  /slab +field lf-sch-stack    \ the walk's stack
  /slab +field lf-sch-builtins \ names the checker looks up itself
  /slab +field lf-sch-seen     \ per term number: stamp of the last walk (32 bits)
end-structure
create lf-sched /lf-sched allot  lf-sched /lf-sched erase

\ ---- The slabs: all of cells but the walk's stamps; and the two queues
\ (lib/pqueue.fs), lowest declaration first.
create lf-sch-cell-slabs
  ' lf-sch-ctxs , ' lf-sch-jobs , ' lf-sch-ats , ' lf-sch-states , ' lf-sch-waits ,
  ' lf-sch-froms , ' lf-sch-deps , ' lf-sch-nfroms , ' lf-sch-names ,
  ' lf-sch-rfroms , ' lf-sch-rdeps ,
  ' lf-sch-named , ' lf-sch-dseen , ' lf-sch-stack , ' lf-sch-builtins ,
here lf-sch-cell-slabs - 1 cells / constant lf-sch-cell-slabs#
: lf-sch-slab ( k -- slab ) cells lf-sch-cell-slabs + @ lf-sched swap execute ;
: lf-sch-slab-init ( unit slab -- outcome ) over slab-limit-max swap slab-init ;
: lf-sch-queues-init ( -- outcome )
  ['] sort-signed lf-sched lf-sch-ready pq-init
  ['] sort-signed lf-sched lf-sch-laters pq-init outcome-and ;
\ Two outcomes are made one with outcome-and (lib/outcome.fs): the first
\ that is not ok (review FRK F6: OR-ing them made an invalid slab full).
: lf-sch-slabs-init ( -- outcome )
  1 u32s lf-sched lf-sch-seen lf-sch-slab-init
  lf-sch-cell-slabs# 0 ?do 1 cells i lf-sch-slab lf-sch-slab-init outcome-and loop
  lf-sch-queues-init outcome-and ;
: lf-sch-slabs-free ( -- )
  lf-sch-cell-slabs# 0 ?do i lf-sch-slab slab-free loop lf-sched lf-sch-seen slab-free
  lf-sched lf-sch-ready pq-free lf-sched lf-sch-laters pq-free ;
\ Units up to n in use, the new ones zero: ok, or full.
: lf-sch-zero ( i k slab -- ) >r swap r@ slab-at swap r> slab-unit * erase ;
: lf-sch-hold ( n slab -- outcome )
  tuck slab-count - dup 0> 0= if 2drop outcome-ok exit then
  2dup swap slab-claim ok-then? 0= if nip nip exit then swap rot lf-sch-zero outcome-ok ;
\ Pushing a cell, popping the last one, emptying.
: lf-sch-push ( x slab -- outcome )
  1 over slab-claim ok-then? if swap slab-at ! outcome-ok else nip nip then ;
: lf-sch-pop ( slab -- x ) dup slab-count 1- over slab-at @ swap -1 swap slab-commit ;
: lf-sch-empty ( slab -- ) dup slab-count negate swap slab-commit ;
: lf-sch-cell@ ( i slab -- x ) slab-at @ ;
: lf-sch-any? ( queue -- flag ) pq-count 0> ;

\ ---- Fields and counts.
: lf-sch-n ( -- n ) lf-sched lf-sch-count @ ;
: lf-sch-state ( d -- addr ) lf-sched lf-sch-states slab-at ;
: lf-sch-state@ ( d -- state ) lf-sch-state @ lf-sch-mask and ;
: lf-sch-state! ( state d -- )
  lf-sch-state dup @ lf-sch-mask invert and rot or swap ! ;
: lf-sch-flag! ( flag d -- ) lf-sch-state dup @ rot or swap ! ;
: lf-sch-flag? ( flag d -- flag ) lf-sch-state @ and 0<> ;
: lf-sch-wait ( d -- addr ) lf-sched lf-sch-waits slab-at ;
: lf-sch-from@ ( d -- k ) lf-sched lf-sch-froms lf-sch-cell@ ;
: lf-sch-nfrom@ ( d -- k ) lf-sched lf-sch-nfroms lf-sch-cell@ ;
: lf-sch-rfrom@ ( d -- k ) lf-sched lf-sch-rfroms lf-sch-cell@ ;
: lf-sch-stamp@ ( -- n ) lf-sched lf-sch-stamp @ ;
: lf-sch-count+ ( field-addr -- ) 1 swap +! ;
: lf-sched-stop ( -- d ) lf-sched lf-sch-stop-at @ ;
: lf-sched-broken? ( -- flag ) lf-sched lf-sch-broken @ ;
: lf-sched-cause ( -- n ) lf-sched lf-sch-cause @ ;
: lf-sch-break ( cause -- ) lf-sched lf-sch-cause ! true lf-sched lf-sch-broken ! ;
: lf-sched-reached ( -- n ) lf-sched lf-sch-frontier @ ;
: lf-sched-checked? ( d -- flag ) lf-sch-checked swap lf-sch-flag? ;
: lf-sched-launched ( -- n ) lf-sched lf-sch-launched# @ ;
: lf-sched-reruns ( -- n ) lf-sched lf-sch-reruns# @ ;
: lf-sched-unready ( -- n ) lf-sched lf-sch-unready# @ ;
: lf-sched-forced ( -- n ) lf-sched lf-sch-forced# @ ;
: lf-sched-renewed ( -- n ) lf-sched lf-sch-renewed# @ ;
: lf-sched-edges ( -- n ) lf-sched lf-sch-deps slab-count ;
\ Planted faults (see the header), compiled only into tests.
1 constant lf-fault-hasty  2 constant lf-fault-trusting  4 constant lf-fault-careless
8 constant lf-fault-unordered
[defined] lf-sched-fault-hooks [if]
variable lf-sched-faults  0 lf-sched-faults !
: lf-sch-fault? ( bit -- flag ) lf-sched-faults @ and 0<> ;
[else]
: lf-sch-fault? ( bit -- false ) drop false ;
[then]

\ ---- The plan. The checker's own lookups by name: literals' types and
\ reductions (literals.fs, reduce-nat.fs, string-literals.fs), the
\ quotient's names and Eq (quot.fs), Bool's for Nat's decisions, and the
\ allowlisted axioms' statements (axiom-allowlist.fs). A name that cannot
\ be made is left out: a check that needs it is run again if it began too
\ early.
: lf-sch-builtin ( c-addr u -- )
  lf-stmt-intern if lf-sched lf-sch-builtins lf-sch-push drop else drop then ;
: lf-sch-builtins-nat ( -- )
  s" Nat" lf-sch-builtin s" Nat.zero" lf-sch-builtin s" Nat.succ" lf-sch-builtin
  s" Bool" lf-sch-builtin s" Bool.true" lf-sch-builtin s" Bool.false" lf-sch-builtin ;
: lf-sch-builtins-text ( -- )
  s" Char" lf-sch-builtin s" Char.ofNat" lf-sch-builtin s" List" lf-sch-builtin
  s" List.nil" lf-sch-builtin s" List.cons" lf-sch-builtin s" String" lf-sch-builtin
  s" String.mk" lf-sch-builtin s" String.ofList" lf-sch-builtin ;
: lf-sch-builtins-quot ( -- )
  s" Eq" lf-sch-builtin s" Eq.refl" lf-sch-builtin s" Quot" lf-sch-builtin
  s" Quot.mk" lf-sch-builtin s" Quot.lift" lf-sch-builtin s" Quot.ind" lf-sch-builtin
  s" propext" lf-sch-builtin s" Classical.choice" lf-sch-builtin
  s" Quot.sound" lf-sch-builtin ;
: lf-sch-builtins-make ( -- )
  lf-sched lf-sch-builtins lf-sch-empty
  lf-sch-builtins-nat lf-sch-builtins-text lf-sch-builtins-quot ;

\ A name the current declaration's set takes, once: added to its names.
: lf-sch-named@ ( name -- addr ) lf-sched lf-sch-named slab-at ;
: lf-sch-stamped? ( addr -- flag )
  dup @ lf-sch-stamp@ = if drop false else lf-sch-stamp@ swap ! true then ;
: lf-sch-fresh-name? ( name -- flag ) lf-sch-named@ lf-sch-stamped? ;
: lf-sch-name ( name -- outcome )
  dup 0> 0= if drop outcome-ok exit then
  dup 1+ lf-sched lf-sch-named lf-sch-hold ok-then? 0= if exit then
  dup lf-sch-fresh-name? if lf-sched lf-sch-names lf-sch-push else drop outcome-ok then ;

\ The walk over a declaration's terms, each node once per declaration:
\ the two children of a binary node (an application, a binder, and since
\ compact-store plan step S5's parts 4-5 a let and a projection), a
\ constant's name and a projection leaf's structure name; any other node
\ names nothing.
: lf-sch-seen@ ( t -- addr ) lf-sched lf-sch-seen slab-at ;
: lf-sch-fresh-term? ( t -- flag )
  dup lf-sched lf-sch-seen slab-count u< 0= if drop false exit then
  lf-sch-seen@ dup u32@ lf-sch-stamp@ = if drop false exit then
  lf-sch-stamp@ swap u32! true ;
: lf-sch-term ( t -- outcome ) lf-sched lf-sch-stack lf-sch-push ;
: lf-sch-two ( first second -- outcome )
  lf-sch-term ok-then? 0= if exit then lf-sch-term ;
: lf-sch-const ( cref -- outcome ) lf-cref-slot lf-crec-name @ lf-sch-name ;
: lf-sch-visit ( tag first second -- outcome )
  rot dup lf-term-binary-tag? if drop lf-sch-two exit then
  case lf-tag-constant of drop lf-sch-const endof
    lf-tag-proj of drop lf-sch-name endof
    >r 2drop outcome-ok r> endcase ;
: lf-sch-step ( -- outcome )
  lf-sched lf-sch-stack lf-sch-pop
  dup lf-sch-fresh-term? 0= if drop outcome-ok exit then
  lf-term-read if lf-sch-visit else outcome-invalid then ;
: lf-sch-more? ( outcome -- outcome flag )
  dup ok? lf-sched lf-sch-stack slab-count 0> and ;
: lf-sch-walk ( root -- outcome )
  lf-sch-term begin lf-sch-more? while drop lf-sch-step repeat ;
: lf-sch-root ( t -- outcome ) dup 0< if drop outcome-ok else lf-sch-walk then ;

\ A member's names: its own, its type's and value's, and its inductive
\ data's (a type's all and ctors, a constructor's type, a recursor's all
\ and each rule's constructor and right side).
: lf-sch-item ( items i -- items outcome ) cells over + @ lf-sch-name ;
: lf-sch-list ( items n -- outcome ) ['] lf-sch-item ok-each nip ;
: lf-sch-rule ( rule -- outcome )
  dup lf-irule-ctor lf-sch-name ok-then? 0= if exit then lf-irule-rhs lf-sch-root ;
: lf-sch-rule-at ( rules i -- rules outcome ) over swap lf-irc-rule lf-sch-rule ;
: lf-sch-rules ( data -- outcome ) lf-irc-rules@ ['] lf-sch-rule-at ok-each nip ;
: lf-sch-type-data ( data -- outcome )
  dup lf-ity-all@ lf-sch-list ok-then? 0= if exit then lf-ity-ctors@ lf-sch-list ;
: lf-sch-rec-data ( data -- outcome )
  dup lf-irc-all@ lf-sch-list ok-then? 0= if exit then lf-sch-rules ;
: lf-sch-data ( decl -- outcome )
  dup lf-idecl-data 0= if drop outcome-ok exit then
  dup lf-idecl-data swap lf-idecl-kind @ case
    lf-kind-inductive of lf-sch-type-data endof
    lf-kind-constructor of lf-ict-induct lf-more-field lf-sch-name endof
    lf-kind-recursor of lf-sch-rec-data endof
    nip outcome-ok swap endcase ;
: lf-sch-own ( decl -- decl outcome ) dup lf-idecl-name @ lf-sch-name ;
: lf-sch-type ( decl -- decl outcome ) dup lf-idecl-type @ lf-sch-root ;
: lf-sch-value ( decl -- decl outcome ) dup lf-idecl-value @ lf-sch-root ;
: lf-sch-member ( m -- outcome )
  lf-input-decl lf-sch-own ok-then? 0= if exit then
  lf-sch-type ok-then? 0= if exit then lf-sch-value ok-then? 0= if exit then lf-sch-data ;

\ A block's members: its first u, then each later declaration whose
\ block header names u as its first.
: lf-sch-member-of? ( m u -- flag )
  over lf-sch-n < 0= if 2drop false exit then
  swap lf-input-decl lf-idecl-header ?dup 0= if drop false exit then
  lf-hdr-first lf-more-field = ;
: lf-sch-span ( u -- n )
  dup 1+ begin 2dup swap lf-sch-member-of? while 1+ repeat swap - ;
: lf-sch-member-at ( u k -- u outcome ) over + lf-sch-member ;
: lf-sch-members ( u -- outcome ) dup lf-sch-span ['] lf-sch-member-at ok-each nip ;
: lf-sch-builtin-name ( i -- outcome ) lf-sched lf-sch-builtins lf-sch-cell@ lf-sch-name ;
: lf-sch-builtins-add ( -- outcome )
  lf-sched lf-sch-builtins slab-count ['] lf-sch-builtin-name ok-each ;

\ The slots a name gives the set of declaration u: every declaration of
\ that name below u, and of the type whose generated recursor the name
\ may be (T for T.rec and T.rec_k), each slot once.
: lf-sch-dseen@ ( d -- addr ) lf-sched lf-sch-dseen slab-at ;
: lf-sch-dep ( d -- outcome )
  dup lf-sch-dseen@ dup @ lf-sch-stamp@ = if 2drop outcome-ok exit then
  lf-sch-stamp@ swap ! lf-sched lf-sch-deps lf-sch-push ;
: lf-sch-below ( d u -- outcome ) over > if lf-sch-dep else drop outcome-ok then ;
: lf-sch-chain ( name u -- outcome )
  >r lf-input-newest outcome-ok begin over 0< 0= over ok? and while
    drop dup r@ lf-sch-below swap lf-input-before swap
  repeat nip r> drop ;
: lf-sch-held ( name u -- outcome )
  swap lf-env-type-name ?dup if swap lf-sch-chain else drop outcome-ok then ;
: lf-sch-slots ( name u -- outcome )
  2dup lf-sch-chain ok-then2? 0= if exit then lf-sch-held ;
: lf-sch-name@ ( k -- name ) lf-sched lf-sch-names lf-sch-cell@ ;
: lf-sch-names-end ( -- k ) lf-sched lf-sch-names slab-count ;
: lf-sch-sets ( u -- outcome )
  outcome-ok lf-sch-names-end 2 pick lf-sch-nfrom@ ?do
    ok-then? 0= if unloop exit then i lf-sch-name@ over lf-sch-slots
  loop nip ;

\ Declaration u's plan: where its set and names begin; a member after
\ its block's first has none (it waits for the first); any other takes
\ its block's names and the checker's own, then their slots.
: lf-sch-starts! ( u -- )
  lf-sched lf-sch-deps slab-count over lf-sched lf-sch-froms slab-at !
  lf-sch-names-end swap lf-sched lf-sch-nfroms slab-at ! ;
: lf-sch-unit ( u -- outcome )
  1 lf-sched lf-sch-stamp +! lf-sched lf-sch-stack lf-sch-empty
  dup lf-sch-members ok-then? 0= if exit then
  lf-sch-builtins-add ok-then? 0= if exit then lf-sch-sets ;
: lf-sch-plan-one ( u -- outcome )
  dup lf-sch-starts! dup lf-env-trailing?
  if lf-sch-trailing swap lf-sch-state! outcome-ok else lf-sch-unit then ;
: lf-sch-plan-all ( -- outcome ) lf-sch-n ['] lf-sch-plan-one ok-each ;
\ The ends: entry n of the starts.
: lf-sch-ends! ( -- ) lf-sch-n lf-sch-starts! ;

\ The dependents of each slot (the sets turned around): counted, summed,
\ then filled with lf-sch-dseen as each slot's cursor; and each
\ declaration's count of slots to wait for.
: lf-sch-rfrom ( d -- addr ) lf-sched lf-sch-rfroms slab-at ;
: lf-sch-dep@ ( k -- d ) lf-sched lf-sch-deps lf-sch-cell@ ;
: lf-sch-count-deps ( -- )
  lf-sched lf-sch-deps slab-count 0 ?do 1 i lf-sch-dep@ 1+ lf-sch-rfrom +! loop ;
: lf-sch-sum ( -- )
  lf-sch-n 0 ?do i lf-sch-rfrom @ i 1+ lf-sch-rfrom +! loop ;
: lf-sch-cursors ( -- ) lf-sch-n 0 ?do i lf-sch-rfrom @ i lf-sch-dseen@ ! loop ;
: lf-sch-place ( u d -- )
  lf-sch-dseen@ dup @ lf-sched lf-sch-rdeps slab-at rot swap ! 1 swap +! ;
: lf-sch-place-set ( u -- )
  dup 1+ lf-sch-from@ over lf-sch-from@ ?do dup i lf-sch-dep@ lf-sch-place loop drop ;
: lf-sch-fill ( -- ) lf-sch-n 0 ?do i lf-sch-place-set loop ;
: lf-sch-waits! ( -- )
  lf-sch-n 0 ?do i 1+ lf-sch-from@ i lf-sch-from@ - i lf-sch-wait ! loop ;
: lf-sch-turn-room ( -- outcome )
  lf-sch-n 1+ lf-sched lf-sch-rfroms lf-sch-hold
  lf-sched lf-sch-deps slab-count lf-sched lf-sch-rdeps lf-sch-hold outcome-and ;
: lf-sch-turn ( -- outcome )
  lf-sch-turn-room dup ok? 0= if exit then drop
  lf-sch-count-deps lf-sch-sum lf-sch-cursors lf-sch-fill lf-sch-waits! outcome-ok ;

\ Room for every array the plan fills: ok, full, or invalid for a slab
\ that is not live (the first that failed).
: lf-sch-also ( outcome n slab -- outcome' ) lf-sch-hold outcome-and ;
: lf-sch-arrays ( -- outcome )
  lf-sch-n 1+ dup lf-sched lf-sch-states lf-sch-hold
  over lf-sched lf-sch-waits lf-sch-also over lf-sched lf-sch-froms lf-sch-also
  over lf-sched lf-sch-nfroms lf-sch-also swap lf-sched lf-sch-dseen lf-sch-also
  lf-term-base lf-term-count @ + lf-sched lf-sch-seen lf-sch-also ;
\ The readiness sets of the current context's input (see the header),
\ once after lf-sched-init: ok, full, or invalid for a node that cannot
\ be read.
: lf-sch-count! ( -- )
  lf-input-count dup lf-sched lf-sch-count ! lf-sched lf-sch-stop-at ! ;
: lf-sched-plan ( -- outcome )
  lf-sch-count! lf-sch-arrays dup ok? 0= if exit then drop lf-sch-builtins-make
  lf-sch-plan-all dup ok? 0= if exit then drop lf-sch-ends! lf-sch-turn ;

\ ---- Workers.
: lf-sch-workers ( -- n ) lf-sched lf-sch-ctxs slab-count ;
: lf-sched-workers ( -- n ) lf-sch-workers ;
: lf-sch-ctx ( k -- addr ) lf-sched lf-sch-ctxs slab-at ;
: lf-sch-job ( k -- addr ) lf-sched lf-sch-jobs slab-at ;
: lf-sch-at ( k -- addr ) lf-sched lf-sch-ats slab-at ;
\ A worker: its context, no job; full (invalid for a list that is not
\ live), the context not taken and nothing added, when one of its three
\ lists cannot grow: room is made in all three before any is pushed
\ (review FRK F1).
: lf-sch-room ( slab -- outcome ) 1 swap slab-room ;
: lf-sch-worker-room ( -- outcome )
  lf-sched lf-sch-ctxs lf-sch-room lf-sched lf-sch-jobs lf-sch-room outcome-and
  lf-sched lf-sch-ats lf-sch-room outcome-and ;
: lf-sched-add ( context -- outcome )
  lf-sch-worker-room dup ok? 0= if nip exit then drop
  lf-sched lf-sch-ctxs lf-sch-push 0 lf-sched lf-sch-jobs lf-sch-push outcome-and
  -1 lf-sched lf-sch-ats lf-sch-push outcome-and ;
: lf-sch-in ( k -- ) lf-sch-ctx @ context-use ;
: lf-sch-home ( -- ) lf-sched lf-sch-home-ctx @ context-use ;
: lf-sch-idle? ( k -- flag ) dup lf-sch-ctx @ 0<> swap lf-sch-job @ 0= and ;
: lf-sch-idle ( -- k|-1 )
  lf-sch-workers 0 ?do i lf-sch-idle? if i unloop exit then loop -1 ;
\ Each worker's job waited for (after a THROW in the driving task), then
\ its context freed.
: lf-sch-free-worker ( k -- )
  dup lf-sch-job @ ?dup if job-wait drop then 0 over lf-sch-job !
  dup lf-sch-ctx @ ?dup if context-free drop then 0 swap lf-sch-ctx ! ;
: lf-sch-free-workers ( -- ) lf-sch-workers 0 ?do i lf-sch-free-worker loop ;
\ Free the workers and every block, then start empty: lf-sched-init,
\ before workers are added and the plan made, gives ok or full.
: lf-sched-free ( -- ) lf-sch-free-workers lf-sch-slabs-free lf-sched /lf-sched erase ;
: lf-sched-init ( -- outcome ) lf-sched-free lf-sch-slabs-init ;

\ ---- Finality, as the publisher left it (read raw: the driving task
\ holds no snapshot), and the frontier below which every slot is final.
: lf-sch-final? ( d -- flag ) lf-env lf-env-slot lf-slot-state @ lf-state-final = ;
: lf-sch-stop! ( d -- ) lf-sched lf-sch-stop-at dup @ rot min swap ! ;
: lf-sch-ready! ( d -- )
  lf-sch-queued over lf-sch-state! lf-sched lf-sch-ready pq-push ok? 0=
  if true lf-sched lf-sch-broken ! then ;
: lf-sch-later! ( d -- )
  lf-sch-later over lf-sch-state! lf-sched lf-sch-laters pq-push ok? 0=
  if true lf-sched lf-sch-broken ! then ;
: lf-sch-front@ ( -- n ) lf-sched lf-sch-frontier @ ;
: lf-sch-advance ( -- )
  begin lf-sch-front@ dup lf-sch-n < if lf-sch-final? else drop false then while
    1 lf-sched lf-sch-frontier +!
  repeat ;
\ Declarations waiting for every slot below them, once that holds.
: lf-sch-due? ( -- flag )
  lf-sched lf-sch-laters dup lf-sch-any? 0= if drop false exit then
  pq-min lf-sch-front@ > 0= ;
: lf-sch-due ( d -- ) dup lf-sch-state@ lf-sch-later = if lf-sch-ready! else drop then ;
: lf-sch-release ( -- )
  lf-sch-advance begin lf-sch-due? while lf-sched lf-sch-laters pq-pop lf-sch-due
  repeat ;

\ A slot seen final: each declaration whose set holds it waits for one
\ slot less, and is ready when none is left.
: lf-sch-rdep@ ( k -- u ) lf-sched lf-sch-rdeps lf-sch-cell@ ;
: lf-sch-one-less ( u -- )
  dup lf-sch-state@ lf-sch-waiting <> if drop exit then
  -1 over lf-sch-wait +! dup lf-sch-wait @ 0= if lf-sch-ready! else drop then ;
: lf-sch-wake ( s -- )
  dup 1+ lf-sch-rfrom@ swap lf-sch-rfrom@ ?do i lf-sch-rdep@ lf-sch-one-less loop ;
: lf-sch-note ( s -- )
  lf-sch-noted over lf-sch-flag? if drop exit then
  dup lf-sch-final? 0= if drop exit then lf-sch-noted over lf-sch-flag! lf-sch-wake ;
\ After d's hand-over: the slots of d and of its block's later members
\ that are final now; a member its first left open is checked alone,
\ once every slot below it is final.
: lf-sch-trail ( m -- )
  dup lf-sch-final? 0= if lf-sch-later! exit then
  lf-sch-done over lf-sch-state! lf-sch-note ;
: lf-sch-members-of ( d -- )
  dup lf-sch-span over + over 1+ ?do
    i lf-sch-state@ lf-sch-trailing = if i lf-sch-trail then
  loop drop ;
: lf-sch-published ( d -- ) dup lf-sch-note lf-sch-members-of lf-sch-release ;

\ ---- Handing out. lf-sch-ready? asks lf-env-ready? for each name of
\ d's set (G-P5): a refusal is a fault of the plan; d then waits for
\ every slot below it. A declaration from the later heap needs no test:
\ the frontier is past it.
: lf-sch-names-ready? ( d -- flag )
  true swap dup 1+ lf-sch-nfrom@ over lf-sch-nfrom@ ?do
    i lf-sch-name@ over lf-env-ready? rot and swap
  loop drop ;
: lf-sch-test? ( d -- flag )
  dup lf-sch-front@ > lf-fault-trusting lf-sch-fault? 0= and
  if lf-sch-names-ready? else drop true then ;
: lf-sch-unready ( d -- ) lf-sched lf-sch-unready# lf-sch-count+ lf-sch-later! ;
\ Begin d's check in worker k's context and submit it; a refused
\ beginning is the serial run's stop at d (kept invalid); a refused job
\ breaks the run.
: lf-sch-keep-call ( outcome d -- ) lf-sched lf-sch-keep @ execute ;
: lf-sch-refused ( d -- )
  outcome-invalid over lf-sch-keep-call dup lf-sch-stop!
  lf-sch-done lf-sch-checked or swap lf-sch-state! ;
: lf-sch-begun? ( d k -- flag )
  lf-sch-in dup lf-env-begin ok? if drop true else lf-sch-refused false then lf-sch-home ;
: lf-sch-submitted ( job d k -- )
  tuck lf-sch-at ! lf-sch-job ! lf-sched lf-sch-running# lf-sch-count+
  lf-sched lf-sch-launched# lf-sch-count+ ;
: lf-sch-submit ( d k -- )
  dup lf-sch-ctx @ lf-sched lf-sch-check @ job-submit
  ?dup if 2drop 2drop 2 lf-sch-break exit then
  -rot over lf-sch-running swap lf-sch-state! lf-sch-submitted ;
\ Before d is handed out, lf-sched-pre! 's word (plan step 6.2.5c4): 0,
\ check it; 1, it published d itself (with its block); 2, ask again once
\ every slot below d is final (at the frontier, check it: review of
\ snap-compat L6); 3, stop the run at d (L4).
: lf-sch-pre-asked ( d -- n ) lf-sched lf-sch-pre @ ?dup if execute else drop 0 then ;
: lf-sch-pre-of ( d -- n )
  dup lf-sch-pre-asked dup 2 = if over lf-sch-front@ > 0= if drop 0 then then nip ;
: lf-sch-pre-published ( d -- ) lf-sch-done over lf-sch-state! lf-sch-published ;
: lf-sch-pre-stop ( d -- ) dup lf-sch-stop! lf-sch-done swap lf-sch-state! ;
: lf-sch-pre-act ( d n -- )
  case 1 of lf-sch-pre-published endof 2 of lf-sch-later! endof swap lf-sch-pre-stop
  endcase ;
: lf-sch-pre-done? ( d -- flag )
  dup lf-sch-pre-of ?dup 0= if drop false exit then lf-sch-pre-act true ;
: lf-sch-launch ( d k -- )
  over lf-sch-test? 0= if drop lf-sch-unready exit then
  over lf-sch-pre-done? if 2drop exit then
  2dup lf-sch-begun? if lf-sch-submit else 2drop then ;

\ ---- Settling worker k's job. A check that began too early is run
\ again later; any other is handed over (G-P6 records a THROW), its
\ scratch rolled back and its facts kept, all in the worker's context,
\ as lf-env-step and cli/check-run.fs's step do in the serial run. A
\ THROW, a failed hand-over or rollback stops the run at d (as the serial
\ run stops), and a spent context is replaced.
: lf-sch-renew ( k -- )
  dup lf-sch-ctx @ context-free drop 0 over lf-sch-ctx !
  lf-sched lf-sch-maker @ catch if drop exit then
  if 2drop exit then swap lf-sch-ctx ! lf-sched lf-sch-renewed# lf-sch-count+ ;
: lf-sch-rerun ( ior k -- renew? )
  lf-sched lf-sch-reruns# lf-sch-count+ lf-sch-at @ lf-sch-later!
  if true else lf-input-rollback ok? 0= then ;
\ Where a check's facts are kept: at its declaration (with the planted
\ fault lf-fault-unordered, at its place among the hand-overs).
: lf-sch-kept-at ( d -- d' )
  lf-sched lf-sch-handed# dup @ swap lf-sch-count+
  lf-fault-unordered lf-sch-fault? if nip else drop then ;
: lf-sch-handed ( outcome fault? d -- renew? )
  >r lf-input-rollback ok? 0= or swap r@ lf-sch-kept-at lf-sch-keep-call
  lf-env-spent? or dup if r@ lf-sch-stop! then
  lf-sch-done lf-sch-checked or r@ lf-sch-state! r> lf-sch-published ;
: lf-sch-hand ( ior k -- renew? )
  lf-sch-at @ tuck lf-env-hand-over-job rot lf-sch-handed ;
: lf-sch-early? ( -- flag ) lf-env-early? lf-fault-careless lf-sch-fault? 0= and ;
: lf-sch-settled ( ior k -- renew? )
  lf-sch-early? if lf-sch-rerun else lf-sch-hand then ;
: lf-sch-settle ( k -- )
  dup lf-sch-job @ job-wait 0 2 pick lf-sch-job ! -1 lf-sched lf-sch-running# +!
  over lf-sch-in over lf-sch-settled lf-sch-home if lf-sch-renew else drop then ;
: lf-sch-wait-one ( -- )
  lf-sched lf-sch-jobs slab-base lf-sch-workers job-wait-any
  dup 0< 0= if lf-sch-settle exit then
  drop 3 lf-sch-break 0 lf-sched lf-sch-running# ! ;

\ ---- The run. Fill every idle worker from the ready heap (dropping
\ declarations beyond a stop), wait for one job, repeat while jobs run.
\ When nothing runs and nothing is ready while a slot below the stop is
\ still open, the declaration that owns it is handed out (a fault of the
\ plan, counted; never in a correct plan).
: lf-sch-takable? ( d -- flag )
  dup lf-sched-stop < swap lf-sch-state@ lf-sch-queued = and ;
: lf-sch-take ( -- d|-1 )
  begin lf-sched lf-sch-ready lf-sch-any? while
    lf-sched lf-sch-ready pq-pop dup lf-sch-takable? if exit then drop
  repeat -1 ;
: lf-sch-fill-workers ( -- )
  begin lf-sched-broken? 0= lf-sch-idle dup 0< 0= rot and while
    lf-sch-take dup 0< if 2drop exit then swap lf-sch-launch
  repeat drop ;
: lf-sch-busy? ( -- flag ) lf-sched lf-sch-running# @ 0> ;
: lf-sched-tick! ( xt -- ) lf-sched lf-sch-tick ! ;
: lf-sched-pre! ( xt -- ) lf-sched lf-sch-pre ! ;
: lf-sched-final ( -- n ) lf-sched-reached lf-sched-stop min ;
: lf-sch-ticked ( -- ) lf-sched lf-sch-tick @ ?dup if execute then ;
: lf-sch-loop ( -- )
  begin lf-sch-fill-workers lf-sch-busy? while lf-sch-wait-one lf-sch-ticked repeat ;
: lf-sch-owner ( d -- u )
  dup lf-input-decl lf-idecl-header ?dup 0= if exit then
  over lf-sch-state@ lf-sch-trailing = if nip lf-hdr-first lf-more-field else drop then ;
: lf-sch-waiting? ( u -- flag )
  lf-sch-state@ dup lf-sch-waiting = swap lf-sch-later = or ;
: lf-sch-stuck ( -- d|-1 )
  lf-sch-front@ dup lf-sched-stop < 0= if drop -1 exit then
  lf-sch-owner dup lf-sch-waiting? 0= if drop -1 then ;
\ After the jobs ran out: more to do when declarations became due (the
\ frontier passed them), or when one is stuck and so is handed out.
: lf-sch-forced ( d -- ) lf-sched lf-sch-forced# lf-sch-count+ lf-sch-ready! ;
\ Declarations at or past the stop, or no longer queued, are dropped from
\ the ready heap first, so that only a takable one counts as more work.
: lf-sch-prune ( -- )
  begin lf-sched lf-sch-ready lf-sch-any? dup if drop
    lf-sched lf-sch-ready pq-min lf-sch-takable? 0= then while
    lf-sched lf-sch-ready pq-pop drop repeat ;
\ Whether some worker still has a context (one lost to a THROW and not
\ replaced has none).
: lf-sch-worker? ( -- flag )
  false lf-sch-workers 0 ?do i lf-sch-ctx @ 0<> or loop ;
\ More work with no worker to do it ends the run, broken, as the serial
\ run's stop at the THROW leaves the rest unchecked.
: lf-sch-more ( more? -- more? )
  dup if lf-sch-worker? 0= if drop 1 lf-sch-break false then then ;
: lf-sch-force ( -- more? )
  lf-sched-broken? if false exit then lf-sch-release lf-sch-prune
  lf-sched lf-sch-ready lf-sch-any? if true lf-sch-more exit then
  lf-sch-stuck dup 0< if drop false exit then lf-sch-forced true lf-sch-more ;
: lf-sch-free? ( d -- flag ) lf-sch-wait @ 0= lf-fault-hasty lf-sch-fault? or ;
: lf-sch-first ( d -- )
  dup lf-sch-state@ lf-sch-waiting = over lf-sch-free? and
  if lf-sch-ready! else drop then ;
: lf-sch-pool-size ( -- )
  lf-sch-workers 1 max task-cores min task-workers <> if lf-sch-workers pool-workers! then ;
\ Start the pool for the run before it begins: 0, or the pool's refusal.
: lf-sched-pool-start ( -- ior ) lf-sch-pool-size pool-start ;
\ Threads only where stores become visible in program order (x86-64,
\ from /proc/sys/kernel/arch; unreadable: not known, so serial).
: lf-sch-arch-read ( -- c-addr u )
  s" /proc/sys/kernel/arch" r/o open-file if drop pad 0 exit then
  >r pad dup 40 r@ read-line 0= and and r> close-file drop ;
lf-sch-arch-read s" x86_64" compare 0= constant lf-sch-x86?
task-host task-threads <> lf-sch-x86? or constant lf-sched-host-ok
\ A slot final before the run, taken from a snapshot (env-import.fs, plan
\ step SN4), is done and wakes the declarations that wait for it.
: lf-sch-taken ( d -- )
  dup lf-sch-final? 0= if drop exit then lf-sch-done over lf-sch-state! lf-sch-note ;
: lf-sch-start ( -- )
  lf-context @ lf-sched lf-sch-home-ctx ! lf-sch-pool-size
  lf-sch-n 0 ?do i lf-sch-taken loop lf-sch-n 0 ?do i lf-sch-first loop ;
\ Run every declaration (see the header); the driving context is current
\ again afterwards and the pool stopped.
: lf-sched-run ( check keep maker -- )
  lf-sched lf-sch-maker ! lf-sched lf-sch-keep ! lf-sched lf-sch-check !
  lf-sch-start begin lf-sch-loop lf-sch-force 0= until
  lf-sch-advance lf-sch-home pool-stop ;
