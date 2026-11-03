\ Tests of the checked environment v0 (ADR 0012; plan task 2.2.2):
\ structural name equality, the input and its marks, environments and
\ their identities, and the rows of ADR 0012's test matrix that need no
\ check-declaration (task 2.2.3), driven by the synthetic check of
\ tests/support/env-cases.fs: row 2 (nothing changes on failure, checked
\ at every step), 3 (names), 4 (universe parameters as far as the
\ environment records and checks them), 5 (handles), 6 (atomicity: fuel at
\ every step, no room, a THROW in the publisher), 7 (axiom sets and
\ provenance), 8 (determinism), the publisher's re-check, corrupted state,
\ and the diagnostics each failure records. Interleaved checks (row 9) are
\ in environment-tasks.fs. Everything runs in the main context, which
\ holds the input (src/core/input.fs).
include ../support/tester.fs
include ../support/checks.fs
require ../support/env-cases.fs

\ ---------------------------------------------------------------------------
\ Structural name equality (src/core/name-equal.fs).
T{ n.A n.A lf-name-equal? n.A n.B lf-name-equal? -> true false }T
T{ n.Nat.add n.Nat.add lf-name-equal? n.Nat n.Nat.add lf-name-equal? -> true false }T
T{ n.Nat.add n.A lf-name-equal? 0 0 lf-name-equal? 0 n.A lf-name-equal? -> false true false }T
T{ n.A 999 lf-name-equal? -1 n.A lf-name-equal? -> false false }T
\ A second entry with the same text, made by hand, equals the first:
\ correctness never assumes that equal names share one ID.
: twin ( -- id )
  0 lf-name-tag-str lf-name-new nip >r
  n.A lf-name-slot lf-entry-payload @ r@ lf-name-slot lf-entry-payload !
  1 r@ lf-name-slot lf-entry-length ! r> ;
twin constant n.A-twin
T{ n.A-twin n.A = n.A-twin n.A lf-name-equal? n.A n.A-twin lf-name-equal? -> false true true }T
T{ n.A-twin n.B lf-name-equal? -> false }T
: num ( prefix n -- id ) lf-name-num 0= abort" num" ;
n.A 3 num constant n.A.3
n.A 4 num constant n.A.4
T{ n.A.3 n.A.3 lf-name-equal? n.A.3 n.A.4 lf-name-equal? n.A.3 n.A lf-name-equal? -> true false false }T
\ A corrupted name store fails closed.
lf-name-count @ constant names-now
names-now 1+ lf-name-count !
T{ n.A n.A lf-name-equal? -> false }T
names-now lf-name-count !
T{ n.A n.A lf-name-equal? -> true }T

\ ---------------------------------------------------------------------------
\ The input. lf-input-add refuses bad records; nothing is added after the
\ input ends; rollback returns scratch to the marks.
lf-input-reset
: try-add ( -- i outcome ) buf lf-input-add ;
: bad-add? ( -- flag ) lf-input-count try-add nip outcome-invalid = swap lf-input-count = and ;
: max-params ( -- ) lf-param-capacity 0 ?do n.u param loop ;
n.A def
T{ 0 buf lf-idecl-name ! bad-add? -> true }T
n.A def 999 buf lf-idecl-name !
T{ bad-add? -> true }T
n.A def 0 buf lf-idecl-kind !
T{ bad-add? -> true }T
n.A def 9 buf lf-idecl-kind !
T{ bad-add? -> true }T
n.A def 3 buf lf-idecl-safety !
T{ bad-add? -> true }T
n.A def 3 buf lf-idecl-hint !
T{ bad-add? -> true }T
n.A def lf-hint-abbrev buf lf-idecl-hint ! 1 buf lf-idecl-height !
T{ bad-add? -> true }T
n.A def lf-hint-regular buf lf-idecl-hint ! -1 buf lf-idecl-height !
T{ bad-add? -> true }T
n.A thm lf-hint-regular buf lf-idecl-hint !
T{ bad-add? -> true }T
n.A def lf-param-capacity 1+ buf lf-idecl-arity !
T{ bad-add? -> true }T
n.A def 0 param
T{ bad-add? -> true }T
n.A def 999 param
T{ bad-add? -> true }T
n.A def 999 buf lf-idecl-type !
T{ bad-add? -> true }T
n.A def -2 buf lf-idecl-value !
T{ bad-add? -> true }T
n.A def lf-hint-regular buf lf-idecl-hint ! 7 buf lf-idecl-height !
T{ try-add -> 0 outcome-ok }T
n.A def max-params
T{ try-add -> 1 outcome-ok }T
T{ lf-input-intact? lf-input-count -> false 2 }T
T{ 0 lf-input-read nip lf-input-rollback -> outcome-invalid outcome-invalid }T
T{ ' lf-input-end rs-checked lf-input-intact? -> outcome-ok true }T
T{ lf-input-end -> outcome-invalid }T
n.B def
T{ try-add lf-input-count -> -1 outcome-invalid 2 }T
T{ 1 lf-input-read nip 2 lf-input-read nip -1 lf-input-read nip -> outcome-ok outcome-invalid outcome-invalid }T
\ Scratch above the marks is rolled back, name bytes included; identities
\ go on.
lf-term-count @ constant terms-then
lf-name-used @ constant bytes-then
0 lf-term-sort 2drop 0 s" scratch" lf-name-str 2drop
T{ lf-term-count @ terms-then 1+ = lf-name-used @ bytes-then > -> true true }T
T{ ' lf-input-rollback rs-checked lf-term-count @ lf-name-used @ -> outcome-ok terms-then bytes-then }T
T{ lf-input-intact? -> true }T
\ The name bytes are part of the input: with fewer in use than when
\ loading ended, it is not intact.
lf-name-used @ 1- lf-name-used !
T{ lf-input-intact? lf-input-rollback -> false outcome-invalid }T
lf-name-used @ 1+ lf-name-used !
T{ lf-input-intact? -> true }T
\ The fingerprint covers every input store (records, identities, count and
\ generation below its mark) and the name bytes: changing any of them
\ changes it. A guard against mistakes, not forgery (ADR 0012, amended).
: flip ( addr -- ) dup @ invert swap ! ;
: flip-byte ( addr -- ) dup c@ 1 xor swap c! ;
\ Whether flipping and restoring addr with xt ( addr -- ) changes the print.
: sees? ( addr xt -- flag )
  lf-input-print >r 2dup execute lf-input-print r> <> >r execute r> ;
: generation ( k -- addr ) lf-input-store store-generation ;
: last-record ( k -- addr ) lf-input-marked swap 1- swap store-slot ;
: last-identity ( k -- addr ) lf-input-marked swap 1- swap store-identity ;
T{ 0 generation ' flip sees? 1 generation ' flip sees? 2 generation ' flip sees? -> true true true }T
T{ 3 generation ' flip sees? 4 generation ' flip sees? -> true true }T
T{ 0 last-record ' flip sees? 2 last-record ' flip sees? 4 last-record ' flip sees? -> true true true }T
T{ 0 last-identity ' flip sees? 4 last-identity ' flip sees? -> true true }T
T{ lf-name-bytes ' flip-byte sees? lf-input-print lf-input-fingerprint = -> true true }T
\ Loading cannot end with the name bytes out of range.
lf-input-reset n.A def add
lf-name-used @ constant used-now
lf-name-byte-capacity 1+ lf-name-used !
T{ lf-input-end lf-input-sealed? -> outcome-invalid false }T
used-now lf-name-used !
T{ lf-input-end lf-input-intact? -> outcome-ok true }T
\ A rollback below an input mark breaks the input: it is no longer intact
\ and nothing can be rolled back; restoring the count mends it.
lf-term-count @ 1- lf-term-count !
T{ lf-input-intact? lf-input-rollback -> false outcome-invalid }T
lf-term-count @ 1+ lf-term-count !
T{ lf-input-intact? -> true }T
\ The input store holds lf-input-capacity declarations.
lf-input-reset
T{ lf-input-intact? -> false }T
: fill-input ( -- n ) 0 begin n.A def try-add nip ok? while 1+ repeat ;
T{ fill-input lf-input-count -> lf-input-capacity lf-input-capacity }T
T{ try-add -> -1 outcome-full }T

\ ---------------------------------------------------------------------------
\ Environments: made only over an intact input; identities grow; free and
\ use refuse what is not a live environment.
lf-input-reset
T{ 8 lf-env-new -> 0 outcome-invalid }T
main-input
T{ -1 lf-env-new 1 lf-env-pool-max + lf-env-new -> 0 outcome-invalid 0 outcome-invalid }T
lf-env-serial @ constant serial-before
T{ 8 ' lf-env-new rs-checked swap constant env-a -> outcome-ok }T
lf-env-serial @ constant id-a
T{ id-a serial-before 1+ = env-a lf-envh-identity @ id-a = -> true true }T
T{ env-a lf-env-length env-a lf-envh-allowed @ env-a lf-envh-mode @ -> main-count 0 lf-mode-final }T
create not-env 64 cells allot  not-env 64 cells erase
T{ 0 lf-env-use not-env lf-env-use not-env lf-env-free 0 lf-env-free -> outcome-invalid outcome-invalid outcome-invalid outcome-invalid }T
T{ env-a ' lf-env-use rs-checked lf-env env-a = -> outcome-ok true }T
T{ 0 lf-env-outcome 0 lf-env-handle -> outcome-invalid 0 -1 outcome-invalid }T

\ ---------------------------------------------------------------------------
\ Rows 2 and 3: the main input, checked step by step. Every outcome is
\ reached, every step changes only its own slot and never the input, a
\ failure appends nothing, and the verdicts follow N1, N2 and K5.
T{ ' syn-check main-count checked-run step-failures @ -> 0 }T
T{ main-count verdicts-match? -> true }T
\ Dependencies, ascending and distinct, and the pool holds them in order.
: deps ( d -- first count ) slot@ dup lf-slot-deps @ swap lf-slot-count @ ;
: dep ( k -- d ) pool store-slot @ ;
T{ 1 deps 8 deps 23 deps 26 deps -> 0 1 1 2 3 3 6 1 }T
T{ 0 dep 1 dep 2 dep 3 dep 4 dep 5 dep 6 dep -> 0 0 1 1 11 21 24 }T
T{ pool-count 0 deps -> 7 0 0 }T
\ An accepted record is the input declaration, copied whole; a failed one
\ holds only its state and outcome.
: same-decl? ( d -- flag ) dup slot@ lf-slot-decl swap lf-input-decl /lf-idecl tuck compare 0= ;
T{ 0 same-decl? 11 same-decl? 23 same-decl? -> true true true }T
T{ 2 slot@ lf-slot-decl lf-idecl-name @ 3 slot@ lf-slot-count @ -> 0 0 }T
\ Nothing is ever reported as accepted that was not: handles exist only
\ for accepted slots.
: accepted-handles? ( -- flag )
  true main-count 0 ?do i lf-env-handle nip nip ok? i expected@ ok? = and loop ;
T{ accepted-handles? -> true }T
\ Lookups in a view of the whole environment.
T{ lf-env-view -> outcome-ok }T
T{ n.A lf-env-lookup n.B lf-env-lookup n.C lf-env-lookup -> 0 outcome-ok 1 outcome-ok 8 outcome-ok }T
T{ n.D lf-env-lookup n.F lf-env-lookup n.Z lf-env-lookup -> -1 outcome-unknown -1 outcome-unsupported -1 outcome-rejected }T
T{ n.X lf-env-lookup n.Nat lf-env-lookup n.A-twin lf-env-lookup -> 24 outcome-ok -1 outcome-rejected 0 outcome-ok }T
T{ 999 lf-env-lookup 0 lf-env-lookup -> -1 outcome-invalid -1 outcome-rejected }T
T{ n.A 27 lf-env-ready? n.A -1 lf-env-ready? n.A 28 lf-env-ready? 999 5 lf-env-ready? -> true false false false }T
\ A view is not a check: no N2, parameters or publication.
T{ lf-env-own-name n.u lf-env-param? lf-env-own-params -> outcome-invalid outcome-invalid outcome-invalid }T
T{ lf-env-hand-over -> outcome-invalid true }T
\ Without any snapshot, nothing is published and the hand-over is a fault,
\ whichever slots are final.
lf-env-clear
T{ 0 slot@ lf-slot-final? lf-env-hand-over -> true outcome-invalid true }T
T{ 5 true ?keep 5 false ?keep -> 5 true false }T

\ ---------------------------------------------------------------------------
\ Row 4: universe parameters, as far as the environment records and checks
\ them. Slot 0 is A.{u}, 11 is J.{u v}, 23 is T.{v u}, 1 has none.
lf-env-view drop
: param@ ( params k -- name ) cells + @ ;
: two-params ( d -- n first second outcome )
  lf-env-params >r over 0 param@ rot 1 param@ r> ;
T{ 0 lf-env-params rot @ -rot -> n.u 1 outcome-ok }T
T{ 11 two-params -> 2 n.u n.v outcome-ok }T
T{ 23 two-params -> 2 n.v n.u outcome-ok }T
T{ 1 lf-env-params -> 1 slot@ lf-slot-decl lf-idecl-params 0 outcome-ok }T
\ L1: zero, exact, too few and too many levels.
T{ 0 0 lf-env-arity? 1 0 lf-env-arity? 2 0 lf-env-arity? -> outcome-rejected outcome-ok outcome-rejected }T
T{ 1 11 lf-env-arity? 2 11 lf-env-arity? 3 11 lf-env-arity? -> outcome-rejected outcome-ok outcome-rejected }T
T{ 0 1 lf-env-arity? 1 1 lf-env-arity? -> outcome-ok outcome-rejected }T
\ Parameters of a declaration that was not accepted are not readable.
T{ 2 lf-env-params 1 2 lf-env-arity? 99 lf-env-params -> 0 0 outcome-invalid outcome-invalid 0 0 outcome-invalid }T

\ ---------------------------------------------------------------------------
\ Row 5: handles. Environment B checks the same input; slot 23 is
\ checked there with its snapshot open.
T{ 0 lf-env-handle 23 lf-env-handle 2 lf-env-handle -> id-a 0 outcome-ok id-a 23 outcome-ok 0 -1 outcome-invalid }T
8 fresh-env
lf-env constant env-b
lf-env-serial @ constant id-b
T{ id-b id-a > -> true }T
' syn-check 23 checked-run
T{ step-failures @ 23 lf-env-begin -> 0 outcome-ok }T
\ Old handles stay valid in later snapshots.
T{ id-b 0 lf-env-handle? id-b 1 lf-env-handle? id-b 21 lf-env-handle? -> outcome-ok outcome-ok outcome-ok }T
\ From another environment, from the future (d = i and d > i), to a
\ rejected or undecided declaration, forged numbers.
T{ id-a 0 lf-env-handle? id-b 23 lf-env-handle? id-b 24 lf-env-handle? -> outcome-invalid outcome-invalid outcome-invalid }T
T{ id-b 2 lf-env-handle? id-b 3 lf-env-handle? id-b 16 lf-env-handle? -> outcome-invalid outcome-invalid outcome-invalid }T
T{ id-b -1 lf-env-handle? id-b 999 lf-env-handle? 0 0 lf-env-handle? -> outcome-invalid outcome-invalid outcome-invalid }T
T{ id-b 1+ 0 lf-env-handle? max-n 0 lf-env-handle? -> outcome-invalid outcome-invalid }T
\ The open check of 23: its lookups see only slots below it.
T{ lf-env-own-name n.Y lf-env-lookup n.X lf-env-lookup -> outcome-ok -1 outcome-rejected -1 outcome-rejected }T
T{ n.u lf-env-param? n.v lf-env-param? n.w lf-env-param? -> outcome-ok outcome-ok outcome-rejected }T
T{ lf-env-own-params 999 lf-env-param? -> outcome-ok outcome-invalid }T
\ Depending: only accepted slots below 23, each once, kept ascending.
T{ 21 lf-env-depend 1 lf-env-depend 11 lf-env-depend 1 lf-env-depend -> outcome-ok outcome-ok outcome-ok outcome-ok }T
T{ lf-cand-count@ 0 lf-cand-dep @ 1 lf-cand-dep @ 2 lf-cand-dep @ -> 3 1 11 21 }T
T{ 2 lf-env-depend 23 lf-env-depend 24 lf-env-depend -1 lf-env-depend -> outcome-invalid outcome-invalid outcome-invalid outcome-invalid }T
T{ lf-cand-count@ -> 3 }T
\ The check finishes and is published; slot 23 is final with its record.
outcome-ok lf-env-finish
T{ lf-env-hand-over lf-input-rollback -> outcome-ok false outcome-ok }T
T{ 23 deps nip 23 same-decl? -> 3 true }T
\ The publisher's pool mark is in the environment's header.
T{ lf-env lf-envh-pub-mark mark-store @ pool = -> true }T
\ Publishing twice, beginning a final slot: refused, nothing changes.
env-digest constant digest-b
T{ lf-env-hand-over 23 lf-env-begin lf-env-hand-over env-digest digest-b = -> outcome-invalid true outcome-invalid outcome-invalid true true }T
\ A freed environment: its handles fail in a new one made at once, and
\ its snapshot is gone.
T{ 24 lf-env-begin lf-env lf-env-free lf-env -> outcome-ok outcome-ok 0 }T
T{ id-b 0 lf-env-handle? lf-env-own-name lf-env-hand-over -> outcome-invalid outcome-invalid outcome-invalid true }T
8 fresh-env
lf-env-serial @ constant id-c
' syn-check 5 checked-run
T{ 5 lf-env-begin id-b 0 lf-env-handle? id-c 0 lf-env-handle? -> outcome-ok outcome-invalid outcome-ok }T
env-free
T{ env-a lf-env-free -> outcome-ok }T
\ A check started before a slot it needs is final ends invalid, and reads
\ nothing of that slot.
8 fresh-env
lf-env-serial @ constant id-e
' syn-check 1 checked-run
T{ 8 lf-env-begin id-e 0 lf-env-handle? id-e 1 lf-env-handle? 1 lf-env-depend -> outcome-ok outcome-ok outcome-invalid outcome-invalid }T
T{ n.B lf-env-lookup lf-env-own-name 1 lf-env-params -> -1 outcome-invalid outcome-invalid 0 0 outcome-invalid }T
T{ ' syn-check 8 checked-step ' syn-check 4 checked-step -> outcome-invalid outcome-invalid }T
env-free
\ A check whose later slots are already final, as a parallel run may
\ leave them: it reads none of them, by handle, dependency or name.
: all-but-8 ( -- ) main-count 0 ?do i 8 <> if ['] syn-check i checked-step drop then loop ;
8 fresh-env
lf-env-serial @ constant id-d
all-but-8
T{ 8 lf-env-begin id-d 11 lf-env-handle? id-d 21 lf-env-handle? id-d 1 lf-env-handle? -> outcome-ok outcome-invalid outcome-invalid outcome-ok }T
T{ n.J lf-env-lookup 11 lf-env-depend 11 lf-env-params -> -1 outcome-rejected outcome-invalid 0 0 outcome-invalid }T
T{ 2 11 lf-env-arity? n.X lf-env-lookup -> outcome-invalid -1 outcome-rejected }T
\ ... nor by its results (G-P4), which it reads below it as any view.
T{ 11 lf-env-outcome 21 lf-env-axioms 11 lf-env-handle nip nip -> outcome-invalid 0 outcome-invalid outcome-invalid }T
T{ 1 lf-env-outcome 1 lf-env-axioms 1 lf-env-handle nip nip -> outcome-ok 0 outcome-ok outcome-ok }T
T{ ' syn-check 8 checked-step main-count verdicts-match? -> outcome-ok true }T
env-free

\ ---------------------------------------------------------------------------
\ Row 6: atomicity. Fuel: declaration 23 needs 5 units (audit, own name,
\ three uses); with less it is exhausted at every step and publishes
\ nothing, with 5 it is accepted.
: fuel-trial ( n -- outcome )
  23 fuel 8 fresh-env ['] syn-check main-count checked-run 23 lf-env-outcome env-free ;
: fuel-trials ( -- flag ) true 5 0 ?do i fuel-trial outcome-exhausted = and loop ;
T{ fuel-trials step-failures @ -> true 0 }T
T{ 5 fuel-trial step-failures @ -> outcome-ok 0 }T
1000 23 fuel
\ No room in the pool: with room for one dependency, 1 is accepted and the
\ others that use any are full; with none, 1 is full and its users are
\ unknown (K5).
1 fresh-env
T{ ' syn-check main-count checked-run step-failures @ lf-env-view -> 0 outcome-ok }T
T{ 1 lf-env-outcome 8 lf-env-outcome 23 lf-env-outcome 26 lf-env-outcome -> outcome-ok outcome-full outcome-full outcome-full }T
T{ pool-count -> 1 }T
env-free
0 fresh-env
T{ ' syn-check main-count checked-run step-failures @ -> 0 }T
T{ 0 lf-env-outcome 1 lf-env-outcome 8 lf-env-outcome 21 lf-env-outcome -> outcome-ok outcome-full outcome-unknown outcome-ok }T
T{ pool-count -> 0 }T
env-free
\ A THROW in the publisher before the final mark: the step is a fault, the
\ slot is not final and cleared, the pool rolled back, nothing else
\ changed, the input unchanged.
variable throw-at
: throw-hook ( -- ) lf-env-limit throw-at @ = if -77 throw then ;
: cleared? ( d -- flag ) slot@ /lf-slot 1 cells / cells-zero? ;
: throw-step ( d -- flag )
  ['] syn-check over lf-env-step true = swap outcome-invalid = and swap cleared? and ;
: unchanged? ( -- flag )
  changed 0= pool-digest pool-before @ = and input-digest input-before @ = and ;
: throw-trial ( d -- flag )
  dup throw-at ! 8 fresh-env ['] syn-check over checked-run snap
  throw-step unchanged? and env-free ;
' throw-hook is lf-env-before-final
T{ 8 throw-trial 23 throw-trial 2 throw-trial 0 throw-trial -> true true true true }T
\ The serial run stops there, the context not spent: the check did not
\ throw.
8 throw-at ! 8 fresh-env
T{ ' syn-check ' main-maker lf-env-run lf-env-view lf-env-spent? -> outcome-invalid outcome-ok false }T
T{ 7 lf-env-outcome 8 lf-env-outcome 9 lf-env-outcome -> outcome-rejected outcome-invalid outcome-invalid }T
' lf-env-no-fault is lf-env-before-final
\ The slot can be published once the fault is gone.
T{ ' syn-check 8 lf-env-step lf-env-view 8 lf-env-outcome -> outcome-ok false outcome-ok outcome-ok }T
env-free
\ A pool that cannot be marked is a fault, with nothing written
\ (white-box: lf-env-hand-over finds the pool sound before it marks it).
8 fresh-env
' syn-check 1 checked-run
1 lf-env-begin drop syn-check
pool-count constant pool-then
pool store-capacity @ 1+ pool store-count !
T{ 1 slot@ lf-env-guarded 1 slot@ lf-slot-final? -> outcome-invalid true false }T
pool-then pool store-count !
T{ lf-env-hand-over 1 slot@ lf-slot-final? lf-input-rollback -> outcome-ok false true outcome-ok }T
env-free
\ A pool shape store-init refuses: the memory is freed, nothing is made.
T{ main-count 0 lf-env-bytes allocate throw -1 swap lf-env-made -> 0 outcome-invalid }T
\ Inside a job (lf-owner set, as job-run sets it) nothing makes, chooses,
\ frees or publishes an environment (G-P1); environment-tasks.fs does the
\ same in real jobs.
8 fresh-env
0 lf-env-begin drop syn-check
1 lf-owner !
T{ 8 lf-env-new lf-env lf-env-use lf-env lf-env-free -> 0 outcome-invalid outcome-invalid outcome-invalid }T
T{ lf-env-hand-over ' syn-check 1 lf-env-step -> outcome-invalid true outcome-invalid true }T
T{ ' syn-check ' main-maker lf-env-run -> outcome-invalid }T
0 lf-owner !
T{ 0 slot@ lf-slot-final? lf-env-hand-over 0 slot@ lf-slot-final? -> false outcome-ok false true }T
T{ lf-input-rollback -> outcome-ok }T
env-free

\ A THROW inside a check (G-P6): the declaration is invalid and the
\ context spent, and lf-env-run goes on in a new context from its maker,
\ which it frees at the end; the spent context refuses to begin another
\ check. Each run starts in a spare context holding the main input, so
\ that the main context stays usable for the tests below.
: throwing-check ( -- ) me 1 = if -78 throw then syn-check ;
create check-contexts decls cells allot
variable makes
: counting-maker ( -- context ior ) 1 makes +! main-maker ;
: noting-check ( -- ) lf-context @ me cells check-contexts + ! throwing-check ;
: checked-in ( i -- context ) cells check-contexts + @ ;
: spare ( -- context ) main-maker throw dup context-use ;
: unspare ( context -- ) context-main context-use context-free throw ;
spare constant spare-1
8 fresh-env 0 makes !
T{ ' noting-check ' counting-maker lf-env-run makes @ lf-context @ spare-1 = -> outcome-ok 1 true }T
T{ 0 checked-in spare-1 = 1 checked-in spare-1 = 2 checked-in spare-1 <> -> true true true }T
T{ 26 checked-in 2 checked-in = 2 checked-in context-main <> -> true true }T
lf-env-view drop
T{ 1 lf-env-outcome 8 lf-env-outcome 23 lf-env-outcome 26 lf-env-outcome -> outcome-invalid outcome-unknown outcome-unknown outcome-ok }T
env-free 8 fresh-env
T{ lf-env-spent? 0 lf-env-begin lf-diag@ nip -> true outcome-invalid 0 0 lf-diag-publisher-fault }T
spare-1 unspare env-free 8 fresh-env
T{ lf-env-spent? 0 lf-env-begin -> false outcome-ok }T
env-free
\ The step records the THROW and spends the context.
spare constant spare-2
8 fresh-env
' syn-check 1 checked-run
T{ ' throwing-check 1 lf-env-step lf-diag@ nip lf-env-spent? -> outcome-invalid false 1 -78 lf-diag-publisher-fault true }T
env-free spare-2 unspare
\ A maker that fails, throws or gives the current context stops the run
\ after the THROW, with slot 1 invalid and slot 2 not final; the run's
\ caller is current again.
: no-maker ( -- context ior ) 0 -1 ;
: throwing-maker ( -- context ior ) -80 throw ;
: same-maker ( -- context ior ) lf-context @ 0 ;
: maker-trial ( maker -- outcome slot1 final2? back? )
  spare >r 8 fresh-env ['] throwing-check swap lf-env-run lf-env-view drop
  1 lf-env-outcome 2 slot@ lf-slot-final? lf-context @ r@ = env-free r> unspare ;
T{ ' no-maker maker-trial -> outcome-invalid outcome-invalid false true }T
T{ ' throwing-maker maker-trial -> outcome-invalid outcome-invalid false true }T
T{ ' same-maker maker-trial -> outcome-invalid outcome-invalid false true }T
\ A check that never finishes is invalid.
: silent-check ( -- ) ;
8 fresh-env
T{ ' silent-check main-count checked-run step-failures @ -> 0 }T
T{ 0 lf-env-outcome 1 lf-env-outcome -> outcome-invalid outcome-invalid }T
env-free
\ The candidate's own limit: lf-env-dep-capacity dependencies; one more
\ is full. Input: 16 definitions, one using four, then one more.
: wide-input-1 ( -- )
  n.A def add n.B def add n.C def add n.D def add n.E def add n.F def add
  n.G def add n.H def add n.I def add n.J def add n.K def add n.L def add ;
: wide-input ( -- )
  lf-input-reset wide-input-1 n.M def add n.N def add n.P def add n.Q def add
  n.R def n.A uses n.B uses n.C uses n.D uses add n.S def add ends ;
wide-input
8 fresh-env
' syn-check 17 checked-run
: depend-all ( n -- outcome ) outcome-ok swap 0 ?do drop i lf-env-depend loop ;
T{ 17 lf-env-begin lf-env-dep-capacity depend-all lf-cand-count@ -> outcome-ok outcome-ok lf-env-dep-capacity }T
T{ 16 lf-env-depend lf-cand-count@ 3 lf-env-depend -> outcome-full lf-env-dep-capacity outcome-ok }T
\ Sixteen dependencies need room for sixteen in the pool: four are left.
outcome-ok lf-env-finish
T{ lf-env-hand-over lf-env-view 17 lf-env-outcome pool-count -> outcome-full false outcome-ok outcome-full 4 }T
env-free

\ ---------------------------------------------------------------------------
\ Row 7: axiom sets and provenance. Every accepted record of the main
\ input has the empty set, computed: "axioms: none".
main-input
8 fresh-env
' syn-check main-count checked-run
: axioms-none? ( -- flag )
  true main-count 0 ?do i expected@ ok? if i lf-env-axioms outcome-ok = swap 0= and and then loop ;
lf-env-view drop
T{ axioms-none? 2 lf-env-axioms 3 lf-env-axioms -> true 0 outcome-invalid 0 outcome-invalid }T
env-free
\ With a test-only allowlist bit on a synthetic record, the union reaches
\ every user, directly or not; without it in the allowlist, a user is a
\ fault (invalid) and its own users unknown.
: rest ( -- ) main-count 1 ?do ['] syn-check i checked-step drop loop lf-env-view drop ;
: axiom-trial ( allowed -- )
  8 fresh-env lf-env lf-envh-allowed ! ['] syn-check 1 checked-run 1 0 slot@ lf-slot-axioms ! rest ;
1 axiom-trial
T{ 1 lf-env-axioms 8 lf-env-axioms 23 lf-env-axioms 26 lf-env-axioms -> 1 outcome-ok 1 outcome-ok 1 outcome-ok 0 outcome-ok }T
T{ 0 lf-env-axioms 11 lf-env-axioms -> 1 outcome-ok 0 outcome-ok }T
env-free
0 axiom-trial
T{ 1 lf-env-outcome 8 lf-env-outcome 23 lf-env-outcome 11 lf-env-outcome 26 lf-env-outcome -> outcome-invalid outcome-unknown outcome-unknown outcome-ok outcome-ok }T
env-free
\ A check that drops a dependency's bit is caught by the publisher.
: lossy-check ( -- ) syn-check 0 lf-env-cand lf-cand-axioms ! ;
8 fresh-env 1 lf-env lf-envh-allowed !
' syn-check 1 checked-run
1 0 slot@ lf-slot-axioms !
T{ ' lossy-check 1 checked-step ' lossy-check 2 checked-step -> outcome-invalid outcome-rejected }T
env-free
\ Provenance: a record marked "not re-checked" labels its users in a
\ development run, and is a fault in a final run.
: provenance-trial ( mode -- )
  8 fresh-env lf-env lf-envh-mode ! ['] syn-check 1 checked-run
  lf-provenance-saved 0 slot@ lf-slot-provenance ! rest ;
: provenance ( d -- p ) slot@ lf-slot-provenance @ ;
lf-mode-development provenance-trial
T{ 1 lf-env-outcome 1 provenance 23 provenance 11 provenance -> outcome-ok 1 1 0 }T
env-free
lf-mode-final provenance-trial
T{ 1 lf-env-outcome 11 lf-env-outcome 11 provenance -> outcome-invalid outcome-ok 0 }T
env-free
T{ step-failures @ -> 0 }T

\ ---------------------------------------------------------------------------
\ The publisher's re-check catches checks that claim ok wrongly.
: run-from ( to from -- ) ?do ['] syn-check i checked-step drop loop ;
8 fresh-env
3 0 run-from
\ An unknown outcome is never published as ok.
3 lf-env-begin drop outcome-unknown lf-env-finish
T{ lf-env-hand-over lf-env-view 3 lf-env-outcome 3 lf-env-handle -> outcome-unknown false outcome-ok outcome-unknown 0 -1 outcome-invalid }T
\ A duplicate of an accepted name claimed ok (N2 skipped).
7 4 run-from
7 lf-env-begin drop outcome-ok lf-env-finish
T{ lf-recheck lf-env-hand-over lf-env-view 7 lf-env-outcome -> 4 true outcome-invalid false outcome-ok outcome-invalid }T
\ A dependency that is not accepted, or out of order, or a corrupted count.
8 lf-env-begin drop 1 lf-env-depend drop 3 lf-env-cand lf-cand-deps ! outcome-ok lf-env-finish
T{ lf-env-hand-over -> outcome-invalid false }T
9 lf-env-begin drop 0 lf-env-depend drop 1 lf-env-depend drop
1 lf-env-cand lf-cand-deps ! 0 lf-env-cand lf-cand-deps cell+ ! outcome-ok lf-env-finish
T{ lf-env-hand-over -> outcome-invalid false }T
10 lf-env-begin drop lf-env-dep-capacity 1+ lf-env-cand lf-cand-count ! outcome-ok lf-env-finish
T{ 0 lf-env-depend lf-env-hand-over -> outcome-invalid outcome-invalid false }T
\ An axiom set that differs from the union of the dependencies'.
11 lf-env-begin drop 1 lf-env-cand lf-cand-axioms ! outcome-ok lf-env-finish
T{ lf-recheck lf-env-hand-over -> 2 true outcome-invalid false }T
\ An ok claim after an undecided or an unsupported earlier declaration of
\ its name: lf-env-own-name says unknown or unsupported (K5), and the
\ publisher refuses it; the name keeps resolving to nothing accepted.
12 lf-env-begin drop outcome-ok lf-env-finish
T{ lf-env-hand-over lf-diag@ nip -> outcome-invalid false 12 4 lf-diag-recheck }T
20 13 run-from
20 lf-env-begin drop outcome-ok lf-env-finish
T{ lf-env-hand-over lf-diag@ nip -> outcome-invalid false 20 4 lf-diag-recheck }T
lf-env-view drop
T{ 12 lf-env-outcome 12 lf-env-handle nip nip n.D lf-env-lookup -> outcome-invalid outcome-invalid -1 outcome-unknown }T
\ F: slot 5 unsupported, slot 20 invalid (undecided): unknown first.
T{ 20 lf-env-outcome n.F lf-env-lookup -> outcome-invalid -1 outcome-unknown }T
T{ lf-input-rollback -> outcome-ok }T
env-free
\ A check that begins another declaration is a fault: its candidate is
\ not published, the run stops, and both slots can still be checked.
8 fresh-env
' syn-check 1 checked-run
: hijack ( -- ) 1 lf-env-begin drop syn-check ;
T{ ' hijack 2 lf-env-step lf-diag@ nip -> outcome-invalid true 2 6 lf-diag-recheck }T
T{ 1 slot@ lf-slot-final? 2 slot@ lf-slot-final? scratch-gone? -> false false true }T
T{ ' syn-check 1 lf-env-step ' syn-check 2 lf-env-step -> outcome-ok false outcome-rejected false }T
env-free
\ L3 and scope: a repeated parameter, an axiom and an unsafe definition
\ claimed ok are faults; the check sees the first with lf-env-own-params.
lf-input-reset
n.A def n.u param n.u param add
n.B lf-kind-axiom decl no-value add
n.C def lf-safety-unsafe buf lf-idecl-safety ! add
n.D def add
ends
8 fresh-env
0 lf-env-begin drop
T{ lf-env-own-params n.u lf-env-param? -> outcome-rejected outcome-ok }T
outcome-ok lf-env-finish
T{ lf-env-hand-over -> outcome-invalid false }T
1 lf-env-begin drop outcome-ok lf-env-finish
T{ lf-env-hand-over -> outcome-invalid false }T
2 lf-env-begin drop outcome-ok lf-env-finish
T{ lf-env-hand-over -> outcome-invalid false }T
\ The candidate's outcome is sanitised: a value outside the vocabulary is
\ invalid.
3 lf-env-begin drop 99 lf-env-cand lf-cand-outcome !
T{ lf-env-hand-over lf-env-view 3 lf-env-outcome -> outcome-invalid false outcome-ok outcome-invalid }T
env-free

\ ---------------------------------------------------------------------------
\ Corruption fails closed: a slot state that is not final, two accepted
\ slots of one name, a damaged environment header or pool, a changed input.
main-input
8 fresh-env
' syn-check main-count checked-run
lf-env-view drop
T{ 1 slot@ lf-slot-state @ -> lf-state-final }T
2 1 slot@ lf-slot-state !
T{ n.B lf-env-lookup 1 lf-env-outcome 1 lf-env-handle nip nip -> -1 outcome-invalid outcome-invalid outcome-invalid }T
lf-state-final 1 slot@ lf-slot-state !
T{ n.B lf-env-lookup -> 1 outcome-ok }T
outcome-ok 7 slot@ lf-slot-outcome !
T{ n.A lf-env-lookup -> -1 outcome-invalid }T
outcome-rejected 7 slot@ lf-slot-outcome !
99 lf-env lf-envh-length !
T{ n.A lf-env-lookup 0 lf-env-outcome -> -1 outcome-invalid outcome-invalid }T
main-count lf-env lf-envh-length !
pool-count constant pool-now
pool store-capacity @ 1+ pool store-count !
T{ 0 lf-env-outcome n.A lf-env-lookup -> outcome-invalid -1 outcome-invalid }T
pool-now pool store-count !
T{ 0 lf-env-outcome n.A lf-env-lookup -> outcome-ok 0 outcome-ok }T
lf-term-count @ 1- lf-term-count !
T{ 0 lf-env-outcome n.A lf-env-lookup -> outcome-invalid -1 outcome-invalid }T
lf-term-count @ 1+ lf-term-count !
T{ 0 lf-env-outcome -> outcome-ok }T
\ A new input: the old environment is bound to the old one.
main-input
T{ 0 lf-env-outcome n.A lf-env-lookup lf-env-view -> outcome-invalid -1 outcome-invalid outcome-invalid }T
env-free

\ ---------------------------------------------------------------------------
\ Diagnostics (docs/programming/DIAGNOSTICS.md): each failure records its
\ code and numbers in the context's record; the first one wins, and
\ lf-env-begin clears it. The verdicts above are the same with recording.
: diag ( -- n1 n2 code ) lf-diag@ nip ;
8 fresh-env
' syn-check 7 checked-run
\ A step's diagnostic explains its declaration.
T{ ' syn-check 7 lf-env-step drop diag -> outcome-rejected n.A 0 lf-diag-already-declared }T
T{ ' syn-check 8 lf-env-step drop diag -> outcome-ok 0 0 lf-diag-none }T
T{ ' syn-check 9 lf-env-step drop diag -> outcome-rejected n.H 9 lf-diag-unknown-constant }T
T{ ' syn-check 14 lf-env-step drop diag -> outcome-invalid 13 14 lf-diag-too-early }T
: finish-run ( -- )
  main-count 0 ?do i slot@ lf-slot-final? 0= if ['] syn-check i checked-step drop then loop ;
finish-run
lf-env-view drop
lf-diag-clear
T{ n.D lf-env-lookup diag -> -1 outcome-unknown 3 outcome-unknown lf-diag-dependency-undecided }T
lf-diag-clear
T{ n.F lf-env-lookup diag -> -1 outcome-unsupported 5 0 lf-diag-dependency-unsupported }T
lf-diag-clear
T{ 999 lf-env-lookup diag -> -1 outcome-invalid 999 0 lf-diag-bad-argument }T
lf-diag-clear
T{ 0 0 lf-env-arity? diag -> outcome-rejected 0 1 lf-diag-level-count }T
lf-diag-clear
T{ 12345 0 lf-env-handle? diag -> outcome-invalid 12345 0 lf-diag-env-handle }T
lf-diag-clear
T{ 2 lf-env-depend diag -> outcome-invalid lf-env-serial @ 2 lf-diag-env-handle }T
\ The first failure wins.
T{ n.Z lf-env-lookup diag -> -1 outcome-rejected lf-env-serial @ 2 lf-diag-env-handle }T
T{ 999 lf-env-begin diag -> outcome-invalid 999 0 lf-diag-bad-argument }T
env-free
\ L2, then the publisher: a failed re-check, with its part (4: N2).
8 fresh-env
' syn-check 7 checked-run
11 lf-env-begin drop
T{ n.w lf-env-param? diag -> outcome-rejected n.w 0 lf-diag-undeclared-param }T
7 lf-env-begin drop outcome-ok lf-env-finish
T{ lf-env-hand-over drop diag -> outcome-invalid 7 4 lf-diag-recheck }T
env-free
\ ... and when a slot of its name below it is not final yet (the check
\ started too early), even though none is accepted: an open slot never
\ reads as accepted.
8 fresh-env
7 lf-env-begin drop outcome-ok lf-env-finish
T{ 0 slot@ lf-slot-accepted? 0 slot@ lf-slot-outcome @ -> false outcome-ok }T
T{ lf-env-hand-over drop diag -> outcome-invalid 7 4 lf-diag-recheck }T
env-free
\ ... even when that open slot already holds a rejected outcome, as a slot
\ being published does before its final mark.
8 fresh-env
outcome-rejected 0 slot@ lf-slot-outcome !
7 lf-env-begin drop outcome-ok lf-env-finish
T{ lf-env-hand-over drop diag 0 slot@ lf-slot-final? -> outcome-invalid 7 4 lf-diag-recheck false }T
env-free
\ No room in the pool: dependencies needed and capacity.
1 fresh-env
' syn-check 8 checked-run
T{ ' syn-check 8 lf-env-step drop diag -> outcome-full 3 1 lf-diag-pool-full }T
env-free
\ A THROW in the publisher (in a check: above, with G-P6).
8 fresh-env
' syn-check 1 checked-run
3 throw-at ! ' throw-hook is lf-env-before-final
T{ ' syn-check 3 lf-env-step diag -> outcome-invalid true 3 -77 lf-diag-publisher-fault }T
' lf-env-no-fault is lf-env-before-final
env-free
\ L3 and the candidate's own limit.
lf-input-reset n.A def n.u param n.u param add ends
8 fresh-env
T{ 0 lf-env-begin lf-env-own-params diag -> outcome-ok outcome-rejected 0 0 lf-diag-duplicate-param }T
env-free
wide-input
8 fresh-env
' syn-check 17 checked-run
17 lf-env-begin drop lf-env-dep-capacity depend-all drop
T{ 16 lf-env-depend diag -> outcome-full lf-env-dep-capacity lf-env-dep-capacity lf-diag-deps-full }T
env-free

\ ---------------------------------------------------------------------------
\ K5's tie-break (ADR 0012 E5, as amended): with an undecided and an
\ unsupported earlier declaration of a name, and none accepted, a user is
\ unknown, in either input order, by lookup and by N2; the first
\ undecided one is recorded. Claiming ok instead is refused (part 4).
: tie-input ( -- )
  lf-input-reset
  n.A lf-kind-axiom decl no-value outcome-unsupported audit add   \ 0 unsupported
  n.A def outcome-unknown audit add                              \ 1 unknown
  n.B def n.A uses add                                           \ 2 unknown (K5)
  n.C def outcome-unknown audit add                              \ 3 unknown
  n.C lf-kind-axiom decl no-value outcome-unsupported audit add  \ 4 unsupported
  n.D def n.C uses add                                           \ 5 unknown (K5)
  n.A def add n.C def add ends ;                                 \ 6, 7 unknown (N2)
tie-input
8 fresh-env
' syn-check 2 checked-run
T{ ' syn-check 2 checked-step lf-diag@ nip -> outcome-unknown 1 outcome-unknown lf-diag-dependency-undecided }T
' syn-check 3 checked-step drop ' syn-check 4 checked-step drop
T{ ' syn-check 5 checked-step lf-diag@ nip -> outcome-unknown 3 outcome-unknown lf-diag-dependency-undecided }T
T{ ' syn-check 6 checked-step ' syn-check 7 checked-step step-failures @ -> outcome-unknown outcome-unknown 0 }T
lf-env-view drop
T{ 0 lf-env-outcome 1 lf-env-outcome 2 lf-env-outcome -> outcome-unsupported outcome-unknown outcome-unknown }T
T{ 3 lf-env-outcome 4 lf-env-outcome -> outcome-unknown outcome-unsupported }T
T{ n.A lf-env-lookup n.C lf-env-lookup -> -1 outcome-unknown -1 outcome-unknown }T
env-free
8 fresh-env
' syn-check 6 checked-run
6 lf-env-begin drop
T{ lf-env-own-name -> outcome-unknown }T
outcome-ok lf-env-finish
T{ lf-recheck lf-env-hand-over -> 4 true outcome-invalid false }T
env-free
main-input

\ ---------------------------------------------------------------------------
\ Row 8: determinism. The same input checked twice, in two environments
\ and two ways, gives the same verdicts and the same digests.
8 fresh-env
T{ ' syn-check ' main-maker lf-env-run -> outcome-ok }T
env-digest constant run-1
T{ main-count verdicts-match? -> true }T
env-free
8 fresh-env
T{ ' syn-check main-count checked-run step-failures @ -> 0 }T
T{ env-digest run-1 = main-count verdicts-match? -> true true }T
\ A second run over a finished environment is refused.
T{ ' syn-check ' main-maker lf-env-run env-digest run-1 = -> outcome-invalid true }T
env-free
T{ ' syn-check ' main-maker lf-env-run -> outcome-invalid }T
T{ lf-env-spent? -> false }T

\ The identity serial: once spent, no environment can be made.
lf-env-serial @ constant serial-now
max-n lf-env-serial !
T{ 8 lf-env-new -> 0 outcome-full }T
serial-now lf-env-serial !
T{ step-failures @ -> 0 }T
T{ depth -> 0 }T
bye
