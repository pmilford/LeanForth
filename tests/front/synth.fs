\ Unit tests of instance search (plan FE1e5; src/front/synth.fs) over the
\ Init slice tests/front/whnf-slice.ndjson and its elaboration data (20
\ instances, 476 left out): answers found (one level, and two levels with
\ a consumer resumed by its subgoals' answers), none (a subgoal with no
\ candidate), the stuck signal (trySynthInstance's undef,
\ synthPending's false), each unsupported rule with its code (a tried
\ candidate left out, 119; a goal that is a pi, 117; Lean's check of a
\ result that holds a metavariable, 121; an answer that keeps one of the
\ search's, 118), invalid (no class, 110; a term not live), exhausted
\ (each budget) and full (each heap request refused); the candidates
\ tried, in Lean's order (S1 §9: a left-out one only when tried); the
\ cache (a second search tries nothing; a reset context's is gone); the
\ out-parameters made new and the cache key's wildcards; the size limit;
\ new answers by type; synthPending's tests and its depth limit; the
\ hooks inside isDefEq (isDefEqArgs' postponed instance argument filled
\ by synthPending with the machine set aside, and the instance-typed
\ assignment and its synthesis fallback, the admissible spines); step's
\ order (resume first), resume's sizes, consume's filter, nested searches'
\ own tables, the cache's synthPendingDepth, outer level metavariables in
\ a key; budget and heap-refusal sweeps over three goals; and that a
\ search leaves no depth, mark, call or node behind. Pinned Lean's own
\ answers on all of Init are tests/front/check_synth.py's (make
\ reference-synth). Every T{ }T checks the data stack's depth.
include ../support/tester.fs
include ../support/heap-watch.fs
\ Every module first: a context member declared after menv-load would
\ move the context under the loaded slice.
require ../../src/front/synth.fs
require ./whnf-cases.fs

: num ( u -- t ) lf-hterm-cell must drop ;
: ?lv ( -- level ) lf-level-mvar-new made ;
: ?tv ( level -- t ) lf-level-succ must sort mv-natural lf-mvar-new made ;
: c0 ( c-addr u -- t ) 0 -rot cn ;
: add0 ( t -- t' ) >r l0 1 s" Add" cn r> app ;
: ofnat0 ( t u -- t' ) >r >r l0 1 s" OfNat" cn r> app r> num app ;
: ofnat? ( u -- t ) >r ?lv dup ?tv swap 1 s" OfNat" cn swap app r> num app ;
: add? ( -- t ) ?lv dup ?tv swap 1 s" Add" cn swap app ;
: hadd? ( -- t )
  ?lv ?lv ?lv 3 s" HAdd" cn lv1 ?tv app lv1 ?tv app lv1 ?tv app ;
: le ( a b -- t ) >r >r l0 1 s" LE.le" cn nat app s" instLENat" c0 app r> app r> app ;
: lt ( a b -- t ) >r >r l0 1 s" LT.lt" cn nat app s" instLTNat" c0 app r> app r> app ;
: p-and ( p q -- t ) >r s" And" c0 swap app r> app ;
: dec ( p -- t ) s" Decidable" c0 swap app ;
: dec-le ( a b -- t ) >r s" Nat.decLe" c0 swap app r> app ;
: dec-lt ( a b -- t ) >r s" Nat.decLt" c0 swap app r> app ;
: inst-named ( c-addr u -- i ) menv-name elab-decl-of drop elab-instance-of drop ;
: tried# ( -- n ) lf-synth-tried nip ;
: tried@ ( k -- v ) cells lf-synth-tried drop + @ ;
: tried? ( k c-addr u -- flag ) inst-named swap tried@ = ;
: none-in? ( flag slab -- flag' ) slab-count 0= and ;
: clean? ( -- flag )   \ no depth, mark, call, node, answer or saved machine left
  lf-mctx-depth 0= lf-mctx-marks 0= and sy-calls none-in? sy-gens none-in?
  sy-entries none-in? sy-resume none-in? sy-cnodes none-in? sy-answers none-in?
  sy-cands none-in? sy-tcl none-in? de-saved none-in? ;
: same? ( inst flag outcome e -- same? flag outcome ) >r rot r> lf-meta-eqv drop -rot ;
: assigned? ( mvar -- flag ) lf-mvar-value dup if nip then ;
: synth ( t -- inst flag outcome ) lf-synth-instance ;

\ ---- Answers. Add Nat: its three candidates, the two left out first;
\ only instAddNat, the last, is tried (S1 §9).
T{ nat add0 synth s" instAddNat" c0 same? tried# 0 s" instAddNat" tried? clean?
   -> true true outcome-ok 1 true true }T
T{ nat 0 ofnat0 synth s" instOfNatNat" c0 0 num app same? -> true true outcome-ok }T
\ Two levels: instDecidableAnd's subgoals Decidable (2 <= 3) and
\ Decidable (1 < 2) each a new goal, answered, resumed in turn.
: le-and-lt ( -- t ) 2 num 3 num le 1 num 2 num lt p-and ;
: and-answer ( -- t )
  s" instDecidableAnd" c0 2 num 3 num le app 1 num 2 num lt app
  2 num 3 num dec-le app 1 num 2 num dec-lt app ;
T{ le-and-lt dec synth and-answer same? -> true true outcome-ok }T
T{ tried# 0 s" instDecidableAnd" tried? 1 s" Nat.decLe" tried? 2 s" Nat.decLt" tried?
   clean? -> 3 true true true true }T
\ A known goal: Decidable (2 <= 3 /\ 2 <= 3)'s second subgoal has the
\ first one's key; the consumer waits on its entry and takes its answer
\ (Nat.decLe tried once).
: le-twice ( -- t ) 2 num 3 num le 2 num 3 num le p-and ;
: twice-answer ( -- t )
  s" instDecidableAnd" c0 2 num 3 num le app 2 num 3 num le app
  2 num 3 num dec-le app 2 num 3 num dec-le app ;
T{ le-twice dec synth twice-answer same? tried# clean? -> true true outcome-ok 2 true }T
\ An answer with free variables: Decidable (a <= b) is Nat.decLe a b,
\ checkMayHaveSideEffects following a and b to their types.
T{ fa fb le dec synth fa fb dec-le same? -> true true outcome-ok }T
\ The let variable g (whnf-cases.fs's) in the answer: its value followed
\ too.
T{ fg 3 num le dec synth fg 3 num dec-le same? -> true true outcome-ok }T
\ A candidate whose type does not unify: Add.{1} Nat against instAddNat's
\ Add.{0} Nat (keys equal, levels not) fails, and the next, left out,
\ is tried: 119.
T{ lv1 1 s" Add" cn nat app synth tried# 0 s" instAddNat" tried?
   -> -1 false outcome-unsupported 2 true }T
\ mkConstWithFreshMVarLevels: instHAdd.{?u}.
: hadd-level ( -- level ) s" instHAdd" menv-name lf-menv-find drop lf-meta-const-fresh drop
  lf-term-first@ lf-cref-slot lf-cref-pairs drop 0 lf-cref-pair@ drop ;
T{ hadd-level lf-level-mvar? -> true }T
\ The constants' refusals (meta-env.fs): a level that names none is
\ invalid (review s1-synth-b re-check L-c), a level word that fails
\ passes its outcome on, and no room for the constant reference or for
\ its term is full; none makes a constant.
create no-such-level -1 ,
: hadd-decl ( -- d ) s" instHAdd" menv-name lf-menv-find drop ;
: no-level ( -- level outcome ) -1 outcome-exhausted ;
: fresh-hadd ( -- term outcome ) hadd-decl lf-meta-const-fresh ;
: crefs-full ( xt -- i*x )   \ xt run with the references' limit at their count
  lf-cref-capacity >r lf-cref-count @ lf-cref-capacity! drop execute
  r> lf-cref-capacity! drop ;
T{ s" instHAdd" menv-name lf-name-generation @ no-such-level 1 lf-meta-const-at
   hadd-decl ' no-level lf-meta-const-with -> -1 outcome-invalid -1 outcome-exhausted }T
: terms-full ( xt -- i*x )   \ xt run with the terms' limit at their count
  lf-term-capacity >r lf-term-count @ lf-term-capacity! drop execute
  r> lf-term-capacity! drop ;
T{ ' fresh-hadd crefs-full ' fresh-hadd terms-full fresh-hadd nip
   -> -1 outcome-full -1 outcome-full outcome-ok }T
\ A level word that makes a constant itself (a nested call, at HAdd.hAdd's
\ second level) leaves the outer constant's first level as it was, and
\ every call leaves me-pairs as it found it (re-check L-c: cut back, not
\ cleared).
variable level-calls
: nesting-level ( -- level outcome )
  1 level-calls +! level-calls @ 2 = if fresh-hadd 2drop then lv1 outcome-ok ;
: level-of ( term k -- level )
  >r lf-term-first@ lf-cref-slot lf-cref-pairs drop r> lf-cref-pair@ drop ;
: hadd-fn ( -- d ) s" HAdd.hAdd" menv-name lf-menv-find drop ;
: nested-levels ( -- l0 l1 l2 outcome calls )
  0 level-calls ! hadd-fn ['] nesting-level lf-meta-const-with >r
  dup 0 level-of over 1 level-of rot 2 level-of r> level-calls @ ;
T{ me-pairs slab-count nested-levels me-pairs slab-count
   -> 0 lv1 lv1 lv1 outcome-ok 3 0 }T
\ A count below zero makes the constant at no level, as zero does.
T{ s" instHAdd" menv-name lf-name-generation @ no-such-level -1 lf-meta-const-at
   swap lf-term-first@ lf-cref-slot lf-cref-pairs nip -> outcome-ok 0 }T
\ The scan follows a Sort's level and max and imax levels: Sort (max ?u
\ 1), Sort (imax 1 ?u); a level metavariable of the search's depth is
\ what abstractMVars would keep (sy-deep-mvar?), an outer one not.
T{ ?lv lv1 lf-level-max must sort sy-scan sy-found slab-count 0 sy-found@ nip
   -> outcome-ok 1 sy-lmvar }T
T{ lv1 ?lv lf-level-imax must sort sy-scan sy-found slab-count -> outcome-ok 1 }T
: deep-sorts ( -- inner? outcome outer? outcome )   \ one depth deeper
  ?lv true lf-mctx-depth{ made >r ?lv sort sy-deep-mvar? rot sort sy-deep-mvar?
  r> }lf-mctx-depth drop ;
T{ deep-sorts -> true outcome-ok false outcome-ok }T
\ A goal that whnf makes a pi (a beta redex): 117.
: beta-pi ( -- t ) lv1 sort 0 bv lam nat nat add0 tpi app ;
T{ beta-pi synth lf-synth-error -> -1 false outcome-unsupported 117 }T
\ None: Decidable (p /\ q) of propositions p, q: its subgoal Decidable p
\ has no candidate, so no generator, and the search ends.
l0 sort char P local constant fp'   l0 sort char Q local constant fq'
T{ fp' fq' p-and dec synth tried# clean? -> -1 false outcome-ok 1 true }T
\ The answer is assigned to no outer metavariable; an outer level one in
\ the goal is assigned by assignOutParams' isDefEq (Add.{?u} Nat).
variable lu
T{ ?lv dup lu ! 1 s" Add" cn nat app synth nip nip lu @ lf-level-mvar-value nip
   -> outcome-ok true }T

\ ---- The stuck signal, from a key (a recursor stuck on ?n, below Add's
\ root): lf-synth-instance passes it on, trySynthInstance makes it undef.
: rec-q ( -- t ) rec nat nat lam app zero app nat nat 0 bv lam lam app ?n app ;
T{ rec-q add0 synth -> -1 false lf-meta-stuck }T
T{ rec-q add0 lf-try-synth nat add0 lf-try-synth rot drop nat nat tpi add0 lf-try-synth
  rot drop
   -> -1 lf-synth-undef outcome-ok lf-synth-some outcome-ok lf-synth-none
  outcome-unsupported }T
T{ fp' fq' p-and dec lf-try-synth -> -1 lf-synth-none outcome-ok }T

\ ---- Unsupported, each with its code. The slice leaves instOfNatQ,
\ String.instHAddCharRaw and instAddQ out: S1's stuck problems try them
\ first (pinned Lean tries just these, S1 §9): 119.
T{ 0 ofnat? synth lf-synth-error tried# -> -1 false outcome-unsupported 119 1 }T
T{ 0 tried@ lf-inst-left-out? -> true }T
T{ hadd? synth lf-synth-error -> -1 false outcome-unsupported 119 }T
T{ add? synth lf-synth-error -> -1 false outcome-unsupported 119 }T
\ A goal that is a pi, or whose whnf is (117).
T{ nat nat add0 tpi synth lf-synth-error -> -1 false outcome-unsupported 117 }T
\ OfNat Nat ?k: instOfNatNat ?k, which holds the outer ?k: Lean's check
\ (121).
: done ( outcome -- ) ok? 0= abort" synth test: a step failed" ;
: ofnat-hole ( -- t )
  nat mv-natural lf-mvar-new made >r l0 1 s" OfNat" cn nat app r> app ;
T{ ofnat-hole synth lf-synth-error -> -1 false outcome-unsupported 121 }T
\ An answer that keeps a metavariable of the search's depth (118).
: deep-node ( -- c )   \ a consumer whose metavariable holds a new one
  true lf-mctx-depth{ made drop nat nat mv-natural lf-mvar-new made
  nat mv-natural lf-mvar-new made dup >r swap lf-mvar-assign done r> sy-cnode-open made ;
T{ sy-enter deep-node sy-answer-expr nip lf-synth-error -> outcome-ok
  outcome-unsupported 118 }T
: deep-done ( -- ) lf-mctx-latest }lf-mctx-depth drop sy-leave ;
T{ deep-done clean? -> true }T

\ ---- Invalid: a goal of no class (110, getInstances' error); a term
\ that is not live.
T{ nat synth lf-synth-error -> -1 false outcome-invalid 110 }T
T{ -1 synth -> -1 false outcome-invalid }T
T{ clean? -> true }T

\ ---- The cache: a second search of the same goal tries nothing; a
\ reset context (mctx-epoch@) has another cache; the cache is not used
\ with a local instance in the context, and a goal with metavariables
\ and no out-parameter keys it as it is.
T{ nat add0 synth s" instAddNat" c0 same? tried# -> true true outcome-ok 0 }T
T{ sy-cache slab-count 0> mctx-epoch@ 1+ sy sy-epoch ! nat add0 synth nip nip tried#
   -> true outcome-ok 1 }T
\ synthPendingDepth keys the cache: the entry made at depth 0 is missed
\ at depth 1 (a search, instAddNat tried), found at depth 0.
: at-pending ( n -- tried ) sy sy-pending ! nat add0 synth 2drop drop tried# 0 sy sy-pending ! ;
T{ 1 at-pending 0 at-pending -> 1 0 }T
: add-local ( -- old )
  lf-mctx-view dup nat add0 lf-lctx-local made 0 0 lf-local-new made
  s" Add" menv-name lf-local-instance made lf-view-push made lf-mctx-view! ;
T{ add-local sy-cache-ok? swap lf-mctx-view! sy-cache-ok? -> false true }T
\ A search with a local instance in the context: no cache, and
\ instances.fs's rule (unsupported).
T{ add-local nat add0 synth rot drop rot lf-mctx-view! -> false outcome-unsupported }T
\ synthPending passes on a failure that is not the stuck signal.
T{ add? mv-synthetic lf-mvar-new made lf-synth-pending -> false outcome-unsupported }T

\ ---- preprocessOutParam: HAdd Nat Nat Nat's out-parameter (its third
\ argument) and out-level made new metavariables; the cache key's made
\ wildcards (Lean's __wild__): a loose bound variable and a level
\ parameter.
: hadd-nat ( -- t ) l0 l0 l0 3 s" HAdd" cn nat app nat app nat app ;
: last-arg ( t -- a ) lf-term-second@ ;
: head-level ( t k -- level ) swap lf-meta-head lf-term-first@ lf-cref-slot
  lf-cref-pairs drop
  swap lf-cref-pair@ drop ;
T{ hadd-nat sy-out-param nip -> outcome-ok }T
T{ hadd-nat sy-out-param drop dup last-arg lf-mvar? swap 2 head-level lf-level-mvar?
   -> true true }T
T{ hadd-nat dup sy-head-class drop sy-wild-key nip -> outcome-ok }T
T{ hadd-nat dup sy-head-class drop sy-wild-key drop dup last-arg sy-tc-base 1-
  lf-term-bvar-is?
   swap 2 head-level lf-level-tag@ -> true lf-level-tag-param }T
T{ hadd-nat sy-head-class drop sy-outs? nat add0 sy-head-class drop sy-outs?
   nat sy-head-class -> true false false }T

\ ---- Table keys: assignable metavariables and level ones of the
\ search's depth placeholders, numbered from the left; outer ones kept.
?lv constant ou1   ?lv constant ou2     \ outer level metavariables
T{ sy-enter true lf-mctx-depth{ made constant kscope -> outcome-ok }T
: inner ( -- m ) nat mv-natural lf-mvar-new made ;
inner constant m1   inner constant m2
: pair ( a b -- t ) >r >r l0 l0 2 s" Prod" cn r> app r> app ;
T{ m1 m2 pair lf-synth-key drop m2 m1 pair lf-synth-key drop lf-meta-eqv
   -> true outcome-ok }T
T{ m1 m1 pair lf-synth-key drop m1 m2 pair lf-synth-key drop lf-meta-eqv
   -> false outcome-ok }T
T{ ?n m1 pair lf-synth-key drop ?n m2 pair lf-synth-key drop lf-meta-eqv
   m1 ?n pair lf-synth-key drop ?n m1 pair lf-synth-key drop lf-meta-eqv
   -> true outcome-ok false outcome-ok }T
T{ m1 m2 pair lf-synth-key drop 0 sy-tc drop 1 sy-tc drop pair lf-meta-eqv
   m1 assigned? -> true outcome-ok false }T
\ Level metavariables: the search's depth's are placeholders, numbered
\ apart from the terms'; outer ones kept (Sort ?u1, Sort ?u2 differ).
: sort-key ( level -- key ) sort lf-synth-key drop ;
T{ ?lv sort-key ?lv sort-key lf-meta-eqv ou1 sort-key ou2 sort-key lf-meta-eqv
   -> true outcome-ok false outcome-ok }T

\ ---- addAnswer: none at the size limit; isNewAnswer by type.
: size-node ( n -- c )   \ Add Nat's consumer at size n, in this search
  nat add0 lf-synth-key drop nat add0 mv-natural lf-mvar-new made sy-cnode-open made
  tuck scn@ sc-size ! dup lf-mctx-snapshot made swap scn@ sc-snap ! ;
: add-entry ( c -- ) scn@ sc-key @ sy-root sy-entry-new drop ;
: answers# ( -- n ) sy-answers slab-count ;
T{ lf-synth-max-size size-node dup add-entry dup scn@ sc-mvar @ s" instAddNat" c0
   lf-mvar-assign drop answers# swap sy-add-answer answers# -> 0 outcome-ok 0 }T
T{ lf-synth-max-size 1- size-node dup scn@ sc-mvar @ s" instAddNat" c0 lf-mvar-assign drop
   sy-add-answer answers# 0 san@ sa-size @ -> outcome-ok 1 128 }T
T{ lf-synth-max-size 1- size-node dup scn@ sc-mvar @ s" instAddNat" c0 lf-mvar-assign drop
   sy-add-answer 0 sen@ se-answers @ run-count -> outcome-ok 1 }T
T{ 0 sen@ se-answers @ run-count sy-c syc-result @ s" instAddNat" c0 lf-meta-eqv
   -> 1 true outcome-ok }T
\ isNewAnswer with two older answers, of types Add Nat and Mul Nat: one of
\ type Add Nat is not new (the later Mul Nat does not make it new), one of
\ type Nat is.
: typed-answer ( type -- a ) 0 1 sy-answer-new made tuck san@ sa-type ! ;
: two-answers ( -- e )   \ entry 0's answers: [Add Nat, Mul Nat]
  0 nat add0 typed-answer run-push made l0 1 s" Mul" cn nat app typed-answer run-push made
  0 sen@ se-answers ! 0 ;
T{ nat add0 typed-answer two-answers sy-new-answer? nat typed-answer two-answers
   sy-new-answer? -> false outcome-ok true outcome-ok }T
T{ kscope }lf-mctx-depth sy-leave clean? -> outcome-ok true }T

\ ---- canonInstances: a generator of a goal with no metavariable that
\ has an answer is popped (sy-canon?); one with a metavariable is not.
: canon-gen ( open -- g )
  >r nat add0 lf-synth-key drop nat add0 mv-natural lf-mvar-new made 0 sy-gen-open made
  r> over sgn@ sg-open ! ;
T{ sy-enter false canon-gen dup sgn@ sg-key @ sy-root sy-entry-new swap sy-canon?
   -> outcome-ok outcome-ok false outcome-ok }T
T{ 0 sen@ se-answers dup @ 0 run-push drop swap ! false canon-gen sy-canon?
   true canon-gen sy-canon? -> true outcome-ok false outcome-ok }T
\ A goal no entry has (Mul Nat) is not popped.
: mul-gen ( -- g ) l0 1 s" Mul" cn nat app lf-synth-key drop nat 0 sy-gen-open made
  false over sgn@ sg-open ! ;
T{ mul-gen sy-canon? -> false outcome-ok }T
\ A goal whose only metavariable is a level one (Add.{?u} Nat) has
\ metavariables (hasMVar): its generator is open, never popped by
\ canonInstances.
: lvl-gen ( -- g )
  nat add0 lf-synth-key drop ?lv 1 s" Add" cn nat app mv-natural lf-mvar-new made 0
  sy-gen-open made ;
: gen-open? ( g -- flag outcome ) sy-gen-goal >r drop sgn@ sg-open @ r> ;
T{ lvl-gen gen-open? -> true outcome-ok }T
T{ sy-leave clean? -> true }T

\ ---- A nested search (synthPending inside a search) has its own table
\ and gives back only what it added: the outer search's generator and
\ entry stay, and the inner one finds no outer entry.
: add-key ( -- key ) nat add0 lf-synth-key drop ;
: outer-gen ( -- ) false canon-gen sgn@ sg-key @ sy-root sy-entry-new done ;
T{ sy-enter outer-gen sy-enter add-key sy-find sy-gens slab-count sy-entries slab-count
   -> outcome-ok outcome-ok -1 false outcome-ok 1 1 }T
T{ false canon-gen drop sy-leave sy-gens slab-count add-key sy-find sy-leave clean?
   -> 1 0 true outcome-ok true }T

\ ---- consume: only the subgoals not yet assigned stay (?m1 assigned,
\ ?m2 not: [?m2]).
: two-goals ( -- c )
  sy-enter done nat add0 lf-synth-key drop nat add0 mv-natural lf-mvar-new made
  sy-cnode-open made nat mv-natural lf-mvar-new made dup >r s" Nat.zero" c0 lf-mvar-assign
  done 0 r> run-push made nat mv-natural lf-mvar-new made dup >r run-push made
  over scn@ sc-goals ! r> ;
: left-goals ( c m2 -- n same? outcome )
  >r dup sy-goals-left swap scn@ sc-goals @ dup run-count swap 0 run@ r> = rot ;
T{ two-goals left-goals sy-leave clean? -> 1 true outcome-ok true }T

\ ---- step: resume comes before generate. With a (consumer, answer) on
\ the resume stack and a generator with nothing left to try, the pair is
\ taken: the answer instAddNat is unified with the consumer's subgoal ?m
\ (its goal ?g := ?m), a node of the goal with the sizes added (5 + 3)
\ consumes it, and the root gets the answer; the generator stays.
variable rg   variable rm
: resume-node ( -- c )   \ ?g's consumer at size 5, its subgoal ?m, its entry
  nat add0 mv-natural lf-mvar-new made rg !  nat add0 mv-natural lf-mvar-new made rm !
  rg @ rm @ lf-mvar-assign done  nat add0 lf-synth-key drop rg @ sy-cnode-open made
  0 rm @ run-push made over scn@ sc-goals !  5 over scn@ sc-size !
  lf-mctx-snapshot made over scn@ sc-snap !  dup add-entry ;
: resume-ready ( -- )
  resume-node s" instAddNat" c0 3 sy-answer-new made sy-resume slab-2push done
  false canon-gen 0 swap sgn@ sg-idx ! ;
: newest-size ( -- n ) sy-cnodes slab-count 1- scn@ sc-size @ ;
T{ sy-enter true lf-mctx-depth{ made constant rscope -> outcome-ok }T
T{ resume-ready sy-step sy-gens slab-count sy-resume slab-count newest-size
   -> true outcome-ok 1 0 8 }T
T{ sy-c syc-result @ s" instAddNat" c0 lf-meta-eqv -> true outcome-ok }T
T{ rscope }lf-mctx-depth sy-leave clean? -> outcome-ok true }T

\ ---- synthPending (synthPendingImp): a synthetic opaque metavariable,
\ one whose type is no class and a nesting past maxSynthPendingDepth are
\ false, the stuck signal too; a class goal is filled; one assigned
\ meanwhile stays.
: pending ( type kind -- mvar ) lf-mvar-new made ;
T{ nat add0 mv-opaque pending lf-synth-pending -> false outcome-ok }T
T{ nat mv-natural pending lf-synth-pending -> false outcome-ok }T
T{ rec-q add0 mv-synthetic pending lf-synth-pending -> false outcome-ok }T
T{ nat add0 mv-synthetic pending dup lf-synth-pending rot assigned?
   -> true outcome-ok true }T
T{ lf-synth-max-pending 1+ sy sy-pending ! nat add0 mv-synthetic pending lf-synth-pending
   0 sy sy-pending ! -> false outcome-ok }T
T{ lf-synth-max-pending sy sy-pending ! nat add0 mv-synthetic pending lf-synth-pending
   0 sy sy-pending ! -> true outcome-ok }T
T{ nat add0 mv-synthetic pending dup s" instAddNat" c0 lf-mvar-assign drop
   s" instAddNat" c0 sy-fill
   -> false outcome-ok }T
T{ -1 lf-synth-pending -> false outcome-invalid }T

\ ---- The hooks inside isDefEq. isDefEqArgs postpones Add.add's instance
\ argument ?i and trySynthPending fills it (a nested search, the machine
\ set aside), then compares it: @Add.add Nat ?i a b =?= @Add.add Nat
\ instAddNat a b. Add.add is a reducible definition, and lazy delta
\ (plan S2, merge A) comes first: until it is merged the answer is
\ unsupported, never false.
: add-add ( inst -- t ) >r l0 1 s" Add.add" cn nat app r> app fa app fb app ;
: filled-or-later ( mvar flag outcome -- ok? )
  dup outcome-unsupported = if 2drop assigned? 0= exit then
  ok? and swap assigned? and ;
T{ nat add0 mv-synthetic pending dup add-add s" instAddNat" c0 add-add lf-meta-defeq
   filled-or-later clean? -> true true }T
\ An instance-typed metavariable: assigned when the types agree at
\ instances transparency; else (a value whose spine ends in an
\ assignable metavariable is not admissible) synthPending fills it (a
\ nested search: instAddNat tried) and the value must be its instance:
\ ?k := instAddNat; fx is not instAddNat: false, or unsupported until
\ plan S2's lazy delta compares it with the definition instAddNat, never
\ true, nothing kept.
: inst-typed ( type -- mvar ) mv-natural pending dup lf-mvar-mark-inst done ;
\ Each runs xt inside a mark and a depth scope, both closed after.
: in-scopes ( i*x xt -- j*x closed? )
  lf-mctx-mark made >r true lf-mctx-depth{ made >r execute r> }lf-mctx-depth
  r> lf-mctx-rollback outcome-and ok? ;
: other-cache ( -- ) mctx-epoch@ 1+ sy sy-epoch ! ;
: direct ( -- flag outcome assigned? )
  nat add0 inst-typed dup s" instAddNat" c0 lf-meta-defeq rot assigned? ;
T{ ' direct in-scopes -> true outcome-ok true true }T
variable kk
: k-hole ( -- k ) nat add0 mv-natural pending dup kk ! ;
: k-filled? ( -- flag ) kk @ lf-mvar-value drop s" instAddNat" c0 lf-meta-eqv drop ;
: via-k ( -- flag outcome assigned? filled? )
  nat add0 inst-typed dup k-hole lf-meta-defeq rot assigned? k-filled? ;
T{ other-cache ' via-k in-scopes tried# clean? -> true outcome-ok true true true 1 true }T
: never-true ( flag outcome -- ok? ) dup outcome-unsupported = if 2drop true exit then
  ok? swap 0= and ;
: via-fx ( -- ok? ) nat add0 inst-typed dup fx lf-meta-defeq never-true swap assigned?
  0= and ;
T{ other-cache ' via-fx in-scopes tried# clean? -> true true 1 true }T
\ spineMVarsAdmissible: a value whose spine ends in a read-only (outer)
\ metavariable, through an application or a lambda, or in a pi node, is
\ admissible: the types compared, assigned, nothing synthesized.
nat nat add0 tpi mv-natural pending constant ?g     \ outer: read-only in the scopes
nat add0 mv-natural pending constant ?o
l0 ?tv constant ?ty
: tried-none? ( -- flag ) tried# 0= ;
: via-app ( -- flag outcome assigned? )
  sy-tried slab-clear nat add0 inst-typed dup ?g fa app lf-meta-defeq rot assigned? ;
T{ ' via-app in-scopes tried-none? -> true outcome-ok true true true }T
: via-lam ( -- flag outcome assigned? )
  nat nat add0 tpi inst-typed dup nat ?o lam lf-meta-defeq rot assigned? ;
T{ ' via-lam in-scopes -> true outcome-ok true true }T
: via-pi ( -- flag outcome assigned? )
  lv1 sort inst-typed dup nat ?ty tpi lf-meta-defeq rot assigned? ;
T{ ' via-pi in-scopes -> true outcome-ok true true }T
\ Not admissible, and synthPending finds nothing (Decidable (p /\ q)):
\ false; types that differ where the metavariable's type is a pi:
\ unsupported (Lean compares them at implicit transparency first).
: via-none ( -- flag outcome assigned? )
  fp' fq' p-and dec inst-typed dup k-hole lf-meta-defeq rot assigned? ;
T{ other-cache ' via-none in-scopes -> false outcome-ok false true }T
: via-pi-type ( -- flag outcome )
  nat nat add0 tpi inst-typed fx lf-meta-defeq ;
T{ ' via-pi-type in-scopes -> false outcome-unsupported true }T
\ A synthetic opaque metavariable of this depth is read-only too (not
\ assignSyntheticOpaque): admissible, nothing synthesized.
: via-opaque ( -- flag outcome assigned? tried )
  sy-tried slab-clear nat add0 inst-typed dup nat nat add0 tpi mv-opaque pending fa app
  lf-meta-defeq rot assigned? tried# ;
T{ ' via-opaque in-scopes -> true outcome-ok true 0 true }T
\ A projection's spine is its structure's: ?x.1 for an assignable ?x of
\ this depth is not admissible, so synthPending runs (instAddNat tried).
: prod-add ( -- t ) l0 l0 2 s" Prod" cn nat add0 app nat app ;
: via-proj ( -- tried )
  sy-tried slab-clear nat add0 inst-typed prod-add mv-natural pending 0 proj lf-meta-defeq
  2drop tried# ;
T{ other-cache ' via-proj in-scopes -> 1 true }T
\ synthPending searches in the metavariable's own local context: its
\ local instance means no cache and instances.fs's rule (unsupported),
\ not the current context's answer.
: pending-in-local ( -- flag outcome )
  add-local nat add0 mv-synthetic lf-mvar-new made swap lf-mctx-view! lf-synth-pending ;
T{ other-cache pending-in-local -> false outcome-unsupported }T

\ ---- Exhausted: each budget from 0 answers exhausted or the answer, and
\ nothing is left behind (Decidable (2 <= 3 /\ 1 < 2): two levels).
: budget-run ( k -- inst flag outcome )
  lf-meta-budget! mctx-epoch@ 1+ sy sy-epoch ! le-and-lt dec synth
  lf-meta-default-budget lf-meta-budget! ;
: budget-ok? ( k -- flag )
  budget-run dup outcome-exhausted = if drop 2drop clean? exit then
  and-answer same? swap rot and swap ok? and clean? and ;
\ The steps the search takes (each budget below it exhausted, at it the
\ answer), every 1/40 of them tried.
: steps ( -- n )
  lf-meta-default-budget lf-meta-budget! mctx-epoch@ 1+ sy sy-epoch ! le-and-lt dec
  synth
  2drop drop lf-meta-default-budget lf-meta-budget - lf-meta-default-budget
  lf-meta-budget! ;
steps constant need
: budgets-ok? ( -- flag ) true need 0 do i budget-ok? and need 40 / 1 max +loop ;
T{ budgets-ok? 0 budget-run need 1- budget-run nip nip need budget-run -rot 2drop
   -> true -1 false outcome-exhausted outcome-exhausted outcome-ok }T

\ ---- Full: each heap request of a search refused in turn (its slabs
\ shrunk first): full, or the answer; nothing is left behind.
: shrink ( slab -- ) dup slab-clear slab-trim drop ;
: fresh ( -- )
  mctx-epoch@ 1+ sy sy-epoch ! sy-gens shrink sy-cnodes shrink sy-entries shrink
  sy-answers shrink sy-resume shrink sy-cands shrink sy-found shrink sy-todo shrink
  sy-calls shrink de-saved shrink ;
: refused ( k -- inst flag outcome fired? )
  le-and-lt dec swap fresh heap-refusals ! synth heap-refusals @ 0= 0 heap-refusals ! ;
: refusal-ok? ( k -- flag fired? )
  refused >r dup outcome-full = if drop 2drop clean? r> exit then
  and-answer same? swap rot and swap ok? and clean? and r> ;
: refusals-ok? ( -- flag )
  true 800 1 do i refusal-ok? -rot and swap 0= if leave then loop ;
: fired? ( k -- flag ) refused >r 2drop drop r> ;
T{ refusals-ok? 800 fired? -> true false }T
\ A nested search (via-k: synthPending fills ?k inside isDefEq, the
\ machine set aside on de-saved) with each heap request of the isDefEq
\ refused in turn: the answer, or full with nothing left set aside
\ (review s1-synth-b re-check M-a: de-aside cuts de-saved back when it
\ has no room).
variable refuse-at   variable refusal-fired
: refusing ( mvar k -- flag outcome )   \ isDefEq, its refuse-at-th heap request refused
  refuse-at @ heap-refusals ! lf-meta-defeq heap-refusals @ 0= refusal-fired !
  0 heap-refusals ! ;
: k-made? ( -- flag ) kk @ assigned? dup if drop k-filled? then ;   \ k-filled? if any
: via-k-refused ( -- flag outcome assigned? filled? )
  nat add0 inst-typed dup k-hole refusing rot assigned? k-made? ;
: via-k-ends? ( flag outcome assigned? filled? closed? -- ok? )
  >r 2swap dup outcome-full = if 2drop 2drop r> clean? and exit then
  ok? and and and r> and clean? and ;
: via-k-swept ( k -- ok? fired? )
  refuse-at ! fresh ['] via-k-refused in-scopes via-k-ends? refusal-fired @ ;
: via-k-sweep ( -- flag )
  true 400 1 do i via-k-swept -rot and swap 0= if leave then loop ;
T{ via-k-sweep 400 via-k-swept nip -> true false }T
\ A goal that keeps a metavariable (OfNat Nat ?k): unification's
\ checkAssignment runs (assign-check.fs's occurs check), so each refusal
\ answers full, or Lean's check of the result (121), and leaves nothing
\ behind (review s1-synth-b H1: a refused occurs check left two cells).
: hole-refused ( k -- inst flag outcome fired? )
  ofnat-hole swap fresh heap-refusals ! synth heap-refusals @ 0= 0 heap-refusals ! ;
: hole-ok? ( k -- flag fired? )
  hole-refused >r nip nip dup outcome-full = if drop clean? r> exit then
  outcome-unsupported = lf-synth-error 121 = and clean? and r> ;
: hole-refusals-ok? ( -- flag )
  true 1000 1 do i hole-ok? -rot and swap 0= if leave then loop ;
: hole-fired? ( k -- flag ) hole-refused >r 2drop drop r> ;
T{ hole-refusals-ok? 1000 hole-fired? -> true false }T
\ The same for each budget and each refusal of a known goal's search
\ (Decidable (2 <= 3 /\ 2 <= 3): its second subgoal waits on the first's
\ entry), and for each budget of OfNat Nat ?k: exhausted or full with
\ nothing left behind, else the search's own end.
variable sweep-goal   variable sweep-end
: swept ( inst flag outcome -- flag )
  dup outcome-full = over outcome-exhausted = or if drop 2drop clean? exit then
  sweep-end @ execute clean? and ;
: sweep! ( goal-xt end-xt -- ) sweep-end ! sweep-goal ! ;
: refused-run ( k -- flag fired? )
  sweep-goal @ execute swap fresh heap-refusals ! synth
  heap-refusals @ 0= 0 heap-refusals ! >r swept r> ;
: refusal-sweep ( -- flag )
  true 1000 1 do i refused-run -rot and swap 0= if leave then loop ;
: budget-swept ( k -- flag exhausted? )
  lf-meta-budget! other-cache sweep-goal @ execute synth
  lf-meta-default-budget lf-meta-budget! dup outcome-exhausted = >r swept r> ;
: budget-sweep ( -- flag steps )   \ every 3rd budget until one is enough: that budget
  true -1 20000 0 do drop i budget-swept -rot and swap 0= if i leave then -1 3 +loop ;
: twice-goal ( -- t ) le-twice dec ;
: twice-end ( inst flag outcome -- flag ) twice-answer same? swap rot and swap ok? and ;
: hole-end ( inst flag outcome -- flag )
  outcome-unsupported = lf-synth-error 121 = and nip nip ;
T{ ' twice-goal ' twice-end sweep! refusal-sweep budget-sweep 0> -> true true true }T
T{ ' ofnat-hole ' hole-end sweep! budget-sweep 0> -> true true }T
\ The same for each term-store limit from the store's count up (the
\ terms-full pattern; review s1-synth-b re-check L-a): full with nothing
\ left behind, until a limit has room for the search; how many were full.
: terms-at ( i*x xt k -- j*x )   \ xt run with room for k more terms
  lf-term-capacity >r lf-term-count @ + lf-term-capacity! drop execute
  r> lf-term-capacity! drop ;
: room-run ( k -- flag full? )
  other-cache sweep-goal @ execute ['] synth rot terms-at dup outcome-full = >r swept r> ;
: room-sweep ( -- flag fulls )   \ each room until one is enough: that room
  true -1 1000 0 do drop i room-run -rot and swap 0= if i leave then -1 loop ;
T{ ' twice-goal ' twice-end sweep! room-sweep 0> -> true true }T
T{ ' ofnat-hole ' hole-end sweep! room-sweep 0> -> true true }T
bye
