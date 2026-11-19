\ Instance search (plan FE1e5; docs/design/FE1E_APPLICATIONS.md §3.4-3.7,
\ S1_INTERFACE.md §2, §3, §8, §9): a port of Lean 4.35.0's synthInstance?
\ (Lean/Meta/SynthInstance.lean, its line numbers below), tabled
\ resolution in Lean's order, over instances.fs's candidates and
\ defeq.fs's isDefEq.
\ - lf-synth-instance ( type -- inst flag outcome ): synthInstanceCore?
\   (962) in its configuration (isDefEqStuckEx, foApprox and ctxApprox
\   on, constApprox and univApprox off, instances transparency; Lean's
\   inTypeClassResolution changes only isDefEqProj, which defeq.fs
\   answers unsupported): the type instantiated; preprocess (741: whnf;
\   the kind, and the cache key with the out-parameter arguments and
\   out-levels made wildcards); the cache; else, one depth deeper with
\   level assignments allowed (withNewMCtxDepth: every assignment made
\   inside is undone at its end), preprocessOutParam (779: new
\   metavariables for the out-parameters and out-levels) and main (679);
\   then applyAbstractResult? (881): assignOutParams (829: isDefEq of the
\   type and the result's type at default transparency, synthetic opaque
\   assignable), the result instantiated; cacheResult (947). Flag true
\   and the instance, or false (Lean's none, the caller's "failed to
\   synthesize").
\ - main: a new metavariable of the type, its table key and the root's
\   generator; then step (656) until the root has an answer or both
\   stacks are empty. resume (639) takes the newest (consumer, answer):
\   in the consumer's state the answer is unified with its next subgoal
\   (tryAnswer, 428), then consume. Else generate (594) on the newest
\   generator: none left, or canonInstances (a goal without
\   metavariables that has an answer), pops it; else its next candidate,
\   from the last (getInstances, instances.fs), is tried: tryResolve
\   (346) with getSubgoals (317: a natural metavariable for each binder
\   of the instance's type, whnf where none is left, the subgoals in the
\   instance's synthesis order, each marked instance-typed), isDefEq of
\   the goal and the instance's type, the goal's metavariable assigned
\   (directly when the goal has no metavariable, else by isDefEq), then
\   consume (538): the subgoals not yet assigned; none left: addAnswer
\   (469: none at lf-synth-max-size; a new answer, by its type, wakes
\   the waiters: the root takes it, a consumer goes on the resume
\   stack); else the first subgoal's table key: a known goal queues its
\   answers for the consumer, which waits on it; an unknown one gets a
\   generator (newSubgoal, 260; none, and no entry, when it has no
\   candidate). Each node keeps its metavariable context as a snapshot
\   of mvars.fs's trail, switched to before it is used (withMCtx).
\ - Table keys (mkTableKey, 160): the goal instantiated, each assignable
\   metavariable and each level metavariable of the search's depth
\   replaced by a placeholder, numbered in the order a walk from the
\   left meets them (Lean's _tc.i), by assigning them under a mark,
\   instantiating and rolling back. A term placeholder is the loose
\   bound variable sy-tc-base + i, which no closed type holds (Lean's is
\   a free variable no context declares), a level one a level
\   metavariable the search makes; terms and levels are numbered apart,
\   which gives the equalities of Lean's one count. Keys compare by
\   Lean's Expr == (term-eqv.fs).
\ - The cache (Meta.Cache.synthInstance): by the cache key's type and
\   synthPendingDepth, when the context has no local instance (with one
\   it is not used, which changes no answer); emptied with the context
\   (mctx-epoch@). Lean's __wild__ wildcards are the loose bound
\   variable sy-tc-base - 1 and the level parameter named __wild__.
\   A failed attempt keeps it (it is not in tactic-run.fs's tac-state
\   chain), as Lean's Meta.SavedState.restore keeps Meta.State.cache
\   (Meta/Basic.lean 624-626 restores only mctx, zetaDeltaFVarIds and
\   postponed; review R3 of 2026-11-18). No entry then names a
\   metavariable that is gone: an answer holding one of the search's is
\   unsupported (118, 121) and never cached; a rollback (mvars.fs) undoes
\   assignments, not declarations, so a metavariable made inside the
\   attempt keeps its number and no later one takes it; and no tactic
\   rollback takes back a term node (the front end's one term rollback,
\   the hand-over, ends the declaration).
\ - lf-try-synth ( type -- inst code outcome ): trySynthInstance (1018):
\   lf-synth-some, lf-synth-none, or lf-synth-undef for the stuck signal;
\   it searches through defeq.fs's hook lf-meta-synth (this file's
\   lf-synth-instance), so a test can stand in for the search.
\ - lf-synth-pending ( mvar -- flag outcome ): synthPendingImp (1037):
\   false for a synthetic opaque metavariable, one whose type is no class
\   and past maxSynthPendingDepth (lf-synth-max-pending) nested calls;
\   else lf-synth-instance of its type in its local context (the stuck
\   signal is false) and the instance assigned (false when it was
\   assigned meanwhile).
\ - lf-synth-key ( type -- key outcome ): mkTableKey of an instantiated
\   type. A candidate's constant comes from mvars.fs's lf-meta-const-fresh
\   (mkConstWithFreshMVarLevels), a renamed head from meta-env.fs's
\   lf-meta-const-at.
\ - lf-synth-tried ( -- addr n ): the instances tried (tryResolve) since
\   the last search that is not nested began, in order (Lean's
\   trace.Meta.synthInstance apply lines); lf-synth-error ( -- code ):
\   the code (src/author/errors.fs) the last failure set, 0 for none.
\ Loading sets defeq.fs's hooks lf-meta-synth and lf-meta-synth-pending.
\ Not ported, unsupported with a code: a goal or subgoal whose type is or
\ reduces to a pi (117: getInstances' and tryResolve's binders,
\ removeUnusedArguments?), an answer that keeps a metavariable or level
\ metavariable of the search (118: abstractMVars,
\ openAbstractMVarsResult), a tried candidate the export left out (119)
\ or whose check could not finish (120; S1 §9: only when tried), Lean's
\ check of a result that holds metavariables (121:
\ checkMayHaveSideEffects); a local instance (instances.fs). Invalid
\ 111: an out-parameter past the class's arguments. Fuel: each step and
\ each node a walk visits spends one step of meta-config.fs's budget;
\ Lean's maxHeartbeats is not reproduced (owner, 2026-11-12, FE1E §3.7).
\ Outcomes: ok; lf-meta-stuck (Meta layer only); invalid (110, 111, the
\ data's refusals, a term that is not live); unsupported; exhausted;
\ full. A search nests only through synthPending inside a unification,
\ at most lf-synth-max-pending + 1 deep, so the host stack's depth stays
\ bounded. Untrusted: only the kernel's check of a finished term decides.
\ State: the record sy (the error, synthPendingDepth, the cache's epoch,
\ a key's counts), the slab sy-calls (a search's goal, kind, cache key,
\ answer, root state and the counts of the slabs it adds to, sy-scoped,
\ when it began; the newest is the running one) and the slabs sy-gens,
\ sy-cnodes, sy-entries, sy-answers, sy-resume, sy-cache, sy-cands,
\ sy-todo, sy-found, sy-tcl, sy-args, sy-mvars, sy-lv and sy-tried, in the
\ checker context (ADR 0009); sy-scoped is a read-only table of their
\ words. Loads in decimal whatever BASE is, then
\ restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/runs.fs
require ../lib/bounds.fs
require ../author/errors.fs
require ./goals.fs
require ./meta-env.fs
require ./instances.fs
require ./defeq.fs

128 constant lf-synth-max-size   \ synthInstance.maxSize
1 constant lf-synth-max-pending  \ maxSynthPendingDepth
1 constant lf-synth-some   0 constant lf-synth-none   -1 constant lf-synth-undef
-1 constant sy-root              \ the root's waiter
1 19 lshift constant sy-tc-base  \ a key's placeholder i: bound variable sy-tc-base + i
0 constant sy-no-mvars   1 constant sy-plain   2 constant sy-outs   \ preprocess's kinds
begin-structure /syc        \ a search
  field: syc-type           \ the goal, preprocessed
  field: syc-kind
  field: syc-ckey           \ the cache key's type, or -1: no cache
  field: syc-result         \ the root's answer, or -1
  field: syc-snap           \ the root's state
  field: syc-gens   field: syc-resume   field: syc-entries   \ sy-scoped's slabs'
  field: syc-cnodes   field: syc-answers   field: syc-cands   \ counts at its
  field: syc-tcl                                              \ start, in its order
end-structure
begin-structure /sy
  field: sy-error           \ the last failure's code, or 0
  field: sy-pending         \ synthPendingDepth
  field: sy-epoch           \ the context's epoch the cache holds terms of
  field: sy-keyed           \ a key's term placeholders so far
  field: sy-lkeyed          \ and its level ones
end-structure
begin-structure /sgen       \ a generator node
  field: sg-mvar   field: sg-key   field: sg-snap
  field: sg-first           \ its candidates, from sg-first in sy-cands
  field: sg-idx             \ how many are left to try
  field: sg-open            \ true: its goal has a metavariable
end-structure
begin-structure /scon       \ a consumer node
  field: sc-mvar   field: sc-key   field: sc-snap
  field: sc-goals           \ its subgoals, a run
  field: sc-size
  field: sc-body            \ while tryResolve runs: the goal's body,
  field: sc-val             \ the instance's value
  field: sc-ibody           \ and its type's body
end-structure
begin-structure /sent  field: se-key  field: se-waiters  field: se-answers  end-structure
begin-structure /sans  field: sa-expr  field: sa-type  field: sa-size  end-structure
begin-structure /sche  field: sk-type  field: sk-depth  field: sk-result  end-structure
/sy context-record: sy
/syc context-slab: sy-calls
/sgen context-slab: sy-gens
/scon context-slab: sy-cnodes
/sent context-slab: sy-entries
/sans context-slab: sy-answers
2 cells context-slab: sy-resume
/sche context-slab: sy-cache
1 cells context-slab: sy-cands
2 cells context-slab: sy-todo
2 cells context-slab: sy-found
1 cells context-slab: sy-tcl
1 cells context-slab: sy-args
1 cells context-slab: sy-mvars
1 cells context-slab: sy-lv
1 cells context-slab: sy-tried

\ The slabs a search adds to, given back at its end (sy-leave), in the
\ order of syc-gens .. syc-tcl.
create sy-scoped ' sy-gens , ' sy-resume , ' sy-entries , ' sy-cnodes , ' sy-answers ,
  ' sy-cands , ' sy-tcl ,
7 constant sy-scoped#
: sy-scoped@ ( i -- slab ) cells sy-scoped + @ execute ;
: syc-count ( syc i -- addr ) cells swap syc-gens + ;
: sy-c ( -- syc ) sy-calls slab-last ;
: lf-synth-error ( -- code ) sy sy-error @ ;
: sy-refuse ( code -- -1 outcome ) dup sy sy-error ! lf-author-outcome -1 swap ;
: lf-synth-tried ( -- addr n ) sy-tried slab-base sy-tried slab-count ;
: sy-false ( x outcome -- false outcome ) nip false swap ;

\ ---- The metavariables and free variables of a term, each once, in the
\ order a walk from the left meets them (Lean's normExpr and
\ abstractExprMVars: a node's first part before its second, a constant's
\ universe arguments in order), as (leaf, kind) pairs on sy-found. The
\ walk takes (x, term or level) pairs off sy-todo, one budget step each.
0 constant sy-term   1 constant sy-level
2 constant sy-mvar   3 constant sy-lmvar   4 constant sy-fvar
: sy-todo+ ( x kind -- outcome ) sy-todo slab-2push ;
: sy-found@ ( k -- x kind ) sy-found slab-at 2@ ;
: sy-other? ( x kind k -- x kind flag ) sy-found@ 2over d= 0= ;
: sy-note ( x kind -- outcome )
  sy-found slab-count ['] sy-other? all? if sy-found slab-2push else 2drop outcome-ok
  then ;
: sy-parts ( t -- outcome )
  dup lf-term-second@ sy-term sy-todo+ ok-then? if lf-term-first@ sy-term sy-todo+ then ;
: sy-level-at ( addr n k -- addr n outcome )   \ the last level first
  >r 2dup r> - 1- lf-cref-pair@ drop sy-level sy-todo+ ;
: sy-levels ( const -- outcome )
  lf-term-first@ lf-cref-slot lf-cref-pairs dup ['] sy-level-at ok-each nip nip ;
: sy-sort-level ( sort -- outcome ) lf-term-first@ sy-level sy-todo+ ;
: sy-leaf ( t -- outcome )
  dup lf-term-tag@ case
    lf-tag-mvar of sy-mvar sy-note endof   lf-tag-fvar of sy-fvar sy-note endof
    lf-tag-constant of sy-levels endof   lf-tag-symbolic-sort of sy-sort-level endof
    nip outcome-ok swap endcase ;
: sy-level-two ( l -- outcome )
  dup lf-level-second@ sy-level sy-todo+ ok-then? if lf-level-first@ sy-level sy-todo+
  then ;
: sy-level-visit ( l -- outcome )
  dup lf-level-tag@ case
    lf-level-tag-succ of lf-level-first@ sy-level sy-todo+ endof
    lf-level-tag-max of sy-level-two endof   lf-level-tag-imax of sy-level-two endof
    lf-level-tag-mvar of sy-lmvar sy-note endof   nip outcome-ok swap endcase ;
: sy-term-visit ( t -- outcome ) dup lf-term-binary? if sy-parts else sy-leaf then ;
: sy-visit ( x kind -- flag outcome )
  lf-meta-spend? 0= if 2drop false outcome-exhausted exit then
  sy-term = if sy-term-visit else sy-level-visit then true swap ;
: sy-walk ( t -- outcome )   \ adds what t holds to sy-found
  sy-todo slab-clear sy-term sy-todo+ dup ok? 0= if exit then
  drop sy-todo ['] sy-visit slab-2all? nip ;
: sy-scan ( t -- outcome ) sy-found slab-clear sy-walk ;
\ What a scan found: a metavariable, term or level (hasMVar), a term one
\ (hasExprMVar), one of the search's depth (what abstractMVars keeps).
: sy-kind@ ( k -- kind ) sy-found@ nip ;
: sy-fvar-at? ( k -- flag ) sy-kind@ sy-fvar = ;
: sy-not-mvar-at? ( k -- flag ) sy-kind@ sy-mvar <> ;
: sy-found-all? ( xt -- flag ) sy-found slab-count swap all? ;
: sy-deep? ( x kind -- flag )
  case sy-mvar of lf-mvar-depth drop lf-mctx-depth = endof
    sy-lmvar of lf-level-mvar-depth lf-mctx-depth = endof  nip false swap endcase ;
: sy-shallow-at? ( k -- flag ) sy-found@ sy-deep? 0= ;
: sy-mvar? ( t -- flag outcome ) sy-scan ['] sy-fvar-at? sy-found-all? 0= swap ;
: sy-expr-mvar? ( t -- flag outcome ) sy-scan ['] sy-not-mvar-at? sy-found-all? 0= swap ;
: sy-deep-mvar? ( t -- flag outcome ) sy-scan ['] sy-shallow-at? sy-found-all? 0= swap ;

\ ---- Table keys (mkTableKey).
: sy-tc ( i -- t outcome ) sy-tc-base + lf-term-bvar room-result ;
: sy-tcl-new ( -- outcome ) lf-level-mvar-new ok-then? if sy-tcl slab-push then ;
: sy-tcl@ ( i -- level outcome )   \ the search's level placeholder i, made when new
  sy-c syc-tcl @ + dup sy-tcl slab-count = if sy-tcl-new dup ok? 0= if nip no-result exit
  then drop then sy-tcl slab-at @ outcome-ok ;
: sy-next ( addr -- i ) dup @ swap 1 swap +! ;
: sy-key-mvar ( m -- outcome )
  dup lf-mvar-assignable? 0= if drop outcome-ok exit then
  sy sy-keyed sy-next sy-tc ok-then? if lf-mvar-assign else nip then ;
: sy-key-lmvar ( l -- outcome )
  dup lf-level-mvar-depth lf-mctx-depth <> if drop outcome-ok exit then
  sy sy-lkeyed sy-next sy-tcl@ ok-then? if lf-level-mvar-assign else nip then ;
: sy-key-leaf ( k -- outcome )
  sy-found@ case sy-mvar of sy-key-mvar endof  sy-lmvar of sy-key-lmvar endof
    nip outcome-ok swap endcase ;
: sy-placed ( t -- key outcome )
  0 sy sy-keyed ! 0 sy sy-lkeyed ! sy-found slab-count ['] sy-key-leaf ok-each
  ok-then? if lf-instantiate-mvars else no-result then ;
: sy-key-marked ( t mark -- key outcome ) >r sy-placed r> lf-mctx-rollback outcome-and ;
: sy-key-made ( t -- key outcome ) lf-mctx-mark ok-then? if sy-key-marked else nip
  no-result
  then ;
: lf-synth-key ( type -- key outcome ) dup sy-scan ok-then? if sy-key-made else
  no-result then ;
: sy-key-for ( mvar -- key outcome )
  lf-mvar-type-instantiated ok-then? if lf-synth-key else no-result then ;

\ ---- The table: this search's entries (Lean's tableEntries), each a
\ goal's key with its waiters and answers as runs (lib/runs.fs), found by
\ Lean's Expr ==.
\ The first i in lo .. hi-1 whose test xt ( key i -- key flag outcome )
\ holds (the xt kept as an outer loop's index, read with J): i and true;
\ -1 and false when none does, or with the first failing test's outcome.
: sy-hit ( key lo hi xt -- i found? outcome )
  dup 1+ swap ?do swap ?do i j execute ok-then? 0= if nip -1 false rot unloop unloop
    exit then if drop i true outcome-ok unloop unloop exit then
  loop loop drop -1 false outcome-ok ;
: sen@ ( e -- addr ) sy-entries slab-at ;
: sy-entry-hit? ( key e -- key flag outcome ) sen@ se-key @ over lf-meta-eqv ;
: sy-find ( key -- e found? outcome )
  sy-c syc-entries @ sy-entries slab-count ['] sy-entry-hit? sy-hit ;
: sy-entry-new ( key waiter -- outcome )
  0 swap run-push ok-then? 0= if nip exit then
  1 sy-entries slab-claim ok-then? 0= if nip nip exit then
  sen@ tuck se-waiters ! tuck se-key ! 0 swap se-answers ! outcome-ok ;
: sy-run+ ( x addr -- outcome )   \ x at the end of the run at addr
  tuck @ swap run-push ok-then? if swap ! outcome-ok else nip then ;
: sy-wait ( waiter e -- outcome ) sen@ se-waiters sy-run+ ;

\ ---- Nodes.
: sgn@ ( g -- addr ) sy-gens slab-at ;
: scn@ ( c -- addr ) sy-cnodes slab-at ;
: san@ ( a -- addr ) sy-answers slab-at ;
: sy-gen-open ( key mvar snap -- g outcome )
  1 sy-gens slab-claim ok-then? 0= if nip nip nip no-result exit then
  dup >r sgn@ tuck sg-snap ! tuck sg-mvar ! sg-key ! r> outcome-ok ;
: sy-cnode-open ( key mvar -- c outcome )   \ size 0, no subgoal yet
  1 sy-cnodes slab-claim ok-then? 0= if nip nip no-result exit then
  dup >r scn@ dup /scon erase tuck sc-mvar ! sc-key ! r> outcome-ok ;
: sy-answer-new ( expr size -- a outcome )
  1 sy-answers slab-claim ok-then? 0= if nip nip no-result exit then
  dup >r san@ tuck sa-size ! sa-expr ! r> outcome-ok ;

\ ---- newSubgoal: the goal's candidates (getInstances) copied, a
\ generator and an entry with its first waiter; none of either when it
\ has no candidate. The goal must not be (or reduce to) a pi.
: sy-pi-free ( type -- outcome )
  dup lf-term-pi? if drop lfa-e-synth-pi sy-refuse nip exit then
  lf-meta-whnf ok-then? if lf-term-pi? if lfa-e-synth-pi sy-refuse nip else outcome-ok
  then
  then ;
: sy-cands-copy ( addr n -- first outcome )
  dup sy-cands slab-claim ok-then? 0= if nip nip no-result exit then
  dup >r sy-cands slab-at swap cells move r> outcome-ok ;
: sy-gen-cands ( g addr n -- outcome )
  dup >r sy-cands-copy ok-then? 0= if nip r> drop exit then
  over sgn@ sg-first ! r> swap sgn@ sg-idx ! outcome-ok ;
: sy-gen-goal ( g -- g type outcome )   \ instantiated, its metavariables noted
  dup sgn@ sg-mvar @ lf-mvar-type-instantiated ok-then? 0= if no-result exit then
  dup sy-mvar? ok-then? 0= if nip no-result exit then >r over r> swap sgn@ sg-open !
  outcome-ok ;
: sy-inst-code ( addr n outcome -- addr n outcome )   \ the table's code, when it set one
  dup ok? 0= lf-inst-error 0<> and if lf-inst-error sy sy-error ! then ;
: sy-gen-fill ( g -- outcome )
  sy-gen-goal ok-then? 0= if nip exit then dup sy-pi-free ok-then? 0= if nip exit then
  lf-inst-candidates sy-inst-code ok-then? if sy-gen-cands else nip nip then ;
: sy-gen-entry ( g waiter -- outcome )   \ when the goal had candidates, else dropped
  over sgn@ sg-idx @ if swap sgn@ sg-key @ swap sy-entry-new exit then
  2drop sy-gens slab-drop outcome-ok ;
: sy-new-subgoal ( key mvar snap waiter -- outcome )
  >r sy-gen-open ok-then? 0= if r> drop exit then
  dup sy-gen-fill ok-then? if r> sy-gen-entry else r> drop sy-gens slab-drop then ;

\ ---- addAnswer: mkAnswer (the consumer's metavariable instantiated; it
\ must keep nothing of the search's depth: 118), dropped at the size
\ limit; a new answer by its type (isNewAnswer) is kept and wakes the
\ entry's waiters.
: sy-answer-expr ( c -- expr outcome )
  scn@ sc-mvar @ lf-instantiate-mvars ok-then? 0= if no-result exit then
  dup sy-deep-mvar? ok-then? 0= if nip no-result exit then
  if drop lfa-e-synth-mvars sy-refuse else outcome-ok then ;
: sy-mk-answer ( c -- a outcome )
  dup sy-answer-expr ok-then? 0= if nip no-result exit then
  swap scn@ sc-size @ 1+ sy-answer-new ok-then? 0= if no-result exit then
  dup san@ sa-expr @ lf-infer ok-then? if over san@ sa-type ! outcome-ok else nip
  no-result then ;
: sy-other-type ( type a -- type new? outcome )   \ a's type is not type
  san@ sa-type @ over lf-meta-eqv ok-then? if 0= outcome-ok else false swap then ;
: sy-old-other ( type new? a -- type new? outcome )   \ none compared once one is equal
  swap if sy-other-type else drop false outcome-ok then ;
: sy-new-answer? ( a e -- flag outcome )   \ no older answer has its type
  sen@ se-answers @ swap san@ sa-type @ true rot ['] sy-old-other run-each rot drop ;
: sy-wake ( a waiter -- outcome )
  dup sy-root = if drop san@ sa-expr @ sy-c syc-result ! outcome-ok exit then
  swap sy-resume slab-2push ;
: sy-wake1 ( a waiter -- a outcome ) over swap sy-wake ;
: sy-wake-all ( a e -- outcome ) sen@ se-waiters @ ['] sy-wake1 run-each nip ;
: sy-add-new ( a e -- outcome )
  2dup sen@ se-answers sy-run+ ok-then? if sy-wake-all else nip nip then ;
: sy-add-checked ( a e -- outcome )
  2dup sy-new-answer? ok-then? 0= if nip nip exit then if sy-add-new else 2drop
  outcome-ok then ;
: sy-entry-of ( c -- e outcome )   \ the consumer's goal's entry, made with its generator
  scn@ sc-key @ sy-find ok-then? 0= if nip exit then 0= if drop -1 outcome-invalid else
  outcome-ok then ;
: sy-add-answer ( c -- outcome )
  dup scn@ sc-size @ lf-synth-max-size < 0= if drop outcome-ok exit then
  dup sy-entry-of ok-then? 0= if nip exit then
  swap sy-mk-answer ok-then? if swap sy-add-checked else nip then ;

\ ---- consume: in the consumer's state, its subgoals not yet assigned;
\ none left: an answer; else the first one's table entry, waited on, its
\ answers queued; or a new goal.
: sy-goals-left ( c -- outcome )
  dup scn@ sc-goals @ ['] lf-goal-unassigned? run-filter
  ok-then? if swap scn@ sc-goals ! outcome-ok else nip then ;
: sy-queue1 ( c a -- c outcome ) over swap sy-resume slab-2push ;
: sy-queue ( c e -- outcome )   \ every answer of e, in order, for the consumer
  sen@ se-answers @ ['] sy-queue1 run-each nip ;
: sy-known ( c e -- outcome ) 2dup sy-wait ok-then? if sy-queue else nip nip then ;
: sy-first ( c -- mvar ) scn@ sc-goals @ 0 run@ ;
: sy-unknown ( c key -- outcome )
  swap dup >r dup sy-first swap scn@ sc-snap @ r> sy-new-subgoal ;
: sy-waits ( c key -- outcome )
  dup sy-find ok-then? 0= if nip nip nip exit then
  if nip sy-known else drop sy-unknown then ;
: sy-next-goal ( c -- outcome ) dup sy-first sy-key-for ok-then? if sy-waits else nip
  then ;
: sy-consume ( c -- outcome )
  dup scn@ sc-snap @ lf-mctx-switch ok-then? if dup sy-goals-left ok-then? then
  0= if exit then dup scn@ sc-goals @ run-count if sy-next-goal else sy-add-answer then ;

\ ---- getSubgoals and tryResolve, with a consumer node c of the
\ generator's goal: the goal's body (forallTelescopeReducing: no pi), the
\ instance's value at new level metavariables and its type's body past a
\ natural metavariable for each binder (whnf where none is left), the
\ subgoals in its synthesis order, marked instance-typed; isDefEq of the
\ two bodies; the goal's metavariable assigned the value (mkLambdaFVars
\ of no binder), directly when the goal's body has no metavariable left,
\ else by isDefEq.
: sy-no2 ( outcome -- -1 -1 outcome ) -1 -1 rot ;
: sy-body! ( c -- outcome )
  dup scn@ sc-mvar @ lf-mvar-type 0= if drop outcome-invalid exit then
  dup sy-pi-free ok-then? if swap scn@ sc-body ! outcome-ok else nip then ;
: sy-binder-mvar ( pi -- pi m outcome )
  dup lf-term-first@ mv-natural lf-mvar-new ok-then? if dup sy-mvars slab-push else
  no-result
  then ;
: sy-binder ( val pi -- val' type outcome )
  sy-binder-mvar ok-then? 0= if nip nip sy-no2 exit then
  tuck lf-meta-open ok-then? 0= if nip nip sy-no2 exit then >r lf-meta-app r>
  swap ;
: sy-stop ( outcome -- -1 -1 false outcome ) sy-no2 false swap ;
: sy-inst-step ( val type -- val' type' more? outcome )
  dup lf-term-pi? if sy-binder true swap exit then
  lf-meta-whnf ok-then? 0= if nip sy-stop exit then
  dup lf-term-pi? if sy-binder true swap else false outcome-ok then ;
: sy-telescope ( val type -- val' body outcome )
  begin sy-inst-step ok-then? 0= if exit then while repeat outcome-ok ;
: sy-inst-val ( i -- val outcome )
  elab-instance@ 2drop lf-menv-of-data ok-then? if lf-meta-const-fresh else no-result
  then ;
: sy-inst-type ( i -- val type outcome ) sy-inst-val ok-then? if dup lf-infer else
  sy-no2 then ;
: sy-val! ( val body c -- ) scn@ tuck sc-ibody ! sc-val ! ;
: sy-inst! ( c i -- outcome )   \ getSubgoals: the value and the type's body
  sy-mvars slab-clear sy-inst-type ok-then? if sy-telescope ok-then? if
    rot sy-val! outcome-ok exit then then nip nip ;
: sy-goal-at ( run k order -- run' outcome )   \ the k-th of the order, marked
  swap cells + @ dup sy-mvars slab-count index? 0= if drop outcome-invalid exit then
  sy-mvars slab-at @ dup lf-mvar-mark-inst ok-then? if run-push else nip then ;
: sy-goals! ( c i -- outcome )
  0 swap elab-instance-order swap ['] sy-goal-at ok-fold
  ok-then? if swap scn@ sc-goals ! outcome-ok else nip then ;
: sy-prepare ( c i -- outcome )
  over sy-body! ok-then? 0= if nip exit then 2dup sy-inst! ok-then? 0= if nip exit then
  sy-goals! ;
: sy-direct? ( c -- flag outcome )   \ the goal's body, instantiated, has no metavariable
  scn@ sc-body @ lf-instantiate-mvars ok-then? if sy-expr-mvar? swap 0= swap else false
  swap
  then ;
: sy-goal-val ( c -- mvar val ) scn@ dup sc-mvar @ swap sc-val @ ;
: sy-assign ( c -- flag outcome )
  dup sy-direct? ok-then? 0= if sy-false exit then
  if sy-goal-val lf-mvar-assign true swap else sy-goal-val lf-meta-defeq then ;
: sy-unify ( c -- flag outcome ) scn@ dup sc-body @ swap sc-ibody @ lf-meta-defeq ;
: sy-resolve ( c i -- flag outcome )
  over swap sy-prepare dup ok? 0= if sy-false exit then drop
  dup sy-unify ok-then? 0= if sy-false exit then if sy-assign else drop false outcome-ok
  then ;

\ ---- generate: the newest generator's next candidate, from the last,
\ tried in its state (S1 §9: a left-out or unverified one answers
\ unsupported then); none left, or canonInstances, pops it.
: sy-candidate ( v -- outcome )
  dup sy-tried slab-push ok-then? 0= if exit then
  dup lf-inst-left-out? if drop lfa-e-synth-left-out sy-refuse nip exit then
  lf-inst-verified? if outcome-ok else lfa-e-synth-unchecked sy-refuse nip then ;
: sy-canon? ( g -- flag outcome )   \ a goal without metavariables that has an answer
  sgn@ dup sg-open @ if drop false outcome-ok exit then
  sg-key @ sy-find ok-then? 0= if sy-false exit then
  if sen@ se-answers @ run-count 0<> else drop false then outcome-ok ;
: sy-candidate-at ( g -- v ) sgn@ dup sg-first @ swap sg-idx @ + sy-cands slab-at @ ;
: sy-cnode-of ( g -- c outcome ) dup sgn@ sg-key @ swap sgn@ sg-mvar @ sy-cnode-open ;
: sy-snap! ( c -- outcome ) lf-mctx-snapshot ok-then? if swap scn@ sc-snap ! outcome-ok
  else nip
  then ;
: sy-resolved ( c flag outcome -- outcome )   \ consume on true
  ok-then? 0= if nip exit then 0= if drop outcome-ok exit then
  dup sy-snap! dup ok? if drop sy-consume else nip then ;
: sy-try-next ( g -- outcome )
  dup sgn@ -1 swap sg-idx +! dup sgn@ sg-snap @ lf-mctx-switch ok-then? 0= if exit then
  dup sy-candidate-at dup sy-candidate ok-then? 0= if nip exit then
  swap sy-cnode-of ok-then? 0= if nip exit then tuck swap sy-resolve sy-resolved ;
: sy-pop-gen ( -- outcome ) sy-gens slab-drop outcome-ok ;
: sy-generate ( -- outcome )
  sy-gens slab-count 1- dup sgn@ sg-idx @ 0= if drop sy-pop-gen exit then
  dup sy-canon? ok-then? 0= if nip exit then if drop sy-pop-gen else sy-try-next then ;

\ ---- resume: the newest (consumer, answer): in the consumer's state the
\ answer against its next subgoal (tryAnswer); then consume a node of its
\ goal with the other subgoals, the sizes added.
: sy-answer-to ( c a -- flag outcome )
  over scn@ sc-snap @ lf-mctx-switch dup ok? 0= if nip nip false swap exit then drop
  san@ sa-expr @ swap sy-first swap lf-meta-defeq ;
: sy-after ( c' c -- c' outcome )   \ c's subgoals but the first, the state now
  scn@ sc-goals @ 1 run-after ok-then? if over scn@ sc-goals ! dup sy-snap! then ;
: sy-next-node ( c a -- c' outcome )
  san@ sa-size @ over scn@ sc-size @ + over scn@ dup sc-key @ swap sc-mvar @ sy-cnode-open
  ok-then? 0= if nip nip no-result exit then tuck scn@ sc-size ! swap sy-after ;
: sy-resume-one ( -- outcome )
  sy-resume slab-2pop 2dup sy-answer-to ok-then? 0= if nip nip exit then
  if sy-next-node ok-then? if sy-consume then else 2drop outcome-ok then ;

\ ---- synth and main.
: sy-above? ( slab base -- flag ) swap slab-count < ;
: sy-step ( -- more? outcome )
  lf-meta-spend? 0= if false outcome-exhausted exit then
  sy-resume sy-c syc-resume @ sy-above? if sy-resume-one true swap exit then
  sy-gens sy-c syc-gens @ sy-above? if sy-generate true swap else false outcome-ok then ;
: sy-done? ( -- flag ) sy-c syc-result @ 0< 0= ;
: sy-synth ( -- outcome )
  begin sy-done? if outcome-ok exit then sy-step ok-then? 0= if exit then 0= until
  outcome-ok ;
: sy-root-goal ( type -- key mvar outcome )
  dup mv-natural lf-mvar-new ok-then? 0= if nip sy-no2 exit then
  swap lf-synth-key ok-then? if swap outcome-ok else nip sy-no2 then ;
: sy-main ( type -- outcome )
  sy-root-goal ok-then? 0= if nip exit then lf-mctx-snapshot ok-then? 0= if nip nip exit
  then
  dup sy-c syc-snap ! sy-root sy-new-subgoal ['] sy-synth ok-and ;

\ ---- preprocessOutParam and the cache key: the class's out-parameter
\ arguments and out-levels replaced, by new metavariables or wildcards.
\ The spine's arguments are on sy-args (the last first), the head's
\ levels on sy-lv.
: sy-head-class ( type -- k true | false )   \ the class record of a head with arguments
  dup lf-term-const? if drop false exit then
  lf-meta-head lf-dt-const? if lf-dt-const-decl if elab-class-of exit then then false ;
: sy-outs? ( k -- flag ) dup elab-class-out-params nip swap elab-class-out-levels nip or
  0<> ;
: sy-arg-addr ( i -- addr ) sy-args slab-count 1- swap - sy-args slab-at ;
: sy-app-arg ( f k y -- f' outcome ) drop sy-args lf-meta-arg lf-meta-app ;
: sy-rebuild ( head -- t outcome ) sy-args slab-count 0 ['] sy-app-arg ok-fold ;
: sy-lv-put ( xt j addr -- xt outcome )   \ out-level addr[j] the xt's new level
  swap cells + @ dup sy-lv slab-count index? 0= if drop outcome-invalid exit then
  over execute ok-then? if swap sy-lv slab-at ! outcome-ok else nip then ;
: sy-relevel ( k xt -- outcome )
  swap elab-class-out-levels swap ['] sy-lv-put ok-fold nip ;
: sy-renamed ( head -- head' outcome )   \ its name at sy-lv's levels
  lf-term-first@ lf-cref-slot lf-cref-name@ sy-lv slab-base sy-lv slab-count
  lf-meta-const-at ;
: sy-new-head ( head k xt -- head' outcome )
  >r over sy-lv lf-meta-levels-fill ok-then? 0= if
    r> drop nip no-result exit then
  r> sy-relevel ok-then? if sy-renamed else no-result then ;
\ preprocessOutParam's arguments: the class's type walked with whnf, an
\ out-parameter a new metavariable of its binder's type (invalid 111 when
\ the type has no binder left).
: sy-pi-whnf ( ctype -- pi outcome )
  lf-meta-whnf ok-then? 0= if no-result exit then
  dup lf-term-pi? if outcome-ok else drop lfa-e-synth-args sy-refuse then ;
: sy-out? ( i k -- flag ) elab-class-out-params cells-has? ;
: sy-out-mvar ( pi i -- arg outcome )
  swap lf-term-first@ mv-natural lf-mvar-new ok-then? if tuck swap sy-arg-addr !
  outcome-ok
  else nip no-result then ;
: sy-arg-for ( pi i k -- arg outcome )
  over swap sy-out? if sy-out-mvar else nip sy-args lf-meta-arg outcome-ok then ;
: sy-out-arg ( ctype i k -- ctype' outcome )
  rot sy-pi-whnf ok-then? 0= if nip nip no-result exit then
  dup >r -rot sy-arg-for ok-then? if r> swap lf-meta-open else r> drop no-result then ;
: sy-out-args ( head k -- t outcome )
  over lf-infer ok-then? 0= if nip nip no-result exit then
  swap sy-args slab-count swap ['] sy-out-arg ok-fold ok-then? if drop sy-rebuild else nip
  no-result then ;
: sy-fresh-level ( -- level outcome ) lf-level-mvar-new ;
: sy-out-type ( type k -- type' outcome )
  swap sy-args lf-meta-spine ok-then? 0= if nip no-result exit then
  over ['] sy-fresh-level sy-new-head ok-then? 0= if nip no-result exit then
  swap dup elab-class-out-params nip if sy-out-args else drop sy-rebuild then ;
: sy-out-param ( type -- type' outcome )   \ preprocessOutParam
  dup sy-head-class 0= if outcome-ok exit then
  dup sy-outs? if sy-out-type else drop outcome-ok then ;
\ The cache key's wildcards (Lean's __wild__).
: sy-wild ( -- t outcome ) sy-tc-base 1- lf-term-bvar room-result ;
: sy-wild-level ( -- level outcome )
  0 s" __wild__" lf-name-str if lf-level-param room-result else -1 outcome-full then ;
: sy-wild-at ( addr j -- addr outcome )
  over swap cells + @ dup sy-args slab-count index? 0= if drop outcome-ok exit then
  sy-wild ok-then? if swap sy-arg-addr ! outcome-ok else nip then ;
: sy-wild-args ( k -- outcome ) elab-class-out-params ['] sy-wild-at ok-each nip ;
: sy-wild-key ( type k -- ckey outcome )
  swap sy-args lf-meta-spine ok-then? 0= if nip no-result exit then
  over ['] sy-wild-level sy-new-head ok-then? 0= if nip no-result exit then
  swap sy-wild-args ok-then? if sy-rebuild else no-result then ;

\ ---- preprocess: the goal whnf (no pi: 117), its kind and cache key.
: sy-goal-whnf ( type -- type' outcome )
  dup sy-pi-free ok-then? if lf-meta-whnf else no-result then ;
: sy-kinded ( ckey kind -- outcome ) sy-c syc-kind ! sy-c syc-ckey ! outcome-ok ;
: sy-mvar-kind ( type -- outcome )
  dup sy-head-class if dup sy-outs? if sy-wild-key ok-then? if sy-outs sy-kinded then exit
  then drop then sy-plain sy-kinded ;
: sy-preprocess ( type -- outcome )
  lf-instantiate-mvars ok-then? if sy-goal-whnf else no-result then ok-then? 0= if exit
  then
  dup sy-c syc-type ! dup sy-mvar? ok-then? 0= if nip exit then
  if sy-mvar-kind else sy-no-mvars sy-kinded then ;

\ ---- The cache: entries of this context's epoch, by key type and
\ synthPendingDepth; used only when the context has no local instance.
: skn@ ( i -- addr ) sy-cache slab-at ;
: sy-local-free? ( view i -- view flag ) over swap lf-view-local lf-local-class 0= ;
: sy-cache-ok? ( -- flag )
  lf-mctx-view dup lf-view-valid? 0= if drop false exit then
  dup lf-view-count ['] sy-local-free? all? nip ;
: sy-cache-fresh ( -- )
  mctx-epoch@ sy sy-epoch @ <> if sy-cache slab-clear mctx-epoch@ sy sy-epoch ! then ;
: sy-cache-hit? ( key i -- key flag outcome )
  skn@ dup sk-depth @ sy sy-pending @ = if sk-type @ over lf-meta-eqv else drop false
  outcome-ok then ;
: sy-cache-find ( key -- i found? outcome )
  0 sy-cache slab-count ['] sy-cache-hit? sy-hit ;
: sy-cache-result ( i -- r ) skn@ sk-result @ ;
: sy-cache-lookup ( -- i found? outcome )   \ the entry
  sy-cache-ok? 0= if -1 sy-c syc-ckey ! then sy-cache-fresh
  sy-c syc-ckey @ dup 0< if false outcome-ok exit then sy-cache-find ;
: sy-cache-put ( r -- outcome )   \ cacheResult
  sy-c syc-ckey @ 0< if drop outcome-ok exit then
  1 sy-cache slab-claim ok-then? 0= if nip exit then
  skn@ tuck sk-result ! sy-c syc-ckey @ over sk-type ! sy sy-pending @ swap sk-depth !
  outcome-ok ;
\ cacheResult's value: with out-parameters the answer, else the result.
: sy-cache-value ( inst -- r ) sy-c syc-kind @ sy-outs = if drop sy-c syc-result @ then ;

\ ---- applyAbstractResult? and applyCachedAbstractResult?: the answer
\ (none: -1) opened (it keeps nothing of the search: the identity),
\ assignOutParams, the result instantiated and, unless cached, Lean's
\ check where it may have effects (checkMayHaveSideEffects: a
\ metavariable in the result or in the types or values of its free
\ variables, followed through them): not ported (121).
: sy-none ( outcome -- -1 false outcome ) -1 false rot ;
: sy-assign-outs ( result -- flag outcome )
  lf-infer ok-then? 0= if false swap exit then
  sy-c syc-type @ swap ['] lf-meta-defeq lf-defeq-flags lf-defeq-opaque or lf-tr-default
  lf-meta-with ;
: sy-inst-walk ( t -- outcome ) lf-instantiate-mvars ok-then? if sy-walk then ;
: sy-fvar-walk ( fvar -- outcome )
  dup lf-fvar-type sy-inst-walk ok-then? 0= if exit then
  dup lf-fvar-let? if lf-fvar-value sy-inst-walk else drop outcome-ok then ;
: sy-closure-at ( k -- outcome ) sy-found@ sy-fvar = if sy-fvar-walk else drop
  outcome-ok then ;
: sy-closure ( -- outcome )   \ sy-found grows as the free variables are followed
  0 begin dup sy-found slab-count < while dup sy-closure-at dup ok? 0= if nip exit then
  drop 1+ repeat drop outcome-ok ;
: sy-effects? ( result -- flag outcome )
  sy-scan dup ok? if drop sy-closure then dup ok? 0= if false swap exit then
  drop ['] sy-fvar-at? sy-found-all? 0= outcome-ok ;
: sy-checked ( r -- inst flag outcome )
  dup sy-effects? ok-then? 0= if nip sy-none exit then
  if drop lfa-e-synth-check sy-refuse false swap else true outcome-ok then ;
: sy-apply ( result -- inst flag outcome )
  dup 0< if false outcome-ok exit then dup sy-assign-outs ok-then? 0= if nip sy-none
  exit then
  0= if drop -1 false outcome-ok exit then
  lf-instantiate-mvars ok-then? if sy-checked else sy-none then ;
: sy-apply-cached ( r -- inst flag outcome )
  dup 0< if false outcome-ok exit then dup sy-assign-outs ok-then? 0= if nip sy-none
  exit then
  if true outcome-ok else drop -1 false outcome-ok then ;
: sy-cache-after ( inst flag outcome -- inst flag outcome )
  dup ok? 0= if exit then drop over sy-cache-value sy-cache-put ;

\ ---- synthInstanceCore?: the search one depth deeper (main of the goal,
\ its out-parameters made new unless it has metavariables and no
\ out-parameter), the answer applied and cached.
: sy-search-type ( -- type outcome )
  sy-c syc-type @ sy-c syc-kind @ sy-plain = if outcome-ok else sy-out-param then ;
: sy-deep ( -- outcome ) sy-search-type ok-then? if sy-main then ;
: sy-search ( -- outcome )
  true lf-mctx-depth{ ok-then? 0= if exit then >r sy-deep r> }lf-mctx-depth outcome-and ;
: sy-miss ( -- inst flag outcome )
  sy-search dup ok? 0= if sy-none exit then drop sy-c syc-result @ sy-apply
  sy-cache-after ;
: sy-core ( type -- inst flag outcome )
  sy-preprocess dup ok? 0= if sy-none exit then drop
  sy-cache-lookup ok-then? 0= if nip sy-none exit then
  if sy-cache-result sy-apply-cached else drop sy-miss then ;

\ ---- A search's call: its record, the slabs' counts at its start; at
\ its end everything it added given back.
: sy-counts! ( syc -- )
  sy-scoped# 0 do i sy-scoped@ slab-count over i syc-count ! loop drop ;
: sy-enter ( -- outcome )
  sy-calls slab-count 0= if sy-tried slab-clear then
  1 sy-calls slab-claim ok-then? 0= if exit then drop
  sy-c dup /syc erase -1 over syc-result ! -1 over syc-ckey ! sy-counts! outcome-ok ;
: sy-leave ( -- )
  sy-c sy-scoped# 0 do dup i syc-count @ i sy-scoped@ slab-cut loop drop
  sy-calls slab-drop ;
: sy-flags ( -- flags )
  lf-defeq-flags lf-defeq-stuck or lf-defeq-fo or lf-defeq-ctx or
  lf-defeq-const lf-defeq-univ or invert and ;
: lf-synth-instance ( type -- inst flag outcome )
  0 sy sy-error ! sy-enter dup ok? 0= if nip sy-none exit then drop
  ['] sy-core sy-flags lf-tr-instances lf-meta-with sy-leave ;

\ ---- trySynthInstance and synthPendingImp.
: lf-try-synth ( type -- inst code outcome )
  lf-meta-synth dup lf-meta-stuck = if drop 2drop -1 lf-synth-undef outcome-ok exit then
  dup ok? 0= if nip lf-synth-none swap exit then drop
  if lf-synth-some else lf-synth-none then outcome-ok ;
: sy-opaque? ( mvar -- flag outcome )
  lf-mvar-kind if mv-opaque = outcome-ok else false outcome-invalid then ;
: sy-class-type? ( mvar -- flag outcome )
  lf-mvar-type drop lf-class? ok-then? if if drop true else false then outcome-ok else
  false swap then ;
: sy-pending-ok? ( mvar -- flag outcome )   \ synthPendingImp's tests
  dup sy-opaque? ok-then? 0= if sy-false exit then if drop false outcome-ok exit then
  sy-class-type? ok-then? if sy sy-pending @ lf-synth-max-pending > 0= and outcome-ok else
  false swap then ;
: sy-in-view ( type view -- inst flag outcome )
  lf-mctx-view >r lf-mctx-view! lf-synth-instance r> lf-mctx-view! ;
: sy-pending-synth ( mvar -- inst flag outcome )   \ one synthPending deeper; stuck: none
  1 sy sy-pending +! dup lf-mvar-type drop swap lf-mvar-view drop sy-in-view
  -1 sy sy-pending +! dup lf-meta-stuck = if drop 2drop -1 false outcome-ok then ;
: sy-fill ( mvar inst -- flag outcome )   \ unless it was assigned meanwhile
  over lf-mvar-value if drop 2drop false outcome-ok else lf-mvar-assign true swap then ;
: lf-synth-pending ( mvar -- flag outcome )
  dup sy-pending-ok? ok-then? 0= if sy-false exit then 0= if drop false outcome-ok exit
  then
  dup sy-pending-synth ok-then? 0= if nip nip false swap exit then
  if sy-fill else 2drop false outcome-ok then ;

' lf-synth-instance is lf-meta-synth
' lf-synth-pending is lf-meta-synth-pending

base !   \ the BASE this file was loaded with
