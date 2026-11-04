\ Definitional equality as Lean's kernel decides it (ADR 0014 Q1, Q3;
\ plan task 4.2.2b): ports of quick_is_def_eq (type_checker.cpp
\ 802-826), is_def_eq_binding (752-779), is_def_eq_app (878-895),
\ is_def_eq_args (830-838) and the steps of is_def_eq_core (1132-1207)
\ that LeanForth has, at the referee commit eb6cafb7 (ADR 0014,
\ Reproduction). [kernel] code: experimental, not through the review
\ gate, not independently audited.
\
\ Answers. A comparison answers yes or no, as Lean's is_def_eq, or fails:
\ unknown where a step Lean would take is not ported (each named below),
\ exhausted, full or invalid. A failure anywhere ends the whole
\ comparison with it (ADR 0014 Q1): the port never goes on as if a
\ sub-step had answered no.
\ - quick_is_def_eq: yes when the terms are equal by Lean's == (mixed-
\   compare.fs, lf-expr-equal); two lambdas or two Pis by
\   is_def_eq_binding; two Sorts by Lean's is_equivalent on their levels
\   (level-compare.fs, ADR 0011 Amendment 1); otherwise undecided. Lean's
\   success cache (succeeded_before, 804) waits for plan task 4.2.7: it
\   changes no answer, since is_def_eq is a function of its arguments
\   (type_checker.h 33-39).
\ - is_def_eq_binding walks both telescopes while both are binders of the
\   first's kind: a pair of domains that are not == must be is_def_eq
\   (else no), the domains read with the free variables of the binders
\   before (instantiate_rev); each binder then gets a free variable of the
\   right side's domain (ADR 0003 Amendment 1, B2); then the bodies.
\   Where neither body uses its bound variable Lean puts the placeholder
\   dontcare instead (772): no later domain or body then mentions that
\   binder, so the placeholder is never substituted and the free variable
\   LeanForth always makes gives the same terms (without the loose-
\   variable data Lean tests, ADR 0014 Q12).
\ - is_def_eq_core (1132-1207), in Lean's order: (1) quick_is_def_eq
\   decides yes or no; (2) the Bool.true test is skipped: it only ever
\   answers yes, after unfolding (K7, plan task 4.2.2d); (3) whnf_core of
\   both sides (whnf.fs) and, when either changed, quick_is_def_eq again;
\   then the steps that can only answer yes, on the reduced terms: (6)
\   the same constant with equivalent universe arguments, (7) the same
\   free variable, (10) is_def_eq_app. When none says yes the answer is
\   unknown (diagnostic 30, the two terms): proof irrelevance (4, plan
\   task 4.2.5), lazy delta reduction (5, task 4.2.2d), eta (11, task
\   4.2.4), structure eta and unit-like types (12, 14, task 5.2.2) may
\   decide there, and only after them would Lean say no (15). Skipping
\   steps 4 and 5 here is sound for a yes: steps 6, 7 and 10 answer yes
\   only for terms equal up to beta and universe equivalence, which Lean
\   finds equal whatever route it takes (ADR 0003, the argument
\   conversion has always rested on). A whnf_core that is unknown (a
\   recursor at the head, whnf.fs) leaves that side unreduced for those
\   steps, as the old conversion compared it, and never lets step 3 say
\   no.
\ - is_def_eq_app: both applications, the functions is_def_eq and the
\   argument counts equal, then the arguments left to right; the first
\   pair that is not equal ends it, false. is_def_eq_args: the arguments
\   last first, then both spines must end together (lazy delta's same-
\   head test, plan task 4.2.2d; here for its unit tests).
\
\ Passes. Every comparison is a visit on a frames record that the caller
\ gives (lib/frame.fs), as in whnf.fs: lf-defeq-call ( t s frames cont
\ -- ... frames next ), cont getting ( flag outcome frames ), and
\ lf-defeq-on ( t s frames -- flag outcome ) runs one to its end as a
\ loop of its own. Each visit costs one unit of the frames' fuel, as does
\ each binder pair of a telescope and each argument pair beyond a visit's
\ first; == (one unit per node visited), level comparisons and the
\ substitutions are paid from it too. Inputs must be closed audited terms
\ whose free variables are live; the nodes, free variables and local
\ context entries a comparison makes stay for the caller to discard
\ (mixed-convert.fs restores the stores and drops them).
\
\ State: the free variables of the telescopes being compared, a growable
\ array used as a stack (each is_def_eq_binding visit pushes its binders'
\ and pops them when it ends, whatever its outcome), and its depth, in
\ one record; both members of the checker context (lib/context.fs). A
\ THROW out of a pass leaves the depth wrong: lf-defeq-reset empties it.
\ A few steps are deferred only so that words defined before them can
\ name them; they are set once, while loading.

require ../lib/lib.fs
require ../lib/slab.fs
require ../core/diagnostics.fs
require ../core/local-context.fs
require ../core/names.fs
require ../core/name-equal.fs
require ../core/terms.fs
require ./level-compare.fs
require ./mixed-compare.fs
require ./mixed-head.fs
require ./mixed-open.fs
require ./whnf.fs

begin-structure /lf-dqs
  field: lf-dqs-depth        \ free variables on the stack below
end-structure
/lf-dqs context-record: lf-dq-state
1 cells context-slab: lf-dq-subst

: lf-dq-site ( -- site ) c" defeq lf-defeq" ;
: lf-dq-depth ( -- addr ) lf-dq-state lf-dqs-depth ;
\ Recovery after a THROW out of a pass: an empty stack.
: lf-defeq-reset ( -- ) 0 lf-dq-depth ! ;

\ Lean's lbool: yes 1, no 0, undecided -1. quick_is_def_eq answers one.
1 constant lf-dq-yes
0 constant lf-dq-no
-1 constant lf-dq-undef
: lf-dq-flag ( lbool -- flag ) lf-dq-yes = ;
: lf-dq-lbool ( flag -- lbool ) if lf-dq-yes else lf-dq-no then ;

\ ---------------------------------------------------------------------------
\ Opening visits of two terms: when the frames admit it (fuel, then
\ room); a refused one continues at once with 0 and the outcome,
\ recorded as a diagnostic. A step ends its visit with ( x outcome frames
\ 0 ); a failure's x is no answer.
: lf-dq-refused ( t s frames cont outcome -- 0 outcome frames cont )
  >r over r@ swap lf-dq-site lf-diag-frames drop 2swap 2drop 0 r> 2swap ;
: lf-dq-open ( t s frames cont xt -- ... frames next )
  >r over frame-admit dup ok? if drop r> frame-open else r> drop lf-dq-refused then ;
: lf-dq-failed ( outcome frames -- 0 outcome frames 0 ) >r 0 swap r> 0 ;
: lf-dq-answer ( flag frames -- flag outcome frames 0 ) outcome-ok swap 0 ;
\ Ending a visit that saved n cells: they are dropped first.
: lf-dq-drop-failed ( outcome frames n -- 0 outcome frames 0 )
  over frame-drop lf-dq-failed ;
: lf-dq-drop-answer ( flag frames n -- flag outcome frames 0 )
  over frame-drop lf-dq-answer ;
\ Going on within the same visit costs one unit of fuel.
: lf-dq-spend ( frames -- outcome )
  dup frame-fuel @ 0> if -1 swap frame-fuel +! outcome-ok exit then
  lf-dq-site lf-diag-frames-fuel outcome-exhausted ;
\ Two terms kept across a child's visit, t below s.
: lf-dq-save2 ( t s frames -- t s frames ) >r 2dup swap r@ frame-save r@ frame-save r> ;
: lf-dq-pick2 ( frames -- t s ) dup 1 swap frame-pick swap 0 swap frame-pick ;
\ The frames' fuel lent to a pass that keeps its own, and taken back.
: lf-dq-lend ( frames addr -- ) swap frame-fuel @ swap ! ;
: lf-dq-repay ( frames addr -- ) @ swap frame-fuel ! ;

\ ---------------------------------------------------------------------------
\ Leaves of the comparison, each paid from the frames' fuel.
\ Lean's ==, recording nothing when the terms differ.
: lf-dq-same ( t s frames -- flag outcome )
  >r r@ frame-fuel @ lf-expr-equal r> lf-mcompare-fuel lf-dq-repay ;
\ is_def_eq(level, level), Lean's is_equivalent (781-787) on level-
\ compare's fuel: yes, no (an undecided comparison that level-compare.fs
\ found apart), or a failure; names it cannot order are unknown.
: lf-dq-level-answer ( outcome -- flag outcome )
  dup ok? if drop true outcome-ok exit then
  dup outcome-unknown = lf-lcmp-apart @ and if drop false outcome-ok exit then
  false swap ;
\ An answer, yes or no, leaves the diagnostic as it was (level-compare.fs
\ notes a difference): Lean's no is no failure.
: lf-dq-level-eq ( l1 l2 -- flag outcome )
  lf-diag@ 2>r 2>r lf-lcmp-fuel @ true lf-level-compare-run lf-dq-level-answer
  dup ok? if 2r> 2r> lf-diag! else 2r> 2r> 2drop 2drop then ;
: lf-dq-levels ( l1 l2 frames -- flag outcome )
  >r r@ lf-lcmp-fuel lf-dq-lend lf-dq-level-eq r> lf-lcmp-fuel lf-dq-repay ;
\ is_def_eq(levels, levels) (789-799): the same number, each pair
\ equivalent, the first that is not ends it. Unchecked: the arrays are
\ two constants' reference pairs, which no level comparison moves.
: lf-dq-level-pairs ( ta sa n -- flag outcome )
  0 ?do over i lf-cref-pair@ drop over i lf-cref-pair@ drop lf-dq-level-eq
    ok-then? 0= if nip nip false swap unloop exit then
    0= if 2drop false outcome-ok unloop exit then
  loop 2drop true outcome-ok ;
: lf-dq-level-lists ( t s -- flag outcome )
  lf-whnf-cref lf-cref-pairs rot lf-whnf-cref lf-cref-pairs
  rot over <> if 2drop drop false outcome-ok exit then
  >r swap r> lf-dq-level-pairs ;

\ The node kinds the steps test.
: lf-dq-tag ( node -- tag ) lf-term-tag@ ;
: lf-dq-tags? ( t s -- flag ) lf-dq-tag swap lf-dq-tag = ;
: lf-dq-binder? ( node -- flag ) lf-dq-tag dup lf-tag-lam = swap lf-tag-pi = or ;
: lf-dq-app? ( node -- flag ) lf-dq-tag lf-tag-app = ;
: lf-dq-apps? ( t s -- flag ) lf-dq-app? swap lf-dq-app? and ;
: lf-dq-both? ( t s tag -- flag ) tuck swap lf-dq-tag = -rot swap lf-dq-tag = and ;
: lf-dq-count ( node -- n ) lf-mhead-spine nip ;

\ Step 6 (1170-1172): two constants of the same name whose universe
\ arguments are equivalent; on level-compare's fuel.
: lf-dq-names? ( t s -- flag )
  lf-whnf-cref lf-crec-name @ swap lf-whnf-cref lf-crec-name @ lf-name-same? ;
: lf-dq-consts ( t s frames -- flag outcome )
  >r 2dup lf-tag-constant lf-dq-both? 0= if 2drop r> drop false outcome-ok exit then
  2dup lf-dq-names? 0= if 2drop r> drop false outcome-ok exit then
  r@ lf-lcmp-fuel lf-dq-lend lf-dq-level-lists r> lf-lcmp-fuel lf-dq-repay ;
\ Step 7 (1174-1175): the same free variable (one node per entry).
: lf-dq-fvars? ( t s -- flag )
  2dup lf-tag-fvar lf-dq-both? if lf-term-first@ swap lf-term-first@ = else 2drop false then ;

\ ---------------------------------------------------------------------------
\ The visits refer to each other; each is set once below.
defer lf-dq-visit ( t s frames -- ... frames next )
defer lf-qk-visit ( t s frames -- ... frames next )
defer lf-bd-visit ( t s frames -- ... frames next )
defer lf-ap-visit ( t s frames -- ... frames next )
defer lf-ar-visit ( t s frames -- ... frames next )
: lf-dq-call ( t s frames cont -- ... frames next ) ['] lf-dq-visit lf-dq-open ;
: lf-qk-call ( t s frames cont -- ... frames next ) ['] lf-qk-visit lf-dq-open ;
: lf-bd-call ( t s frames cont -- ... frames next ) ['] lf-bd-visit lf-dq-open ;
: lf-ap-call ( t s frames cont -- ... frames next ) ['] lf-ap-visit lf-dq-open ;
: lf-ar-call ( t s frames cont -- ... frames next ) ['] lf-ar-visit lf-dq-open ;

\ ---------------------------------------------------------------------------
\ quick_is_def_eq (802-826): ( lbool outcome ).
: lf-qk-bound ( flag outcome frames -- lbool outcome frames 0 )
  >r dup ok? if swap lf-dq-lbool swap then r> 0 ;
: lf-qk-sorts ( t s frames -- lbool outcome frames 0 )
  >r lf-term-first@ swap lf-term-first@ swap r@ lf-dq-levels
  ok-then? if lf-dq-lbool outcome-ok else lf-dq-undef swap then r> 0 ;
: lf-qk-undecided ( t s frames -- lbool outcome frames 0 )
  >r 2drop lf-dq-undef outcome-ok r> 0 ;
: lf-qk-kinds ( t s frames -- ... frames next )
  >r 2dup lf-dq-tags? 0= if r> lf-qk-undecided exit then
  over lf-dq-binder? if r> ['] lf-qk-bound lf-bd-call exit then
  over lf-dq-tag lf-tag-symbolic-sort = if r> lf-qk-sorts else r> lf-qk-undecided then ;
:noname ( t s frames -- ... frames next )
  >r 2dup r@ lf-dq-same ok-then? 0= if nip nip lf-dq-undef swap r> 0 exit then
  if 2drop lf-dq-yes outcome-ok r> 0 else r> lf-qk-kinds then ; is lf-qk-visit

\ ---------------------------------------------------------------------------
\ is_def_eq_binding (752-779). The visit keeps the stack's depth when it
\ began (base) and the telescope's kind below everything else it saves,
\ and pops its free variables on every way out (lf-bd-done).
: lf-bd-base ( frames -- base ) 1 swap frame-pick ;
: lf-bd-kind ( frames -- tag ) 0 swap frame-pick ;
: lf-bd-done ( x outcome frames -- x outcome frames 0 )
  dup lf-bd-base lf-dq-depth ! 2 over frame-drop 0 ;
: lf-bd-fail ( outcome frames -- 0 outcome frames 0 ) >r 0 swap r> lf-bd-done ;
: lf-bd-false ( frames -- false outcome frames 0 ) >r false outcome-ok r> lf-bd-done ;
\ A domain or body with the visit's free variables put for its loose
\ bound variables (instantiate_rev), on the frames' fuel.
: lf-bd-subst ( base -- addr n ) dup lf-dq-subst slab-at swap lf-dq-depth @ swap - ;
: lf-bd-open ( node frames -- node' outcome )
  >r r@ lf-bd-base lf-bd-subst r@ lf-open-fuel lf-dq-lend lf-instantiate-rev
  r> lf-open-fuel lf-dq-repay ;
: lf-bd-domain ( binder frames -- type outcome ) >r lf-term-first@ r> lf-bd-open ;
\ A new free variable of type pushed (Lean's mk_local_decl, 770): ok,
\ or full.
: lf-bd-push ( type -- outcome )
  lf-dq-depth @ 1+ lf-dq-subst slab-hold ok-then? 0= if exit then
  lf-lctx-local ok-then? 0= if exit then
  lf-dq-depth @ lf-dq-subst slab-at ! 1 lf-dq-depth +! outcome-ok ;
\ The last step: the bodies, opened, compared by is_def_eq (777-778).
: lf-bd-bodies ( t s frames -- ... frames next )
  >r swap r@ lf-bd-open ok-then? 0= if nip r> lf-bd-fail exit then
  swap r@ lf-bd-open ok-then? 0= if nip r> lf-bd-fail exit then
  r> ['] lf-bd-done lf-dq-call ;
\ After a binder pair: the next pair while both bodies are binders of the
\ telescope's kind (776), else the bodies.
defer lf-bd-pair ( t s frames -- ... frames next )
: lf-bd-next ( t s frames -- ... frames next )
  dup lf-dq-spend dup ok? if drop lf-bd-pair exit then
  rot drop rot drop swap lf-bd-fail ;
: lf-bd-advance ( t s frames -- ... frames next )
  >r lf-term-second@ swap lf-term-second@ swap 2dup r@ lf-bd-kind lf-dq-both?
  r> swap if lf-bd-next else lf-bd-bodies then ;
\ The binder's free variable, of the right side's domain read with the
\ visit's free variables (var_s_type, 761, 769).
: lf-bd-bind ( t s type frames -- ... frames next )
  >r lf-bd-push dup ok? 0= if nip nip r> lf-bd-fail exit then drop r> lf-bd-advance ;
: lf-bd-same-domain ( t s frames -- ... frames next )
  >r dup r@ lf-bd-domain ok-then? 0= if nip nip r> lf-bd-fail exit then r> lf-bd-bind ;
\ Domains that are not ==: both opened and compared by is_def_eq
\ (760-765), t, s and the right one saved across the comparison.
: lf-bd-save3 ( t s ts frames -- ts frames )
  >r rot r@ frame-save swap r@ frame-save dup r@ frame-save r> ;
: lf-bd-saved3 ( frames -- t s ts )
  >r 2 r@ frame-pick 1 r@ frame-pick 0 r@ frame-pick 3 r> frame-drop ;
: lf-bd-domains-back ( flag outcome frames -- ... frames next )
  >r ok-then? 0= if 3 r@ frame-drop r> lf-bd-fail exit then
  if r@ lf-bd-saved3 r> lf-bd-bind else 3 r@ frame-drop r> lf-bd-false then ;
: lf-bd-differ ( t s frames -- ... frames next )
  >r dup r@ lf-bd-domain ok-then? 0= if nip nip r> lf-bd-fail exit then
  2 pick r@ lf-bd-domain ok-then? 0= if nip nip nip r> lf-bd-fail exit then
  r> swap >r lf-bd-save3 r> -rot ['] lf-bd-domains-back lf-dq-call ;
: lf-bd-domains ( t s -- td sd ) lf-term-first@ swap lf-term-first@ swap ;
:noname ( t s frames -- ... frames next )
  >r 2dup lf-bd-domains r@ lf-dq-same ok-then? 0= if nip nip r> lf-bd-fail exit then
  if r> lf-bd-same-domain else r> lf-bd-differ then ; is lf-bd-pair
:noname ( t s frames -- ... frames next )
  lf-dq-depth @ over frame-save 2 pick lf-dq-tag over frame-save lf-bd-pair ; is lf-bd-visit

\ ---------------------------------------------------------------------------
\ is_def_eq_app (878-895). The visit keeps t and s, then the number of
\ arguments n and the next argument i, compared left to right.
: lf-ap-i ( frames -- i n ) dup 0 swap frame-pick swap 1 swap frame-pick ;
: lf-ap-nth ( node frames -- arg ) lf-ap-i swap - 1- 0 ?do lf-term-first@ loop lf-term-second@ ;
defer lf-ap-arg ( frames -- ... frames next )
: lf-ap-next ( flag outcome frames -- ... frames next )
  >r ok-then? 0= if r> 4 lf-dq-drop-failed exit then
  0= if false r> 4 lf-dq-drop-answer exit then
  r@ frame-restore 1+ r@ frame-save r> lf-ap-arg ;
:noname ( frames -- ... frames next )
  >r r@ lf-ap-i = if true r> 4 lf-dq-drop-answer exit then
  3 r@ frame-pick r@ lf-ap-nth 2 r@ frame-pick r@ lf-ap-nth
  r> ['] lf-ap-next lf-dq-call ; is lf-ap-arg
: lf-ap-fn ( flag outcome frames -- ... frames next )
  >r ok-then? 0= if r> 2 lf-dq-drop-failed exit then
  0= if false r> 2 lf-dq-drop-answer exit then
  r@ lf-dq-pick2 lf-dq-count swap lf-dq-count tuck <>
  if drop false r> 2 lf-dq-drop-answer exit then
  r@ frame-save 0 r@ frame-save r> lf-ap-arg ;
:noname ( t s frames -- ... frames next )
  >r 2dup lf-dq-apps? 0= if 2drop false r> lf-dq-answer exit then
  r> lf-dq-save2 >r lf-whnf-head swap lf-whnf-head swap r> ['] lf-ap-fn lf-dq-call
  ; is lf-ap-visit

\ is_def_eq_args (830-838): the last arguments first, while both are
\ applications; then neither may be one.
: lf-ar-next ( flag outcome frames -- ... frames next )
  >r ok-then? 0= if r> 2 lf-dq-drop-failed exit then
  0= if false r> 2 lf-dq-drop-answer exit then
  r@ lf-dq-pick2 2 r@ frame-drop lf-term-first@ swap lf-term-first@ swap
  r@ lf-dq-spend dup ok? if drop r> lf-ar-visit else nip nip r> lf-dq-failed then ;
:noname ( t s frames -- ... frames next )
  >r 2dup lf-dq-apps? 0= if lf-dq-app? 0= swap lf-dq-app? 0= and r> lf-dq-answer exit then
  r> lf-dq-save2 >r lf-term-second@ swap lf-term-second@ swap r> ['] lf-ar-next lf-dq-call
  ; is lf-ar-visit

\ ---------------------------------------------------------------------------
\ is_def_eq_core (1132-1207), steps 1, 3, 6, 7 and 10 (see the header).
\ The visit keeps t and s, then whnf_core of each (tn, sn), -1 for a side
\ whose whnf_core was unknown, which those steps then read unreduced.
: lf-dq-cells ( frames -- t s tn sn )
  >r 3 r@ frame-pick 2 r@ frame-pick 1 r@ frame-pick 0 r> frame-pick ;
: lf-dq-or ( x y -- y|x ) dup 0< if drop else nip then ;
: lf-dq-sides ( frames -- tn sn ) lf-dq-cells rot swap lf-dq-or >r lf-dq-or r> ;
: lf-dq-changed? ( t s tn sn -- tn sn flag )
  2dup 0< swap 0< or if 2swap 2drop false exit then
  2swap 2over rot <> -rot <> or ;
: lf-dq-kept ( node outcome -- node' outcome' )
  dup outcome-unknown = if 2drop -1 outcome-ok then ;
: lf-dq-undecided ( t s -- ) lf-dq-site lf-diag-undecided lf-diag-note ;
\ Step 10 has answered; not yes is unknown, the reduced terms recorded.
: lf-dq-app-back ( flag outcome frames -- ... frames next )
  >r ok-then? 0= if r> 4 lf-dq-drop-failed exit then
  if true r> 4 lf-dq-drop-answer exit then
  r@ lf-dq-sides lf-dq-undecided outcome-unknown r> 4 lf-dq-drop-failed ;
\ Steps 6, 7, then 10.
: lf-dq-tail ( frames -- ... frames next )
  >r r@ lf-dq-sides 2dup r@ lf-dq-consts ok-then? 0= if nip nip r> 4 lf-dq-drop-failed exit then
  if 2drop true r> 4 lf-dq-drop-answer exit then
  2dup lf-dq-fvars? if 2drop true r> 4 lf-dq-drop-answer exit then
  r> ['] lf-dq-app-back lf-ap-call ;
: lf-dq-quick2 ( lbool outcome frames -- ... frames next )
  >r ok-then? 0= if r> 4 lf-dq-drop-failed exit then
  dup lf-dq-undef <> if lf-dq-flag r> 4 lf-dq-drop-answer exit then drop
  r> lf-dq-tail ;
: lf-dq-sn ( sn outcome frames -- ... frames next )
  >r lf-dq-kept ok-then? 0= if r> 3 lf-dq-drop-failed exit then
  r@ frame-save r@ lf-dq-cells lf-dq-changed?
  if r> ['] lf-dq-quick2 lf-qk-call else 2drop r> lf-dq-tail then ;
: lf-dq-tn ( tn outcome frames -- ... frames next )
  >r lf-dq-kept ok-then? 0= if r> 2 lf-dq-drop-failed exit then
  r@ frame-save 1 r@ frame-pick r> ['] lf-dq-sn lf-whnf-core-call ;
: lf-dq-quick1 ( lbool outcome frames -- ... frames next )
  >r ok-then? 0= if r> 2 lf-dq-drop-failed exit then
  dup lf-dq-undef <> if lf-dq-flag r> 2 lf-dq-drop-answer exit then drop
  r@ lf-dq-pick2 drop r> ['] lf-dq-tn lf-whnf-core-call ;
:noname ( t s frames -- ... frames next )
  lf-dq-save2 ['] lf-dq-quick1 lf-qk-call ; is lf-dq-visit

\ ---------------------------------------------------------------------------
\ The public words (see the header). Each -on word runs one visit to its
\ end; lf-quick-on answers Lean's lbool (lf-dq-yes, lf-dq-no,
\ lf-dq-undef), the others a flag.
: lf-defeq-call ( t s frames cont -- ... frames next ) lf-dq-call ;
: lf-defeq-on ( t s frames -- flag outcome ) ['] lf-dq-call frame-through drop ;
: lf-quick-on ( t s frames -- lbool outcome ) ['] lf-qk-call frame-through drop ;
: lf-defeq-binding-on ( t s frames -- flag outcome ) ['] lf-bd-call frame-through drop ;
: lf-defeq-app-on ( t s frames -- flag outcome ) ['] lf-ap-call frame-through drop ;
: lf-defeq-args-on ( t s frames -- flag outcome ) ['] lf-ar-call frame-through drop ;
