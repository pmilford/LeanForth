\ Definitional equality as Lean's kernel decides it (ADR 0014 Q1, Q3, Q6,
\ Q7, Q8; ADR 0015 R4, R5; plan tasks 4.2.2b, 4.2.2d, 4.2.4, 4.2.5 and
\ 5.2.2): ports of quick_is_def_eq (type_checker.cpp 802-826),
\ is_def_eq_binding (752-779), is_def_eq_app (878-895), is_def_eq_args
\ (830-838), try_eta_expansion (841-853), try_eta_struct_core (856-872),
\ is_def_eq_proof_irrel (899-906), lazy_delta_reduction and its step
\ (959-1075) with try_unfold_proj_app (950-957), lazy_delta_proj_reduction
\ (1084-1102), is_def_eq_unit_like (1119-1130) and is_def_eq_core
\ (1132-1207), at the referee commit
\ eb6cafb7 (ADR 0014, Reproduction). [kernel] code: not through the
\ review gate (AGENTS.md).
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
\   success cache (succeeded_before, 804, filled by is_def_eq 1211) is
\   kernel/caches.fs's, through the hooks lf-qk-other and lf-dq-entry
\   (plan task 4.2.7), as are == by skeleton (lf-dq-known-same?) and the
\   failure cache below (lf-lz-failed?, lf-lz-failure).
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
\ - is_def_eq_core, in Lean's order: (1) quick_is_def_eq decides yes or
\   no; (2) when s is the constant Bool.true (by name) and t has no free
\   variable, or in eager mode (lf-dq-eager), yes when whnf(t) is
\   Bool.true too; (3) whnf_core of both sides with cheap_proj (whnf.fs:
\   a projection's term put in whnf_core, not whnf) and, when either
\   changed, quick_is_def_eq again; (4) proof irrelevance: when t is a
\   proof, is_def_eq of t's type and s's type is the answer, yes or no;
\   (5) lazy delta reduction (below), which may answer yes
\   or no and leaves both sides as far unfolded as it got; (6) the same
\   constant with equivalent universe arguments, yes; (7) the same free
\   variable, yes; (8) both sides projections of one field of one
\   structure: lazy_delta_proj_reduction of their terms (below), yes;
\   (9) whnf_core of both sides without cheap_proj: when either is a new
\   node (Lean's is_eqp), is_def_eq_core of the two is the answer;
\   (10) is_def_eq_app,
\   yes; (11) eta: when exactly one side is a lambda and the whnf of the
\   other's type is a Pi of domain D, is_def_eq of the lambda and
\   fun x : D => other x, yes; (12) structure eta, tn against sn, then sn
\   against tn: when the second is a constructor of a non-recursive
\   structure I applied to its parameters and fields, the two types
\   is_def_eq and then each field is_def_eq to the first's projection
\   onto it (Lean's Expr.proj), yes (BL-7, Lean's own limitation, stays:
\   two variables are never equated field by field); (13) a string
\   literal against String.ofList x, either way round: is_def_eq_core of
\   the literal's constructor form in whnf and the other side
\   (kernel/string-literals.fs, plan task 5.2.3); (14) unit-like types: when the whnf of
\   t's type is headed by a non-recursive structure whose constructor has
\   no field, is_def_eq_core of that type and s's type is the answer;
\   (15) otherwise no.
\ - Whether t is a proof (step 4) is Lean's is_prop of its type (383-389):
\   the type of t's type, put in whnf, is a Sort whose level normalizes to
\   zero. A Sort is a type, never a proof, and so is a free variable whose
\   type is a Sort, and a Pi without a typer (with one a Pi is typed, as
\   Lean's infer_pi may throw on it); otherwise the types come from the
\   typer the caller lends, Lean's infer_type in infer-only mode
\   (lf-dq-typer: mixed-infer.fs, aside). Step 4 asks it for t's type
\   first, and for s's only when t is a proof, step 11 for the other
\   side's and steps 12 and 14 for both sides',
\   each a free variable's type without it (Lean's infer_fvar).
\ - lazy_delta_reduction loops, one unit of fuel a round. First
\   is_def_eq_offset: both sides zero (the literal 0 or Nat.zero) is yes;
\   both with a predecessor (a literal above 0, or Nat.succ x by name)
\   answer as the predecessors compare; then, while neither side has a
\   free variable or in eager mode, a side reduce_nat computes (K7,
\   reduce-nat.fs; plan task 5.2.3) is replaced by its value, compared
\   with the other side, and that is the answer (whnf's own reduce_nat,
\   whnf.fs, has no such test: Lean's whnf has none, 732). Then one step
\   (lazy_delta_reduction_step): is_delta of each side (whnf.fs); neither,
\   the loop ends undecided; one, it unfolds; both, compare's hints decide
\   (declaration.cpp 24-49): the greater regular height first, the
\   abbreviation first, the side whose hint is not opaque first, else
\   both -- but first, for two applications of the same declaration with
\   a regular hint, equivalent universe arguments and is_def_eq_args
\   answer yes. Where only one side unfolds, try_unfold_proj_app first:
\   the other side, when its head is a projection, put in whnf_core
\   without cheap_proj, takes its place when that is not == to it.
\   Each unfolded side goes through whnf_core with cheap_proj; then
\   quick_is_def_eq answers yes, no, or the loop goes on. Lean's failure
\   cache (failed_before, 1004-1009) only skips an argument test that
\   failed before, which would fail again (kernel/caches.fs keeps it).
\ - lazy_delta_proj_reduction (step 8) runs the same step on the two
\   projections' terms tc and sc, a visit of its own, until it answers:
\   yes is yes; otherwise, when reduce_proj_core finds the field of both
\   (iota.fs, through the hook lf-dq-reduce-proj), is_def_eq_core of the
\   fields is the answer, else is_def_eq_core of tc and sc.
\ - is_def_eq_app: both applications, the functions is_def_eq and the
\   argument counts equal, then the arguments left to right; the first
\   pair that is not equal ends it, false. is_def_eq_args: the arguments
\   last first, then both spines must end together. Applications,
\   functions and counts are Lean's (is_app, get_app_fn): a projection
\   (core/projections.fs, a node over a projection leaf and its term) is
\   Lean's Expr.proj, no application, and so is a let term.
\ Doubt. Where the port cannot tell whether a step it passes would have
\ answered yes, it goes on, records the first such step (the doubt
\ record), and lf-defeq-on reports a final no as unknown with it: outside
\ a check of the checked environment, a constant at a head of lazy delta
\ (K1, diagnostic 64: the signature index holds no values), and steps 4,
\ 11, 12 and 14 without a typer (diagnostics 87, 88, 89 and 89; a bare
\ call, as the unit tests make). A check of the checked environment
\ always has a typer and a snapshot, so it never doubts. Where steps 12
\ and 14 cannot look a constant up (outside a check, or an inductive
\ block's own while it is checked), they are unknown (diagnostic 89, or
\ the doubt when there is one). A yes reached with a doubt is
\ Lean's yes under these conditions, which it needs (review rvU4 B1): (a)
\ without a typer, steps 6, 7, 10 and 11 answer yes only for terms equal
\ up to beta, eta and universe equivalence (step 4 needs the typer);
\ (b) lazy delta's by-name rules have run as Lean runs them (K7 and
\ is_def_eq_offset come before the doubt), and a constant of the
\ signature index has no value -- the assumption of a comparison outside
\ a check, which accepts no theorem; (c) where step 4 is skipped, Lean
\ would compare the two sides' types, equal for terms equal up to beta,
\ eta and universe equivalence (ADR 0003's argument); where step 11, 12
\ or 14 is skipped, Lean could only have said yes sooner.
\
\ Passes. Every comparison is a visit on a frames record that the caller
\ gives (lib/frame.fs), as in whnf.fs: lf-defeq-call ( t s frames cont
\ -- ... frames next ), cont getting ( flag outcome frames ), and
\ lf-defeq-on ( t s frames -- flag outcome ) runs one to its end as a
\ loop of its own (a no from lf-defeq-call is final only without doubt,
\ which lf-defeq-on settles). Each visit costs one unit of the frames'
\ fuel, as does each binder pair of a telescope, each argument pair
\ beyond a visit's first and each round of lazy delta; ==, level
\ comparisons, the substitutions, unfolding and the typer are paid from
\ it too. Inputs must be closed audited terms whose free variables are
\ live; the nodes, free variables and local context entries a comparison
\ makes stay for the caller to discard (mixed-convert.fs restores the
\ stores and drops them).
\
\ State: the free variables of the telescopes being compared, a growable
\ array used as a stack (each is_def_eq_binding visit pushes its binders'
\ and pops them when it ends, whatever its outcome), its depth, the
\ typer, the eager flag and the doubt record, in one record; both members
\ of the checker context (lib/context.fs). The caller sets the typer and
\ the eager flag around a comparison. A THROW out of a pass leaves the
\ record wrong: lf-defeq-reset empties it (and whnf.fs's cheap_proj
\ mode). A few steps are deferred only so that words defined before them
\ can name them, and lf-dq-reduce-proj so that iota.fs can set it; they
\ are set once, while loading.

require ../lib/lib.fs
require ../lib/slab.fs
require ../core/diagnostics.fs
require ../core/input.fs
require ../core/let-terms.fs
require ../core/local-context.fs
require ../core/names.fs
require ../core/name-equal.fs
require ../core/projections.fs
require ../core/terms.fs
require ./env-signature.fs
require ./level-compare.fs
require ./level-value.fs
require ./mixed-compare.fs
require ./mixed-head.fs
require ./mixed-open.fs
require ./whnf.fs

begin-structure /lf-dqs
  field: lf-dqs-depth        \ free variables on the stack below
  field: lf-dqs-typer        \ infer_type ( node frames -- type outcome ), or 0
  field: lf-dqs-eager        \ true in Lean's eager mode (m_eager_reduce)
  field: lf-dqs-doubt        \ the doubt record: its diagnostic code, or 0
  field: lf-dqs-dt           \ and its two terms
  field: lf-dqs-ds
end-structure
/lf-dqs context-record: lf-dq-state
1 cells context-slab: lf-dq-subst

: lf-dq-site ( -- site ) c" defeq lf-defeq" ;
: lf-dq-depth ( -- addr ) lf-dq-state lf-dqs-depth ;
\ The typer and the eager flag, which the caller sets (see the header).
: lf-dq-typer ( -- addr ) lf-dq-state lf-dqs-typer ;
: lf-dq-eager ( -- addr ) lf-dq-state lf-dqs-eager ;
\ Recovery after a THROW out of a pass: an empty record, whnf_core's
\ mode without cheap_proj.
: lf-defeq-reset ( -- ) lf-dq-state /lf-dqs erase lf-whnf-reset ;

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
: lf-dq-open ( t s frames cont xt -- ... frames next ) ['] lf-dq-refused frame-open-or ;
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
\ The two cells on top: t and s, and from step 3 tn and sn.
: lf-dq-sides ( frames -- t s ) dup 1 swap frame-pick swap 0 swap frame-pick ;
\ The frames' fuel lent to a pass that keeps its own, and taken back.
: lf-dq-lend ( frames addr -- ) swap frame-fuel @ swap ! ;
: lf-dq-repay ( frames addr -- ) @ swap frame-fuel ! ;

\ ---------------------------------------------------------------------------
\ Leaves of the comparison, each paid from the frames' fuel.
\ Lean's ==, recording nothing when the terms differ. Two terms the
\ caches know equal (one skeleton, kernel/caches.fs, which sets the hook)
\ are equal at no cost; otherwise the walk decides.
defer lf-dq-known-same? ( t s -- flag )
:noname ( t s -- flag ) 2drop false ; is lf-dq-known-same?
: lf-dq-same ( t s frames -- flag outcome )
  >r 2dup lf-dq-known-same? if 2drop r> drop true outcome-ok exit then
  r@ frame-fuel @ lf-expr-equal r> lf-mcompare-fuel lf-dq-repay ;
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
: lf-dq-level-pair ( ta sa i -- ta sa flag outcome )
  >r over r@ lf-cref-pair@ drop over r> lf-cref-pair@ drop lf-dq-level-eq ;
: lf-dq-level-pairs ( ta sa n -- flag outcome ) ['] lf-dq-level-pair ok-all? 2swap 2drop ;
: lf-dq-level-lists ( t s -- flag outcome )
  lf-const-slot lf-cref-pairs rot lf-const-slot lf-cref-pairs
  rot over <> if 2drop drop false outcome-ok exit then
  >r swap r> lf-dq-level-pairs ;

\ The node kinds the steps test.
: lf-dq-tag ( node -- tag ) lf-term-tag@ ;
: lf-dq-tags? ( t s -- flag ) lf-dq-tag swap lf-dq-tag = ;
: lf-dq-binder? ( node -- flag ) lf-dq-tag lf-term-binder-tag? ;
\ Lean's is_proj, is_app, get_app_fn and get_app_num_args (see the
\ header): a projection and a let term are no applications.
: lf-dq-proj? ( node -- flag ) lf-proj? ;
: lf-dq-app? ( node -- flag ) lf-dq-tag lf-tag-app = ;
: lf-dq-apps? ( t s -- flag ) lf-dq-app? swap lf-dq-app? and ;
: lf-dq-both? ( t s tag -- flag ) tuck swap lf-dq-tag = -rot swap lf-dq-tag = and ;
: lf-dq-fn ( node -- fn n )
  0 begin over lf-dq-app? while 1+ swap lf-term-first@ swap repeat ;
: lf-dq-head ( node -- fn ) lf-dq-fn drop ;
: lf-dq-count ( node -- n ) lf-dq-fn nip ;

\ Step 6 (1170-1172): two constants of the same name whose universe
\ arguments are equivalent; on level-compare's fuel.
: lf-dq-names? ( t s -- flag )
  lf-const-name swap lf-const-name lf-name-same? ;
: lf-dq-consts ( t s frames -- flag outcome )
  >r 2dup lf-tag-constant lf-dq-both? 0= if 2drop r> drop false outcome-ok exit then
  2dup lf-dq-names? 0= if 2drop r> drop false outcome-ok exit then
  r@ lf-lcmp-fuel lf-dq-lend lf-dq-level-lists r> lf-lcmp-fuel lf-dq-repay ;
\ Step 7 (1174-1175): the same free variable (one node per entry).
: lf-dq-fvars? ( t s -- flag )
  2dup lf-tag-fvar lf-dq-both?
  if lf-term-first@ swap lf-term-first@ = else 2drop false then ;

\ ---------------------------------------------------------------------------
\ The visits refer to each other; each is set once below.
defer lf-dq-visit ( t s frames -- ... frames next )
defer lf-qk-visit ( t s frames -- ... frames next )
defer lf-bd-visit ( t s frames -- ... frames next )
defer lf-ap-visit ( t s frames -- ... frames next )
defer lf-ar-visit ( t s frames -- ... frames next )
defer lf-es-visit ( t s frames -- ... frames next )
defer lf-lz-loop ( frames -- ... frames next )
\ The first step of an is_def_eq visit: lf-dq-visit, or the success
\ cache's step around it (kernel/caches.fs sets it).
defer lf-dq-entry ( t s frames -- ... frames next )
' lf-dq-visit is lf-dq-entry
: lf-dq-call ( t s frames cont -- ... frames next ) ['] lf-dq-entry lf-dq-open ;
\ Lean's is_def_eq_core called directly (is_def_eq_offset 1049, lazy
\ delta's reduce_nat 1062 and 1064, is_def_eq_unit_like 1129): the visit
\ itself, so the success cache keeps nothing (review rvCONV L1), as Lean's
\ cache_success runs only in is_def_eq (1211).
: lf-dq-core-call ( t s frames cont -- ... frames next ) ['] lf-dq-visit lf-dq-open ;
: lf-qk-call ( t s frames cont -- ... frames next ) ['] lf-qk-visit lf-dq-open ;
: lf-bd-call ( t s frames cont -- ... frames next ) ['] lf-bd-visit lf-dq-open ;
: lf-ap-call ( t s frames cont -- ... frames next ) ['] lf-ap-visit lf-dq-open ;
: lf-ar-call ( t s frames cont -- ... frames next ) ['] lf-ar-visit lf-dq-open ;
: lf-es-call ( t s frames cont -- ... frames next ) ['] lf-es-visit lf-dq-open ;

\ ---------------------------------------------------------------------------
\ quick_is_def_eq (802-826): ( lbool outcome ).
: lf-qk-bound ( flag outcome frames -- lbool outcome frames 0 )
  >r dup ok? if swap lf-dq-lbool swap then r> 0 ;
: lf-qk-sorts ( t s frames -- lbool outcome frames 0 )
  >r lf-term-first@ swap lf-term-first@ swap r@ lf-dq-levels
  ok-then? if lf-dq-lbool outcome-ok else lf-dq-undef swap then r> 0 ;
: lf-qk-undecided ( t s frames -- lbool outcome frames 0 )
  >r 2drop lf-dq-undef outcome-ok r> 0 ;
\ Two literals that are not == are not equal (quick_is_def_eq, Lit),
\ also a natural-number and a string literal (both Lean's Lit kind).
: lf-dq-literals? ( t s -- flag )
  lf-dq-tag lf-literal-tag? swap lf-dq-tag lf-literal-tag? and ;
: lf-qk-kinds ( t s frames -- ... frames next )
  >r 2dup lf-dq-literals? if 2drop lf-dq-no outcome-ok r> 0 exit then
  2dup lf-dq-tags? 0= if r> lf-qk-undecided exit then
  over lf-dq-binder? if r> ['] lf-qk-bound lf-bd-call exit then
  over lf-dq-tag lf-tag-symbolic-sort = if r> lf-qk-sorts else r> lf-qk-undecided then ;
\ After ==: lf-qk-kinds, or Lean's succeeded_before (804) first
\ (kernel/caches.fs sets it).
defer lf-qk-other ( t s frames -- ... frames next )
' lf-qk-kinds is lf-qk-other
:noname ( t s frames -- ... frames next )
  >r 2dup r@ lf-dq-same ok-then? 0= if nip nip lf-dq-undef swap r> 0 exit then
  if 2drop lf-dq-yes outcome-ok r> 0 else r> lf-qk-other then ; is lf-qk-visit

\ ---------------------------------------------------------------------------
\ is_def_eq_binding (752-779). The visit keeps the stack's depth when it
\ began (base) and the telescope's kind below everything else it saves,
\ and pops its free variables on every way out (lf-bd-done).
: lf-bd-base ( frames -- base ) 1 swap frame-pick ;
: lf-bd-kind ( frames -- tag ) 0 swap frame-pick ;
\ The free variables open, also told to the derivation log, which counts
\ them as binders around the rules opened meanwhile.
: lf-dq-depth! ( n -- ) dup lf-dq-depth ! lf-log-binders! ;
: lf-bd-done ( x outcome frames -- x outcome frames 0 )
  dup lf-bd-base lf-dq-depth! 2 over frame-drop 0 ;
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
  dup lf-log-depth swap lf-fvar-depth!
  lf-dq-depth @ lf-dq-subst slab-at ! lf-dq-depth @ 1+ lf-dq-depth! outcome-ok ;
\ The last step: the bodies, opened, compared by is_def_eq (777-778).
: lf-bd-bodies ( t s frames -- ... frames next )
  >r swap r@ lf-bd-open ok-then? 0= if nip r> lf-bd-fail exit then
  swap r@ lf-bd-open ok-then? 0= if nip r> lf-bd-fail exit then
  r> ['] lf-bd-done lf-dq-call ;
\ After a binder pair: the next pair while both bodies are binders of the
\ telescope's kind (776), else the bodies. The next pair is the step the
\ frames' loop runs next, never a call: a telescope of any length keeps
\ the host's stacks flat.
defer lf-bd-pair ( t s frames -- ... frames next )
: lf-bd-next ( t s frames -- ... frames next )
  dup lf-dq-spend dup ok? if drop ['] lf-bd-pair exit then
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
  lf-dq-depth @ over frame-save 2 pick lf-dq-tag over frame-save lf-bd-pair ;
is lf-bd-visit

\ ---------------------------------------------------------------------------
\ is_def_eq_app (878-895). The visit keeps t and s, then the number of
\ arguments n and the next argument i, compared left to right.
: lf-ap-i ( frames -- i n ) dup 0 swap frame-pick swap 1 swap frame-pick ;
: lf-ap-nth ( node frames -- arg )
  lf-ap-i swap - 1- 0 ?do lf-term-first@ loop lf-term-second@ ;
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
  r@ lf-dq-sides lf-dq-count swap lf-dq-count tuck <>
  if drop false r> 2 lf-dq-drop-answer exit then
  r@ frame-save 0 r@ frame-save r> lf-ap-arg ;
:noname ( t s frames -- ... frames next )
  >r 2dup lf-dq-apps? 0= if 2drop false r> lf-dq-answer exit then
  r> lf-dq-save2 >r lf-dq-head swap lf-dq-head swap r> ['] lf-ap-fn lf-dq-call
  ; is lf-ap-visit

\ is_def_eq_args (830-838): the last arguments first, while both are
\ applications; then neither may be one.
: lf-ar-next ( flag outcome frames -- ... frames next )
  >r ok-then? 0= if r> 2 lf-dq-drop-failed exit then
  0= if false r> 2 lf-dq-drop-answer exit then
  r@ lf-dq-sides 2 r@ frame-drop lf-term-first@ swap lf-term-first@ swap
  r@ lf-dq-spend dup ok? if drop r> lf-ar-visit else nip nip r> lf-dq-failed then ;
:noname ( t s frames -- ... frames next )
  >r 2dup lf-dq-apps? 0= if lf-dq-app? 0= swap lf-dq-app? 0= and r> lf-dq-answer exit then
  r> lf-dq-save2 >r lf-term-second@ swap lf-term-second@ swap r> ['] lf-ar-next lf-dq-call
  ; is lf-ar-visit

\ ---------------------------------------------------------------------------
\ is_def_eq_core (1132-1207; see the header). The visit keeps t and s,
\ then, from step 3, tn and sn: whnf_core of each, which lazy delta
\ updates. A step that ends the visit drops its four cells.
: lf-dq-cells ( frames -- t s tn sn )
  >r 3 r@ frame-pick 2 r@ frame-pick 1 r@ frame-pick 0 r> frame-pick ;
: lf-dq-sides! ( tn sn frames -- ) >r 2 r@ frame-drop swap r@ frame-save r> frame-save ;
: lf-dq-end ( flag frames -- flag outcome frames 0 ) 4 lf-dq-drop-answer ;
\ Whether whnf_core changed either side: a new node (Lean's is_eqp).
: lf-dq-changed? ( t s tn sn -- tn sn flag ) 2swap 2over rot <> -rot <> or ;
: lf-dq-end-failed ( outcome frames -- 0 outcome frames 0 ) 4 lf-dq-drop-failed ;
\ A child's answer to a step that may say yes: yes ends the visit with
\ yes, a failure ends it with the failure, no goes on to the next step,
\ xt ( frames -- ... frames next ).
: lf-dq-yes-or ( flag outcome frames xt -- ... frames next )
  2>r ok-then? 0= if 2r> drop lf-dq-end-failed exit then
  if true 2r> drop lf-dq-end else 2r> execute then ;

\ The doubt record (see the header): the first step passed that might
\ have answered yes, with its terms; lf-dq-settle turns a final no into
\ unknown, recorded with it.
: lf-dq-doubt ( t s code -- )
  lf-dq-state lf-dqs-doubt @ if 2drop drop exit then
  lf-dq-state tuck lf-dqs-doubt ! tuck lf-dqs-ds ! lf-dqs-dt ! ;
: lf-dq-doubted ( -- )
  lf-dq-state >r r@ lf-dqs-dt @ r@ lf-dqs-ds @ lf-dq-site r> lf-dqs-doubt @ lf-diag-note ;
: lf-dq-settle ( flag outcome -- flag outcome )
  dup ok? 2 pick 0= and lf-dq-state lf-dqs-doubt @ and 0= if exit then
  2drop lf-dq-doubted 0 outcome-unknown ;

\ The constants Lean matches by name here: Bool.true (step 2, whatever
\ its universe arguments) and Nat.succ with one argument (K7, whnf.fs).
: lf-dq-bool-true? ( name -- flag )
  dup s" true" lf-name-str-is? 0= if drop false exit then
  lf-name-prefix@ s" Bool" lf-name-top? ;
: lf-dq-true? ( node -- flag )
  dup lf-whnf-const? if lf-const-name lf-dq-bool-true? else drop false then ;
: lf-dq-succ? ( node -- flag ) dup lf-dq-count 1 = if lf-whnf-k7? else drop false then ;
\ is_def_eq_offset's is_nat_zero and is_nat_succ: the literal 0 or
\ Nat.zero; a literal above 0 or Nat.succ x, and its predecessor (x, or
\ the literal one less: reduce-nat.fs).
: lf-dq-nat-zero? ( node -- flag )
  dup lf-lit-leaf? if lf-term-second@ 0= else lf-whnf-zero? then ;
: lf-dq-pred? ( node -- flag )
  dup lf-lit-leaf? if lf-term-second@ 0<> else lf-dq-succ? then ;
: lf-dq-pred ( node -- pred outcome )
  dup lf-lit-leaf? if lf-reduce-nat-pred else lf-term-second@ outcome-ok then ;

\ ---------------------------------------------------------------------------
\ Types, for steps 4, 11 and 14 (see the header). A Sort is a type, and
\ so is a free variable whose type is a Sort: Lean's infer_type gives
\ their types without a test that can fail. So is a Pi, but Lean's
\ infer_pi tests that each domain and the body are types even in
\ infer-only mode, and throws typeExpected for an ill-typed Pi that
\ reduction made (plan task 4.2.7d): with a typer a Pi is typed as Lean
\ types it, and only without one taken as a type.
: lf-dq-sort? ( node -- flag ) lf-dq-tag lf-tag-symbolic-sort = ;
: lf-dq-pi? ( node -- flag ) lf-dq-tag lf-tag-pi = ;
: lf-dq-typeish? ( node -- flag )
  dup lf-dq-sort? if drop true exit then lf-dq-pi? lf-dq-typer @ 0= and ;
: lf-dq-fvar? ( node -- flag ) lf-dq-tag lf-tag-fvar = ;
: lf-dq-plain-type? ( t -- flag )
  dup lf-dq-typeish? if drop true exit then
  dup lf-dq-fvar? if lf-fvar-type lf-dq-sort? else drop false then ;
: lf-dq-typed ( node frames -- type outcome ) lf-dq-typer @ execute ;
\ ensure_sort (62-70) of a type's type, as is_prop calls it: its whnf a
\ Sort, its level; else Lean's typeExpected, thrown out of the comparison
\ (a well-typed term's type may have a type whose whnf is stuck, as in
\ Lean's tests bugs/*-subst-prop): rejected, diagnostic 55 (follow-up
\ of task 5.2.1b).
: lf-dq-sorted ( type frames -- level outcome )
  lf-whnf-on ok-then? 0= if no-result exit then
  dup lf-dq-sort? if lf-term-first@ outcome-ok exit then
  0 lf-dq-site lf-diag-type-expected lf-diag! -1 outcome-rejected ;
: lf-dq-zero? ( level frames -- flag outcome )
  >r r@ frame-fuel @ lf-level-zero? r> lf-lvalue-fuel lf-dq-repay ;
\ is_prop (383-389) of a type: its type, put in whnf, a Sort whose level
\ is zero.
: lf-dq-prop? ( type frames -- flag outcome )
  >r r@ lf-dq-typed ok-then? 0= if r> drop false swap exit then
  r@ lf-dq-sorted ok-then? 0= if r> drop false swap exit then
  r> lf-dq-zero? ;
\ Whether t is a proof (901-902): yes with t's type, no, or undecided
\ without a typer; the type is 0 unless yes, both are 0 on a failure.
: lf-dq-unproved ( outcome -- 0 0 outcome ) 0 0 rot ;
: lf-dq-proof-of ( type frames -- type lbool outcome )
  over lf-dq-sort? if 2drop 0 lf-dq-no outcome-ok exit then
  over swap lf-dq-prop? ok-then? 0= if nip lf-dq-unproved exit then
  if lf-dq-yes else drop 0 lf-dq-no then outcome-ok ;
: lf-dq-proof? ( t frames -- type lbool outcome )
  over lf-dq-plain-type? if 2drop 0 lf-dq-no outcome-ok exit then
  lf-dq-typer @ 0= if 2drop 0 lf-dq-undef outcome-ok exit then
  tuck lf-dq-typed ok-then? 0= if nip lf-dq-unproved exit then swap lf-dq-proof-of ;

\ Inductive types (ADR 0015), for steps 12 and 14: the declaration a name
\ has in the check's snapshot, or 0 for Lean's generated recursor (no
\ inductive type or constructor); unknown for a constant the check
\ declares itself (an inductive block's own, whose data is not yet
\ checked) and outside a check, where LeanForth cannot look (plan task
\ 5.2.2); or the lookup's failure, rejected (N1) for no such constant:
\ Lean's env().get throws unknownConstant there (try_eta_struct_core 859,
\ is_non_rec_structure, inductive.cpp 29). A found constant is its slot
\ d, or -1 for Lean's generated recursor that no slot holds.
: lf-dq-found ( name -- d outcome )
  lf-whnf-env? 0= if drop 0 outcome-unknown exit then
  dup lf-envsig-local if 2drop 0 outcome-unknown exit then
  lf-env-lookup-pass ;
: lf-dq-named ( name -- decl outcome )
  lf-dq-found ok-then? 0= if 0 swap exit then
  dup 0< if drop 0 outcome-ok else lf-whnf-decl then ;
\ What xt ( name -- decl outcome ) finds for the name of node's head
\ constant; (0 ok) when the head is no constant.
: lf-dq-head-by ( node xt -- decl outcome )
  >r lf-whnf-head dup lf-whnf-const? 0= if r> 2drop 0 outcome-ok exit then
  lf-const-name r> execute ;
: lf-dq-head-named ( node -- decl outcome ) ['] lf-dq-named lf-dq-head-by ;
\ is_non_rec_structure (inductive.cpp 28-33) of the type named name, with
\ the numIndices and is_rec LeanForth's block check computed, never the
\ file's (lf-env-structure; ADR 0015 section 8, owner answer Q2; review
\ rvCONV B2: Lean's replay ignores the file's, its kernel uses its own):
\ (decl ok) for such a type, (0 ok) for any other constant, or a failure
\ (unknown, diagnostic 89, for an inductive type without a shape).
: lf-dq-structure ( name -- decl|0 outcome )
  lf-dq-found ok-then? 0= if 0 swap exit then
  dup 0< if drop 0 outcome-ok else lf-env-structure then ;
: lf-dq-head-structure ( node -- decl|0 outcome ) ['] lf-dq-structure lf-dq-head-by ;
: lf-dq-ctor? ( decl -- flag )
  dup if dup lf-idecl-kind @ lf-kind-constructor = swap lf-idecl-data 0<> and then ;

\ A constructor's inductive type and its number of parameters.
: lf-dq-induct ( decl -- name ) lf-idecl-data lf-ict-induct lf-more-field ;
: lf-dq-params ( decl -- n ) lf-idecl-data lf-ict-params lf-more-field ;
: lf-dq-type-of ( t frames -- type outcome )
  over lf-dq-fvar? if drop lf-fvar-type outcome-ok else lf-dq-typed then ;
\ Whether a term's type can be had: a free variable's always, any other
\ term's only from a typer.
: lf-dq-typable? ( t -- flag ) lf-dq-fvar? lf-dq-typer @ 0<> or ;
\ For steps 11 and 14: the whnf of t's type, with yes; 0 and no for a
\ Sort, or a Pi without a typer, whose type is a Sort; 0 and undecided when the type
\ cannot be had; 0 0 on a failure.
: lf-dq-whnf-type ( t frames -- type lbool outcome )
  over lf-dq-typeish? if 2drop 0 lf-dq-no outcome-ok exit then
  over lf-dq-typable? 0= if 2drop 0 lf-dq-undef outcome-ok exit then
  tuck lf-dq-type-of ok-then? 0= if nip lf-dq-unproved exit then
  swap lf-whnf-on ok-then? 0= if lf-dq-unproved exit then lf-dq-yes outcome-ok ;
\ A type that passed a test kept with yes, else 0 and no.
: lf-dq-kept ( type flag -- type yes | 0 no ) if lf-dq-yes else drop 0 lf-dq-no then ;
\ A lookup that cannot tell (an inductive block's own constant, or
\ outside a check) is recorded with the doubt when there is one, else
\ with both terms (diagnostic 89); any other failure has its own.
: lf-dq-gap-note ( t s outcome -- outcome )
  dup outcome-unknown <> if nip nip exit then
  lf-dq-state lf-dqs-doubt @ if nip nip lf-dq-doubted exit then
  >r lf-dq-site lf-diag-structure-pending lf-diag-note r> ;

\ Step 12 (1197-1198): try_eta_struct (type_checker.h 97-99) tries its
\ core with s = sn, then with s = tn; no from both goes on to step 14.
\ try_eta_struct_core(t, s) (856-872) applies when s is a constructor of
\ a non-recursive structure I applied to its parameters and fields: then
\ infer_type(t) and infer_type(s) must be is_def_eq, and each field s_i,
\ left to right, is_def_eq to t's projection mk_proj(I, i - nparams, t)
\ (core/projections.fs); the first no answers no, all yes answer yes.
\ Lean's own limitation BL-7 stays: two variables of a structure are
\ never equated field by field. Without a typer the types cannot be had:
\ a doubt (diagnostic 89), and no.
: lf-dq-full-ctor? ( s decl -- flag )
  lf-idecl-data >r r@ lf-ict-params lf-more-field r> lf-ict-fields lf-more-field +
  swap lf-dq-count = ;
\ s's constructor when the step applies, else 0.
: lf-dq-struct-ctor ( s -- decl|0 outcome )
  dup lf-dq-head-named ok-then? 0= if nip 0 swap exit then
  dup lf-dq-ctor? 0= if 2drop 0 outcome-ok exit then
  tuck lf-dq-full-ctor? 0= if drop 0 outcome-ok exit then
  dup lf-dq-induct lf-dq-structure ok-then? 0= if nip 0 swap exit then
  0= if drop 0 then outcome-ok ;
\ try_eta_struct_core(t, s) is a visit of its own, ( flag outcome ). It
\ keeps t, s, I's name, nparams and the next argument i (pick 4 to 0).
: lf-es-fail ( outcome frames -- 0 outcome frames 0 ) 5 lf-dq-drop-failed ;
: lf-es-answer ( flag frames -- flag outcome frames 0 ) 5 lf-dq-drop-answer ;
: lf-es-keep ( t s decl frames -- t s frames )
  >r dup lf-dq-induct swap lf-dq-params 2over swap r@ frame-save r@ frame-save
  swap r@ frame-save dup r@ frame-save r@ frame-save r> ;
\ Argument i of an application, 0 the leftmost.
: lf-es-arg ( s i -- arg )
  over lf-dq-count swap - 1- 0 ?do lf-term-first@ loop lf-term-second@ ;
\ mk_proj(I, i - nparams, t) (core/projections.fs): full without room.
: lf-es-proj ( frames -- node outcome )
  >r 4 r@ frame-pick 2 r@ frame-pick 0 r@ frame-pick 1 r> frame-pick - lf-proj-of ;
defer lf-es-field ( frames -- ... frames next )
: lf-es-next ( flag outcome frames -- ... frames next )
  >r ok-then? 0= if r> lf-es-fail exit then
  0= if false r> lf-es-answer exit then
  r@ frame-restore 1+ r@ frame-save r> lf-es-field ;
:noname ( frames -- ... frames next )
  >r 0 r@ frame-pick 3 r@ frame-pick lf-dq-count = if true r> lf-es-answer exit then
  r@ lf-es-proj ok-then? 0= if r> lf-es-fail exit then
  3 r@ frame-pick 0 r@ frame-pick lf-es-arg r> ['] lf-es-next lf-dq-call
  ; is lf-es-field
: lf-es-types-back ( flag outcome frames -- ... frames next )
  >r ok-then? 0= if r> lf-es-fail exit then
  if r> lf-es-field else false r> lf-es-answer then ;
\ infer_type(t), then infer_type(s); both 0 on a failure.
: lf-es-types ( t s frames -- tt ts outcome )
  >r swap r@ lf-dq-type-of ok-then? 0= if nip r> drop lf-dq-unproved exit then
  swap r> lf-dq-typed ok-then? 0= if nip lf-dq-unproved exit then outcome-ok ;
: lf-es-typed ( t s frames -- ... frames next )
  >r r@ lf-es-types ok-then? 0= if nip r> lf-es-fail exit then
  r> ['] lf-es-types-back lf-dq-call ;
: lf-es-doubt ( t s frames -- false outcome frames 0 )
  >r lf-diag-structure-pending lf-dq-doubt false r> lf-dq-answer ;
:noname ( t s frames -- ... frames next )
  >r dup lf-dq-struct-ctor ok-then? 0= if lf-dq-gap-note r> lf-dq-failed exit then
  ?dup 0= if 2drop false r> lf-dq-answer exit then
  lf-dq-typer @ 0= if drop r> lf-es-doubt exit then
  r> lf-es-keep lf-es-typed ; is lf-es-visit

\ Step 14 (1203-1204), is_def_eq_unit_like (1119-1130): when the whnf of
\ t's type is headed by a non-recursive structure whose constructor has
\ no field, is_def_eq_core of that type and s's type is the answer, yes
\ or no; otherwise no. A type that cannot be had without a typer: a doubt
\ (diagnostic 89), and no.
: lf-dq-no-field? ( sdecl|0 -- flag outcome )
  dup 0= if outcome-ok exit then
  lf-idecl-data lf-ity-ctors@ drop @ lf-dq-named ok-then? 0= if false swap exit then
  dup lf-dq-ctor? if lf-idecl-data lf-ict-fields lf-more-field 0= else drop false then
  outcome-ok ;
\ The whnf of t's type when it is such a structure, with yes; else 0 and
\ no, or undecided without a typer; 0 0 on a failure.
: lf-dq-unit-type ( t frames -- type lbool outcome )
  lf-dq-whnf-type dup ok? 0= if exit then drop
  dup lf-dq-yes <> if outcome-ok exit then drop
  dup lf-dq-head-structure ok-then? 0= if nip lf-dq-unproved exit then
  lf-dq-no-field? ok-then? 0= if nip lf-dq-unproved exit then lf-dq-kept outcome-ok ;

\ Steps 12 to 15. A lookup that cannot tell is unknown, recorded as
\ lf-dq-gap-note does.
: lf-dq-no-step ( frames -- false outcome frames 0 ) false swap lf-dq-end ;
: lf-dq-gap ( outcome frames -- 0 outcome frames 0 )
  >r r@ lf-dq-sides rot lf-dq-gap-note r> lf-dq-end-failed ;
: lf-dq-unit-doubt ( frames -- false outcome frames 0 )
  >r r@ lf-dq-sides lf-diag-structure-pending lf-dq-doubt r> lf-dq-no-step ;
: lf-dq-unit-back ( flag outcome frames -- ... frames next )
  >r ok-then? 0= if r> lf-dq-end-failed else r> lf-dq-end then ;
: lf-dq-unit-compare ( type frames -- ... frames next )
  >r r@ lf-dq-sides nip dup lf-dq-typable? 0= if 2drop r> lf-dq-unit-doubt exit then
  r@ lf-dq-type-of ok-then? 0= if nip r> lf-dq-end-failed exit then
  r> ['] lf-dq-unit-back lf-dq-core-call ;
: lf-dq-unit-step ( frames -- ... frames next )
  >r r@ lf-dq-sides drop r@ lf-dq-unit-type ok-then? 0= if nip r> lf-dq-gap exit then
  dup lf-dq-yes = if drop r> lf-dq-unit-compare exit then
  nip lf-dq-undef = if r> lf-dq-unit-doubt else r> lf-dq-no-step then ;
\ Step 13 (1200-1201), try_string_lit_expansion: kernel/string-literals.fs
\ sets it (plan task 5.2.3, strings); it goes on to step 14 when it does
\ not apply, as this default always does.
defer lf-dq-string-step ( frames -- ... frames next )
' lf-dq-unit-step is lf-dq-string-step
: lf-dq-struct-other ( flag outcome frames -- ... frames next )
  ['] lf-dq-string-step lf-dq-yes-or ;
\ try_eta_struct_core(t, s): its visit when it applies, else no at once
\ (s's constructor looked up here, so that a step that does not apply
\ opens no visit and spends no fuel).
: lf-dq-struct-call ( t s frames cont -- ... frames next )
  2>r dup lf-dq-struct-ctor ok-then? 0= if lf-dq-gap-note 0 swap 2r> exit then
  if 2r> lf-es-call else 2drop false outcome-ok 2r> then ;
\ The other way round: the constructor sought on t.
: lf-dq-struct-swapped ( frames -- ... frames next )
  >r r@ lf-dq-sides swap r> ['] lf-dq-struct-other lf-dq-struct-call ;
: lf-dq-struct-back ( flag outcome frames -- ... frames next )
  ['] lf-dq-struct-swapped lf-dq-yes-or ;
: lf-dq-struct-step ( frames -- ... frames next )
  dup lf-dq-sides rot ['] lf-dq-struct-back lf-dq-struct-call ;

\ Step 11 (1194-1195), try_eta_expansion (type_checker.h 94-96) and its
\ core (841-853): when exactly one side is a lambda, the other side's type
\ put in whnf; a Pi of domain D gives fun x : D => other x (846: Lean's
\ binder name and annotation are not compared, quick_is_def_eq's ==), and
\ is_def_eq of the lambda (left) and that; yes ends the visit, no goes on
\ to step 12. Without a typer, other than a free variable's, the step is
\ undecided: a doubt.
: lf-dq-eta-sides ( tn sn -- lambda other true | false )
  over lf-whnf-lam? over lf-whnf-lam? 2dup = if 2drop 2drop false exit then
  drop if true else swap true then ;
\ The other side's type in whnf: yes a Pi, no, or undecided; the Pi is 0
\ unless yes, both are 0 on a failure. A Sort's or a Pi's type is a Sort.
: lf-dq-eta-pi ( other frames -- pi lbool outcome )
  lf-dq-whnf-type dup ok? 0= if exit then drop
  dup lf-dq-yes <> if outcome-ok exit then
  drop dup lf-dq-tag lf-tag-pi = lf-dq-kept outcome-ok ;
\ fun x : D => other x, closed as other is; full without room.
: lf-dq-eta-expand ( other pi -- lambda outcome )
  lf-term-first@ swap 0 lf-term-bvar 0= if 2drop lf-rebuild-full exit then
  lf-term-app 0= if drop lf-rebuild-full exit then lf-term-lam lf-rebuild-allocated ;
: lf-dq-eta-back ( flag outcome frames -- ... frames next )
  ['] lf-dq-struct-step lf-dq-yes-or ;
: lf-dq-eta-compare ( lambda other pi frames -- ... frames next )
  >r lf-dq-eta-expand ok-then? 0= if nip r> lf-dq-end-failed exit then
  r> ['] lf-dq-eta-back lf-dq-call ;
: lf-dq-eta-try ( lambda other frames -- ... frames next )
  >r dup r@ lf-dq-eta-pi ok-then? 0= if nip nip nip r> lf-dq-end-failed exit then
  dup lf-dq-yes = if drop r> lf-dq-eta-compare exit then
  lf-dq-undef = if r@ lf-dq-sides lf-diag-eta-pending lf-dq-doubt then
  2drop drop r> lf-dq-struct-step ;
: lf-dq-eta-step ( frames -- ... frames next )
  dup lf-dq-sides lf-dq-eta-sides if rot lf-dq-eta-try else lf-dq-struct-step then ;

\ A child's answer that is the visit's (also steps 4, 8 and 9 and lazy
\ delta's).
: lf-dq-final ( flag outcome frames -- ... frames next )
  >r ok-then? 0= if r> lf-dq-end-failed exit then r> lf-dq-end ;

\ Step 10.
: lf-dq-app-back ( flag outcome frames -- ... frames next )
  ['] lf-dq-eta-step lf-dq-yes-or ;
: lf-dq-app-step ( frames -- ... frames next )
  dup lf-dq-sides rot ['] lf-dq-app-back lf-ap-call ;

\ Step 9 (1185-1188): whnf_core of tn, then of sn, without cheap_proj
\ (whnf.fs), tn's kept across sn's visit; when either is a new node
\ (Lean's is_eqp), is_def_eq_core of the two is the answer, else step 10.
: lf-dq-full-sn ( snn outcome frames -- ... frames next )
  >r ok-then? 0= if 1 r@ frame-drop r> lf-dq-end-failed exit then
  r@ frame-restore swap r@ lf-dq-sides 2swap lf-dq-changed?
  if r> ['] lf-dq-final lf-dq-core-call else 2drop r> lf-dq-app-step then ;
: lf-dq-full-tn ( tnn outcome frames -- ... frames next )
  >r ok-then? 0= if r> lf-dq-end-failed exit then
  r@ lf-dq-sides nip swap r@ frame-save r> ['] lf-dq-full-sn lf-whnf-core-call ;
: lf-dq-full-step ( frames -- ... frames next )
  dup lf-dq-sides drop swap ['] lf-dq-full-tn lf-whnf-core-call ;

\ Step 8 (1177-1183): tn and sn projections of one field of one
\ structure (Lean compares the names and the indices): yes when
\ lazy_delta_proj_reduction (below) of their terms answers yes, a visit
\ of its own with the cells leaf, leaf, tc and sc; else step 9.
: lf-dq-leaves? ( leaf leaf' -- flag )
  2dup lf-proj-idx swap lf-proj-idx =
  if lf-proj-name swap lf-proj-name lf-name-same? else 2drop false then ;
: lf-dq-same-proj? ( tn sn -- flag )
  2dup lf-dq-proj? swap lf-dq-proj? and 0= if 2drop false exit then
  lf-term-first@ swap lf-term-first@ lf-dq-leaves? ;
: lf-lzp-visit ( tn sn frames -- ... frames next )
  >r over lf-term-first@ dup r@ frame-save r@ frame-save
  swap lf-term-second@ r@ frame-save lf-term-second@ r@ frame-save r> lf-lz-loop ;
: lf-dq-proj-back ( flag outcome frames -- ... frames next )
  ['] lf-dq-full-step lf-dq-yes-or ;
: lf-dq-proj-step ( frames -- ... frames next )
  dup lf-dq-sides 2dup lf-dq-same-proj? 0= if 2drop lf-dq-full-step exit then
  rot ['] lf-dq-proj-back ['] lf-lzp-visit lf-dq-open ;

\ Steps 6 and 7, then 8.
: lf-dq-tail ( frames -- ... frames next )
  >r r@ lf-dq-sides 2dup r@ lf-dq-consts
  ok-then? 0= if nip nip r> lf-dq-end-failed exit then
  if 2drop true r> lf-dq-end exit then
  2dup lf-dq-fvars? if 2drop true r> lf-dq-end exit then
  2drop r> lf-dq-proj-step ;

\ ---------------------------------------------------------------------------
\ Lazy delta reduction (959-1075; see the header) on the visit's tn and
\ sn. compare (declaration.cpp 24-49) of two declarations' hints: -1
\ unfolds t first, 1 s, 0 both.
: lf-lz-hints ( dt ds -- kt ks ) lf-idecl-hint @ swap lf-idecl-hint @ swap ;
: lf-lz-heights ( dt ds -- c )
  lf-idecl-height @ swap lf-idecl-height @ 2dup = if 2drop 0 else < if -1 else 1 then then ;
: lf-lz-kinds ( kt ks -- c )
  over lf-hint-opaque = if 2drop 1 exit then
  dup lf-hint-opaque = if 2drop -1 exit then
  drop lf-hint-abbrev = if -1 else 1 then ;
: lf-lz-compare ( dt ds -- c )
  2dup lf-lz-hints 2dup <> if lf-lz-kinds nip nip exit then
  drop lf-hint-regular = if lf-lz-heights else 2drop 0 then ;

\ The step serves two loops (lf-lz-loop): is_def_eq_core's, on the cells
\ t, s, tn and sn, and lazy_delta_proj_reduction's (step 8), on leaf,
\ leaf, tc and sc. A visit whose cell 3 is a projection leaf is the
\ second: a leaf is never a term, and step 3's whnf_core refuses a t
\ that is one (invalid) before lazy delta begins.
: lf-lz-proj? ( frames -- flag ) 3 swap frame-pick lf-proj-leaf? ;

\ reduce_proj_core (420-441) of c for leaf, the first step of a visit of
\ its own that ends with ( field|-1 outcome frames 0 ); iota.fs, which
\ holds the constructor lookups, sets it; unknown until then.
defer lf-dq-reduce-proj ( c leaf frames -- ... frames next )
:noname ( c leaf frames -- -1 outcome frames 0 )
  >r lf-dq-site lf-diag-undecided lf-diag-note -1 outcome-unknown r> 0 ;
is lf-dq-reduce-proj
: lf-dq-reduce-call ( c leaf frames cont -- ... frames next )
  ['] lf-dq-reduce-proj lf-dq-open ;
\ lazy_delta_proj_reduction's end (1089-1098), when its step answers
\ undecided or no: reduce_proj_core of tc, then of sc (tc's field kept
\ across); is_def_eq_core of the two fields when both are found, else of
\ tc and sc, is the answer.
: lf-lzp-sides ( frames -- ... frames next )
  dup lf-dq-sides rot ['] lf-dq-final lf-dq-core-call ;
: lf-lzp-s-back ( fs outcome frames -- ... frames next )
  >r r@ frame-restore -rot ok-then? 0= if nip r> lf-dq-end-failed exit then
  dup 0< if 2drop r> lf-lzp-sides exit then
  r> ['] lf-dq-final lf-dq-core-call ;
: lf-lzp-t-back ( ft outcome frames -- ... frames next )
  >r ok-then? 0= if r> lf-dq-end-failed exit then
  dup 0< if drop r> lf-lzp-sides exit then
  r@ lf-dq-sides nip 3 r@ frame-pick rot r@ frame-save
  r> ['] lf-lzp-s-back lf-dq-reduce-call ;
: lf-lzp-reduce ( frames -- ... frames next )
  dup lf-dq-sides drop 3 2 pick frame-pick rot ['] lf-lzp-t-back lf-dq-reduce-call ;
\ The step's ends that differ between the loops: undecided (DefUnknown)
\ goes on to step 6, or ends lazy_delta_proj_reduction; no (DefDiff) is
\ the answer, or ends it.
: lf-lz-unknown ( frames -- ... frames next )
  dup lf-lz-proj? if lf-lzp-reduce else lf-dq-tail then ;
: lf-lz-differ ( frames -- ... frames next )
  dup lf-lz-proj? if lf-lzp-reduce else false swap lf-dq-end then ;

\ After an unfolding: quick_is_def_eq answers yes or no, or the loop goes
\ on (1017-1021).
: lf-lz-quick-back ( lbool outcome frames -- ... frames next )
  >r ok-then? 0= if r> lf-dq-end-failed exit then
  dup lf-dq-undef = if drop r> ['] lf-lz-loop exit then
  lf-dq-flag if true r> lf-dq-end else r> lf-lz-differ then ;
: lf-lz-quick ( frames -- ... frames next )
  >r r@ lf-dq-sides r> ['] lf-lz-quick-back lf-qk-call ;
\ t's side unfolded: tn' takes tn's place, then step xt ( frames -- ...
\ frames next ); a failure ends the visit.
: lf-lz-t! ( tn' frames -- frames ) dup >r lf-dq-sides nip r@ lf-dq-sides! r> ;
: lf-lz-t-then ( tn' outcome frames xt -- ... frames next )
  2>r ok-then? 0= if 2r> drop lf-dq-end-failed exit then 2r> >r lf-lz-t! r> execute ;
: lf-lz-t-back ( tn' outcome frames -- ... frames next ) ['] lf-lz-quick lf-lz-t-then ;
: lf-lz-s-back ( sn' outcome frames -- ... frames next )
  >r ok-then? 0= if r> lf-dq-end-failed exit then
  r@ lf-dq-sides drop swap r@ lf-dq-sides! r> lf-lz-quick ;
\ A side unfolded (unfold_definition) and put in whnf_core with
\ cheap_proj, a child visit continuing with cont.
: lf-lz-unfold ( node frames cont -- ... frames next )
  >r tuck lf-whnf-unfold ok-then? 0= if r> drop swap lf-dq-end-failed exit then
  swap r> lf-whnf-cheap-call ;
\ t's side unfolded, then cont.
: lf-lz-unfold-tn ( frames cont -- ... frames next )
  >r dup lf-dq-sides drop swap r> lf-lz-unfold ;
: lf-lz-unfold-t ( frames -- ... frames next ) ['] lf-lz-t-back lf-lz-unfold-tn ;
: lf-lz-unfold-s ( frames -- ... frames next )
  dup lf-dq-sides nip swap ['] lf-lz-s-back lf-lz-unfold ;
: lf-lz-both-back ( tn' outcome frames -- ... frames next )
  ['] lf-lz-unfold-s lf-lz-t-then ;
: lf-lz-unfold-both ( frames -- ... frames next ) ['] lf-lz-both-back lf-lz-unfold-tn ;
\ Where only one side unfolds (971-991): try_unfold_proj_app (950-957)
\ on the other first. When its head is a projection (Lean's get_app_fn
\ is_proj), its whnf_core without cheap_proj, a child visit; a result
\ that is not == to it (Lean's !=: a new node is walked, lf-dq-same)
\ takes its place, then quick_is_def_eq; otherwise the side unfolds.
: lf-lz-proj-head? ( node -- flag ) lf-whnf-head lf-proj? ;
: lf-lz-new? ( old new frames -- flag outcome )
  >r 2dup = if 2drop r> drop false outcome-ok exit then
  r> lf-dq-same ok-then? if 0= outcome-ok else false swap then ;
: lf-lz-proj-t-back ( tn' outcome frames -- ... frames next )
  >r ok-then? 0= if r> lf-dq-end-failed exit then
  r@ lf-dq-sides drop over r@ lf-lz-new? ok-then? 0= if nip r> lf-dq-end-failed exit then
  if outcome-ok r> lf-lz-t-back else drop r> lf-lz-unfold-s then ;
: lf-lz-proj-s-back ( sn' outcome frames -- ... frames next )
  >r ok-then? 0= if r> lf-dq-end-failed exit then
  r@ lf-dq-sides nip over r@ lf-lz-new? ok-then? 0= if nip r> lf-dq-end-failed exit then
  if outcome-ok r> lf-lz-s-back else drop r> lf-lz-unfold-t then ;
: lf-lz-try-t ( frames -- ... frames next )
  dup lf-dq-sides drop dup lf-lz-proj-head? 0= if drop lf-lz-unfold-s exit then
  swap ['] lf-lz-proj-t-back lf-whnf-core-call ;
: lf-lz-try-s ( frames -- ... frames next )
  dup lf-dq-sides nip dup lf-lz-proj-head? 0= if drop lf-lz-unfold-t exit then
  swap ['] lf-lz-proj-s-back lf-whnf-core-call ;
\ The same declaration with a regular hint, both applications (998-1011):
\ equivalent universe arguments and is_def_eq_args, yes; otherwise both
\ unfold.
\ Lean's failure cache (failed_before and cache_failure, 1004-1009) on the
\ visit's tn and sn: whether the test failed before, and recording that
\ it failed; by default never, and nothing (kernel/caches.fs sets them).
defer lf-lz-failed? ( frames -- frames flag )
:noname ( frames -- frames flag ) false ; is lf-lz-failed?
defer lf-lz-failure ( frames -- frames )
:noname ( frames -- frames ) ; is lf-lz-failure
: lf-lz-args-back ( flag outcome frames -- ... frames next )
  >r ok-then? 0= if r> lf-dq-end-failed exit then
  if true r> lf-dq-end else r> lf-lz-failure lf-lz-unfold-both then ;
: lf-lz-levels ( tn sn frames -- flag outcome )
  >r lf-whnf-head swap lf-whnf-head swap r@ lf-lcmp-fuel lf-dq-lend lf-dq-level-lists
  r> lf-lcmp-fuel lf-dq-repay ;
: lf-lz-arguments ( frames -- ... frames next )
  lf-lz-failed? if lf-lz-unfold-both exit then
  >r r@ lf-dq-sides r@ lf-lz-levels ok-then? 0= if r> lf-dq-end-failed exit then
  if r@ lf-dq-sides r> ['] lf-lz-args-back lf-ar-call
  else r> lf-lz-failure lf-lz-unfold-both then ;
: lf-lz-same? ( dt ds frames -- flag )
  >r over = swap lf-idecl-hint @ lf-hint-regular = and r> lf-dq-sides lf-dq-apps? and ;
\ The step's choice, from is_delta of each side: a declaration or
\ lf-whnf-none.
: lf-lz-none? ( d -- flag ) lf-whnf-none = ;
: lf-lz-decide ( dt ds frames -- ... frames next )
  >r over lf-lz-none? over lf-lz-none? and if 2drop r> lf-lz-unknown exit then
  over lf-lz-none? if 2drop r> lf-lz-try-t exit then
  dup lf-lz-none? if 2drop r> lf-lz-try-s exit then
  2dup lf-lz-compare ?dup if nip nip 0< if r> lf-lz-unfold-t else r> lf-lz-unfold-s then exit then
  r@ lf-lz-same? if r> lf-lz-arguments else r> lf-lz-unfold-both then ;
: lf-lz-delta ( node -- decl outcome )
  lf-whnf-head dup lf-whnf-const? if lf-whnf-delta-of else drop lf-whnf-none outcome-ok then ;
\ Outside a check (K1, see the header): a constant at either head is a
\ doubt, and the loop ends undecided.
: lf-lz-blind ( frames -- ... frames next )
  >r r@ lf-dq-sides 2dup lf-whnf-head lf-whnf-const? swap lf-whnf-head lf-whnf-const? or
  if lf-diag-needs-unfolding lf-dq-doubt else 2drop then r> lf-lz-unknown ;
\ One step of lazy_delta_reduction_step: is_delta of each side, then the
\ choice.
: lf-lz-step ( frames -- ... frames next )
  lf-whnf-env? 0= if lf-lz-blind exit then
  >r r@ lf-dq-sides swap lf-lz-delta ok-then? 0= if nip r> lf-dq-end-failed exit then
  swap lf-lz-delta ok-then? 0= if nip r> lf-dq-end-failed exit then
  r> lf-lz-decide ;
\ The loop's first tests (1043-1066). is_def_eq_offset: both sides
\ zero is yes; both with a predecessor (lf-dq-pred, by name for Nat.succ)
\ compare those by is_def_eq_core, and that is the answer. Then, when
\ neither side has a free variable or in eager mode, reduce_nat on tn,
\ then on sn (whnf.fs, lf-whnf-nat-call): where it computes v,
\ is_def_eq_core of v and the other side is the answer (plan task
\ 5.2.3); otherwise the step. lazy_delta_proj_reduction's loop is the
\ step alone (1085-1087). Each round costs one unit of fuel.
: lf-lz-offset ( t s frames -- ... frames next )
  >r lf-dq-pred ok-then? 0= if nip r> lf-dq-end-failed exit then
  swap lf-dq-pred ok-then? 0= if nip r> lf-dq-end-failed exit then
  swap r> ['] lf-dq-final lf-dq-core-call ;
: lf-lz-closed? ( tn sn frames -- flag outcome )
  >r swap r@ lf-whnf-free? ok-then? 0= if nip r> drop false swap exit then
  if drop r> drop false outcome-ok exit then
  r> lf-whnf-free? ok-then? if 0= outcome-ok else false swap then ;
: lf-lz-nat-s-back ( r outcome frames -- ... frames next )
  >r ok-then? 0= if r> lf-dq-end-failed exit then
  dup lf-whnf-none = if drop r> lf-lz-step exit then
  r@ lf-dq-sides drop swap r> ['] lf-dq-final lf-dq-core-call ;
: lf-lz-nat-s ( frames -- ... frames next )
  dup lf-dq-sides nip dup lf-whnf-k7?
  if swap ['] lf-lz-nat-s-back lf-whnf-nat-call else drop lf-lz-step then ;
: lf-lz-nat-t-back ( r outcome frames -- ... frames next )
  >r ok-then? 0= if r> lf-dq-end-failed exit then
  dup lf-whnf-none = if drop r> lf-lz-nat-s exit then
  r@ lf-dq-sides nip r> ['] lf-dq-final lf-dq-core-call ;
: lf-lz-nat-t ( frames -- ... frames next )
  dup lf-dq-sides drop dup lf-whnf-k7?
  if swap ['] lf-lz-nat-t-back lf-whnf-nat-call else drop lf-lz-nat-s then ;
: lf-lz-nat ( frames -- ... frames next )
  >r r@ lf-dq-sides lf-whnf-k7? swap lf-whnf-k7? or 0= if r> lf-lz-step exit then
  lf-dq-eager @ if r> lf-lz-nat-t exit then
  r@ lf-dq-sides r@ lf-lz-closed? ok-then? 0= if r> lf-dq-end-failed exit then
  if r> lf-lz-nat-t else r> lf-lz-step then ;
:noname ( frames -- ... frames next )
  dup lf-dq-spend dup ok? 0= if swap lf-dq-end-failed exit then drop
  dup lf-lz-proj? if lf-lz-step exit then
  >r r@ lf-dq-sides 2dup lf-dq-nat-zero? swap lf-dq-nat-zero? and
  if 2drop true r> lf-dq-end exit then
  2dup lf-dq-pred? swap lf-dq-pred? and if r> lf-lz-offset exit then
  2drop r> lf-lz-nat ; is lf-lz-loop

\ ---------------------------------------------------------------------------
\ Step 4 (1163-1164), is_def_eq_proof_irrel (899-906): when t is a proof,
\ is_def_eq of its type and s's type is the answer, yes or no; when it is
\ not, lazy delta; undecided (no typer) a doubt, then lazy delta.
: lf-dq-irrel ( type frames -- ... frames next )
  >r r@ lf-dq-sides nip r@ lf-dq-type-of ok-then? 0= if nip r> lf-dq-end-failed exit then
  r> ['] lf-dq-final lf-dq-call ;
: lf-dq-proof-step ( frames -- ... frames next )
  >r r@ lf-dq-sides drop r@ lf-dq-proof? ok-then? 0= if nip r> lf-dq-end-failed exit then
  dup lf-dq-yes = if drop r> lf-dq-irrel exit then
  lf-dq-undef = if r@ lf-dq-sides lf-diag-proof-pending lf-dq-doubt then
  drop r> lf-lz-loop ;
\ Step 3: whnf_core with cheap_proj of t (tn), then of s (sn);
\ quick_is_def_eq again when either changed.
: lf-dq-quick2 ( lbool outcome frames -- ... frames next )
  >r ok-then? 0= if r> lf-dq-end-failed exit then
  dup lf-dq-undef <> if lf-dq-flag r> lf-dq-end exit then drop r> lf-dq-proof-step ;
: lf-dq-sn ( sn outcome frames -- ... frames next )
  >r ok-then? 0= if r> 3 lf-dq-drop-failed exit then
  r@ frame-save r@ lf-dq-cells lf-dq-changed?
  if r> ['] lf-dq-quick2 lf-qk-call else 2drop r> lf-dq-proof-step then ;
: lf-dq-tn ( tn outcome frames -- ... frames next )
  >r ok-then? 0= if r> 2 lf-dq-drop-failed exit then
  r@ frame-save 1 r@ frame-pick r> ['] lf-dq-sn lf-whnf-cheap-call ;
: lf-dq-core ( frames -- ... frames next )
  dup lf-dq-sides drop swap ['] lf-dq-tn lf-whnf-cheap-call ;
\ Step 2 (1142-1146), on the visit's t and s.
: lf-dq-true-back ( t' outcome frames -- ... frames next )
  >r ok-then? 0= if r> 2 lf-dq-drop-failed exit then
  lf-dq-true? if true r> 2 lf-dq-drop-answer else r> lf-dq-core then ;
: lf-dq-bool ( frames -- ... frames next )
  >r r@ lf-dq-sides lf-dq-true? 0= if drop r> lf-dq-core exit then
  lf-dq-eager @ if r> ['] lf-dq-true-back lf-whnf-call exit then
  dup r@ lf-whnf-free? ok-then? 0= if nip r> 2 lf-dq-drop-failed exit then
  if drop r> lf-dq-core else r> ['] lf-dq-true-back lf-whnf-call then ;
\ Step 1.
: lf-dq-quick1 ( lbool outcome frames -- ... frames next )
  >r ok-then? 0= if r> 2 lf-dq-drop-failed exit then
  dup lf-dq-undef <> if lf-dq-flag r> 2 lf-dq-drop-answer exit then drop r> lf-dq-bool ;
:noname ( t s frames -- ... frames next )
  lf-dq-save2 ['] lf-dq-quick1 lf-qk-call ; is lf-dq-visit

\ ---------------------------------------------------------------------------
\ The public words (see the header). Each -on word runs one visit to its
\ end; lf-quick-on answers Lean's lbool (lf-dq-yes, lf-dq-no,
\ lf-dq-undef), the others a flag. lf-defeq-on settles the doubt record.
: lf-defeq-call ( t s frames cont -- ... frames next ) lf-dq-call ;
: lf-defeq-on ( t s frames -- flag outcome )
  0 lf-dq-state lf-dqs-doubt ! ['] lf-dq-call frame-through drop lf-dq-settle ;
: lf-quick-on ( t s frames -- lbool outcome ) ['] lf-qk-call frame-through drop ;
: lf-defeq-binding-on ( t s frames -- flag outcome ) ['] lf-bd-call frame-through drop ;
: lf-defeq-app-on ( t s frames -- flag outcome ) ['] lf-ap-call frame-through drop ;
: lf-defeq-args-on ( t s frames -- flag outcome ) ['] lf-ar-call frame-through drop ;
