\ Level unification of the front end (plan FE1c; ADR 0021 D6): a port of
\ Lean 4.35.0's Meta/LevelDefEq.lean (isLevelDefEqAuxImpl and solve),
\ in Lean's order, over levels with successors, max, imax, universe
\ parameters and level metavariables (src/front/mvars.fs).
\ lf-meta-level-defeq ( l r -- flag outcome ) is Lean's isLevelDefEq
\ (isLevelDefEqAux under checkpointDefEq):
\ - both successors: compare their predecessors;
\ - the same level under their successors (Lean's getLevelOffset ==,
\   structural): equal when they have as many successors;
\ - each side's metavariables instantiated (instantiateLevelMVars) and
\   the side normalized (Level.normalize, level-normalize.fs): when
\   either changes, compare the new pair;
\ - solve l r, then solve r l. A metavariable that is not read-only (its
\   depth is the context's, Lean's isReadOnly) is assigned the other side
\   (the deeper of two metavariables first) unless it occurs there; zero
\   against max a b compares zero with a, then with b (both must hold),
\   against imax a b with b, against a successor is false; succ u
\   against a parameter is false; otherwise undef;
\ - else false when neither side holds an assignable metavariable
\   (hasAssignableLevelMVar); otherwise Lean postpones the pair
\   (postponeIsLevelDefEq): unsupported.
\ Not ported, answered unsupported (never a guess): solveSelfMax (?m
\ against a max holding ?m) and decLevel? of a max or an imax (succ u
\ against one). Lean's univApprox rules apply only in its approximate
\ mode, which the front end has not (Lean's default is off).
\ The comparison runs under a mark of mvars.fs: unless the answer is
\ true, every assignment it made is rolled back, as checkpointDefEq does.
\ Two differences, for instance synthesis (plan FE1e): Lean's isReadOnly
\ and isLevelMVarAssignable compare with mctx.levelAssignDepth, taken
\ here to be lf-mctx-depth (equal until withNewMCtxDepth with
\ allowLevelAssignments := true); and under isDefEqStuckEx Lean throws
\ isDefEqStuck for a stuck pair holding a metavariable, where this
\ answers false.
\ Outcomes: ok with the flag; unsupported as above; invalid for a level
\ that is not in the store or holds a stale metavariable; full when the
\ store or the heap has no room. The pairs a conjunction leaves for later
\ wait on a heap stack. Each round peels successors, or normalizes (a
\ normal form normalizes to itself), or solves, so the loop ends; no host
\ recursion. Untrusted front-end code: only the kernel's check of the
\ finished term decides.
\ Words: lf-meta-level-defeq ( l r -- flag outcome ).
\ State: the slab ld-pairs (a member of the checker context, ADR 0009);
\ the metavariables are mvars.fs's context.

require ../lib/lib.fs
require ../core/levels.fs
require ../core/mvar-leaves.fs
require ./mvars.fs
require ./level-simp.fs
require ./level-normalize.fs

\ The rounds pass the pair and a code: the next round's pair, an answer,
\ Lean's LBool.undef (the next rule), or an outcome that ends it, plus 8.
0 constant ld-no
1 constant ld-yes
2 constant ld-undef
3 constant ld-again
8 constant ld-ends
: ld-end ( outcome -- code ) ld-ends + ;
: ld-answer ( l r code -- flag outcome )
  nip nip dup ld-ends < if ld-yes = outcome-ok else ld-ends - false swap then ;
: ld-undef? ( code -- flag ) ld-undef = ;
\ A test's flag and outcome: end when it holds, else undef; or its failure.
: ld-when ( flag outcome end -- code )
  swap dup ok? if drop swap if ld-end else drop ld-undef then else nip nip ld-end then ;

\ The pairs still to compare: a conjunction's second.
2 cells context-slab: ld-pairs
: ld-push ( l r -- outcome )
  1 ld-pairs slab-claim dup ok? 0= if nip nip nip exit then
  drop ld-pairs slab-at 2! outcome-ok ;
: ld-pop ( -- l r ) ld-pairs dup slab-count 1- swap slab-at 2@ -1 ld-pairs slab-commit ;

\ Shapes (ld-offset, ld-base, ld-same? ...): level-simp.fs.
: ld-offsets= ( l r -- flag ) ld-offset nip swap ld-offset nip = ;
: ld-down ( l r -- l' r' ) ld-pred swap ld-pred swap ;
: ld-both-succ? ( l r -- flag ) ld-succ? swap ld-succ? and ;
: ld-peel ( l r -- l' r' ) begin 2dup ld-both-succ? while ld-down repeat ;
: ld-zero? ( level -- flag ) lf-level-tag@ lf-level-tag-zero = ;
\ getLevelOffset ==: the offsets decide.
: ld-bases ( l r -- l r code )
  2dup ld-base swap ld-base lf-meta-level= dup ok? 0= if nip ld-end exit then drop
  if 2dup ld-offsets= negate else ld-undef then ;
\ A stale metavariable anywhere in either level: invalid.
: ld-stale ( l r -- l r code )
  over lf-level-stale-mvar? outcome-invalid ld-when dup ld-undef? 0= if exit then drop
  dup lf-level-stale-mvar? outcome-invalid ld-when ;

\ instantiateLevelMVars and normalize: again with the new pair when a
\ side changes (Lean's !=, structural), else undef with the same pair.
: ld-fresh ( level -- level' outcome )
  lf-level-instantiate-mvars dup ok? if drop lf-meta-level-normalize then ;
: ld-differs ( level level' -- level' code )
  tuck lf-meta-level= dup ok? 0= if nip ld-end exit then
  drop if ld-undef else ld-again then ;
: ld-new1 ( level -- level' code )
  dup ld-fresh dup ok? if drop ld-differs else nip ld-end then ;
: ld-codes ( c1 c2 -- c ) over ld-ends < if max else drop then ;
: ld-normal ( l r -- l' r' code ) swap ld-new1 >r swap ld-new1 r> swap ld-codes ;

\ Metavariables: read-only (Lean's LMVarId.isReadOnly: made at a smaller
\ depth than the context's), assigned.
: ld-depth ( mvar -- depth ) lf-level-mvar-depth ;
: ld-read-only? ( mvar -- flag ) ld-depth lf-mctx-depth < ;
: ld-assign ( mvar value -- code )
  lf-level-mvar-assign dup ok? if drop ld-yes else ld-end then ;

\ solve (succ u) v: false for a parameter v; v is no successor (both
\ were peeled) and no metavariable (solve's rule for (_, ?v) came
\ first); decLevel? of zero has none (undef), of a max or an imax is not
\ ported (unsupported).
: ld-solve-succ ( u v -- u v code )
  dup ld-param? if ld-no exit then
  dup ls-tag lf-level-binary-tag? if outcome-unsupported ld-end else ld-undef then ;
\ solve u v for a metavariable u: read-only, undef; a deeper metavariable
\ v is assigned u; u not in v, u := v; else solveSelfMax for a max v (not
\ ported: unsupported), undef for any other.
: ld-deeper? ( v u -- flag )
  over lf-level-mvar? if ld-depth swap ld-depth < else 2drop false then ;
: ld-self ( u v -- u v code )
  dup ls-max? if outcome-unsupported ld-end else ld-undef then ;
: ld-solve-mvar ( u v -- u v code )
  over ld-read-only? if ld-undef exit then
  2dup swap ld-deeper? if 2dup swap ld-assign exit then
  2dup lf-level-mvar-occurs? dup ok? 0= if nip ld-end exit then drop
  if ld-self else 2dup ld-assign then ;
\ solve zero v: zero =?= max a b is zero =?= a and then zero =?= b (the
\ second waits on ld-pairs); zero =?= imax a b is zero =?= b.
: ld-split ( u v -- u v1 code )
  2dup lf-level-second@ ld-push dup ok? 0= if ld-end exit then
  drop lf-level-first@ ld-again ;
: ld-imax? ( level -- flag ) ls-tag lf-level-tag-imax = ;
: ld-solve-zero ( u v -- u v code )
  dup ld-succ? if ld-no exit then dup ls-max? if ld-split exit then
  dup ld-imax? if lf-level-second@ ld-again else ld-undef then ;
: ld-solve ( u v -- u v code )
  over lf-level-mvar? if ld-solve-mvar exit then dup lf-level-mvar? if ld-undef exit then
  over ld-zero? if ld-solve-zero exit then
  over ld-succ? if ld-solve-succ else ld-undef then ;
\ Both orders, then the stuck pair: false, or postponed (unsupported).
: ld-stuck ( l r -- l r code )
  over lf-level-assignable-mvar? outcome-unsupported ld-when dup ld-undef? 0= if exit then
  drop dup lf-level-assignable-mvar? outcome-unsupported ld-when
  dup ld-undef? if drop ld-no then ;
: ld-solve2 ( l r -- l' r' code )
  ld-solve dup ld-undef? if drop swap ld-solve then
  dup ld-undef? if drop ld-stuck then ;

\ One round of isLevelDefEqAuxImpl; a true pair takes the next waiting.
: ld-round ( l r -- l' r' code )
  ld-peel ld-bases dup ld-undef? 0= if exit then drop
  ld-normal dup ld-undef? 0= if exit then drop ld-solve2 ;
: ld-follow ( l r code -- l' r' code' )
  dup ld-yes = ld-pairs slab-count 0> and if drop 2drop ld-pop ld-again then ;
: ld-loop ( l r -- flag outcome )
  ld-stale dup ld-undef? 0= if ld-answer exit then drop
  begin ld-round ld-follow dup ld-again = while drop repeat ld-answer ;
\ checkpointDefEq: kept when true, else rolled back. The mark is the
\ latest open one, so neither is refused; a refusal would be the answer.
: ld-closed ( flag outcome close -- flag outcome )
  dup ok? if drop else nip nip false swap then ;
: ld-close ( flag outcome mark -- flag outcome )
  >r 2dup ok? and if r> lf-mctx-commit else r> lf-mctx-rollback then ld-closed ;
: ld-mark ( l r -- l r mark true | outcome false )
  lf-mctx-mark dup ok? if drop true else nip nip nip false then ;
\ As checkpointDefEq restores the context on an exception: a THROW inside
\ the rounds rolls the mark back and is thrown on.
: ld-run ( l r mark -- flag outcome )
  >r ['] ld-loop catch ?dup if nip nip r> lf-mctx-rollback drop throw then r> ld-close ;
: lf-meta-level-defeq ( l r -- flag outcome )
  2dup lf-level-pair-valid? 0= if 2drop false outcome-invalid exit then
  ld-pairs slab-clear ld-mark if ld-run else false swap then ;
