\ Level unification of the front end (plan FE1c; ADR 0021 D6): a port of
\ Lean 4.35.0's Meta/LevelDefEq.lean (isLevelDefEqAuxImpl and solve) and
\ Meta/DecLevel.lean (decLevel?), in Lean's order, for levels without max
\ or imax: k successors of zero, a universe parameter or a level
\ metavariable (src/front/mvars.fs). Lean normalizes a level with max or
\ imax (Level.normalize) and has rules of its own for it (solveSelfMax,
\ the univApprox rules); none is ported yet, so such a pair answers
\ unsupported, never a guess.
\ lf-meta-level-defeq ( l r -- flag outcome ) is Lean's isLevelDefEqAux:
\ - both successors: compare their predecessors;
\ - the same level under their successors (Lean's getLevelOffset ==):
\   equal when they have as many successors;
\ - an assigned metavariable: compare the instantiated levels
\   (instantiateLevelMVars, mvars.fs);
\ - solve l r, then solve r l: a metavariable that is not read-only (its
\   depth is the context's, Lean's isReadOnly) is assigned the other side
\   (the deeper of two metavariables first) unless it occurs there; zero
\   is never a successor; succ u against a parameter is false (decLevel?,
\   Lean's next rule, finds no predecessor in these levels);
\ - else false when neither side holds an assignable metavariable;
\   otherwise Lean postpones the pair (postponeIsLevelDefEq): unsupported.
\ An assignment ends the comparison true, so no false answer leaves one
\ behind, as Lean's checkpointDefEq would undo it.
\ Two differences, for instance synthesis (plan FE1e): Lean's isReadOnly
\ and isLevelMVarAssignable compare with mctx.levelAssignDepth, taken
\ here to be lf-mctx-depth (equal until withNewMCtxDepth with
\ allowLevelAssignments := true); and under isDefEqStuckEx Lean throws
\ isDefEqStuck for a stuck pair holding a metavariable, where this
\ answers false.
\ Outcomes: ok with the flag; unsupported as above; invalid for a level
\ that is not in the store or a stale metavariable; full when the store
\ has no room for an instantiated level. Each round peels successors, or
\ instantiates (which mvars.fs keeps acyclic), or answers, so the loop
\ ends; no host recursion. Untrusted front-end code: only the kernel's
\ check of the finished term decides.
\ Words: lf-meta-level-defeq ( l r -- flag outcome ).
\ No state of its own: the metavariables are mvars.fs's context.

require ../lib/lib.fs
require ../core/levels.fs
require ../core/mvar-leaves.fs
require ./mvars.fs
require ./level-simp.fs

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

\ Shapes (ld-offset, ld-base, ld-same? ...): level-simp.fs.
: ld-bases= ( l r -- flag ) ld-base swap ld-base ld-same? ;
: ld-offsets= ( l r -- flag ) ld-offset nip swap ld-offset nip = ;
: ld-down ( l r -- l' r' ) ld-pred swap ld-pred swap ;
: ld-both-succ? ( l r -- flag ) ld-succ? swap ld-succ? and ;
: ld-peel ( l r -- l' r' ) begin 2dup ld-both-succ? while ld-down repeat ;
\ A base with max or imax (not ported); a stale metavariable.
: ld-plain? ( level -- flag ) ld-base lf-level-tag@ lf-level-binary-tag? 0= ;
: ld-flat? ( l r -- flag ) ld-plain? swap ld-plain? and ;
: ld-stale? ( level -- flag )
  ld-base dup lf-level-mvar? if lf-level-mvar-live? 0= else drop false then ;
: ld-sound? ( l r -- flag ) ld-stale? swap ld-stale? or 0= ;

\ Metavariables: assigned, read-only (Lean's LMVarId.isReadOnly: made at
\ a smaller depth than the context's), assignable.
: ld-set? ( level -- flag ) ld-base lf-level-mvar-value dup if nip then ;
: ld-assigned? ( l r -- flag ) ld-set? swap ld-set? or ;
: ld-depth ( mvar -- depth ) lf-level-mvar-depth ;
: ld-read-only? ( mvar -- flag ) ld-depth lf-mctx-depth < ;
: ld-open? ( level -- flag )
  ld-base dup lf-level-mvar? if ld-read-only? 0= else drop false then ;
: ld-assign ( mvar value -- code )
  lf-level-mvar-assign dup ok? if drop ld-yes else ld-end then ;

\ instantiateLevelMVars on both sides, for the next round.
: ld-inst1 ( level -- level' code )
  lf-level-instantiate-mvars dup ok? if drop ld-again else ld-end then ;
: ld-inst ( l r -- l' r' code )
  ld-inst1 dup ld-again = if drop swap ld-inst1 >r swap r> then ;

\ solve (succ u) v: false for a parameter v; else Lean compares u with
\ decLevel? v, which here has none: v is no successor (both were peeled),
\ no max, and a metavariable v met solve's rule for (_, ?v) first; so
\ undef (and Lean's occurs test before it gives undef too).
: ld-solve-succ ( u v -- u v code ) dup ld-param? if ld-no else ld-undef then ;

\ solve u v for a metavariable u: read-only, undef; a deeper metavariable
\ v is assigned u; else u := v. (Lean's next test, u occurring in v, never
\ holds here: v's base is not u, or the first rule had answered.)
: ld-deeper? ( v u -- flag )
  over lf-level-mvar? if ld-depth swap ld-depth < else 2drop false then ;
: ld-solve-mvar ( u v -- u v code )
  over ld-read-only? if ld-undef exit then
  2dup swap ld-deeper? if 2dup swap ld-assign else 2dup ld-assign then ;
: ld-solve-zero ( u v -- u v code ) dup ld-succ? if ld-no else ld-undef then ;
: ld-zero? ( level -- flag ) lf-level-tag@ lf-level-tag-zero = ;
: ld-solve ( u v -- u v code )
  over lf-level-mvar? if ld-solve-mvar exit then dup lf-level-mvar? if ld-undef exit then
  over ld-zero? if ld-solve-zero exit then
  over ld-succ? if ld-solve-succ else ld-undef then ;
\ Both orders, then the stuck pair: false, or postponed (unsupported).
: ld-stuck ( l r -- l r code )
  2dup ld-open? swap ld-open? or if outcome-unsupported ld-end else ld-no then ;
: ld-undef? ( code -- flag ) ld-undef = ;
: ld-solve2 ( l r -- l' r' code )
  ld-solve dup ld-undef? if drop swap ld-solve then
  dup ld-undef? if drop ld-stuck then ;

\ One round of isLevelDefEqAuxImpl.
: ld-round ( l r -- l' r' code )
  ld-peel 2dup ld-sound? 0= if outcome-invalid ld-end exit then
  2dup ld-bases= if 2dup ld-offsets= negate exit then
  2dup ld-flat? 0= if outcome-unsupported ld-end exit then
  2dup ld-assigned? if ld-inst else ld-solve2 then ;
: lf-meta-level-defeq ( l r -- flag outcome )
  2dup lf-level-pair-valid? 0= if 2drop false outcome-invalid exit then
  begin ld-round dup ld-again = while drop repeat ld-answer ;
