\ simpGoal: simp at hypotheses and the target (plan row FE9, simp slice
\ SL1a-2 of docs/design/TACTIC_SIMP.md): Lean 4.35.0's simpGoal
\ (src/lean/Lean/Meta/Tactic/Simp/Main.lean:874-911) with applySimpResult
\ (807-822), over simp/main.fs's lf-simp and lf-goal-simp-target.
\ - lf-goal-simp ( goal target? fvars -- goal' | 0 ): in goal's
\   context (checkNotAssigned first), each hypothesis of the run fvars in
\   order: its type T instantiated and simplified (lf-simp, maxSteps
\   lf-simp-max-steps, simp only's default)
\   to T'. With a proof h: T' False closes the goal, assigned
\   False.elim.{u} target (Eq.mp.{0} T False h fvar); else the hypothesis
\   (its local, T', Eq.mp.{u} T T' h fvar, u T's level) is kept to assert
\   and fvar to clear. With none: T' False closes the goal, assigned
\   False.elim.{u} target fvar; else the goal so far takes T' as the
\   type of the hypothesis at fvar's place (fvar, or the one an earlier
\   change of fvar put there: at[ h h ]; meta-tactic/assert.fs's
\   lf-goal-replace-local-decl-defeq: a hypothesis something depends on
\   not supported yet). Then with target?
\   the target (lf-goal-simp-target, in the goal so far: True closes it);
\   then the kept hypotheses asserted at once (lf-goal-assert-hyps) and
\   the hypotheses simplified with a proof cleared, last first, each kept
\   when something depends on it (tryClearMany). 0 when the goal was
\   closed, else the goal reached; when that is goal itself, Lean's error
\   500 "`simp` made no progress" (failIfUnchanged, Main.lean:909: once,
\   for all the locations together).
\ eraseTheorem (.fvar h) (Main.lean:886) erases nothing here: simp only's
\ rules have origin .decl or .stx (a hypothesis in the brackets,
\ Elab/Tactic/Simp.lean:363), never .fvar (simp [*]'s, slice SL3a), so
\ `simp only [h] at h` rewrites h with itself (twin w-at-self).
\ Lean call list: instantiateMVars -> lf-instantiate!; simp -> lf-simp;
\ mkFalseElim -> lf-mk-false-elim; mkConst Eq.mp, getLevel -> sg-mp;
\ replaceLocalDeclDefEq -> lf-goal-replace-local-decl-defeq; simpTarget
\ -> lf-goal-simp-target; assertHypotheses -> lf-goal-assert-hyps;
\ tryClearMany -> lf-goal-try-clear-many.
\ Throws as meta-must.fs's words do. Untrusted: the kernel checks the
\ finished term. State: sg-frames (a frame per call open, meta-must.fs's
\ lf-with-record), in the checker context (ADR 0009).
\ Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/slab.fs
require ../../lib/runs.fs
require ../../lib/context.fs
require ../../author/errors.fs
require ../tactic-run.fs
require ../meta-tactic/assert.fs
require ./main.fs
require ./congr.fs   \ main.fs's congruence, through its hook sm-congr

500 lfa-lean s" `simp` made no progress" lfa-code: lfa-e-simp-progress
begin-structure /sg
  field: sg-orig      \ the goal given (Lean's mvarId)
  field: sg-goal      \ the goal so far (Lean's mvarIdNew)
  field: sg-max       \ maxSteps
  field: sg-target    \ true: the target too (simplifyTarget)
  field: sg-fvar      \ the hypothesis at hand
  field: sg-asserts   \ toAssert: a run of (local type value) triples
  field: sg-clears    \ the hypotheses simplified with a proof, a run
end-structure
/sg context-slab: sg-frames
: sg ( -- frame ) sg-frames slab-last ;
: sg-goal@ ( -- goal ) sg sg-goal @ ;
: sg-fvar@ ( -- fvar ) sg sg-fvar @ ;
: sg-assert+ ( x -- ) sg sg-asserts lf-run+! ;

\ ---- applySimpResult: Eq.mp.{u} T T' h val (u T's level), False.elim.
: sg-mp-of ( T -- f ) dup lf-level! >r s" Eq.mp" r> lf-mk-const1 swap lf-mk-app ;
: sg-mp ( T T' h val -- e ) 2>r >r sg-mp-of r> 2r> 3 lf-mk-app-n ;
: sg-false? ( e -- flag ) s" False" lf-meta-const-named? ;
: sg-close ( val -- )
  sg-goal@ dup lf-goal-type rot lf-mk-false-elim lf-mvar-assign lf-must ;
: sg-kept ( val T' -- )
  lf-mctx-view sg-fvar@ lf-view-local-of sg-assert+ sg-assert+ sg-assert+
  sg-fvar@ sg sg-clears lf-run+! ;
: sg-proved ( T T' h -- closed? )
  over >r sg-fvar@ sg-mp r> dup sg-false? if drop sg-close true exit then sg-kept false ;
\ The hypothesis at fvar's place in the goal so far: fvar, or the free
\ variable a change by definition put there (Lean keeps fvarId and
\ changes its type in mvarIdNew's context, so at[ h h ] meets h' there).
: sg-place ( fvar -- k ) sg sg-orig @ lf-goal-view swap lf-view-find lf-found ;
: sg-now ( fvar -- fvar' ) sg-place sg-goal@ lf-goal-view swap lf-view-fvar ;
: sg-defeq ( T T' -- closed? )
  nip dup sg-false? if drop sg-fvar@ sg-close true exit then
  sg-goal@ sg-fvar@ sg-now rot lf-goal-replace-local-decl-defeq sg sg-goal ! false ;

\ ---- Each hypothesis, then the target; the goal closed answers true.
: sg-hyp ( fvar -- closed? )
  dup sg sg-fvar ! lf-fvar-type lf-instantiate! dup sg sg-max @ lf-simp
  dup lf-simp-none? if drop sg-defeq else sg-proved then ;
: sg-hyps ( fvars -- closed? ) ['] sg-hyp run-any? ;
: sg-target? ( -- closed? )
  sg sg-target @ 0= if false exit then
  sg-goal@ sg sg-max @ lf-goal-simp-target dup if sg sg-goal ! false else drop true then ;

\ ---- assertHypotheses, then tryClearMany (the last first).
: sg-finish ( -- goal' )
  sg-goal@ sg sg-asserts @ lf-goal-assert-hyps sg sg-clears @ lf-goal-try-clear-many ;
\ failIfUnchanged: the goal reached is the one given.
: sg-progress ( goal' -- goal' )
  dup sg sg-orig @ = if lfa-e-simp-progress lf-tac-stop then ;

: sg-fill ( goal target? fvars -- fvars )
  swap sg sg-target ! swap lf-goal-not-assigned dup sg sg-orig ! sg sg-goal !
  lf-simp-max-steps sg sg-max ! 0 sg sg-asserts ! 0 sg sg-clears ! ;
: sg-body ( fvars -- goal' | 0 )
  sg-hyps if 0 exit then sg-target? if 0 exit then sg-finish sg-progress ;
: sg-run ( goal target? fvars -- goal' | 0 ) sg-fill sg-goal@ ['] sg-body lf-with-goal ;
: lf-goal-simp ( goal target? fvars -- goal' | 0 ) sg-frames ['] sg-run lf-with-record ;

base !   \ the BASE this file was loaded with
