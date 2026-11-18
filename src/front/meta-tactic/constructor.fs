\ MVarId.constructor, the goal operation of the constructor tactic
\ (docs/design/TACTIC_PLUGINS.md 2.4; slice a2-iii), a port of Lean
\ 4.35.0's src/lean/Lean/Meta/Tactic/Constructor.lean:
\   lf-goal-constructor ( goal -- goals )  MVarId.constructorCore
\       (Constructor.lean:23-40) with findAll, as evalConstructor calls it
\       (Elab/Tactic/ElabTerm.lean:326; ConstructorConfig's first is
\       false): in goal's context (checkNotAssigned first), the goal's
\       type put through whnf and instantiated (getType'); its head must be
\       an inductive type's constant (matchConstInduct; else error 382,
\       "target is not an inductive datatype"); each constructor in the
\       declaration's order, at the head's levels, is tried by
\       MVarId.apply (meta-tactic/apply.fs) from a saved state that is
\       always put back (withoutModifyingState, observing?): a Lean error
\       there (an authoring error whose outcome is invalid, a library
\       rejection) means it does not apply; anything else (not supported,
\       no room, no fuel, a fault) stops the run, never a silent choice.
\       None applies: error 383, "no applicable constructor found". The
\       first that applies is applied again, for real; its goals are the
\       result. Lean also logs a warning when several apply; LeanForth has
\       no warnings, so it is not printed (the choice and the term are
\       Lean's).
\ Lean call list: withContext -> the caller's (tactic-core.fs);
\ checkNotAssigned -> lf-goal-not-assigned (goal.fs); getType' ->
\ lf-whnf! then lf-instantiate! (meta-must.fs); getAppFn -> lf-meta-head;
\ matchConstInduct -> lf-menv-find, lf-menv-kind, lf-ity-ctors@ (meta-env.fs,
\ core/input.fs); mkConst ctor us -> lf-mk-const-id with lf-const-levels
\ (app-builder.fs); withoutModifyingState/observing? -> lf-commit-when
\ answering false, with a CATCH; MVarId.apply -> lf-goal-apply
\ (apply.fs); throwTacticEx -> lf-tac-failed (tactic-basic.fs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own (apply's). Loads in decimal whatever BASE is,
\ then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../author/errors.fs
require ../../core/input.fs
require ../../core/constant-term-boundary.fs
require ../mvars.fs
require ../goals.fs
require ../meta-env.fs
require ../term-eqv.fs
require ../tactic-run.fs
require ../tactic-basic.fs
require ../meta-must.fs
require ../app-builder.fs
require ./goal.fs
require ./apply.fs

382 outcome-invalid s" Tactic `constructor` failed: target is not an inductive datatype"
  lfa-code: lfa-e-ctor-target
383 outcome-invalid s" Tactic `constructor` failed: no applicable constructor found"
  lfa-code: lfa-e-ctor-none

\ ---- matchConstInduct on getType''s head: the head constant and its
\ inductive type's constructors, else error 382.
: mco-not-inductive ( -- ) ['] lf-tac-goal-after. lfa-e-ctor-target lf-tac-failed ;
: mco-decl ( c -- d ) lf-const-name lf-menv-find lf-must ;
: mco-inductive? ( head -- flag )
  dup lf-term-const? if mco-decl lf-menv-kind lf-kind-inductive = else drop false then ;
: mco-ctors ( head -- items n )
  mco-decl lf-menv-data ?dup 0= if outcome-unsupported lf-must then lf-ity-ctors@ ;
: mco-head ( goal -- head )
  lf-mvar-type drop lf-whnf! lf-instantiate! lf-meta-head
  dup mco-inductive? 0= if mco-not-inductive then ;
\ Constructor name at the head's levels (mkConst ctor us).
: mco-const ( head name -- e ) swap lf-const-levels lf-mk-const-id ;

\ ---- observing? inside withoutModifyingState: a Lean error is false.
: mco-lean-error? ( code -- flag )
  dup lf-author-throw = if drop lf-author-code lf-author-outcome outcome-invalid = exit then
  dup lf-meta-thrown? if lf-meta-outcome outcome-rejected = else drop false then ;
: mco-caught ( code -- false )
  dup mco-lean-error? 0= if throw then drop lf-tac-forget false ;
: mco-probe ( goal e -- applies? false )
  ['] lf-goal-apply catch ?dup if nip nip mco-caught else drop true then false ;
: mco-applies? ( goal head name -- flag ) mco-const ['] mco-probe lf-commit-when drop ;

\ The first constructor that applies, else error 383.
: mco-name ( items i -- name ) cells + @ ;
: mco-tried? ( goal head items i -- goal head items flag )
  >r 2 pick 2 pick 2 pick r> mco-name mco-applies? ;
: mco-none ( goal head items -- 0 )
  2drop drop ['] lf-tac-goal-after. lfa-e-ctor-none lf-tac-failed 0 ;
: mco-first ( goal head items n -- name )
  0 ?do i mco-tried? if i mco-name nip nip unloop exit then loop mco-none ;
: lf-goal-constructor ( goal -- goals )
  lf-goal-not-assigned dup mco-head 2dup dup mco-ctors mco-first mco-const lf-goal-apply ;
base !   \ the BASE this file was loaded with
