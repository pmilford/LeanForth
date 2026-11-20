\ MVarId.constructor, the goal operation of the constructor tactic
\ (docs/design/TACTIC_PLUGINS.md 2.4; slice a2-iii), a port of Lean
\ 4.35.0's src/lean/Lean/Meta/Tactic/Constructor.lean:
\   lf-goal-constructor ( goal -- goals )  MVarId.constructorCore
\       (Constructor.lean:23-40), as evalConstructor calls it
\       (Elab/Tactic/ElabTerm.lean:326): in goal's context (checkNotAssigned
\       first), the goal's
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
\       result. Lean (findAll true) probes every constructor, to warn
\       when several apply; LeanForth has no warnings and stops at the
\       first that applies (lib/find.fs's find-index): the choice and the
\       term are Lean's.
\   lf-nth-constructor: ( idx expected target-code count-code "name" -- )
\       a record of MVarId.nthConstructor's arguments (Apply.lean:300-314,
\       as evalLeft and evalRight give them, Elab/Tactic/
\       BuiltinTactic.lean:660-664): Lean's idx and expected?, and the two
\       error codes whose texts carry Lean's tactic name; name ( -- nth )
\       gives its address, nth-idx nth-expected nth-target nth-count
\       ( nth -- addr ) its fields. The load aborts unless idx < expected:
\       Lean's out-of-bounds branch, unreachable then, is not ported
\   lf-goal-nth-constructor ( goal nth -- goals )  MVarId.nthConstructor:
\       in goal's context (checkNotAssigned first), getType''s head must be
\       an inductive type's constant (matchConstInduct; else the record's
\       target code, Lean's "target is not an inductive datatype"), with
\       exactly expected constructors (else its count code, Lean's "{name}
\       tactic works for inductive types with exactly {e} constructors"),
\       each with the goal after a blank line (throwTacticEx); then
\       MVarId.apply of constructor idx at the head's levels, with no
\       term? (lf-goal-apply), whose errors pass through (380 naming "the
\       term", 384, 125) and whose goals are the result
\ Lean call list: withContext -> the caller's (tactic-core.fs);
\ checkNotAssigned -> lf-goal-not-assigned (goal.fs); getType' -> lf-goal-type,
\ lf-whnf! then lf-instantiate! (meta-must.fs); getAppFn -> lf-meta-head;
\ matchConstInduct -> lf-match-const-induct (meta-must.fs), its constructors
\ lf-menv-data and lf-ity-ctors@ (meta-env.fs, core/input.fs); mkConst ctor
\ us -> lf-mk-const-id with lf-const-levels (app-builder.fs);
\ withoutModifyingState/observing? -> lf-commit-when answering false, with
\ a CATCH and lf-tac-forget-lean (tactic-msg.fs); MVarId.apply ->
\ lf-goal-apply (apply.fs); throwTacticEx -> lf-tac-ex (tactic-msg.fs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own (apply's). Loads in decimal whatever BASE is,
\ then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/find.fs
require ../../author/errors.fs
require ../../core/input.fs
require ../../core/constant-term-boundary.fs
require ../mvars.fs
require ../goals.fs
require ../meta-env.fs
require ../term-eqv.fs
require ../tactic-run.fs
require ../tactic-msg.fs
require ../meta-must.fs
require ../app-builder.fs
require ./goal.fs
require ./apply.fs

382 outcome-invalid s" Tactic `constructor` failed: target is not an inductive datatype"
  lfa-code: lfa-e-ctor-target
383 outcome-invalid s" Tactic `constructor` failed: no applicable constructor found"
  lfa-code: lfa-e-ctor-none

\ ---- matchConstInduct on getType''s head: the head constant and its
\ inductive type's constructors, else the error code (constructor's 382).
: mco-type ( goal -- t ) lf-goal-type lf-instantiate! lf-whnf! lf-instantiate! ;
: mco-head ( goal code -- head )
  over mco-type lf-meta-head dup lf-match-const-induct if drop nip nip exit then
  drop lf-tac-ex 0 ;
: mco-ctors ( head -- items n )
  lf-match-const-induct lf-found lf-menv-data ?dup 0= if outcome-unsupported lf-must then
  lf-ity-ctors@ ;
\ Constructor k at the head's levels (mkConst ctor us).
: mco-ctor ( head k -- name ) swap mco-ctors drop swap cells + @ ;
: mco-const ( head name -- e ) swap lf-const-levels lf-mk-const-id ;
: mco-at ( head k -- e ) over swap mco-ctor mco-const ;

\ ---- observing? inside withoutModifyingState: a Lean error is false.
: mco-caught ( code -- false ) lf-tac-forget-lean false ;
: mco-probe ( goal e -- applies? false )
  ['] lf-goal-apply catch ?dup if nip nip mco-caught else drop true then false ;
: mco-tried? ( goal head k -- goal head flag )
  >r 2dup r> mco-at ['] mco-probe lf-commit-when drop ;

\ The first constructor that applies, applied again for real; none: error 383.
: mco-apply ( head goal k -- goals ) rot swap mco-at lf-goal-apply ;
: mco-none ( head goal -- 0 ) nip lfa-e-ctor-none lf-tac-ex 0 ;
: lf-goal-constructor ( goal -- goals )
  lf-goal-not-assigned dup lfa-e-ctor-target mco-head tuck dup mco-ctors nip
  ['] mco-tried? find-index if mco-apply else mco-none then ;

\ ---- nthConstructor (Apply.lean:300-314): the record (its cells laid
\ down in the stack's order, the count code first), the goal operation.
begin-structure /nth
  field: nth-count       \ the code of "{name} tactic works for ... exactly {e} ..."
  field: nth-target      \ the code of "target is not an inductive datatype"
  field: nth-expected    \ Lean's expected? (always given here)
  field: nth-idx         \ Lean's idx
end-structure
: mnc-bounded ( nth -- )
  dup nth-idx @ swap nth-expected @ < 0= abort" lf-nth-constructor: idx >= expected" ;
: lf-nth-constructor: ( idx expected target-code count-code "name" -- )
  create , , , , here /nth - mnc-bounded ;
\ The head's inductive type has the count expected, else the count code.
: mnc-counted ( goal nth head -- goal nth head )
  over nth-expected @ over mco-ctors nip = if exit then drop nth-count @ lf-tac-ex ;
: lf-goal-nth-constructor ( goal nth -- goals )
  over lf-goal-not-assigned drop 2dup nth-target @ mco-head mnc-counted
  swap nth-idx @ mco-at lf-goal-apply ;
base !   \ the BASE this file was loaded with
