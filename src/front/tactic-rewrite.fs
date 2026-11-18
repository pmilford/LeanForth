\ Rewriting (plan S2, branch s2-tactics; docs/design/S2_INTERFACE.md 5):
\ by-rewrite[ r1 .. rn ] and by-rw[ r1 .. rn ], the rows of their kinds in
\ the runner (tactic-run.fs), after Lean 4.35.0's Elab/Tactic/Rewrite.lean
\ (evalRewriteSeq, withRWRulesSeq, rewriteTarget, elabRewrite,
\ finishElabRewrite), Meta/Tactic/Rewrite.lean (MVarId.rewrite),
\ Meta/Tactic/Replace.lean (replaceTargetEq), AppBuilder.lean
\ (mkExpectedPropHint, mkEq) and Init/Tactics.lean's rw macro.
\ - by-rewrite[: each rule in order on the main goal, in its context
\   (Lean's rewriteTarget), inside the elaborator's withSynthesize: the
\   target instantiated; the rule elaborated with no expected type,
\   postponing allowed (lf-tac-elab); a rule naming a definition, whose
\   equation theorems Lean would use, is not supported yet (99, FE8); the
\   occurs check (220); MVarId.rewrite: the rule's type instantiated, a
\   natural metavariable for each binder, named as it, the proof applied
\   to them (forallMetaTelescopeReducing: whnf where no pi is left; an
\   instance binder 99, FE5); an Iff 99 (propext, FE5); an Eq, after whnf
\   when it is none (matchEq?), else 218; a pattern headed by a
\   metavariable 219; kabstract (kabstract.fs) at reducible transparency
\   in the tactics' configuration: no occurrence 215 with the pattern, the
\   target and the goal; the new target, the abstracted one with the
\   right side put in, instantiated; the motive fun _a : α => abstracted,
\   checked by Meta.check at transparency all (meta-check.fs; 216) and
\   for dependence (217); the proof congrArg.{u1, u2} α T lhs rhs motive
\   rule, u1 and u2 the levels of α and T, the target's type; then the
\   pending problems synthesized with no postponing (the default
\   instances); a metavariable of the rule left unassigned (Lean's new
\   goals) is not supported yet (99, FE5); replaceTargetEq: a new goal of
\   the new target with the old tag, the goal assigned
\   Eq.mpr.{u} target new (id.{0} (target = new) proof) new-goal, target
\   the goal's type as stored, and the new goal in its place.
\ - by-rw[: the same, then try (with_reducible rfl): by-rfl at reducible
\   transparency (tactic-basic.fs) from a saved state, its failure
\   undone and forgotten, except one that is not supported yet, which
\   stops the run (where Lean's rfl might still succeed).
\ Each rule runs in its own step record (tactic-run.fs, review fe1g3 M2),
\ its fields after tb's; errors at the by-rw[ word with the rule's place
\ second, as the messages Lean gives at the rule. Not ported: Lean's
\ withInstancesTypeCheckNote (a note when the target is not type correct
\ at implicit transparency, which no target LeanForth's tactics make can
\ be), addPPExplicitToExposeDiff in 215's text (plan 8.6), 216's and
\ 217's inner error texts (LeanForth names the application that did not
\ fit), and binderNameHint (no rule of Init's proof set has one).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: the slab trw-mvars (the rule's new metavariables) in the checker
\ context (ADR 0009); everything else in the step record. Loads in
\ decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/runs.fs
require ../core/terms.fs
require ../core/local-context.fs
require ../present/binder-table.fs
require ../author/errors.fs
require ../author/declarations.fs
require ./syntax.fs
require ./mvars.fs
require ./meta-config.fs
require ./goals.fs
require ./instantiate.fs
require ./term-eqv.fs
require ./meta-env.fs
require ./whnf.fs
require ./infer.fs
require ./kabstract.fs
require ./meta-check.fs
require ./elab-pending.fs
require ./tactic-syntax.fs
require ./tactic-run.fs
require ./tactic-basic.fs

begin-structure /trw
  /tb +field trw-tb      \ the step's goal, its type and context (tb)
  field: trw-rule        \ the rule: its argument in the record
  field: trw-heq         \ its proof, applied to its new metavariables
  field: trw-htype       \ that proof's type
  field: trw-alpha       \ the equation's type, left and right sides
  field: trw-lhs
  field: trw-rhs
  field: trw-e           \ the target, instantiated
  field: trw-abst        \ the target, the pattern abstracted
  field: trw-new         \ the new target
  field: trw-etype       \ the target's type
  field: trw-motive      \ fun _a => abst
  field: trw-proof       \ congrArg's proof of target = new
  field: trw-saved       \ the elaborator's pending list, set aside
end-structure
/trw lf-tac-work-cells cells >
[if] .( tactic-rewrite.fs: trw is wider than a step record) cr abort [then]
: trw ( -- addr ) lf-tac-record ;
1 cells context-slab: trw-mvars

\ ---- Errors at the rule (its place second), with or without the goal.
: lfw-rule-at ( -- pos ) trw trw-rule @ lf-tactic-arg nip ;
: lfw-stop ( code -- ) lf-author-code 0= if lfw-rule-at lfa-see! then lf-tac-stop ;
: lfw-failed ( xt code -- ) >r 0 swap lf-tac-detail r> lfw-stop ;

\ ---- The rule: elaborated with no expected type, postponing allowed.
: lfw-node ( -- node ) trw trw-rule @ lf-tactic-arg drop ;
: lfw-definition? ( node -- flag )
  dup syn-kind@ syn-k-const <> if drop false exit then
  syn-a@ lfa-decl-name lf-menv-find ok-then? if lf-menv-kind lf-kind-definition = else
    drop false then ;
: lfw-elaborated ( -- )
  lfw-node dup lfw-definition? if drop lfa-e-tac-form lfw-stop then
  -1 true lf-tac-elab lf-tac-must trw trw-heq ! ;
: lfw-occurs. ( x -- outcome ) drop trw trw-heq @ lf-tac-indented. ;
: lfw-occurs-free ( -- )
  tb tb-goal @ trw trw-heq @ lf-mvar-occurs? lf-tac-must
  if ['] lfw-occurs. lfa-e-tac-occurs lfw-failed then ;

\ ---- forallMetaTelescopeReducing over the rule's type.
\ The rule's binder name and kind, the presentation table's, else its
\ input record's; an unknown kind is refused, 99 (review C4 of 2026-11-18:
\ Lean makes an instance binder's metavariable synthetic, so a guess of
\ explicit is no port).
: lfw-known? ( pi -- flag )
  dup lf-pres-binder@ if 2drop drop true exit then
  lf-term-input-binder@ dup if nip nip then ;
: lfw-binder ( pi -- name kind )
  dup lfw-known? 0= if lfa-e-tac-form lfw-stop then lf-tac-binder ;
: lfw-mvar ( pi -- mvar )
  dup lfw-binder lf-binder-instance = if lfa-e-tac-form lfw-stop then
  swap lf-term-first@ mv-natural lf-mvar-new lf-tac-must tuck swap lf-mvar-tag!
    lf-tac-must ;
: lfw-applied ( mvar -- ) trw trw-heq @ swap lf-tac-app trw trw-heq ! ;
: lfw-enter ( pi -- body )
  dup lfw-mvar dup trw-mvars slab-push lf-tac-must dup lfw-applied lf-meta-open
    lf-tac-must ;
: lfw-pi ( t -- t' flag )   \ a pi, or one whnf makes; else the type as it was
  dup lf-term-pi? if true exit then
  dup lf-meta-whnf lf-tac-must dup lf-term-pi? if nip true else drop false then ;
: lfw-telescope ( -- )
  trw trw-heq @ lf-infer lf-tac-must lf-instantiate-mvars lf-tac-must
  begin lfw-pi while lfw-enter repeat trw trw-htype ! ;

\ ---- matchEq?: Eq α lhs rhs, after whnf when it is none.
: lfw-iff? ( t -- flag ) 2 s" Iff" lf-meta-app-of? ;
: lfw-sides ( eq -- )
  dup lf-term-second@ trw trw-rhs ! lf-term-first@ dup lf-term-second@ trw trw-lhs !
  lf-term-first@ lf-term-second@ trw trw-alpha ! ;
: lfw-prop? ( -- flag ) trw trw-htype @ lf-get-level ok-then? if 0= else drop false then ;
: lfw-descr ( -- c-addr u )
  lfw-prop? if s"  is a proof of" else s"  is a value of type" then ;
: lfw-value. ( x -- outcome )
  drop s"  " lf-pp-emit trw trw-heq @ lf-tac-inline. lfw-descr lf-pp-emit ;
: lfw-htype. ( x -- outcome ) drop trw trw-htype @ lf-tac-indented. ;
: lfw-not-eq ( -- )
  0 ['] lfw-value. lf-tac-inline 0 ['] lfw-htype. lf-tac-detail lfa-e-tac-not-eq
    lfw-stop ;
: lfw-eq ( -- eq )
  trw trw-htype @ dup lf-tac-eq? if exit then lf-meta-whnf lf-tac-must
  dup lf-tac-eq? 0= if drop lfw-not-eq then ;
: lfw-matched ( -- )
  trw trw-htype @ lfw-iff? if lfa-e-tac-form lfw-stop then lfw-eq lfw-sides ;
\ A pattern whose head is a metavariable (219).
: lfw-lhs. ( x -- outcome )
  drop s"  (" lf-pp-emit trw trw-lhs @ lf-tac-inline. s" ) in this equality" lf-pp-emit ;
: lfw-pattern-ok ( -- )
  trw trw-lhs @ lf-meta-head-args drop lf-mvar? 0= if exit then
  0 ['] lfw-lhs. lf-tac-inline 0 ['] lfw-htype. lf-tac-detail lfa-e-tac-mvar-pattern
    lfw-stop ;

\ ---- kabstract, at reducible transparency.
: lfw-target. ( -- outcome ) s\" \nin the target expression\n" trw trw-e @ lf-tac-line. ;
\ A term indented, what xt ( -- outcome ) prints, then the goal.
: lfw-framed. ( term xt -- outcome )
  swap lf-tac-indented. swap ok-and ['] lf-tac-goal. ok-and ;
: lfw-pattern. ( x -- outcome ) drop trw trw-lhs @ ['] lfw-target. lfw-framed. ;
: lfw-no-pattern ( -- ) ['] lfw-pattern. lfa-e-tac-no-pattern lfw-failed ;
: lfw-abstracted ( -- )
  trw trw-e @ trw trw-lhs @ ['] lf-meta-kabstract lf-defeq-elab lf-tr-reducible
    lf-meta-with
  lf-tac-must 0= if lfw-no-pattern then trw trw-abst ! ;
: lfw-new ( -- )
  trw trw-abst @ trw trw-rhs @ lf-meta-instantiate1 lf-tac-must lf-instantiate-mvars
  lf-tac-must trw trw-new ! trw trw-e @ lf-infer lf-tac-must trw trw-etype ! ;

\ ---- The motive: fun _a : α => abst, type correct at all, not dependent.
: lfw-motive! ( -- )
  trw trw-alpha @ trw trw-abst @ lf-term-lam lf-tac-made dup s" _a" lfa-intern
  lf-binder-default lf-pres-binder! lf-tac-must trw trw-motive ! ;
: lfw-app. ( -- outcome )
  lf-meta-check-bad dup 0< if drop outcome-ok exit then
  >r s\" \nError: Application type mismatch in the application\n" r> lf-tac-line. ;
: lfw-motive. ( x -- outcome ) drop trw trw-motive @ ['] lfw-app. lfw-framed. ;
: lfw-checked ( -- )
  trw trw-motive @ lf-tr-all ['] lf-meta-check lf-defeq-elab lf-defeq-mode lf-meta-with
  dup outcome-invalid = if drop ['] lfw-motive. lfa-e-tac-motive lfw-failed then
    lf-tac-must ;
: lfw-at ( -- type ) trw trw-abst @ trw trw-alpha @ lf-lctx-local lf-tac-must
  lf-meta-instantiate1 lf-tac-must lf-infer lf-tac-must ;
: lfw-nothing. ( -- outcome ) outcome-ok ;
: lfw-dependent. ( x -- outcome ) drop trw trw-motive @ ['] lfw-nothing. lfw-framed. ;
: lfw-independent ( -- )
  lfw-at trw trw-etype @ lf-tac-defeq lf-tac-must 0= if
    ['] lfw-dependent. lfa-e-tac-motive-dep lfw-failed then ;

\ ---- The proof: congrArg.{u1, u2} α T lhs rhs motive rule.
: lfw-level ( t -- level ) lf-get-level lf-tac-must ;
: lfw-args ( f -- t )
  trw trw-alpha @ lf-tac-app trw trw-etype @ lf-tac-app trw trw-lhs @ lf-tac-app
  trw trw-rhs @ lf-tac-app trw trw-motive @ lf-tac-app trw trw-heq @ lf-tac-app ;
: lfw-proof! ( -- )
  s" congrArg" trw trw-alpha @ lfw-level trw trw-etype @ lfw-level lf-tac-const2 lfw-args
  trw trw-proof ! ;
\ Lean's new goals: a metavariable of the rule left unassigned.
: lfw-closed ( -- )
  trw trw-proof @ lf-instantiate-mvars lf-tac-must ['] lf-tac-hole? lf-term-holds?
    lf-tac-must
  if lfa-e-tac-form lfw-stop then ;

\ ---- replaceTargetEq: Eq.mpr.{u} target new (id.{0} (target = new) proof) ?new.
: lfw-want ( -- t ) tb tb-want @ ;
: lfw-eq-term ( -- eq )
  lfw-want lf-infer lf-tac-must dup lfw-level s" Eq" lf-tac-const1 swap lf-tac-app
  lfw-want lf-tac-app trw trw-new @ lf-tac-app ;
: lfw-hint ( -- t ) 0 s" id" lf-tac-const1 lfw-eq-term lf-tac-app trw trw-proof @
  lf-tac-app ;
: lfw-mpr ( goal -- value )
  >r lfw-want lfw-level s" Eq.mpr" lf-tac-const1 lfw-want lf-tac-app trw trw-new @
  lf-tac-app lfw-hint lf-tac-app r> lf-tac-app ;
: lfw-goal ( -- goal )
  trw trw-new @ tb tb-goal @ lf-mvar-tag drop tb tb-view @ lf-goal-new lf-tac-must ;
: lfw-replaced ( -- )
  lfw-goal dup lfw-mpr tb tb-goal @ swap lf-mvar-assign lf-tac-must
  0 swap run-push lf-tac-must lf-replace-main lf-tac-must ;

\ ---- One rule (Lean's rewriteTarget inside Term.withSynthesize).
: lfw-begin ( j -- )
  trw trw-rule ! trw-mvars slab-clear lf-elab-synth{ trw trw-saved !
  lfw-want lf-instantiate-mvars lf-tac-must trw trw-e ! ;
: lfw-core ( -- )
  lfw-elaborated lfw-occurs-free lfw-telescope lfw-matched lfw-pattern-ok lfw-abstracted
  lfw-new lfw-motive! lfw-checked lfw-independent lfw-proof! ;
: lfw-synthesized ( -- ) trw trw-saved @ lf-postpone-no }lf-elab-synth lf-tac-must ;
: lfw-rewrite ( j i -- ) drop lfw-begin lfw-core lfw-synthesized lfw-closed lfw-replaced ;
: lfw-rule ( j i -- ) ['] lfw-rewrite lf-tac-step-run ;
: lfw-rules ( i -- )
  dup lf-tactic-step dup tac-first @ swap tac-count @ over + swap ?do i over lfw-rule loop
  drop ;

\ ---- try (with_reducible rfl): a failure (invalid) undone; anything else
\ thrown again, as Lean's try never catches a runtime exception (fuel,
\ room; CoreM.lean:806-810) and a gap of LeanForth's stays one.
: lfw-invalid? ( -- flag ) lf-author-code lf-author-outcome outcome-invalid = ;
: lfw-caught ( code -- ) lfw-invalid? if drop lf-tac-forget else throw then ;
: lfw-rfl ( -- ) lf-tac-step lf-tac-rfl-reducible ;
: lfw-try-rfl ( -- ) ['] lfw-rfl lf-tac-try ?dup if lfw-caught then ;
: lfw-w-rewrite ( i -- ) lfw-rules ;
: lfw-w-rw ( i -- ) lfw-rules lfw-try-rfl ;
' lfw-w-rewrite tac-k-rewrite lf-tactic-action!
' lfw-w-rw tac-k-rw lf-tactic-action!
base !   \ the BASE this file was loaded with
