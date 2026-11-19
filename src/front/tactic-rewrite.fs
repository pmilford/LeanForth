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
\   to them (telescope.fs's forallMetaTelescopeReducing: whnf where no pi
\   is left; a binder of unknown kind unsupported, 93; an instance binder
\   99, FE5); an Iff 99 (propext, FE5); an Eq, after whnf
\   when it is none (matchEq?), else 218; a pattern headed by a
\   metavariable 219; kabstract (kabstract.fs) at reducible transparency
\   in the tactics' configuration: no occurrence 215 with the pattern, the
\   target and the goal; the new target, the abstracted one with the
\   right side put in, instantiated; the motive fun _a : α => abstracted,
\   checked by Meta.check at transparency all (meta-check.fs; 216) and
\   for dependence (217, under withLocalDeclD _a α); the proof
\   congrArg.{u1, u2} α T lhs rhs motive
\   rule, u1 and u2 the levels of α and T, the target's type; then the
\   pending problems synthesized with no postponing (the default
\   instances); a metavariable of the rule left unassigned (Lean's new
\   goals) is not supported yet (99, FE5); replaceTargetEq: a new goal of
\   the new target with the old tag, the goal assigned
\   Eq.mpr.{u} target new (id.{0} (target = new) proof) new-goal, target
\   the goal's type as stored, and the new goal in its place.
\ - by-rw[: the same, then try (with_reducible rfl): by-rfl at reducible
\   transparency (tactics/rfl.fs) from a saved state, its failure
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
\ Terms, binders and the telescope come from the tactic library
\ (app-builder.fs, telescope.fs), as the Lean functions named.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: the slab trw-mvars (the rule's new metavariables), kept in a
\ tactic's saved state on trw-mvars-kept (tac-state:), in the checker
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
require ./tactic-msg.fs
require ./tactic-core.fs
require ./meta-must.fs
require ./app-builder.fs
require ./telescope.fs
require ./meta-tactic/goal.fs

begin-structure /trw
  /tb +field trw-tb      \ the step's goal, its type and context (tb)
  field: trw-rule        \ the rule: its argument in the record
  field: trw-heq         \ its proof, applied to its new metavariables
  field: trw-htype       \ that proof's type
  field: trw-alpha       \ the equation's type, left and right sides
  field: trw-lhs         \ (lhs and rhs a pair: lfw-sides stores them with 2!)
  field: trw-rhs
  field: trw-e           \ the target, instantiated
  field: trw-abst        \ the target, the pattern abstracted
  field: trw-new         \ the new target
  field: trw-etype       \ the target's type
  field: trw-motive      \ fun _a => abst
  field: trw-proof       \ congrArg's proof of target = new
end-structure
/trw lf-tac-work-cells cells >
[if] .( tactic-rewrite.fs: trw is wider than a step record) cr abort [then]
: trw ( -- addr ) lf-tac-record ;
1 cells context-slab: trw-mvars

\ ---- Errors at the rule (its place second), with or without the goal.
: lfw-rule-at ( -- pos ) lf-tac-step trw trw-rule @ lf-tac-arg-at ;
: lfw-stop ( code -- ) lf-author-code 0= if lfw-rule-at lfa-see! then lf-tac-stop ;
: lfw-failed ( xt code -- ) >r 0 swap lf-tac-detail r> lfw-stop ;

\ ---- The rule: elaborated with no expected type, postponing allowed.
: lfw-node ( -- node ) lf-tac-step trw trw-rule @ lf-tac-arg ;
: lfw-definition? ( node -- flag )
  dup syn-kind@ syn-k-const <> if drop false exit then
  syn-a@ lfa-decl-name lf-menv-find ok-then? if lf-menv-kind lf-kind-definition = else
    drop false then ;
: lfw-elaborated ( -- )
  lfw-node dup lfw-definition? if drop lfa-e-tac-form lfw-stop then
  -1 true lf-tac-elab-term trw trw-heq ! ;
: lfw-occurs. ( x -- outcome ) drop trw trw-heq @ lf-tac-indented. ;
: lfw-occurs-free ( -- )
  tb tb-goal @ trw trw-heq @ lf-mvar-occurs? lf-tac-must
  if ['] lfw-occurs. lfa-e-tac-occurs lfw-failed then ;

\ ---- forallMetaTelescopeReducing over the rule's type (telescope.fs:
\ binder kinds from the nodes' records; an unknown one unsupported,
\ review C4 of 2026-11-18): each new metavariable kept in trw-mvars and
\ the rule applied to it (mkAppN heq newMVars). An instance binder is
\ refused, 99: Lean synthesizes it (postprocessAppMVars, FE5).
: lfw-mvar+ ( heq mvar kind -- heq' )
  lf-binder-instance = if lfa-e-tac-form lfw-stop then
  dup trw-mvars slab-push lf-tac-must lf-mk-app ;
: lfw-telescope ( -- )
  trw trw-heq @ dup lf-infer! lf-instantiate! -1 ['] lfw-mvar+
  lf-forall-meta-telescope-reducing trw trw-htype ! trw trw-heq ! ;

\ ---- matchEq? (app-builder.fs): Eq α lhs rhs, after whnf when it is none.
: lfw-iff? ( t -- flag ) 2 s" Iff" lf-meta-app-of? ;
: lfw-sides ( α lhs rhs -- ) swap trw trw-lhs 2! trw trw-alpha ! ;   \ (lhs, rhs a pair)
: lfw-prop? ( -- flag ) trw trw-htype @ lf-get-level ok-then? if 0= else drop false then ;
: lfw-descr ( -- c-addr u )
  lfw-prop? if s"  is a proof of" else s"  is a value of type" then ;
: lfw-value. ( x -- outcome )
  drop s"  " lf-pp-emit trw trw-heq @ lf-tac-inline. lfw-descr lf-pp-emit ;
: lfw-htype. ( x -- outcome ) drop trw trw-htype @ lf-tac-indented. ;
: lfw-not-eq ( -- )
  0 ['] lfw-value. lf-tac-inline 0 ['] lfw-htype. lf-tac-detail lfa-e-tac-not-eq
    lfw-stop ;
: lfw-matched ( -- )
  trw trw-htype @ dup lfw-iff? if lfa-e-tac-form lfw-stop then
  lf-match-eq? 0= if lfw-not-eq then lfw-sides ;
\ A pattern whose head is a metavariable (219).
: lfw-lhs. ( x -- outcome )
  drop s"  (" lf-pp-emit trw trw-lhs @ lf-tac-inline. s" ) in this equality" lf-pp-emit ;
: lfw-pattern-ok ( -- )
  trw trw-lhs @ lf-meta-head-args drop lf-mvar? 0= if exit then
  0 ['] lfw-lhs. lf-tac-inline 0 ['] lfw-htype. lf-tac-detail lfa-e-tac-mvar-pattern
    lfw-stop ;

\ ---- kabstract, at reducible transparency.
: lfw-target. ( -- outcome ) s\" \nin the target expression\n" trw trw-e @ lf-tac-line. ;
: lfw-pattern. ( x -- outcome ) drop trw trw-lhs @ ['] lfw-target. lf-tac-framed. ;
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
  trw trw-alpha @ trw trw-abst @ lf-term-lam lf-made! dup s" _a" lfa-intern
  lf-binder-default lf-pres-binder! lf-tac-must trw trw-motive ! ;
: lfw-app. ( -- outcome )
  lf-meta-check-bad dup 0< if drop outcome-ok exit then
  >r s\" \nError: Application type mismatch in the application\n" r> lf-tac-line. ;
: lfw-motive-framed. ( xt -- outcome ) trw trw-motive @ swap lf-tac-framed. ;
: lfw-motive. ( x -- outcome ) drop ['] lfw-app. lfw-motive-framed. ;
: lfw-checked ( -- )
  trw trw-motive @ lf-tr-all ['] lf-meta-check lf-defeq-elab lf-defeq-mode lf-meta-with
  dup outcome-invalid = if drop ['] lfw-motive. lfa-e-tac-motive lfw-failed then
    lf-tac-must ;
: lfw-at ( a -- flag )   \ isDefEq (inferType (eAbst.instantiate1 a)) eType
  trw trw-abst @ swap lf-meta-instantiate1 lf-tac-must lf-infer! trw trw-etype @
  lf-tac-defeq lf-tac-must ;
: lfw-nothing. ( -- outcome ) outcome-ok ;
: lfw-dependent. ( x -- outcome ) drop ['] lfw-nothing. lfw-motive-framed. ;
: lfw-independent ( -- )
  trw trw-alpha @ s" _a" lfa-intern lf-binder-default ['] lfw-at lf-with-local-decl
  0= if ['] lfw-dependent. lfa-e-tac-motive-dep lfw-failed then ;

\ ---- The proof: congrArg.{u1, u2} α T lhs rhs motive rule (mkApp6).
: lfw-args ( f -- t )
  trw trw-alpha @ trw trw-etype @ trw trw-lhs @ trw trw-rhs @ trw trw-motive @
  trw trw-heq @ 6 lf-mk-app-n ;
: lfw-proof! ( -- )
  s" congrArg" trw trw-alpha @ lf-level! trw trw-etype @ lf-level! 2 lf-mk-const lfw-args
  trw trw-proof ! ;
\ Lean's new goals: a metavariable of the rule left unassigned.
: lfw-closed ( -- )
  trw trw-proof @ lf-instantiate-mvars lf-tac-must ['] lf-mvar-open? lf-term-holds?
    lf-tac-must
  if lfa-e-tac-form lfw-stop then ;

\ ---- replaceTargetEq (meta-tactic/goal.fs), the new goal in the old's
\ place.
: lfw-want ( -- t ) tb tb-want @ ;
: lfw-replaced ( -- )
  tb tb-goal @ trw trw-new @ trw trw-proof @ lf-goal-replace-target-eq
  0 swap run-push lf-tac-must lf-replace-main lf-tac-must ;

\ ---- One rule (Lean's rewriteTarget inside Term.withSynthesize).
: lfw-begin ( j -- )
  trw trw-rule ! trw-mvars slab-clear
  lfw-want lf-instantiate-mvars lf-tac-must trw trw-e ! ;
: lfw-core ( -- )
  lfw-elaborated lfw-occurs-free lfw-telescope lfw-matched lfw-pattern-ok lfw-abstracted
  lfw-new lfw-motive! lfw-checked lfw-independent lfw-proof! ;
\ The pending list set aside around the rule and put back however it
\ ends (review C2 of 2026-11-18: a failed rule left the window open).
: lfw-rewrite ( k i -- )
  drop lfw-begin ['] lfw-core lf-tac-with-synth lfw-closed lfw-replaced ;
\ trw-mvars in a tactic's saved state (tactic-run.fs's tac-state:).
1 cells context-slab: trw-mvars-kept
: lfw-keep ( -- outcome ) trw-mvars trw-mvars-kept slab-keep ;
: lfw-kept ( undo? -- outcome ) trw-mvars trw-mvars-kept slab-kept ;
' lfw-keep ' lfw-kept tac-state:
: lfw-rule ( k i -- ) ['] lfw-rewrite lf-tac-step-run ;
: lfw-rules ( i -- ) dup lf-tac-args# 0 ?do i over lfw-rule loop drop ;

\ ---- try (with_reducible rfl): by-rfl's row (lf-tac-eval) at reducible
\ transparency; a Lean error undone and forgotten, anything else thrown
\ again (tactic-core.fs's lf-tac-try-lean).
: lfw-rfl ( -- ) lf-tac-step tac-k-rfl ['] lf-tac-eval lf-with-reducible ;
: lfw-try-rfl ( -- ) ['] lfw-rfl lf-tac-try-lean drop ;
: lfw-w-rewrite ( i -- ) lfw-rules ;
: lfw-w-rw ( i -- ) lfw-rules lfw-try-rfl ;
' lfw-w-rewrite tac-k-rewrite lf-tactic-action!
' lfw-w-rw tac-k-rw lf-tactic-action!
base !   \ the BASE this file was loaded with
