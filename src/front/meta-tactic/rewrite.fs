\ MVarId.rewrite of the tactic library (docs/design/TACTIC_PLUGINS.md
\ 2.4; plan 9.4.8l-I, commit C3): Lean 4.35.0's Meta/Tactic/Rewrite.lean
\ (:28-104), the goal operation under rw and rewrite (tactics/rewrite.fs);
\ simp later. Each failure throws (meta-must.fs), as Lean's do.
\   lf-goal-rewrite ( goal e heq symm? -- new proof goals )  in goal's
\       context (withContext), goal not assigned (checkNotAssigned, else
\       invalid): heq's type instantiated, a new metavariable for each of
\       its binders, natural, named as the binder, heq applied to them
\       (telescope.fs's forallMetaTelescopeReducing: whnf where no pi is
\       left; a binder of no known kind unsupported); an Eq (matchEq?,
\       app-builder.fs's lf-match-eq?: whnf when it is none), else error
\       218 with Lean's text (heq, whether it is a proof or a value, its
\       type); with symm? true (Lean's ←) heq made Eq.symm.{u} α lhs rhs
\       heq (app-builder.fs's lf-mk-eq-symm, mkEqSymm), its type rhs = lhs
\       (lf-mk-eq) and the sides swapped, α kept; a pattern lhs headed by
\       a metavariable 219 (its equation as swapped); e instantiated
\       and lhs abstracted (kabstract.fs's kabstract at reducible
\       transparency, in the elaborator's flags): no occurrence 215 with
\       the pattern, the target and the goal; new the abstracted e with
\       rhs put in, instantiated; the motive fun _a : α => abstracted,
\       checked by Meta.check at transparency all (meta-check.fs: not type
\       correct 216 with the motive and the failing application) and for
\       dependence (217, under withLocalDeclD _a α: the instantiated
\       body's type defeq e's); proof congrArg.{u1, u2} α T lhs rhs motive
\       heq, u1 and u2 the levels of α and T, e's type; goals the new
\       metavariables still unassigned, a run (Lean's newMVarIds). goal
\       is not assigned. Not supported yet (99, slice LA): an Iff (propext),
\       either way, an instance binder (postprocessAppMVars); Lean's
\       otherMVarIds (getMVarsNoDelayed of heq), appendParentTag and
\       binderNameHint are not ported (the caller refuses new goals).
\ Errors are thrown as authoring errors at the step running
\ (tactic-run.fs's lf-tac-stop), Meta failures as outcomes (meta-must.fs).
\ Not ported: addPPExplicitToExposeDiff in 215's text (plan 8.6), 216's
\ and 217's inner error texts (LeanForth names the application that did
\ not fit), and the explanation Lean adds to 216 and the note to 217.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: mrw-frames (a frame per call open, meta-must.fs's
\ lf-with-record, in the checker context, ADR 0009): a rewrite inside
\ another has its own; the new metavariables are a run (lib/runs.fs).
\ Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/slab.fs
require ../../lib/runs.fs
require ../../lib/context.fs
require ../../core/terms.fs
require ../../present/binder-table.fs
require ../../author/errors.fs
require ../../author/declarations.fs
require ../mvars.fs
require ../meta-config.fs
require ../instantiate.fs
require ../infer.fs
require ../fun-info.fs
require ../kabstract.fs
require ../meta-check.fs
require ../tactic-run.fs
require ../tactic-msg.fs
require ../meta-must.fs
require ../app-builder.fs
require ../telescope.fs
require ./goal.fs

begin-structure /mrw
  field: mrw-goal        \ the goal
  field: mrw-e           \ the target
  field: mrw-symm        \ symm?: right to left (Lean's ←)
  field: mrw-heq         \ the rule's proof, applied to its new metavariables
  field: mrw-htype       \ its type
  field: mrw-mvars       \ the new metavariables, a run
  field: mrw-alpha       \ the equation's type
  field: mrw-lhs         \ and its sides
  field: mrw-rhs
  field: mrw-abst        \ the target, the pattern abstracted
  field: mrw-etype       \ the target's type
  field: mrw-motive      \ fun _a => abst
end-structure
/mrw context-slab: mrw-frames
: mrw ( -- frame ) mrw-frames slab-last ;
: mrw-lhs@ ( -- lhs ) mrw mrw-lhs @ ;
: mrw-motive@ ( -- motive ) mrw mrw-motive @ ;

\ ---- forallMetaTelescopeReducing: each new metavariable kept and heq
\ applied to it (mkAppN heq newMVars); an instance binder refused (99):
\ Lean synthesizes it (postprocessAppMVars, slice LA).
: mrw-mvar+ ( heq mvar kind -- heq' )
  lf-binder-instance = if lfa-e-tac-form lf-tac-stop then
  dup mrw mrw-mvars lf-run+! lf-mk-app ;
: mrw-telescope ( -- )
  mrw mrw-heq @ dup lf-infer! lf-instantiate! -1 ['] mrw-mvar+
  lf-forall-meta-telescope-reducing mrw mrw-htype ! mrw mrw-heq ! ;

\ ---- matchEq? (an Iff refused, 99), else 218 with Lean's text.
: mrw-prop? ( -- flag ) mrw mrw-htype @ lf-get-level ok-then? if 0= else drop false then ;
: mrw-descr ( -- c-addr u )
  mrw-prop? if s"  is a proof of" else s"  is a value of type" then ;
: mrw-value. ( x -- outcome )
  drop s"  " lf-pp-emit mrw mrw-heq @ lf-tac-inline. mrw-descr lf-pp-emit ;
: mrw-htype. ( x -- outcome ) drop mrw mrw-htype @ lf-tac-indented. ;
\ An error whose message's line ends with what xt prints, the rule's
\ type indented below it.
: mrw-typed-stop ( xt code -- )
  >r 0 swap lf-tac-inline 0 ['] mrw-htype. lf-tac-detail r> lf-tac-stop ;
: mrw-matched ( -- )
  mrw mrw-htype @ dup lf-iff-app? if lfa-e-tac-form lf-tac-stop then
  lf-match-eq? 0= if ['] mrw-value. lfa-e-tac-not-eq mrw-typed-stop then
  mrw mrw-rhs ! mrw mrw-lhs ! mrw mrw-alpha ! ;
\ symm (Rewrite.lean:93-97): heq made Eq.symm heq (mkEqSymm), its type
\ rhs = lhs (mkEq) and the sides swapped; α stays the equation's.
: mrw-sides ( -- lhs rhs ) mrw mrw-lhs @ mrw mrw-rhs @ ;
: mrw-swap ( -- ) mrw-sides mrw mrw-lhs ! mrw mrw-rhs ! ;
: mrw-reversed ( -- )
  mrw mrw-heq @ lf-mk-eq-symm mrw mrw-heq !
  mrw-sides swap lf-mk-eq mrw mrw-htype ! mrw-swap ;
: mrw-symmetric ( -- ) mrw mrw-symm @ if mrw-reversed then ;
\ A pattern whose head is a metavariable (219).
: mrw-lhs. ( x -- outcome )
  drop s"  (" lf-pp-emit mrw mrw-lhs @ lf-tac-inline. s" ) in this equality" lf-pp-emit ;
: mrw-pattern-ok ( -- )
  mrw mrw-lhs @ lf-meta-head-args drop lf-mvar? 0= if exit then
  ['] mrw-lhs. lfa-e-tac-mvar-pattern mrw-typed-stop ;
: mrw-equation ( -- ) mrw-telescope mrw-matched mrw-symmetric mrw-pattern-ok ;

\ ---- kabstract, at reducible transparency: no occurrence is 215. A
\ message framed: the term, what xt prints, the goal.
: mrw-framed. ( x xt term -- outcome ) 2>r mrw mrw-goal @ swap 2r> lf-tac-framed-with. ;
: mrw-target. ( x -- outcome )
  drop s\" \nin the target expression\n" mrw mrw-e @ lf-tac-line. ;
: mrw-pattern. ( x -- outcome ) ['] mrw-target. mrw-lhs@ mrw-framed. ;
: mrw-abstracted ( -- abst )
  mrw mrw-e @ lf-instantiate! dup mrw mrw-e ! mrw mrw-lhs @
  ['] lf-meta-kabstract lf-defeq-elab lf-tr-reducible lf-meta-with lf-must
  0= if ['] mrw-pattern. lfa-e-tac-no-pattern lf-tac-failed then dup mrw mrw-abst ! ;
: mrw-new ( abst -- new )
  mrw mrw-rhs @ lf-meta-instantiate1 lf-must lf-instantiate!
  mrw mrw-e @ lf-infer! mrw mrw-etype ! ;

\ ---- The motive: fun _a : α => abst, type correct at all (216), not
\ dependent (217).
: mrw-motive! ( -- )
  mrw mrw-alpha @ mrw mrw-abst @ lf-term-lam lf-made! dup s" _a" lfa-intern
  lf-binder-default lf-pres-binder! lf-must mrw mrw-motive ! ;
: mrw-app. ( x -- outcome )
  drop lf-meta-check-bad dup 0< if drop outcome-ok exit then
  >r s\" \nError: Application type mismatch in the application\n" r> lf-tac-line. ;
: mrw-motive. ( x -- outcome ) ['] mrw-app. mrw-motive@ mrw-framed. ;
: mrw-checked ( -- )
  mrw mrw-motive @ lf-tr-all ['] lf-meta-check lf-defeq-elab lf-defeq-mode lf-meta-with
  dup outcome-invalid = if drop ['] mrw-motive. lfa-e-tac-motive lf-tac-failed then
  lf-must ;
: mrw-at ( a -- flag )   \ isDefEq (inferType (eAbst.instantiate1 a)) eType
  mrw mrw-abst @ swap lf-meta-instantiate1 lf-must lf-infer! mrw mrw-etype @
  lf-tac-defeq lf-must ;
: mrw-dependent. ( x -- outcome ) ['] drop-ok mrw-motive@ mrw-framed. ;
: mrw-independent ( -- )
  mrw mrw-alpha @ s" _a" lfa-intern lf-binder-default ['] mrw-at lf-with-local-decl
  0= if ['] mrw-dependent. lfa-e-tac-motive-dep lf-tac-failed then ;

\ ---- The proof: congrArg.{u1, u2} α T lhs rhs motive heq (mkApp6); the
\ new metavariables left unassigned (newMVarIds).
: mrw-args ( f -- t )
  mrw mrw-alpha @ mrw mrw-etype @ mrw mrw-lhs @ mrw mrw-rhs @ mrw mrw-motive @
  mrw mrw-heq @ 6 lf-mk-app-n ;
: mrw-proof ( -- proof )
  s" congrArg" mrw mrw-alpha @ lf-level! mrw mrw-etype @ lf-level! 2 lf-mk-const
  mrw-args ;
: mrw-goals ( -- goals ) mrw mrw-mvars @ ['] lf-meta-unassigned? run-filter lf-must ;
: mrw-run ( -- new proof goals )
  mrw mrw-goal @ lf-goal-not-assigned drop mrw-equation mrw-abstracted mrw-new
  mrw-motive! mrw-checked mrw-independent mrw-proof mrw-goals ;
: mrw-framed ( goal e heq symm? -- new proof goals )
  mrw mrw-symm ! mrw mrw-heq ! mrw mrw-e ! dup mrw mrw-goal ! ['] mrw-run lf-with-goal ;
: lf-goal-rewrite ( goal e heq symm? -- new proof goals )
  mrw-frames ['] mrw-framed lf-with-record ;
base !   \ the BASE this file was loaded with
