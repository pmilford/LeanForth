\ The declaration glue, the tactics' term hook and #check (plan S1;
\ docs/design/S1_INTERFACE.md 6-8 and 10), after Lean 4.35.0's
\ Elab/MutualDef.lean (elabHeaders, elabFunValues), Elab/Tactic/
\ ElabTerm.lean (Tactic.elabTerm, runTermElab) and Elab/BuiltinCommand.lean
\ (elabCheckCore). At end NAME a natural declaration is elaborated in
\ Lean's order and handed over (front/handover.fs); a #check is
\ elaborated where it stands.
\ - The header (elabHeaders): each parameter's type by elabType
\   (elab-term.fs), a free variable for it whose local, named and of the
\   kind its binder word wrote, is pushed on the current view; the
\   statement by elabType; synthesizeSyntheticMVarsNoPostponing (where
\   default instances fire); instantiated. A statement left with a
\   metavariable, term or level, is not supported yet (139: Lean's
\   levelMVarToParam and a theorem's holes, plan S5).
\ - lf-front-by-statement ( -- type ) (tactic-run.fs's hook) is the
\   header's statement in the parameters' context; lf-front-elaborate
\   ( -- type value ) (handover.fs's hook) adds the proof by
\   elabTermEnsuringType against the statement (a coercion is 131),
\   synthesizeSyntheticMVarsNoPostponing and instantiation, and closes
\   both over the parameters (tactic-run.fs's lf-front-close; an axiom's
\   value is -1).
\ - lf-tac-elab ( node expected postpone? -- term outcome )
\   (tactic-basic.fs's hook, S2_INTERFACE 7): Lean's Tactic.elabTerm,
\   elabTerm against expected (-1: none; any other value is a term), then
\   synthesizeSyntheticMVars, postponing when postpone? is true (Lean's
\   mayPostpone) else not, the term instantiated. A failure stops the run
\   at the tactic's word with the elaboration error (its position as the
\   second one). Term.withSynthesize's end, which S2's rewriting needs,
\   is elab-pending.fs's }lf-elab-synth.
\ - #check (BuiltinCommand.lean:434), a natural word outside declarations
\   (Lean has #check only as a command, Parser/Command.lean: inside a
\   declaration or a tactic block it is error 140, Lean's "unexpected
\   token '#check'; expected term"): TERM #check elaborates TERM with no
\   expected type,
\   synthesizeSyntheticMVarsNoPostponing leaving stuck instance problems,
\   instantiates, and prints "TERM : TYPE" on a line, as the goals print
\   terms (a print that fails stops the run as a Meta step's failure).
\   Not supported yet: a constant alone (Lean prints its
\   signature), a term with a metavariable left (137); Lean's Meta.check
\   of the term is not ported (plan S2's meta-check.fs), the kernel never
\   sees the term. lf-elab-checks ( -- n ) counts the #check lines of the
\   run (cli/leanforth.fs: a text of only #check lines checks nothing and
\   ends with exit 0).
\ - Each declaration and each #check starts with the elaborator's state
\   empty and the budget full (meta-config.fs, --elab-fuel); elaboration
\   runs in the elaborator's Meta configuration (foApprox and ctxApprox,
\   default transparency), the configuration before it given back after.
\ Errors stop the run (author/errors.fs) at end NAME, at the tactic's
\ word or at #check: the elaborator's recorded error (125-139, the Meta
\ layer's 100, 60) with the position it was at, else by outcome (no room
\ 60, fuel 138, unsupported 139, invalid 76). Untrusted: only the
\ kernel's check of the declarations handed over decides anything.
\ State: the record edc (the #check count), in the checker context (ADR
\ 0009). Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../core/terms.fs
require ../core/local-context.fs
require ../present/print-job.fs
require ../present/term-printer.fs
require ../author/errors.fs
require ../author/declarations.fs
require ../author/scopes.fs
require ./syntax.fs
require ./mvars.fs
require ./lctx-views.fs
require ./meta-config.fs
require ./reader.fs
require ./handover.fs
require ./tactic-run.fs
require ./tactic-basic.fs
require ./elab-pending.fs
require ./elab-app.fs
require ./elab-term.fs

begin-structure /edc
  field: edc-checks      \ #check lines run in this run
end-structure
/edc context-record: edc
: lf-elab-checks ( -- n ) edc edc-checks @ ;

\ ---- A fresh start: the elaborator's state empty, the budget full.
: lf-elab-reset ( -- )
  lf-elab-pending-reset lf-elab-app-reset lf-elab-term-reset lf-elab-vars-reset
  lf-meta-budget-start ;
action-of lfa-declaration-fresh constant edc-fresh-before
: edc-fresh ( -- ) edc-fresh-before execute lf-elab-reset ;
' edc-fresh is lfa-declaration-fresh
action-of lfa-run-fresh constant edc-run-before
: edc-run-fresh ( -- ) edc-run-before execute 0 edc edc-checks ! ;
' edc-run-fresh is lfa-run-fresh

\ ---- The elaborator's configuration while xt runs, given back after.
: edc-configured ( i*x xt -- j*x ) lf-defeq-elab lf-tr-default lf-meta-with ;

\ ---- Errors: the run stops at the current token (end NAME, #check).
\ (A failure no step recorded, a print's, has no second position: -1.)
: edc-fail ( outcome -- ) lf-elab-code swap lfa-fail-see ;
: edc-must ( outcome -- ) dup ok? if drop else edc-fail then ;

\ ---- The header: parameters and statement.
: edc-local ( binder fvar -- outcome )
  swap dup lfa-binder-name @ swap lfa-binder-kind @ lf-local-new lf-elab-meta
  ok-then? 0= if exit then lf-mctx-view swap lf-view-push lf-elab-meta
  ok-then? if lf-mctx-view! outcome-ok then ;
: edc-fvar ( binder type -- binder fvar outcome )
  lf-lctx-local lf-elab-meta ok-then? 0= if -1 swap exit then dup lf-elab-var+ ;
: edc-binder ( slot -- outcome )
  lfa-binder dup lfa-binder-domain @ lf-elab-type ok-then? 0= if nip exit then
  edc-fvar dup ok? if drop edc-local else nip nip then ;
\ The parameters: the binders open at := (an axiom, which has no :=, all
\ binders open at end).
: edc-params ( -- n ) lfa-params dup 0< if drop lfa-depth then ;
: edc-binders ( -- outcome ) edc-params ['] edc-binder ok-each ;
: edc-holes ( type -- type outcome ) lfa-e-elab-step lf-elab-closed ;
: edc-statement ( -- type outcome )
  lf-front-statement lf-elab-type ok-then? 0= if no-result exit then
  lf-postpone-no lf-elab-synthesize dup ok? 0= if nip no-result exit then drop
  lf-instantiate-mvars lf-elab-meta ok-then? if edc-holes else no-result then ;
: edc-header ( -- type ) edc-binders edc-must edc-statement edc-must ;
: edc-by-statement ( -- type ) ['] edc-header edc-configured ;
' edc-by-statement is lf-front-by-statement

\ ---- A term proof (elabFunValues), or an axiom's statement alone.
: edc-value ( type -- value outcome )
  lf-front-proof swap lf-elab-ensuring ok-then? 0= if no-result exit then
  lf-postpone-no lf-elab-synthesize dup ok? 0= if nip no-result exit then drop
  lf-instantiate-mvars lf-elab-meta ;
: edc-axiom? ( -- flag ) lf-front-proof 0< ;
: edc-whole ( -- type value )
  edc-header edc-axiom? if lf-front-close-type -1 exit then
  dup edc-value edc-must lf-front-close ;
: edc-elaborate ( -- type value ) ['] edc-whole edc-configured ;
' edc-elaborate is lf-front-elaborate

\ ---- The tactics' hook (Tactic.elabTerm).
: edc-mode ( postpone? -- mode ) if lf-postpone-yes else lf-postpone-no then ;
: edc-tac-run ( node expected postpone? -- term outcome )
  >r lf-elab-term ok-then? 0= if r> drop no-result exit then
  r> edc-mode lf-elab-synthesize dup ok? 0= if nip no-result exit then drop
  lf-instantiate-mvars lf-elab-meta ;
: edc-tac-fail ( outcome -- ) lf-elab-code lfa-see! lf-tac-stop ;
: edc-tac-elab ( node expected postpone? -- term outcome )
  ['] edc-tac-run edc-configured dup ok? 0= if edc-tac-fail then ;
' edc-tac-elab is lf-tac-elab

\ ---- #check.
: edc-printed ( term -- outcome ) ['] type true lf-print-to ;
: edc-check-line ( term type -- )
  swap edc-printed edc-must ."  : " edc-printed edc-must cr ;
: edc-signature? ( node -- flag ) syn-kind@ syn-k-const = ;
: edc-printable ( term -- term outcome ) lfa-e-elab-print lf-elab-closed ;
: edc-check-term ( node -- term outcome )
  -1 lf-elab-term ok-then? 0= if no-result exit then
  lf-postpone-check lf-elab-synthesize dup ok? 0= if nip no-result exit then drop
  lf-instantiate-mvars lf-elab-meta ok-then? if edc-printable else no-result then ;
: edc-check-type ( term -- term type outcome )
  dup lf-infer lf-elab-meta ok-then? 0= if no-result exit then
  lf-instantiate-mvars lf-elab-meta ;
: edc-checked ( node -- )
  dup edc-signature? if syn-at@ lfa-e-elab-print lfa-fail-see exit then
  dup syn-at@ lf-elab-at! edc-check-term edc-must edc-check-type edc-must edc-check-line ;
: edc-w-check ( value -- )
  lf-elab-reset 1 edc edc-checks +! lfn>syntax ['] edc-checked edc-configured ;
: edc-w-check-natural ( -- )
  lfa-inside? 0= lfa-e-check-here lfa-must 1 lfa-args edc-w-check ;
' edc-w-check-natural lfa-natural! #check

base !   \ the BASE this file was loaded with
