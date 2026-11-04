\ check-declaration (plan task 2.2.3; ADR 0011, ADR 0012 E4): the check
\ that the checked environment's publisher runs for each declaration of
\ the input, as the check word ( -- ) of lf-env-run or lf-env-step
\ (env-publish.fs). It checks the declaration of its context's snapshot
\ and ends with lf-env-finish, in ADR 0011's order ("Order"), step by step:
\   1 the audit, before any typing: a definition or theorem, safe, with a
\     value (U1: every other kind is unsupported, axioms too, owner gate
\     answer G3; a definition or theorem without a value is invalid); no
\     unsupported term form in its type or value (U2, the leaves of
\     core/unsupported-forms.fs); both terms closed and well formed (V1,
\     lf-constant-term-scope: invalid);
\   2 its name (N2, with K5 on it: lf-env-own-name);
\   3 its universe parameters distinct (L3: lf-env-own-params);
\   4 the declared type's type, inferred in environment mode (mixed-infer.fs
\     with env-signature.fs): each constant looked up in the snapshot (N1,
\     K5), its universe arguments counted (L1) and within the declaration's
\     parameters (L2), each Sort's level too (L2), binder domains (S2),
\     functions (F1) and arguments (D1-D5), each where Lean's kernel checks
\     it;
\   5 that type is a Sort (S1);
\   6 for a theorem, that Sort is a proposition (S3, Lean's is_prop);
\   7 the value's type, inferred the same way, after the scratch of steps
\     4-6 is discarded (nothing made there is needed again);
\   8 the value's type converts to the declared type (D1-D5 reject).
\ The first step that does not succeed ends the check with its outcome
\ (ADR 0008), and lf-check-step@ tells which; only a check whose every
\ step succeeded ends ok. Its candidate then holds its dependencies, the
\ accepted declarations its type and value name, recorded as inference
\ meets them, with their joined axiom set, which is always empty here
\ (axioms are unsupported, and so is everything that uses one, K5); the
\ publisher re-checks the candidate before anything becomes visible. A
\ comparison that is undecided stays unknown unless a rule of ADR 0011
\ shows Lean's kernel certainly fails it. The audit, then inference, run
\ on one budget of fuel per check, lf-check-budget, which starts at 0 in a
\ new context: a check without a budget is exhausted, never accepted (so a
\ maker that gives lf-env-run a replacement context sets its budget too).
\
\ lf-check-input checks every declaration of this context's input in a
\ new environment; lf-check-verdict. prints a slot's verdict afterwards,
\ an accepted one as "accepted (experimental, not independently audited);
\ axioms: none", the axiom set read from the slot (AGENTS.md, ADR 0011).
\ The printing words run after a check, never inside one.
\
\ [kernel] code: experimental, not through the review gate, not
\ independently audited. Limits: the stores' capacity settings (default
\ 64 terms and levels; lf-term-capacity! and the like), the passes' depth
\ (lf-depth-limit, 64), the environment and inference.
\ State: one record, lf-check-state (the budget, the fuel left in the
\ audit, the step reached, the declaration checked and the last result),
\ and one walk record, lf-check-walker (the U2 audit), both members of the
\ checker context (lib/context.fs). Inference runs on mixed-infer's state.

require ../lib/lib.fs
require ../core/constant-term-scope.fs
require ../core/derivation-log.fs
require ../core/diagnostics.fs
require ../core/input.fs
require ../core/terms.fs
require ../core/unsupported-forms.fs
require ./environment.fs
require ./env-publish.fs
require ./mixed-infer.fs
require ./check-block.fs

begin-structure /lf-chk
  field: lf-chk-budget   \ fuel each check in this context starts with
  field: lf-chk-left     \ fuel left during the audit
  field: lf-chk-step     \ the step the current or last check reached
  field: lf-chk-decl     \ the input record of the declaration checked
  field: lf-chk-found    \ the last result: a type node, or the type's Sort level
end-structure
/lf-chk context-record: lf-check-state
lf-depth-limit context-walk: lf-check-walker

\ The budget of every later check in this context, and the step at which
\ the last one ended: 0 before its snapshot was found, 1-8 as above,
\ lf-step-done when every step succeeded.
: lf-check-budget ( fuel -- ) lf-check-state lf-chk-budget ! ;
: lf-check-step@ ( -- step ) lf-check-state lf-chk-step @ ;

: lf-check-left ( -- addr ) lf-check-state lf-chk-left ;
: lf-check-found ( -- addr ) lf-check-state lf-chk-found ;
: lf-check-decl ( -- decl ) lf-check-state lf-chk-decl @ ;
: lf-check-claim ( -- term ) lf-check-decl lf-idecl-type @ ;
: lf-check-value-root ( -- term ) lf-check-decl lf-idecl-value @ ;
: lf-check-theorem? ( -- flag ) lf-check-decl lf-idecl-kind @ lf-kind-theorem = ;
: lf-check-site ( -- site ) c" check-declaration lf-check-declaration" ;
\ Run xt ( -- outcome ) only when the outcome so far is ok.
: lf-check-then ( outcome xt -- outcome ) over ok? if nip execute else drop then ;
\ Keep a step's result, passing its outcome on.
: lf-check-keep ( x outcome -- outcome ) swap lf-check-found ! ;

\ U1: a definition or theorem, safe; recorded with its kind and safety.
\ One without a value is malformed input (invalid).
: lf-check-kind? ( kind -- flag ) dup lf-kind-definition = swap lf-kind-theorem = or ;
: lf-check-in-scope? ( decl -- flag )
  dup lf-idecl-kind @ lf-check-kind? swap lf-idecl-safety @ lf-safety-safe = and ;
: lf-check-out-of-scope ( decl -- outcome )
  dup lf-idecl-kind @ swap lf-idecl-safety @ lf-check-site lf-diag-unsupported-kind
  lf-diag-note outcome-unsupported ;
: lf-check-no-value ( decl -- outcome )
  lf-idecl-value @ lf-env-limit lf-check-site lf-diag-bad-argument lf-diag-note
  outcome-invalid ;
: lf-check-u1 ( -- outcome )
  lf-check-decl dup lf-check-in-scope? 0= if lf-check-out-of-scope exit then
  dup lf-idecl-value @ 0< if lf-check-no-value else drop outcome-ok then ;

\ U2: no leaf of an unsupported form reachable from a root, each visit one
\ unit of the audit's fuel; recorded with the form and the node. Any other
\ leaf passes here, for V1 to judge.
: lf-check-form ( first second walk -- outcome )
  nip walk-node @ lf-check-site lf-diag-unsupported-form lf-diag-note
  outcome-unsupported ;
: lf-check-forms-dispatch ( first second walk tag -- outcome )
  dup lf-term-binary-tag? if drop walk-children exit then
  lf-tag-unsupported = if lf-check-form else drop 2drop outcome-ok then ;
: lf-check-forms-visit ( walk -- outcome )
  lf-terms ['] lf-check-forms-dispatch walk-visit ;
: lf-check-walked ( outcome -- outcome )
  lf-check-walker walk-fuel @ lf-check-left ! lf-check-walker lf-check-site lf-diag-walk ;
: lf-check-forms ( root -- outcome )
  lf-check-left @ lf-check-walker walk-budget 0= if drop outcome-invalid exit then
  ['] lf-check-forms-visit lf-check-walker walk-run lf-check-walked ;

\ V1: a live root whose graph is well formed, in the session's level
\ context, with every bound variable under its binder; the audit's fuel.
: lf-check-bad-root ( root -- outcome )
  0 lf-check-site lf-diag-malformed lf-diag-note outcome-invalid ;
: lf-check-closed ( root -- outcome )
  dup lf-term-identity 0= if lf-check-bad-root exit then
  0 lf-check-left @ lf-constant-term-scope lf-cts-fuel @ lf-check-left ! ;

\ Step 1, the audit: U1, then U2 and V1, each on the type, then the value.
: lf-check-both ( xt -- outcome )
  >r lf-check-claim r@ execute dup ok? if drop lf-check-value-root r@ execute then
  r> drop ;
: lf-check-u2 ( -- outcome ) ['] lf-check-forms lf-check-both ;
: lf-check-v1 ( -- outcome ) ['] lf-check-closed lf-check-both ;
: lf-check-audit ( -- outcome )
  lf-check-u1 ['] lf-check-u2 lf-check-then ['] lf-check-v1 lf-check-then ;

\ Step 4: the declared type's type, in a new inference job in environment
\ mode, with the fuel the audit left.
\ The derivation log (ADR 0013): steps 4-6 are one proposition step (a
\ theorem) or type step (a definition) of the claim, opened here and
\ closed by step 6 with the Sort's level; a check that ends earlier
\ closes it with its outcome (lf-check-logged). lf-check-type and
\ lf-check-prop each read lf-log? on their own; they agree because
\ during a check lf-log? never turns from false to true: a check's log is
\ held, and only a preset log that is not a check's restarts (after its
\ outermost rule ends). A log truncated between steps 4 and 6 stays off
\ until the next check: step 6 then does not close the formation step,
\ which stays counted as open, and lf-log-close-all closes it.
: lf-check-formation ( -- rule )
  lf-check-theorem? if lf-rule-proposition else lf-rule-type then ;
: lf-check-type ( -- outcome )
  lf-log? if lf-check-claim lf-log-none lf-check-formation lf-log-open then
  lf-check-left @ lf-minfer-start-env lf-check-claim lf-minfer-walk lf-check-keep ;
\ Step 5 (S1): that type is a Sort, whose level is kept.
: lf-check-sort ( -- outcome )
  lf-check-found @ lf-check-site lf-diag-type-expected lf-minfer-sort-rule lf-check-keep ;
\ Step 6 (S3), for a theorem: that level is zero under every assignment.
: lf-check-not-prop ( level -- outcome )
  lf-check-site lf-diag-not-proposition lf-minfer-reject ;
: lf-check-zero ( level -- outcome )
  dup lf-minfer-zero? ok-then? 0= if nip exit then
  if drop outcome-ok else lf-check-not-prop then ;
: lf-check-prop-pass ( -- outcome )
  lf-check-theorem? if lf-check-found @ lf-check-zero else outcome-ok then ;
: lf-check-prop ( -- outcome )
  lf-check-prop-pass lf-log? if lf-check-found @ swap lf-log-close nip then ;
\ Step 7: the scratch of steps 4-6 discarded (back to the input marks), the
\ value's type in a new job with the fuel left.
: lf-check-restart ( -- outcome )
  lf-minfer-fuel @ lf-input-rollback ok-then? if lf-minfer-start-env outcome-ok then ;
: lf-check-infer-value ( -- outcome ) lf-check-value-root lf-minfer-walk lf-check-keep ;
: lf-check-value ( -- outcome ) lf-check-restart ['] lf-check-infer-value lf-check-then ;
\ Step 8 (D1-D5): the value's type against the declared type.
: lf-check-compare ( -- outcome )
  lf-check-found @ lf-check-claim lf-minfer-agree
  lf-check-site lf-diag-value-apart lf-minfer-verdict ;

\ The steps ( -- outcome ), in order.
create lf-check-steps
  ' lf-check-audit , ' lf-env-own-name , ' lf-env-own-params , ' lf-check-type ,
  ' lf-check-sort , ' lf-check-prop , ' lf-check-value , ' lf-check-compare ,
here lf-check-steps - 1 cells / constant lf-check-steps#
lf-check-steps# 1+ constant lf-step-done
: lf-check-step! ( step -- ) lf-check-state lf-chk-step ! ;
: lf-check-do ( k -- outcome ) dup 1+ lf-check-step! cells lf-check-steps + @ execute ;
: lf-check-steps-run ( -- outcome )
  lf-check-steps# 0 ?do i lf-check-do dup ok? 0= if unloop exit then drop loop
  lf-step-done lf-check-step! outcome-ok ;
\ The derivation log (ADR 0013): with it on, the steps are one declaration
\ step of the claim and the value, closed with the check's outcome (and
\ any rule left open by a step that failed with it).
: lf-check-logged ( -- outcome )
  lf-check-claim lf-check-value-root lf-rule-declaration lf-log-open
  lf-check-steps-run lf-log-close-all ;
: lf-check-run ( -- outcome )
  lf-log? if lf-check-logged else lf-check-steps-run then ;

\ The declaration of this context's snapshot, a check's (lf-env-begin),
\ and the budget: ok, or invalid without a check's snapshot of the valid
\ current environment (recorded by lf-env-checking) or an intact input.
: lf-check-begin ( -- outcome )
  0 lf-check-step! lf-check-state lf-chk-budget @ lf-check-left !
  lf-env-checking 0= if outcome-invalid exit then nip
  lf-input-read ok-then? if lf-check-state lf-chk-decl ! outcome-ok then ;
\ A member of an inductive block is checked with its block, all members
\ at once, by check-block.fs (plan task 5.2.1a; ADR 0015), on the same
\ budget; its step is then lf-block-step@'s, and lf-check-step@ stays 0.
\ The derivation log (ADR 0013): with it on, the block check is one
\ inductive-block step of the first member's slot, closed with the
\ block's outcome (and any rule left open by a step that failed with it),
\ as lf-check-logged does for a declaration; its inner steps are not yet
\ logged in detail.
: lf-check-block-pass ( -- outcome ) lf-check-left @ lf-block-check ;
: lf-check-block-logged ( -- outcome )
  lf-env-limit lf-log-none lf-rule-inductive-block lf-log-open lf-check-block-pass
  lf-log-close-all ;
: lf-check-block ( -- outcome )
  lf-log? if lf-check-block-logged else lf-check-block-pass then ;
: lf-check-kind-run ( -- outcome )
  lf-check-decl lf-ind-member? if lf-check-block else lf-check-run then ;
\ Check the declaration of this context's snapshot and end the check with
\ its outcome (lf-env-finish), as described above.
: lf-check-declaration ( -- )
  lf-check-begin ['] lf-check-kind-run lf-check-then lf-env-finish ;

\ Check every declaration of this context's intact input, in input order,
\ each with fuel, in a new environment with room for deps dependencies,
\ which is left current: (env outcome) as lf-env-run gives it, or (0
\ outcome) when no environment could be made. A check that throws stops
\ the run (no replacement context: invalid). Free env with lf-env-free.
: lf-check-no-maker ( -- context ior ) 0 -1 ;
: lf-check-run-all ( env -- env outcome )
  ['] lf-check-declaration ['] lf-check-no-maker lf-env-run ;
: lf-check-used ( env -- env outcome )
  dup lf-env-use dup ok? if drop lf-check-run-all then ;
: lf-check-input ( fuel deps -- env outcome )
  swap lf-check-budget lf-env-new dup ok? if drop lf-check-used then ;

\ Reports, after a run (within lf-env-view's snapshot) or within a later
\ check's: declaration d's verdict, an accepted one labelled, with the
\ axiom set its slot holds (none in the first checker; anything else
\ prints its bits).
: lf-check-label ( -- c-addr u ) s" accepted (experimental, not independently audited)" ;
: lf-check-axioms. ( bits -- ) ." axioms: " ?dup if ." bits " 0 .r else ." none" then ;
: lf-check-accepted. ( d -- )
  lf-check-label type ." ; "
  lf-env-axioms ok? if lf-check-axioms. else drop ." axioms: ?" then ;
: lf-check-verdict. ( d -- )
  dup lf-env-outcome dup ok? if drop lf-check-accepted. else nip outcome-text type then ;
