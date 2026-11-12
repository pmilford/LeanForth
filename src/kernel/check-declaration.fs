\ check-declaration (plan task 2.2.3; ADR 0011, ADR 0012 E4): the check
\ that the checked environment's publisher runs for each declaration of
\ the input, as the check word ( -- ) of lf-env-run or lf-env-step
\ (env-publish.fs). It checks the declaration of its context's snapshot
\ and ends with lf-env-finish, in ADR 0011's order ("Order"), step by step:
\   1 the audit, before any typing: a definition, theorem or opaque
\     declaration with a value, or an axiom or quotient record without one
\     (U1: a value missing or present against its kind is invalid), safe
\     (an unsafe or partial declaration is skipped, as Lean's replay skips
\     it: rejected, reported skipped; plan task 5.2.7); no
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
\ An opaque declaration takes these steps (add_opaque). An axiom
\ (add_axiom, plan task 5.3.1) takes steps 1-6, then 7 joins its own bit
\ (core/axiom-allowlist.fs) to its axiom set. A quotient record (add_quot,
\ plan task 5.2.4; quot.fs) takes 1 U1 alone, 2 its names (add_quot's
\ check_name), 3 Eq's shape, 4 its type's audit (U2, V1: only a warning
\ when it fails) and 5 its name, one of Lean's four; nothing is inferred.
\ The first step that does not succeed ends the check with its outcome
\ (ADR 0008), and lf-check-step@ tells which; only a check whose every
\ step succeeded ends ok. Its candidate then holds its dependencies, the
\ accepted declarations its type and value name, recorded as inference
\ meets them, with their joined axiom set (and an axiom's own bit); the
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
\ axioms: none" or the axioms' names, from the set the slot holds
\ (AGENTS.md, ADR 0011).
\ The printing words run after a check, never inside one.
\
\ [kernel] code: experimental, not through the review gate, not
\ independently audited. Limits: the stores' capacity settings (default
\ 64 terms and levels; lf-term-capacity! and the like), the heap (the
\ passes' explicit stacks grow with the depth: plan task 6.2.0), the
\ fuel, the environment and inference.
\ State: one record, lf-check-state (the budget, the fuel left in the
\ audit, the step reached, the declaration checked and the last result),
\ and one walk record, lf-check-walker (the U2 audit), both members of the
\ checker context (lib/context.fs); its marks are constant-term-boundary.fs's.
\ Inference runs on mixed-infer's state.

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
require ../core/axiom-allowlist.fs
require ./quot.fs
require ./caches.fs

begin-structure /lf-chk
  field: lf-chk-budget   \ fuel each check in this context starts with
  field: lf-chk-left     \ fuel left during the audit
  field: lf-chk-step     \ the step the current or last check reached
  field: lf-chk-decl     \ the input record of the declaration checked
  field: lf-chk-found    \ the last result: a type node, or the type's Sort level
end-structure
/lf-chk context-record: lf-check-state
lf-walk-room context-walk: lf-check-walker

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

\ U1: a definition, theorem, opaque declaration, axiom or quotient
\ record (another kind is unsupported, recorded with its kind and
\ safety). A value is malformed input (invalid) when it is missing for
\ the first three kinds, which have one, or present for the last two,
\ which have none. An unsafe or partial one (a definition marked so, an
\ axiom or opaque declaration marked unsafe; a theorem or quotient record
\ never is) is skipped as Lean's replay skips it, nothing of it checked
\ (Replay.lean 180-183; environment.fs lf-env-skip): rejected, reported
\ skipped, or rejected as a name given twice (plan task 5.2.7).
: lf-check-kind? ( kind -- flag ) dup lf-kind-valued? swap lf-kind-bare? or ;
: lf-check-out-of-scope ( decl -- outcome )
  dup lf-idecl-kind @ swap lf-idecl-safety @ lf-check-site lf-diag-unsupported-kind
  lf-diag-note outcome-unsupported ;
: lf-check-bad-value ( decl -- outcome )
  lf-idecl-value @ lf-env-limit lf-check-site lf-diag-bad-argument lf-diag-note
  outcome-invalid ;
: lf-check-value? ( decl -- flag )
  dup lf-idecl-value @ 0< 0= swap lf-idecl-kind @ lf-kind-valued? = ;
: lf-check-skip ( decl -- outcome )
  dup lf-idecl-kind @ swap lf-idecl-safety @ 1 lf-env-skip ;
: lf-check-safety ( decl -- outcome )
  dup lf-idecl-safety @ lf-safety-safe = if drop outcome-ok else lf-check-skip then ;
: lf-check-u1 ( -- outcome )
  lf-check-decl dup lf-idecl-kind @ lf-check-kind? 0= if lf-check-out-of-scope exit then
  dup lf-check-value? if lf-check-safety else lf-check-bad-value then ;

\ U2: no leaf of an unsupported form reachable from a root, each visit one
\ unit of the audit's fuel; recorded with the form and the node. Any other
\ leaf passes here, for V1 to judge. Each node is looked at once, however
\ many paths reach it (constant-term-boundary.fs's marks, as Lean reads
\ data each node keeps): a node reached again costs its visit's unit only.
: lf-check-form ( first second walk -- outcome )
  nip walk-node @ lf-check-site lf-diag-unsupported-form lf-diag-note
  outcome-unsupported ;
: lf-check-forms-dispatch ( first second walk tag -- outcome )
  dup lf-term-binary-tag? if drop walk-children exit then
  lf-tag-unsupported = if lf-check-form else drop 2drop outcome-ok then ;
: lf-check-forms-once ( first second walk tag -- outcome )
  ['] lf-check-forms-dispatch lf-walk-once ;
: lf-check-forms-visit ( walk -- outcome )
  ['] lf-check-forms-once lf-term-visit ;
: lf-check-walked ( outcome -- outcome )
  lf-check-walker walk-fuel @ lf-check-left ! lf-check-walker lf-check-site lf-diag-walk ;
: lf-check-forms-walk ( root -- outcome )
  lf-check-walker lf-walk-marking
  ['] lf-check-forms-visit lf-check-walker walk-run lf-check-walked ;
\ A root with a data word holds no unsupported leaf (compact-store plan
\ step S6 (c); ADR 0014 Amendment 4): such a leaf has none, and neither
\ has any node above one (core/terms.fs computes the word from the
\ children when the node is made), so it passes at once; a root without
\ one takes the walk, which finds the form (or passes the graph on to V1).
: lf-check-forms-word? ( root -- flag ) lf-term-data@ dup if nip then ;
: lf-check-forms ( root -- outcome )
  lf-check-left @ lf-check-walker walk-budget 0= if drop outcome-invalid exit then
  dup lf-check-forms-word? if drop outcome-ok else lf-check-forms-walk then ;

\ V1: a live root whose graph is well formed, in the session's level
\ context, with every bound variable under its binder; the audit's fuel.
: lf-check-bad-root ( root -- outcome )
  0 lf-check-site lf-diag-malformed lf-diag-note outcome-invalid ;
: lf-check-closed ( root -- outcome )
  dup lf-term-identity 0= if lf-check-bad-root exit then
  0 lf-check-left @ lf-constant-term-scope lf-cts-fuel @ lf-check-left ! ;

\ Step 1, the audit: U1, then U2 and V1, each on the type, then on the
\ value when there is one.
: lf-check-valued? ( -- flag ) lf-check-value-root 0< 0= ;
: lf-check-both ( xt -- outcome )
  >r lf-check-claim r@ execute dup ok? lf-check-valued? and
  if drop lf-check-value-root r@ execute then r> drop ;
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

\ Steps that compare with a statement Lean fixes (core/statement-match.fs),
\ on the fuel the counter at addr holds, which gets what they leave: the
\ audit's for a quotient record, inference's for an axiom's step 7, so
\ that the fuel a check reports used is exact (cli/check-run.fs; review
\ rvAX L2).
: lf-check-matched-on ( xt addr -- outcome )
  dup >r @ lf-stmt-fuel ! execute lf-stmt-fuel @ 0 max r> ! ;
: lf-check-matched ( xt -- outcome ) lf-check-left lf-check-matched-on ;
\ An axiom (add_axiom, environment.cpp 152-158: steps 1-6 as for a
\ definition), then step 7: its own bit joins the candidate's axiom set
\ (core/axiom-allowlist.fs): a listed one when it is the allowlist's
\ statement, else unlisted, which reports mark NOT PROVED.
: lf-check-own-axiom ( -- outcome )
  lf-check-decl lf-axiom-bit ok-then? if lf-env-axiom! outcome-ok then ;
: lf-check-axiom ( -- outcome )
  ['] lf-check-own-axiom lf-minfer-fuel lf-check-matched-on ;
\ A quotient record (add_quot, quot.cpp 47-100; quot.fs), on the audit's
\ fuel: U1; its names (check_name on all four, or its own once the
\ quotient is initialised); Eq's shape; its type, which add_quot never
\ reads, audited as any type (U2, V1), where a refusal only makes it
\ another type than Lean's, its diagnostic put back (review rvAX L1), but
\ running out of fuel or room stands; then its name, one of Lean's four,
\ and its type, Lean's or not (another type or other universe parameters
\ only warn: Lean's replay ignores the record, so its parameters are not
\ checked either); no inference, as Lean's kernel infers nothing there.
: lf-check-quot-eq ( -- outcome ) ['] lf-quot-eq lf-check-matched ;
: lf-check-short? ( outcome -- flag ) dup outcome-exhausted = swap outcome-full = or ;
: lf-check-quot-form ( -- outcome )
  lf-diag@ 2>r 2>r lf-check-claim lf-check-forms
  dup ok? if drop lf-check-claim lf-check-closed then
  dup lf-check-short? if 2r> 2r> 2drop 2drop exit then
  2r> 2r> lf-diag! ok? outcome-ok lf-check-keep ;
: lf-check-builtin ( -- outcome ) lf-check-decl lf-check-found @ lf-quot-builtin ;
: lf-check-quot-type ( -- outcome ) ['] lf-check-builtin lf-check-matched ;

\ The steps ( -- outcome ), in order: of a definition, theorem or opaque
\ declaration (add_definition, add_theorem, add_opaque), of an axiom and
\ of a quotient record; each table a count and its steps.
create lf-check-steps 8 ,
  ' lf-check-audit , ' lf-env-own-name , ' lf-env-own-params , ' lf-check-type ,
  ' lf-check-sort , ' lf-check-prop , ' lf-check-value , ' lf-check-compare ,
create lf-axiom-steps 7 ,
  ' lf-check-audit , ' lf-env-own-name , ' lf-env-own-params , ' lf-check-type ,
  ' lf-check-sort , ' lf-check-prop , ' lf-check-axiom ,
create lf-quot-steps 5 ,
  ' lf-check-u1 , ' lf-quot-names , ' lf-check-quot-eq , ' lf-check-quot-form ,
  ' lf-check-quot-type ,
8 constant lf-check-steps#
lf-check-steps# 1+ constant lf-step-done
: lf-check-table ( -- steps )
  lf-check-decl lf-idecl-kind @ case
    lf-kind-axiom of lf-axiom-steps endof  lf-kind-quotient of lf-quot-steps endof
    lf-check-steps swap endcase ;
: lf-check-step! ( step -- ) lf-check-state lf-chk-step ! ;
: lf-check-do ( steps k -- outcome ) dup 1+ lf-check-step! 1+ cells + @ execute ;
: lf-check-steps-run ( -- outcome )
  lf-check-table dup @ 0 ?do
    dup i lf-check-do dup ok? 0= if nip unloop exit then drop
  loop drop lf-step-done lf-check-step! outcome-ok ;
\ The derivation log (ADR 0013): with it on, the steps are one declaration
\ step of the claim and the value (none for an axiom or a quotient),
\ closed with the check's outcome (and any rule left open by a step that
\ failed with it).
: lf-check-logged-value ( -- term )
  lf-check-valued? if lf-check-value-root else lf-log-none then ;
: lf-check-logged ( -- outcome )
  lf-check-claim lf-check-logged-value lf-rule-declaration lf-log-open
  lf-check-steps-run lf-log-close-all ;
: lf-check-run ( -- outcome )
  lf-log? if lf-check-logged else lf-check-steps-run then ;

\ The structural audit's memo (core/constant-term-boundary.fs) is on in a
\ check of the checked environment, where the caches are (whnf.fs's
\ lf-whnf-env?), and starts afresh with each check: every declaration's
\ entry audit checks its terms anew.
' lf-whnf-env? is lf-audit-checking?
\ In such a check a node made before it -- an input node of the view or a
\ copy the importer made, below the input's term mark -- is given for an
\ equal record a pass makes only once the check reached it (an audit of
\ this check kept it), so what a check meets depends only on its
\ declaration and what it reads, not on the other records of the tier
\ (agent PF, review rvSN4 B1; ADR 0014 Amendment 7). Outside a check (the
\ importer's feed) every node is given.
: lf-check-before? ( n -- flag ) 0 lf-input-mark-count < ;
: lf-check-findable ( n -- flag )
  lf-audit-on? 0= if drop true exit then
  dup lf-check-before? if lf-audit-reached? else drop true then ;
' lf-check-findable is lf-term-findable?
\ Levels likewise (a level made before the check, below the input's level
\ mark, once a scope check of this check found it), but the zero level,
\ which every store holds from its reset.
: lf-check-level-before? ( n -- flag ) dup 0<> swap 1 lf-input-mark-count < and ;
: lf-check-level-findable ( n -- flag )
  lf-audit-on? 0= if drop true exit then
  dup lf-check-level-before? if lf-audit-level-reached? else drop true then ;
' lf-check-level-findable is lf-level-findable?
\ The declaration of this context's snapshot, a check's (lf-env-begin),
\ and the budget: ok, or invalid without a check's snapshot of the valid
\ current environment (recorded by lf-env-checking) or an intact input.
: lf-check-begin ( -- outcome )
  lf-caches-clear lf-audit-afresh
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
\ axiom set its slot holds: none, or the allowlist's names of its listed
\ bits (in Lean's order of names, as #print axioms sorts them), then
\ "unlisted" for any axiom outside the allowlist, which makes the
\ declaration NOT PROVED (the command line names those axioms: their
\ names are file text, which only its printer shows safely).
: lf-check-label ( -- c-addr u ) s" accepted (experimental, not independently audited)" ;
\ Bit's name when bits holds it, then a comma when a higher bit follows.
: lf-check-axiom. ( bits bit -- bits )
  2dup and 0= if drop exit then
  dup lf-axiom-unlisted = if ." unlisted" else dup lf-axiom-name type then
  2* 1- invert over and if ." , " then ;
: lf-check-axioms. ( bits -- )
  ." axioms: " dup 0= if drop ." none" exit then
  lf-axiom-propext lf-check-axiom. lf-axiom-choice lf-check-axiom.
  lf-axiom-sound lf-check-axiom. lf-axiom-unlisted lf-check-axiom. drop ;
: lf-check-accepted. ( d -- )
  lf-check-label type ." ; "
  lf-env-axioms ok? if lf-check-axioms. else drop ." axioms: ?" then ;
\ Any other: "skipped" for one Lean's replay skips (lf-env-skipped?), else
\ its outcome's name.
: lf-check-failed. ( d outcome -- )
  swap lf-env-skipped? if drop ." skipped" else outcome-text type then ;
: lf-check-verdict. ( d -- )
  dup lf-env-outcome dup ok? if drop lf-check-accepted. else lf-check-failed. then ;
