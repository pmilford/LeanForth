\ by-rwa[ r1 .. rn ], Lean's rwa [r1, ..., rn] (plan row TB2, tactic
\ batch 2b; at: batch 3a), a port of Lean 4.35.0's evalRwa and evalRwaAt
\ (src/lean/Lean/Elab/Tactic/Rwa.lean:70-90 over evalRwaCore :42-57; its
\ own elaborator, not the macro rw rs; assumption of earlier versions):
\ focus on the main goal; rewrite rs (by-rewrite['s row on this step: its
\ rules, <- included, and its errors at the rule); then with_reducible
\ rfl, else assumption (Lean's <|>: rfl tried from a saved state, its Lean
\ error undone, then assumption at the transparency in force, default:
\ its error 381 is rwa's; tactic-core.fs's lf-tac-first-of). Lean's inner
\ focus and its closing all_goals (first | with_reducible rfl | assumption
\ | skip) act on the rewrite's side goals, which LeanForth's rewrite
\ refuses (99), so they find none here; its linter's warning that rw
\ alone closes the goal ("`rw` already closes the goal") changes no term
\ and is not printed.
\ - by-rwa[ rs ] at: h, one hypothesis alone (evalRwaAt, Init/
\   Tactics.lean:656): the same with the rewrite getFVarId h, then each
\   rule rewriting that hypothesis in turn, each rule given the one the
\   rule before made (foldRWRulesSeq over rewriteLocalDeclCore:
\   tactics/rewrite.fs's trw-local), and in assumption's place
\   closeUsingFVar (:59-68): the hypothesis named again (the newest local
\   of its name: the last rule's), its type defeq the goal's with
\   synthetic opaque metavariables assignable (else error 456, "Type
\   mismatch: The rewritten hypothesis", with it, its type and the
\   target), closeMainGoal with it.
\ - any other at: (several names, |-, *: Lean's deprecated legacy macro,
\   Init/Tactics.lean:659-661): rw rs at: ..; assumption, by-rw['s row on
\   this step and then assumption's, no focus; the deprecation warning
\   changes no term and is not printed.
\ Lean call list: Tactic.focus -> lf-tac-focus, lf-tac-unfocus
\ (tactic-run.fs); evalTactic rewrite -> lf-tac-eval of tac-k-rewrite;
\ with_reducible rfl -> lf-tac-rfl-reducible; <|> -> lf-tac-first-of;
\ assumption -> tactics/assumption.fs's tas-row; getFVarId ->
\ lf-tac-loc-fvar; rewriteLocalDeclCore -> trw-local; inferType ->
\ lf-infer; isDefEq under withAssignableSyntheticOpaque, the mismatch ->
\ lf-tac-ensure-type-as; closeMainGoal -> lf-goal-checked-assign,
\ lf-tac-pop-main; the legacy rw -> lf-tac-eval of tac-k-rw.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs
require ./assumption.fs
require ./rewrite.fs
require ./rfl.fs

456 outcome-invalid s" Type mismatch: The rewritten hypothesis"
  lfa-code: lfa-e-rwa-mismatch
tac-shape-rules lf-tactic: by-rwa[ constant tac-k-rwa
s" rwa" tac-k-rwa lf-tactic-lean!

: trwa-close ( -- ) ['] tas-row ['] lf-tac-rfl-reducible 2 lf-tac-first-of ;
: trwa-core ( i -- ) tac-k-rewrite lf-tac-eval trwa-close ;
: trwa-focused ( i xt -- ) lf-tac-focus -rot execute lf-tac-unfocus ;

\ ---- at h: the rules folded over the hypothesis, closeUsingFVar.
: trwa-using ( i -- )
  0 lf-tac-loc-fvar tb tb-want @ lfa-e-rwa-mismatch lf-tac-ensure-type-as
  tb tb-goal @ swap lf-goal-checked-assign lf-tac-pop-main ;
: trwa-close-fvar ( -- ) lf-tac-step ['] trwa-using lf-tac-step-run ;
: trwa-close-at ( -- ) ['] trwa-close-fvar ['] lf-tac-rfl-reducible 2 lf-tac-first-of ;
: trwa-rule ( fvar i k -- fvar' i ) swap dup >r trw-local r> ;
: trwa-rules ( fvar i -- ) dup lf-tac-args# 0 ?do i trwa-rule loop 2drop ;
: trwa-at ( i -- ) dup 0 lf-tac-loc-fvar swap trwa-rules trwa-close-at ;
\ One hypothesis named, alone: evalRwaAt; any other location the legacy macro.
: trwa-one? ( i -- flag )
  dup lf-tac-loc# 1 = over lf-tac-loc-goal? 0= and swap lf-tac-loc-all? 0= and ;
: trwa-legacy ( i -- ) tac-k-rw lf-tac-eval tas-row ;
: trwa-located ( i -- ) dup trwa-one? if ['] trwa-at trwa-focused else trwa-legacy then ;
: trwa-run ( i -- )
  dup lf-tac-located? if trwa-located else ['] trwa-core trwa-focused then ;
' trwa-run tac-k-rwa lf-tactic-action!
