\ T e by-replace: h: Lean's replace h : T := e (plan row TB2, tactic batch
\ 2), a port of Lean 4.35.0's evalReplace (src/lean/Lean/Elab/Tactic/
\ BuiltinTactic.lean:666-677): in the main goal's context the hypothesis
\ the name names before (LocalContext.findFromUserName?: the newest
\ accessible local of that name, if any), then have h : T := e run on the
\ same step (by-have:'s row, tactics/have.fs: evalTactic of have), then
\ MVarId.tryClearMany of that hypothesis on the new main goal (meta-tactic/
\ assert.fs's lf-goal-try-clear: kept when something still depends on it;
\ the new h's value does not count, as Lean's clear ignores a have's
\ value). With no such hypothesis, the have alone. Errors and cases not
\ supported yet are by-have:'s.
\ Lean call list: withMainContext, getLCtx -> lf-tac-main, lf-goal-view;
\ getLetDeclVars and findFromUserName? -> lf-tac-arg, lf-view-named-fvar;
\ evalTactic have -> lf-tac-eval of tac-k-have; liftMetaTactic1
\ tryClearMany -> lf-lift-meta-tactic1 of lf-goal-try-clear.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs
require ../meta-tactic/assert.fs
require ./have.fs

tac-shape-decl lf-tactic: by-replace: constant tac-k-replace
s" replace" tac-k-replace lf-tactic-lean!

: trp-old ( i -- fvar|0 )
  lf-tac-main lf-goal-view swap 2 lf-tac-arg lf-view-named-fvar 0= if 0 then ;
: trp-cleared ( old goal -- goal' ) swap lf-goal-try-clear ;
: trp-clear ( old i -- ) over if ['] trp-cleared lf-lift-meta-tactic1 else 2drop then ;
: trp-run ( i -- ) dup trp-old swap dup tac-k-have lf-tac-eval trp-clear ;
' trp-run tac-k-replace lf-tactic-action!
