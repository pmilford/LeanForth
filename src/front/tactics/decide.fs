\ by-decide: Lean's decide (plan row S3, slice S3a; word list
\ .claude/work/briefs/S3-DECIDE-WORDLIST.md), a port of Lean 4.35.0's
\ evalDecide with its default configuration (src/lean/Lean/Elab/Tactic/
\ Decide.lean:83-115, 198-200): closeMainGoalUsing of doElab on the main
\ goal's type P, made ready by preprocessPropToDecide (24-33): P
\ instantiated; when it has a free variable, zetaReduce (Meta/Transform.lean:
\ 198-215) is the identity unless P holds a let or have expression or a let
\ variable, which it would remove or substitute (not ported: unsupported,
\ 93, plan S3b; review s3a-decide B2); a metavariable left is error 252, a
\ free variable 251 (with Lean's hint). Then mkDecide P (app-builder.fs's
\ lf-mk-decide: Decidable.decide P I, the instance I synthesized, else
\ synthInstance's "failed to synthesize", 122), put in whnf at default
\ transparency at least (withAtLeastTransparency): Bool.true closes the
\ goal with of_decide_eq_true P I (id (decide P I = true) (Eq.refl true));
\ Bool.false is error 250, anything else 253 (Lean's first lines; the
\ blame of the reduction, the unfolded instances and the hints are plan
\ S3b). A whnf that answers unsupported or runs out is that outcome (93,
\ 91), never 250 or 253. A let expression in a P without free variables is
\ left to whnf, as Lean leaves it (zetaReduce runs only with one).
\ by-native-decide: Lean's native_decide trusts the compiler
\ (Lean.ofReduceBool, an axiom LeanForth never accepts: ADR 0021 D7), so
\ it is refused, error 254 (unsupported).
\ Lean call list: closeMainGoalUsing -> lf-close-main-goal-using
\ (tactic-core.fs); instantiateMVars -> lf-instantiate!; hasFVar ->
\ lf-meta-has-fvar?; hasMVar -> lf-meta-has-mvar? (app-builder.fs);
\ mkDecide -> lf-mk-decide; withAtLeastTransparency .default <| whnf ->
\ lf-with-at-least (meta-config.fs) of lf-whnf! (meta-must.fs);
\ mkApp3 of Eq.{1} and reflBoolTrue (the nodes mkEq and mkEqRefl make) ->
\ lf-mk-eq, lf-mk-eq-refl; mkExpectedPropHint -> lf-mk-expected-prop-hint;
\ mkApp3 -> lf-mk-app-n (app-builder.fs).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs

250 outcome-invalid s" Tactic `decide` proved that the proposition"
  lfa-code: lfa-e-decide-false
251 outcome-invalid s" Expected type must not contain free variables"
  lfa-code: lfa-e-decide-fvars
252 outcome-invalid s" Expected type must not contain metavariables"
  lfa-code: lfa-e-decide-mvars
253 outcome-invalid s" Tactic `decide` failed to reduce" lfa-code: lfa-e-decide-stuck
254 outcome-unsupported
  s" `native_decide` is not supported: it trusts Lean's compiler (`Lean.ofReduceBool`), "
  lfa-code: lfa-e-native-decide
lfa-e-native-decide lfa-message-of s" never accepted (ADR 0021 D7)" lfa-more,
tac-shape-plain lf-tactic: by-decide constant tac-k-decide
s" decide" tac-k-decide lf-tactic-lean!
tac-shape-plain lf-tactic: by-native-decide constant tac-k-native-decide
s" native_decide" tac-k-native-decide lf-tactic-lean!

\ ---- preprocessPropToDecide: the messages' details, then the tests.
: tdc-hint. ( -- outcome )
  s\" \n\nHint: Use the `+revert` option to automatically clean up and revert " lf-pp-emit
  s" free variables" lf-pp-emit outcome-ok ;
: tdc-revert. ( p -- outcome ) lf-tac-indented. ['] tdc-hint. ok-and ;
: tdc-fail ( p xt code -- ) >r lf-tac-detail r> lf-tac-stop ;
\ zetaReduce (Meta/Transform.lean:198-215) is the identity unless some node
\ of P is a let (or have) expression or a let variable (meta-spine.fs's
\ lf-meta-let-fvar?): not ported, unsupported.
: tdc-let? ( t -- flag ) dup lf-let? swap lf-meta-let-fvar? or ;
: tdc-zeta ( p -- p )
  dup ['] tdc-let? lf-term-holds-node? lf-must if outcome-unsupported lf-must then ;
: tdc-pre ( type -- p )
  lf-instantiate! dup lf-meta-has-fvar? if tdc-zeta then
  dup lf-meta-has-mvar? lf-must if ['] lf-tac-indented. lfa-e-decide-mvars tdc-fail then
  dup lf-meta-has-fvar? if ['] tdc-revert. lfa-e-decide-fvars tdc-fail then ;

\ ---- doElab: Bool.true gives the proof, anything else diagnose's error.
: tdc-bool? ( r c-addr u -- flag ) lf-meta-const-named? ;
\ id (decide P I = true) (Eq.refl true), mkExpectedPropHint reflBoolTrue.
: tdc-refl ( dec -- h )
  s" Bool.true" lf-mk-const0 tuck lf-mk-eq swap lf-mk-eq-refl swap
  lf-mk-expected-prop-hint ;
\ of_decide_eq_true P I h, I the instance mkDecide put last.
: tdc-proof ( p dec -- e )
  s" of_decide_eq_true" lf-mk-const0 -rot dup lf-term-second@ swap tdc-refl
  3 lf-mk-app-n ;
: tdc-false. ( p -- outcome ) lf-tac-indented. s\" \nis false" lf-pp-emit ;
: tdc-stuck. ( dec -- outcome ) lf-tac-indented. s\" \nto `true` or `false`." lf-pp-emit ;
: tdc-diagnose ( p dec r -- )
  s" Bool.false" tdc-bool? if drop ['] tdc-false. lfa-e-decide-false tdc-fail exit then
  nip ['] tdc-stuck. lfa-e-decide-stuck tdc-fail ;
: tdc-whnf ( dec -- r ) ['] lf-whnf! lf-tr-default lf-with-at-least ;
: tdc-decide ( p -- e )
  dup lf-mk-decide dup tdc-whnf dup s" Bool.true" tdc-bool? if drop tdc-proof exit then
  tdc-diagnose ;
: tdc-elab ( type tag -- e ) drop tdc-pre tdc-decide ;
: tdc-run ( i -- ) ['] tdc-elab lf-close-main-goal-using ;
' tdc-run tac-k-decide lf-tactic-action!
: tnd-run ( i -- ) drop lfa-e-native-decide lf-tac-stop ;
' tnd-run tac-k-native-decide lf-tactic-action!
