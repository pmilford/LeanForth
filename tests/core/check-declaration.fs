\ Tests of check-declaration (src/kernel/check-declaration.fs; plan task
\ 2.2.3) through the checked environment's serial publisher: every
\ outcome (accepted, rejected, unknown, unsupported, invalid, exhausted,
\ full), each with the step at which the check ended and the diagnostic
\ that explains it; Lean's order between steps and inside inference (the
\ first failure decides, and its reason is Lean's); the dependencies an
\ accepted declaration records, and none recorded by inference run aside;
\ the input unchanged by checks; the room step 7 gives back; and fuel
\ sweeps (below some fuel a check is exhausted, from there on it has its
\ final outcome, never accepted before). The 62-row table, the binder-domain
\ table and the universe-scope rows are compared with pinned Lean by
\ make test-first-checker-differential, test-binder-domains-differential
\ and test-universe-scope-differential.
\ Cases are written in the prefix text of first-checker-terms.lean and
\ built by tests/support/first-checker-driver.fs: Sorts S <level>, bound
\ variables V <index>, A function argument, L domain body (lambda), P
\ domain body (Pi), C name n levels, X<form>; levels z, s l, p name.
\ Test-only; nothing here accepts a theorem outside the code under test.
include ../support/tester.fs
include ../support/checks.fs
require ../support/first-checker-driver.fs

\ ---------------------------------------------------------------------------
\ Running a case: every declaration checked in a new environment; then the
\ last one's outcome, diagnostic code and step, and the environment freed.
variable the-env
: check-run ( -- )
  lf-input-end ok? must 64 lf-env-new ok? must dup the-env ! lf-env-use ok? must
  ['] lf-check-declaration ['] fc-no-maker lf-env-run ok? must ;
: last-result ( -- outcome code step )
  lf-diag-code@ lf-check-step@ lf-env-view ok? must fc-last lf-env-outcome -rot ;
: env-done ( -- ) the-env @ lf-env-free ok? must ;
: check-last ( -- outcome code step ) check-run last-result env-done ;

\ Steps, by name.
1 constant audit   2 constant name-step   3 constant params-step
4 constant type-step   5 constant sort-step   6 constant prop-step
7 constant value-step   8 constant compare-step

\ ---------------------------------------------------------------------------
\ Accepted (A1): idProp : ∀ (P : Prop), P → P := fun P h => h. Its verdict
\ is labelled; nothing is recorded.
fc-case accepted
fc-decl check thm safe idProp 0 TYPE P S z P V 0 V 1 VALUE L S z L V 0 V 0
T{ check-last -> outcome-ok 0 lf-step-done }T
T{ lf-check-label s" accepted (experimental, not independently audited)" compare -> 0 }T

\ The same as a definition, and over Type as a definition (any Sort).
fc-case definition
fc-decl check def safe idDef 0 TYPE P S s z P V 0 V 1 VALUE L S s z L V 0 V 0
T{ check-last -> outcome-ok 0 lf-step-done }T

\ ---------------------------------------------------------------------------
\ Rejected, one rule each, at the step where Lean's kernel fails.
\ N1: the value names a constant nothing declared.
fc-case n1
fc-decl check thm safe useMissing 0 TYPE P S z P V 0 V 1 VALUE L S z L V 0 A A C missing 0 V 1 V 0
T{ check-last -> outcome-rejected lf-diag-unknown-constant value-step }T
\ N2: a second idProp.
fc-case n2
fc-decl before thm safe idProp 0 TYPE P S z P V 0 V 1 VALUE L S z L V 0 V 0
fc-decl check thm safe idProp 0 TYPE P S z P V 0 V 1 VALUE L S z L V 0 V 0
T{ check-last -> outcome-rejected lf-diag-already-declared name-step }T
\ L1: idProp has no universe parameter but gets one.
fc-case l1
fc-decl before thm safe idProp 0 TYPE P S z P V 0 V 1 VALUE L S z L V 0 V 0
fc-decl check thm safe useOne 0 TYPE P S z P V 0 V 1 VALUE L S z L V 0 A A C idProp 1 z V 1 V 0
T{ check-last -> outcome-rejected lf-diag-level-count value-step }T
\ L2: Sort v in the type of a declaration with only u.
fc-case l2
fc-decl check def safe undeclared 1 u TYPE S s p v VALUE S p v
T{ check-last -> outcome-rejected lf-diag-undeclared-param type-step }T
\ L2 on a constant's universe argument alone: the value fixtureId.{v}
\ where the claim is at Sort u (Lean: check_level in infer_constant).
fc-case l2-argument
fc-decl before def safe fixtureId 1 u TYPE P S p u P V 0 V 1 VALUE L S p u L V 0 V 0
fc-decl check def safe argument 1 u TYPE P S p u P V 0 V 1 VALUE C fixtureId 1 p v
T{ check-last -> outcome-rejected lf-diag-undeclared-param value-step }T
\ L3: u listed twice.
fc-case l3
fc-decl check def safe repeated 2 u u TYPE S s z VALUE S z
T{ check-last -> outcome-rejected lf-diag-duplicate-param params-step }T
\ S1: the declared type is a function.
fc-case s1
fc-decl check thm safe notType 0 TYPE L S z V 0 VALUE L S z V 0
T{ check-last -> outcome-rejected lf-diag-type-expected sort-step }T
\ S3: a theorem over Type.
fc-case s3
fc-decl check thm safe overType 0 TYPE P S s z P V 0 V 1 VALUE L S s z L V 0 V 0
T{ check-last -> outcome-rejected lf-diag-not-proposition prop-step }T
\ F1: h h, where h : P is no function.
fc-case f1
fc-decl check thm safe applyProof 0 TYPE P S z P V 0 V 1 VALUE L S z L V 0 A V 0 V 0
T{ check-last -> outcome-rejected lf-diag-function-expected value-step }T
\ S2: a binder whose domain h is a proof, not a type.
fc-case s2
fc-decl check thm safe domain 0 TYPE P S z P V 0 V 1 VALUE L S z L V 0 L V 0 V 0
T{ check-last -> outcome-rejected lf-diag-domain-type value-step }T
\ D (value): claims ∀ P Q, P → P; the proof is a function from Q.
fc-case d-value
fc-decl check thm safe wrong 0 TYPE P S z P S z P V 1 V 2 VALUE L S z L S z L V 0 V 0
T{ check-last -> outcome-rejected lf-diag-value-apart compare-step }T
\ D (argument): k : (P → P) → P gets fun h : Q => h.
fc-case d-argument
fc-decl check thm safe arg 0 TYPE P S z P S z P P P V 1 V 2 V 2 V 2 VALUE L S z L S z L P P V 1 V 2 V 2 A V 0 L V 1 V 0
T{ check-last -> outcome-rejected lf-diag-argument-apart value-step }T

\ ---------------------------------------------------------------------------
\ Unknown. K5: a declaration that uses an undecided one (here invalid: a
\ definition without a value). K4: a level that is equal only after
\ Lean's normalisation.
fc-case k5
fc-decl before def safe broken 0 TYPE S s z VALUE none
fc-decl check def safe user 0 TYPE S s z VALUE C broken 0
T{ check-last -> outcome-unknown lf-diag-dependency-undecided value-step }T
fc-case k4
fc-decl check def safe spelling 1 u TYPE P S p u P V 0 V 1 VALUE L S m p u p u L V 0 V 0
T{ check-last -> outcome-unknown lf-diag-symbolic-level compare-step }T

\ ---------------------------------------------------------------------------
\ Unsupported. U1: every kind but a safe definition or theorem, before any
\ typing (so even a type that would fail N1). K5: a use of an unsupported
\ declaration. U2: each form, wherever it is.
fc-case axiom
fc-decl check ax safe postulate 0 TYPE C missing 0 VALUE none
T{ check-last -> outcome-unsupported lf-diag-unsupported-kind audit }T
fc-case opaque
fc-decl check opq safe hidden 0 TYPE S s z VALUE S z
T{ check-last -> outcome-unsupported lf-diag-unsupported-kind audit }T
fc-case unsafe
fc-decl check def unsafe risky 0 TYPE S s z VALUE S z
T{ check-last -> outcome-unsupported lf-diag-unsupported-kind audit }T
fc-case partial
fc-decl check def partial looping 0 TYPE S s z VALUE S z
T{ check-last -> outcome-unsupported lf-diag-unsupported-kind audit }T
fc-case uses-axiom
fc-decl before ax safe postulate 0 TYPE S z VALUE none
fc-decl check def safe user 0 TYPE S z VALUE C postulate 0
T{ check-last -> outcome-unsupported lf-diag-dependency-unsupported value-step }T
fc-case let
fc-decl check def safe withLet 0 TYPE S s z VALUE Xlet
T{ check-last -> outcome-unsupported lf-diag-unsupported-form audit }T
fc-case nat-literal
fc-decl check def safe withLiteral 0 TYPE S s z VALUE L S z Xlit
T{ check-last -> outcome-unsupported lf-diag-unsupported-form audit }T
fc-case metadata
fc-decl check thm safe withMetadata 0 TYPE P Xmdata S z VALUE S z
T{ check-last -> outcome-unsupported lf-diag-unsupported-form audit }T
fc-case projection
fc-decl check def safe withProjection 0 TYPE S s z VALUE A Xproj S z
T{ check-last -> outcome-unsupported lf-diag-unsupported-form audit }T
\ The recorded form and node: a projection, the leaf node.
fc-case form-recorded
fc-decl check def safe withProjection 0 TYPE S s z VALUE Xproj
: form-diag ( -- form ) check-run lf-diag@ 2drop drop env-done ;
T{ form-diag -> lf-form-proj }T

\ ---------------------------------------------------------------------------
\ Invalid. V1: a variable without a binder; a concrete Sort in a symbolic
\ term (ADR 0007); a definition without a value; a check outside any
\ check's snapshot.
fc-case loose
fc-decl check thm safe loose 0 TYPE P S z P V 0 V 1 VALUE L S z L V 0 V 2
T{ check-last -> outcome-invalid lf-diag-out-of-scope audit }T
fc-case concrete
fc-read-term S s z constant concrete-type
0 lf-term-sort must constant concrete-value
: concrete-decl ( -- )
  fc-buf /lf-idecl erase lf-kind-definition fc-buf lf-idecl-kind !
  s" concrete" fc-intern fc-buf lf-idecl-name ! lf-hint-regular fc-buf lf-idecl-hint !
  concrete-type fc-buf lf-idecl-type ! concrete-value fc-buf lf-idecl-value !
  fc-buf lf-input-add ok? must drop ;
concrete-decl
T{ check-last nip -> outcome-invalid audit }T
fc-case no-value
fc-decl check def safe noValue 0 TYPE S s z VALUE none
T{ check-last -> outcome-invalid lf-diag-bad-argument audit }T
: outside ( -- outcome step )
  lf-check-declaration lf-env-cand lf-cand-outcome @ lf-check-step@ ;
T{ outside -> outcome-invalid 0 }T

\ ---------------------------------------------------------------------------
\ Exhausted: too little fuel for the audit; and full: a 17th dependency
\ (lf-env-dep-capacity 16), and a term store that fills while the declared
\ type is inferred (the binder-domain table's eta case).
fc-case exhausted
fc-decl check thm safe idProp 0 TYPE P S z P V 0 V 1 VALUE L S z L V 0 V 0
T{ 3 lf-check-budget check-last -> outcome-exhausted lf-diag-fuel audit }T
fc-fuel lf-check-budget
fc-case deps-full
fc-decl before def safe c0 0 TYPE P S z S z VALUE L S z V 0
fc-decl before def safe c1 0 TYPE P S z S z VALUE L S z V 0
fc-decl before def safe c2 0 TYPE P S z S z VALUE L S z V 0
fc-decl before def safe c3 0 TYPE P S z S z VALUE L S z V 0
fc-decl before def safe c4 0 TYPE P S z S z VALUE L S z V 0
fc-decl before def safe c5 0 TYPE P S z S z VALUE L S z V 0
fc-decl before def safe c6 0 TYPE P S z S z VALUE L S z V 0
fc-decl before def safe c7 0 TYPE P S z S z VALUE L S z V 0
fc-decl before def safe c8 0 TYPE P S z S z VALUE L S z V 0
fc-decl before def safe c9 0 TYPE P S z S z VALUE L S z V 0
fc-decl before def safe c10 0 TYPE P S z S z VALUE L S z V 0
fc-decl before def safe c11 0 TYPE P S z S z VALUE L S z V 0
fc-decl before def safe c12 0 TYPE P S z S z VALUE L S z V 0
fc-decl before def safe c13 0 TYPE P S z S z VALUE L S z V 0
fc-decl before def safe c14 0 TYPE P S z S z VALUE L S z V 0
fc-decl before def safe c15 0 TYPE P S z S z VALUE L S z V 0
fc-decl before def safe c16 0 TYPE P S z S z VALUE L S z V 0
fc-decl check def safe user 0 TYPE S z VALUE A C c0 0 A C c1 0 A C c2 0 A C c3 0 A C c4 0 A C c5 0 A C c6 0 A C c7 0 A C c8 0 A C c9 0 A C c10 0 A C c11 0 A C c12 0 A C c13 0 A C c14 0 A C c15 0 A C c16 0 P S z V 0
T{ check-last -> outcome-full lf-diag-deps-full value-step }T
fc-case terms-full
fc-decl check thm safe bdCompare 0 TYPE P P P S s z P A L S s z V 0 P V 0 V 1 P V 1 V 2 S z P A V 0 L S s z L A L S s z V 0 P V 0 V 1 V 0 A V 1 L S s z L P V 0 V 1 L V 1 A V 1 V 0 VALUE L P P S s z P A L S s z V 0 P V 0 V 1 P V 1 V 2 S z L A V 0 L S s z L A L S s z V 0 P V 0 V 1 V 0 V 0
T{ check-last -> outcome-full lf-diag-terms-full type-step }T

\ ---------------------------------------------------------------------------
\ Lean's order: the first failure decides, with Lean's reason.
\ The declared type before the value: S1 in the type, N1 in the value.
fc-case order-type-first
fc-decl check thm safe both 0 TYPE L S z V 0 VALUE C missing 0
T{ check-last -> outcome-rejected lf-diag-type-expected sort-step }T
\ S3 before the value.
fc-case order-prop-first
fc-decl check thm safe both 0 TYPE P S s z P V 0 V 1 VALUE C missing 0
T{ check-last -> outcome-rejected lf-diag-not-proposition prop-step }T
\ A function before its argument: Prop applied to an unknown constant is
\ F1 (Lean's infer_app needs a Pi before it infers the argument) ...
fc-case order-function-first
fc-decl check def safe both 0 TYPE A S z C missing 0 VALUE S z
T{ check-last -> outcome-rejected lf-diag-function-expected type-step }T
\ ... and an unknown constant as the function is N1.
fc-case order-function-unknown
fc-decl check def safe both 0 TYPE A C missing 0 S z VALUE S z
T{ check-last -> outcome-rejected lf-diag-unknown-constant type-step }T
\ An undecided dependency in the type before N1 in the value: unknown.
fc-case order-k5-first
fc-decl before def safe broken 0 TYPE S s z VALUE none
fc-decl check def safe both 0 TYPE C broken 0 VALUE C missing 0
T{ check-last -> outcome-unknown lf-diag-dependency-undecided type-step }T
\ The audit before any typing: U2 in the value, N1 in the type.
fc-case order-audit-first
fc-decl check def safe both 0 TYPE C missing 0 VALUE Xlet
T{ check-last -> outcome-unsupported lf-diag-unsupported-form audit }T
\ N2 before L3, L3 before L2, L2 in the type before L1 in the value.
fc-case order-name-first
fc-decl before thm safe idProp 0 TYPE P S z P V 0 V 1 VALUE L S z L V 0 V 0
fc-decl check thm safe idProp 2 u u TYPE P S p v P V 0 V 1 VALUE L S z L V 0 V 0
T{ check-last -> outcome-rejected lf-diag-already-declared name-step }T
fc-case order-params-first
fc-decl check def safe both 2 u u TYPE S s p v VALUE S p v
T{ check-last -> outcome-rejected lf-diag-duplicate-param params-step }T
fc-case order-l2-first
fc-decl before thm safe idProp 0 TYPE P S z P V 0 V 1 VALUE L S z L V 0 V 0
fc-decl check def safe both 1 u TYPE S s p v VALUE C idProp 1 z
T{ check-last -> outcome-rejected lf-diag-undeclared-param type-step }T
\ Inside one term, a binder's domain before its body: S2 in the first
\ domain, N1 in the body.
fc-case order-domain-first
fc-decl check thm safe both 0 TYPE P S z P V 0 V 1 VALUE L S z L V 0 L V 0 C missing 0
T{ check-last -> outcome-rejected lf-diag-domain-type value-step }T

\ ---------------------------------------------------------------------------
\ Dependencies: an accepted declaration records the accepted ones its type
\ and value name, ascending and distinct, and its axiom set (empty).
fc-case dependencies
fc-decl before def safe fixtureId 1 u TYPE P S p u P V 0 V 1 VALUE L S p u L V 0 V 0
fc-decl before thm safe fixtureUse 0 TYPE P S z P V 0 V 1 VALUE L S z L V 0 A A C fixtureId 1 z V 1 V 0
fc-decl check thm safe cites 0 TYPE P S z P V 0 V 1 VALUE L S z L V 0 A A C fixtureUse 0 V 1 A A C fixtureId 1 z V 1 V 0
: slot-deps ( d -- addr n )
  lf-env lf-env-slot dup lf-slot-deps @ lf-env lf-env-pool store-slot
  swap lf-slot-count @ ;
: deps@ ( d -- d0 d1 n ) slot-deps >r dup @ swap cell+ @ r> ;
: dependencies ( -- n0 n1 d0 d1 n2 axioms )
  check-run lf-env-view ok? must 0 slot-deps nip 1 slot-deps nip 2 deps@
  2 lf-env-axioms ok? must env-done ;
T{ dependencies -> 0 1 0 1 2 0 }T
\ Inference run aside (rule P2, in the search for a rejection) records no
\ dependency. bad : (fun _ : Prop => Prop) D := f, with f : B -> B and
\ D = c0 -> ... -> c14 (each : Prop := forall p, p), records D's 15
\ constants and f, the 16 a check may hold; P2 then infers the type of
\ B -> B aside and meets B. Were B recorded, the dependencies would be
\ full, P2 would fail and the check stay unknown. Lean's kernel rejects
\ it (declTypeMismatch).
fc-case aside-deps
fc-decl before def safe B 0 TYPE S z VALUE P S z V 0
fc-decl before def safe c0 0 TYPE S z VALUE P S z V 0
fc-decl before def safe c1 0 TYPE S z VALUE P S z V 0
fc-decl before def safe c2 0 TYPE S z VALUE P S z V 0
fc-decl before def safe c3 0 TYPE S z VALUE P S z V 0
fc-decl before def safe c4 0 TYPE S z VALUE P S z V 0
fc-decl before def safe c5 0 TYPE S z VALUE P S z V 0
fc-decl before def safe c6 0 TYPE S z VALUE P S z V 0
fc-decl before def safe c7 0 TYPE S z VALUE P S z V 0
fc-decl before def safe c8 0 TYPE S z VALUE P S z V 0
fc-decl before def safe c9 0 TYPE S z VALUE P S z V 0
fc-decl before def safe c10 0 TYPE S z VALUE P S z V 0
fc-decl before def safe c11 0 TYPE S z VALUE P S z V 0
fc-decl before def safe c12 0 TYPE S z VALUE P S z V 0
fc-decl before def safe c13 0 TYPE S z VALUE P S z V 0
fc-decl before def safe c14 0 TYPE S z VALUE P S z V 0
fc-decl before def safe f 0 TYPE P C B 0 C B 0 VALUE L C B 0 V 0
fc-decl check def safe bad 0 TYPE A L S z S z P C c0 0 P C c1 0 P C c2 0 P C c3 0 P C c4 0 P C c5 0 P C c6 0 P C c7 0 P C c8 0 P C c9 0 P C c10 0 P C c11 0 P C c12 0 P C c13 0 C c14 0 VALUE C f 0
T{ check-last -> outcome-rejected lf-diag-value-apart compare-step }T

\ The input is unchanged by every check: its fingerprint, computed again,
\ is the one recorded when loading ended.
fc-case input-unchanged
fc-decl before def safe fixtureId 1 u TYPE P S p u P V 0 V 1 VALUE L S p u L V 0 V 0
fc-decl check thm safe wrong 0 TYPE P S z P S z P V 1 V 2 VALUE L S z L S z L V 0 V 0
: unchanged ( -- flag ) check-run env-done lf-input-print lf-input-fingerprint = ;
T{ unchanged -> true }T

\ Step 7 gives back the room of steps 4-6: composition's declared type
\ takes 11 scratch terms there and its value 20 in step 7. After an
\ earlier axiom (unsupported, so never typed) of 16 terms, the 64-term
\ store holds both only once the 11 are given back; kept, step 7 would be
\ full. Lean's kernel accepts both declarations.
fc-case value-room
fc-decl before ax safe pad 0 TYPE P S s s z P S s s z P S s s z P S s s z P S s s z P S s s z P S s s z P S s s z P S s s z P S s s z P S s s z P S s s z P S s s z P S s s z P S s s z S s s z VALUE none
fc-decl check thm safe composition 0 TYPE P S z P S z P S z P P V 2 V 2 P P V 2 V 2 P V 4 V 3 VALUE L S z L S z L S z L P V 2 V 2 L P V 2 V 2 L V 4 A V 1 A V 2 V 0
T{ check-last -> outcome-ok 0 lf-step-done }T

\ ---------------------------------------------------------------------------
\ Fuel sweeps: for every fuel from 0 to limit, a check of the case's last
\ declaration ends exhausted below some fuel and with its final outcome
\ (the one at limit) from some fuel on; it is never accepted earlier. In
\ between, a rejection's analysis that runs out of fuel leaves the step
\ unknown (ADR 0011, Implementation), so a rejected case may be unknown
\ there; an accepted one never is.
variable sweep-final
variable first-final
variable sweep-ok
: sweep-run ( fuel -- outcome )
  lf-check-budget 64 lf-env-new ok? must dup the-env ! lf-env-use ok? must
  ['] lf-check-declaration ['] fc-no-maker lf-env-run ok? must
  lf-env-view ok? must fc-last lf-env-outcome env-done ;
: sweep-first ( fuel -- ) first-final @ 0< if first-final ! else drop then ;
: sweep-early? ( outcome -- flag )
  dup outcome-exhausted = swap outcome-unknown = sweep-final @ outcome-rejected = and or ;
: sweep-note ( fuel outcome -- )
  dup sweep-final @ = if drop sweep-first exit then nip
  sweep-early? first-final @ 0< and 0= if false sweep-ok ! then ;
: sweep ( limit -- final first ok? )
  lf-input-end ok? must dup sweep-run sweep-final ! -1 first-final ! true sweep-ok !
  1+ 0 ?do i dup sweep-run sweep-note loop
  sweep-final @ first-final @ sweep-ok @ fc-fuel lf-check-budget ;
\ Each gives the final outcome, whether every run kept the rule, and
\ whether some fuel was too little.
: swept ( limit -- final ok? short? ) sweep swap 0> ;
fc-case sweep-accepted
fc-decl check thm safe idProp 0 TYPE P S z P V 0 V 1 VALUE L S z L V 0 V 0
T{ 300 swept -> outcome-ok true true }T
fc-case sweep-composition
fc-decl check thm safe composition 0 TYPE P S z P S z P S z P P V 2 V 2 P P V 2 V 2 P V 4 V 3 VALUE L S z L S z L S z L P V 2 V 2 L P V 2 V 2 L V 4 A V 1 A V 2 V 0
T{ 600 swept -> outcome-ok true true }T
fc-case sweep-rejected
fc-decl check thm safe wrong 0 TYPE P S z P S z P V 1 V 2 VALUE L S z L S z L V 0 V 0
T{ 700 swept -> outcome-rejected true true }T

cases-done
bye
