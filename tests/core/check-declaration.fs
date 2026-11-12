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
\ The caches (kernel/caches.fs; plan task 4.2.7), word by word: equal
\ terms built twice share a skeleton, Sorts of different levels do not; a
\ node's loose bound variables and free-variable bit; a kept value whose
\ node was discarded misses, and so does every key after emptying; each
\ mode of inference has its own table; a success answers both orders; a
\ free variable of an emptied local context has no skeleton. Each test
\ catches a planted fault (.claude/work/CA/faults.py, review CA).
create cache-mark /lf-scratch allot
T{ cache-mark lf-scratch-mark -> outcome-ok }T
lf-caches-clear
: cz ( -- level ) lf-level-tag-zero 0 0 lf-level-add must ;
: csort ( level -- term ) lf-term-symbolic-sort must ;
: cb ( i -- term ) lf-term-bvar must ;
: capp ( f a -- term ) lf-term-app must ;
: cskel ( term -- id ) lf-term-facts must drop ;
: cbits ( term -- bits ) lf-term-facts must nip ;
T{ 1 cb 0 cb capp cskel  1 cb 0 cb capp cskel = -> true }T
T{ cz csort cskel  cz lf-level-succ must csort cskel = -> false }T
T{ 1 cb 0 cb capp cbits  cz csort 0 cb lf-term-lam must cbits  0 cb 0 cb lf-term-lam must cbits
   -> 8 0 4 }T
\ A bound variable whose loose count would overflow a cell has no facts
\ (review rvCACHE L1): every pass meets it uncached, never as closed. The
\ bits are four times the loose count (compact-store plan step S2: a
\ universe-parameter bit joined the free-variable bit). Since step S3 a
\ term's fields are 32 bits wide (core/terms.fs): such an index cannot be
\ stored (the store refuses it, full). Since step S4 the facts are the
\ data word's (no skeleton memo): an index whose range is 2^20 - 1 or
\ more (Lean's own limit, expr.cpp 107-109) has none, the largest below
\ it has.
T{ max-n lf-term-bvar  max-n 2/ lf-term-bvar  max-n 2 rshift 1- lf-term-bvar
   -> false false false }T
T{ u32-mask cb lf-term-facts  lf-data-unknown 1- cb lf-term-facts -> false false }T
T{ lf-data-unknown 2 - cb cbits -> lf-data-unknown 1- 2 lshift }T
0 cb constant ckey
create cbefore /lf-scratch allot
T{ cbefore lf-scratch-mark -> outcome-ok }T
3 cb constant cval
T{ ckey cval lf-cache-whnf lf-cache-node!  ckey lf-cache-whnf lf-cache-node@ -> cval true }T
T{ cbefore lf-scratch-rollback -> outcome-ok }T  4 cb constant cnew
T{ cnew cval =  ckey lf-cache-whnf lf-cache-node@ -> true false }T
T{ ckey cnew lf-cache-whnf lf-cache-node!  lf-caches-clear  ckey lf-cache-whnf lf-cache-node@
   -> false }T
\ A key is its node's identity (compact-store plan step S4): a key given
\ back, its index made again as another node, misses (by index it would
\ hit the stale entry).
T{ cbefore lf-scratch-mark -> outcome-ok }T
5 cb 6 cb capp constant ckey2
T{ ckey2 ckey lf-cache-whnf lf-cache-node!  cbefore lf-scratch-rollback -> outcome-ok }T
6 cb 5 cb capp constant ckey3
T{ ckey3 ckey2 =  ckey3 lf-cache-whnf lf-cache-node@ -> true false }T
: cmode ( flag -- cache ) lf-minfer-aside @ swap lf-minfer-aside ! lf-ci-table swap lf-minfer-aside ! ;
T{ true cmode false cmode -> lf-cache-infer-only lf-cache-infer }T
cz csort constant ctype0   cz lf-level-succ must csort constant ctype1
T{ ctype0 ctype1 lf-cache-success lf-pair!  ctype1 ctype0 lf-cache-success lf-pair@ -> true }T
T{ ctype0 lf-lctx-local ok? swap constant cfvar -> true }T
T{ cfvar cbits -> 1 }T
lf-lctx-reset lf-caches-clear
T{ cfvar lf-term-facts -> false }T
\ Nor has a node above it (the free-variable memo walks to the leaf).
T{ cfvar 1 cb capp lf-term-facts -> false }T
\ m_whnf_core keeps the result of a whnf_core visit without cheap_proj,
\ never with it (type_checker.cpp 547; whnf.fs, plan task 5.2.2): the
\ storing step at the end of a visit, its key (and the count of open
\ terms typed under the scope, lf-cache-save) saved on the frames.
' lf-mconvert-no-visit frames: cframes
: cstored? ( key r flag -- found )
  lf-whnf-cheap !  cframes frame-reset  4 cframes frame-room? must
  over cframes lf-cache-save 2drop  outcome-ok cframes lf-cwc-store 2drop 2drop
  lf-whnf-reset  lf-cache-whnf-core lf-cache-node@ dup if nip then ;
T{ 5 cb 6 cb true cstored? -> false }T
T{ 7 cb 8 cb false cstored? -> true }T
cframes frame-free
T{ cache-mark lf-scratch-rollback -> outcome-ok }T lf-caches-clear

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
\ definition without a value). K6: a level whose specialization depends on
\ object sharing in Lean (ADR 0011, Amendment 1). And no longer K4: a
\ level equal only after Lean's normalisation is equal, as for Lean.
fc-case k5
fc-decl before def safe broken 0 TYPE S s z VALUE none
fc-decl check def safe user 0 TYPE S s z VALUE C broken 0
T{ check-last -> outcome-unknown lf-diag-dependency-undecided value-step }T
fc-case k4
fc-decl check def safe spelling 1 u TYPE P S p u P V 0 V 1 VALUE L S m p u p u L V 0 V 0
T{ check-last -> outcome-ok 0 lf-step-done }T
\ The independent review's cases (ADR 0011, Amendment 1), with Lean's
\ verdicts: the type of a Pi is built with mk_imax, a constant's type is
\ specialized as Lean's instantiate does, and levels compare by Lean's
\ is_equivalent, so these four are rejected (D1), as Lean rejects them;
\ the same with u and v swapped, and with max for imax, are accepted.
fc-case T1
fc-decl check def safe T1 2 u v TYPE S i s p v s p u VALUE P S p v S p u
T{ check-last -> outcome-rejected lf-diag-value-apart compare-step }T
fc-case T2
fc-decl check def safe T2 2 u v TYPE S i s p u s p v VALUE P S p u S p v
T{ check-last -> outcome-ok 0 lf-step-done }T
fc-case T3
fc-decl check def safe T3 2 u v TYPE S m s p v s p u VALUE P S p v S p u
T{ check-last -> outcome-ok 0 lf-step-done }T
fc-case T4
fc-decl check def safe T4 1 u TYPE S i s z s p u VALUE P S z S p u
T{ check-last -> outcome-rejected lf-diag-value-apart compare-step }T
fc-case th
fc-decl check thm safe th 1 u TYPE P S z P V 0 V 1 VALUE L S z L V 0 A L S i s z s p u V 1 P S z S p u
T{ check-last -> outcome-rejected lf-diag-argument-apart value-step }T
fc-case d
fc-decl before def safe T 2 u v TYPE S s i p u p v VALUE S i p u p v
fc-decl check def safe d 1 w TYPE S s i s z s p w VALUE C T 2 s z s p w
T{ check-last -> outcome-rejected lf-diag-value-apart compare-step }T
\ S4 (ADR 0011, Amendment 2): a Pi whose body is not a type, in the value
\ and in the claim (Lean: typeExpected). Behind a constant it was unknown
\ (K1) until plan task 4.2.2c: since then the body's type is put in whnf,
\ unfolding the definition, as Lean's ensure_sort_core does (rows
\ pi-body.needs-unfolding and -wrong of the first checker's table).
fc-case s4-value
fc-decl check def safe piBodyVariable 0 TYPE S s s z VALUE P S s z P V 0 V 0
T{ check-last -> outcome-rejected lf-diag-body-type value-step }T
fc-case s4-claim
fc-decl check thm safe piBodyClaim 0 TYPE P S z P V 0 V 0 VALUE L S z L V 0 V 0
T{ check-last -> outcome-rejected lf-diag-body-type type-step }T
fc-case s4-unfolding
fc-decl before def safe S1 0 TYPE S s s z VALUE S s z
fc-decl check def safe piBodyUnfold 0 TYPE S s s z VALUE P C S1 0 V 0
T{ check-last -> outcome-ok 0 lf-step-done }T
fc-case s4-unfolding-wrong
fc-decl before def safe F1 0 TYPE S s z VALUE P S z S z
fc-decl check def safe piBodyUnfoldWrong 0 TYPE S s s z VALUE P C F1 0 V 0
T{ check-last -> outcome-rejected lf-diag-body-type value-step }T
\ The zero inside a max that LeanForth used to drop at any depth, and
\ Lean's normalize does not drop here.
fc-case zero-rewrite
fc-decl check def safe X 1 u TYPE S s m z i s z s p u VALUE S i s z s p u
T{ check-last -> outcome-rejected lf-diag-value-apart compare-step }T
fc-case k6
fc-decl before def safe T5 1 u TYPE S s i s z s p u VALUE S i s z s p u
fc-decl check def safe S5 1 u TYPE S s i s z s p u VALUE C T5 1 p u
T{ check-last -> outcome-unknown lf-diag-shared-level value-step }T

\ ---------------------------------------------------------------------------
\ Axioms and opaque declarations (plan tasks 5.3.1, 4.2.6): an axiom's
\ type is checked as a definition's (here N1 rejects it), and its own bit
\ joins its axiom set at step 7; an opaque declaration is checked as a
\ definition; a use of an axiom is accepted, its set the axiom's.
fc-case axiom
fc-decl check ax safe postulate 0 TYPE C missing 0 VALUE none
T{ check-last -> outcome-rejected lf-diag-unknown-constant type-step }T
fc-case opaque
fc-decl check opq safe hidden 0 TYPE S s z VALUE S z
T{ check-last -> outcome-ok 0 lf-step-done }T
fc-case opaque-wrong
fc-decl check opq safe hiddenWrong 0 TYPE S z VALUE S z
T{ check-last -> outcome-rejected lf-diag-value-apart compare-step }T
fc-case uses-axiom
fc-decl before ax safe postulate 0 TYPE S z VALUE none
fc-decl check def safe user 0 TYPE S z VALUE C postulate 0
T{ check-last -> outcome-ok 0 lf-step-done }T
\ Skipped (plan task 5.2.7). U1: an unsafe or partial definition, an
\ unsafe axiom or opaque declaration is skipped as Lean's replay skips it
\ (Replay.lean 180-183), nothing of it checked, so an ill-typed or
\ self-referring one too: rejected at the audit, its slot marked skipped;
\ a safe declaration that uses one meets no constant (N1), and one of a
\ skipped one's name is refused (N2), as lean4export's parser refuses a
\ name given twice, which also rejects a skipped one after another of its
\ name, before anything else; an unsafe use of a skipped one is skipped.
: last-skipped? ( -- flag ) lf-env-view ok? must fc-last lf-env-skipped? ;
: check-skip ( -- outcome code step skipped? )
  check-run last-result last-skipped? env-done ;
fc-case unsafe
fc-decl check def unsafe risky 0 TYPE S s z VALUE S z
T{ check-skip -> outcome-rejected lf-diag-skipped audit true }T
fc-case partial
fc-decl check def partial looping 0 TYPE S s z VALUE S z
T{ check-skip -> outcome-rejected lf-diag-skipped audit true }T
fc-case unsafe-ill-typed
fc-decl check def unsafe wrong 0 TYPE S z VALUE S z
T{ check-skip -> outcome-rejected lf-diag-skipped audit true }T
fc-case unsafe-recursive
fc-decl check def unsafe spin 0 TYPE S z VALUE C spin 0
T{ check-skip -> outcome-rejected lf-diag-skipped audit true }T
fc-case unsafe-axiom
fc-decl check ax unsafe postulate 0 TYPE S z VALUE none
T{ check-skip -> outcome-rejected lf-diag-skipped audit true }T
fc-case unsafe-opaque
fc-decl check opq unsafe hidden 0 TYPE S s z VALUE S z
T{ check-skip -> outcome-rejected lf-diag-skipped audit true }T
fc-case safe-uses-unsafe
fc-decl before def unsafe risky 0 TYPE S s z VALUE S z
fc-decl check def safe user 0 TYPE S s z VALUE C risky 0
T{ check-skip -> outcome-rejected lf-diag-unknown-constant value-step false }T
fc-case safe-uses-partial
fc-decl before def partial looping 0 TYPE S s z VALUE S z
fc-decl check thm safe user 0 TYPE C looping 0 VALUE S z
T{ check-skip -> outcome-rejected lf-diag-unknown-constant type-step false }T
fc-case unsafe-uses-unsafe
fc-decl before def unsafe risky 0 TYPE S s z VALUE S z
fc-decl check def unsafe user 0 TYPE S s z VALUE C risky 0
T{ check-skip -> outcome-rejected lf-diag-skipped audit true }T
fc-case safe-after-skipped
fc-decl before ax unsafe twice 0 TYPE S z VALUE none
fc-decl check def safe twice 0 TYPE S s z VALUE S z
T{ check-skip -> outcome-rejected lf-diag-already-declared name-step false }T
fc-case skipped-after-safe
fc-decl before def safe twice 0 TYPE S s z VALUE S z
fc-decl check def unsafe twice 0 TYPE S s z VALUE S z
T{ check-skip -> outcome-rejected lf-diag-already-declared audit false }T
fc-case skipped-after-rejected
fc-decl before def safe twice 0 TYPE S z VALUE S z
fc-decl check def partial twice 0 TYPE S s z VALUE S z
T{ check-skip -> outcome-rejected lf-diag-already-declared audit false }T
fc-case let
fc-decl check def safe withLet 0 TYPE S s z VALUE Xlet
T{ check-last -> outcome-unsupported lf-diag-unsupported-form audit }T
\ A let term (plan task 4.2.3): let x : Sort 1 := Sort 0; x has type Sort 1;
\ a value of the wrong type is Lean's letTypeMismatch.
fc-case let-term
fc-decl check def safe withLetTerm 0 TYPE S s z VALUE E 0 S s z S z V 0
T{ check-last -> outcome-ok 0 lf-step-done }T
fc-case let-term-wrong
fc-decl check def safe withLetWrong 0 TYPE S s z VALUE E 1 S z S z V 0
T{ check-last -> outcome-rejected lf-diag-let-value-apart value-step }T
\ Under A : Prop and h : A: let y : h := h; h has no type for y (Lean's
\ typeExpected, S2's code); fun A => let T : Prop := A; fun y : T => y
\ proves A -> A (its type, a let term, mentions T); let T : Prop := A;
\ let y : T := h; y proves A (h's type A against the let variable T).
fc-case let-type-not-a-type
fc-decl check thm safe withLetProof 0 TYPE P S z P V 0 V 1 VALUE L S z L V 0 E 0 V 0 V 0 V 1
T{ check-last -> outcome-rejected lf-diag-domain-type value-step }T
fc-case let-dependent-body
fc-decl check thm safe withLetBody 0 TYPE P S z P V 0 V 1 VALUE L S z E 0 S z V 0 L V 0 V 0
T{ check-last -> outcome-ok 0 lf-step-done }T
fc-case let-chain
fc-decl check thm safe withLetChain 0 TYPE P S z P V 0 V 1 VALUE L S z L V 0 E 0 S z V 1 E 0 V 0 V 1 V 0
T{ check-last -> outcome-ok 0 lf-step-done }T
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
\ Defence in depth (compact-store plan step S6 (c)): with the entry
\ audit's U2 and V1 skipped (U1 alone as step 1), nothing malformed is
\ accepted: inference meets the loose variable (invalid, out of scope)
\ and the concrete Sort (a tag it does not know: unknown), as would the
\ audits every conversion and rebuilding pass still runs on its roots,
\ once per node per check.
' lf-check-u1 lf-check-steps cell+ !
fc-case loose-unaudited
fc-decl check thm safe loose 0 TYPE P S z P V 0 V 1 VALUE L S z L V 0 V 2
T{ check-last nip -> outcome-invalid value-step }T
fc-case concrete-unaudited
fc-read-term S s z constant concrete-type2
0 lf-term-sort must constant concrete-value2
: concrete-decl2 ( -- )
  fc-buf /lf-idecl erase lf-kind-definition fc-buf lf-idecl-kind !
  s" concrete" fc-intern fc-buf lf-idecl-name ! lf-hint-regular fc-buf lf-idecl-hint !
  concrete-type2 fc-buf lf-idecl-type ! concrete-value2 fc-buf lf-idecl-value !
  fc-buf lf-input-add ok? must drop ;
concrete-decl2
T{ check-last nip -> outcome-unknown value-step }T
' lf-check-audit lf-check-steps cell+ !

\ ---------------------------------------------------------------------------
\ Exhausted: too little fuel for the audit; a 17th dependency, which used
\ to be full (16 per check until plan task 6.2.0) and is accepted; and
\ full: a term store that fills while the declared type is inferred.
fc-case exhausted
fc-decl check thm safe idProp 0 TYPE P S z P V 0 V 1 VALUE L S z L V 0 V 0
T{ 3 lf-check-budget check-last -> outcome-exhausted lf-diag-fuel audit }T
fc-fuel lf-check-budget
fc-case deps-17
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
T{ check-last -> outcome-ok 0 lf-step-done }T
\ The declared type is a telescope of 40 binders (Prop -> ... -> Prop):
\ its 41 nodes and a free variable per binder (plan task 4.2.2a) do not
\ fit the 64 terms. (The binder-domain table's eta case, used here
\ before, now fits: inference discards its scratch as it goes.)
fc-case terms-full
fc-decl check def safe wide 0 TYPE P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z P S z S z VALUE S z
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
\ A rejection records the dependencies its check met. bad : (fun _ : Prop
\ => Prop) D := f, with f : B -> B and D = c0 -> ... -> c14 (each : Prop :=
\ forall p, p), meets D's 15 constants and f (16; once the most a check
\ could hold). Lean's kernel rejects it (declTypeMismatch). A Pi is never
\ typed by P2 (it cannot be a proof), so B stays unmet; see aside-deps-app
\ for inference run aside.
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
\ The dependencies have no room limit of their own now (they grow in the
\ heap), so a rejection no longer shows an extra dependency by itself: the
\ candidate's dependency count when the last check ends does.
variable last-dep-count
: counting-check ( ... ) lf-check-declaration lf-cand-count@ last-dep-count ! ;
: check-counting ( -- outcome code step count )
  lf-input-end ok? must 64 lf-env-new ok? must dup the-env ! lf-env-use ok? must
  ['] counting-check ['] fc-no-maker lf-env-run ok? must
  last-result last-dep-count @ env-done ;
T{ check-counting -> outcome-rejected lf-diag-value-apart compare-step 16 }T
\ Where P2 meets a constant by the type of an application (a Pi or a Sort
\ is not typed: it cannot be a proof): bad : Prop := G u, G : Prop -> Prop,
\ u : K B an axiom, K : Prop -> Prop, B : Prop. Lean rejects it (the
\ argument's type K B is not Prop; appTypeMismatch). P2 infers K B aside
\ and meets K, which is no dependency of bad: G and u only.
fc-case aside-deps-app
fc-decl before def safe B 0 TYPE S z VALUE P S z V 0
fc-decl before def safe K 0 TYPE P S z S z VALUE L S z V 0
fc-decl before ax safe u 0 TYPE A C K 0 C B 0 VALUE none
fc-decl before def safe G 0 TYPE P S z S z VALUE L S z V 0
fc-decl check def safe bad 0 TYPE S z VALUE A C G 0 C u 0
T{ check-counting -> outcome-rejected lf-diag-argument-apart value-step 2 }T

\ The input is unchanged by every check: its fingerprint, computed again,
\ is the one recorded when loading ended.
fc-case input-unchanged
fc-decl before def safe fixtureId 1 u TYPE P S p u P V 0 V 1 VALUE L S p u L V 0 V 0
fc-decl check thm safe wrong 0 TYPE P S z P S z P V 1 V 2 VALUE L S z L S z L V 0 V 0
: unchanged ( -- flag ) check-run env-done lf-input-print lf-input-fingerprint = ;
T{ unchanged -> true }T

\ Step 7 gives back the room of steps 4-6: composition's declared type
\ took 11 scratch terms there before plan task 4.2.2a, and leaves 1 since
\ (a Pi's inference discards its scratch). After an earlier axiom
\ (unsupported, so never typed) of 27 terms, the 64-term store holds the
\ value's inference only once that term is given back; kept, step 7 is
\ full (measured 2026-11-04: 26 Pis in the axiom fit only with the
\ rollback, 27 not at all). Lean's kernel accepts both declarations.
fc-case value-room
fc-decl before ax safe pad 0 TYPE P S s s z P S s s z P S s s z P S s s z P S s s z P S s s z P S s s z P S s s z P S s s z P S s s z P S s s z P S s s z P S s s z P S s s z P S s s z P S s s z P S s s z P S s s z P S s s z P S s s z P S s s z P S s s z P S s s z P S s s z P S s s z P S s s z S s s z VALUE none
fc-decl check thm safe composition 0 TYPE P S z P S z P S z P P V 2 V 2 P P V 2 V 2 P V 4 V 3 VALUE L S z L S z L S z L P V 2 V 2 L P V 2 V 2 L V 4 A V 1 A V 2 V 0
T{ check-last -> outcome-ok 0 lf-step-done }T

\ ---------------------------------------------------------------------------
\ Fuel sweeps: for every fuel from 0 to limit, a check of the case's last
\ declaration ends exhausted below some fuel and with its final outcome
\ (the one at limit) from some fuel on; it is never accepted earlier, and
\ never unknown for want of fuel: a rejection's analysis that runs out of
\ fuel is exhausted (ADR 0008; since plan task 4.2.2c, unknown before). A
\ check is unknown early only when an earlier declaration ran out of fuel
\ (the same budget each): its dependency is undecided (K5, code 35).
variable sweep-final
variable first-final
variable sweep-ok
variable sweep-code
variable sweep-final-code
: sweep-run ( fuel -- outcome )
  lf-check-budget 64 lf-env-new ok? must dup the-env ! lf-env-use ok? must
  ['] lf-check-declaration ['] fc-no-maker lf-env-run ok? must lf-diag-code@ sweep-code !
  lf-env-view ok? must fc-last lf-env-outcome env-done ;
: sweep-first ( fuel -- ) first-final @ 0< if first-final ! else drop then ;
: sweep-early? ( outcome -- flag )
  dup outcome-exhausted = swap outcome-unknown =
  sweep-code @ lf-diag-dependency-undecided = and or ;
\ The final outcome, with the final diagnostic.
: sweep-final? ( outcome -- flag )
  sweep-final @ = sweep-code @ sweep-final-code @ = and ;
: sweep-note ( fuel outcome -- )
  dup sweep-final? if drop sweep-first exit then nip
  sweep-early? first-final @ 0< and 0= if false sweep-ok ! then ;
: sweep ( limit -- final first ok? )
  lf-input-end ok? must dup sweep-run sweep-final ! sweep-code @ sweep-final-code !
  -1 first-final ! true sweep-ok !
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
\ CLI2's case (tests/cli/unfold.lean): Implies A A against A → A needs
\ Implies unfolded by lazy delta reduction: accepted, as Lean does, from
\ 60, the fuel the whole check takes since an application's argument is
\ not closed to be put into a Pi body without loose bound variables
\ (agent PF: Lean's instantiate never reads it); 62 since == is Lean's
\ at every pair
\ (plan step S4: one node is equal and differing data words apart, at
\ no cost); 67 since the audits check each node
\ once per check and read V1 and U2 from data words (plan step S6 (c);
\ 114 since agent EX's audits check each shared node once per audit,
\ 131 since plan task 4.2.7, Lean's caches and cached
\ node data; 138 since plan task 4.2.2d), and at every
\ fuel below exhausted (or unknown for Implies itself out of fuel). Before,
\ it was unknown: K1, then the interim guard of review rvU4 B1 (diagnostic
\ 64); and at every fuel from 151 to 280 unknown, code 30, before 4.2.2c,
\ when ADR 0011's analysis ran out of fuel and left the step unknown.
fc-case sweep-unfolding
fc-decl before def safe Implies 0 TYPE P S z P S z S z VALUE L S z L S z P V 1 V 1
fc-decl check thm safe impliesSelf 0 TYPE P S z A A C Implies 0 V 0 V 0 VALUE L S z L V 0 V 0
T{ 400 sweep -> outcome-ok 60 true }T
\ In a check, with the caches on, lf-term-data@ (core/terms.fs) is the
\ skeleton memo's facts as one data word (compact-store plan step S2),
\ its depth aside: every node inference visits (its lf-minfer-entry hook,
\ spied on here; whnf.fs reads the words itself since plan task 6.5.5) is
\ compared, in the check above run once more.
variable cd-asked  variable cd-known  variable cd-wrong
: cd-pack ( x true | false -- x | -1 ) 0= if -1 then ;
: cd-bits ( data true | false -- x | -1 ) if lf-data-ranges 4 * 1- and else -1 then ;
: cd-facts ( node -- data | -1 ) lf-term-facts if nip lf-cd-word cd-pack else -1 then ;
: cd-note ( node -- )
  1 cd-asked +!  dup lf-term-data@ cd-bits  dup 0< 0= 1 and cd-known +!
  swap cd-facts <> 1 and cd-wrong +! ;
: cd-spy ( node frames -- ... frames next ) over cd-note lf-ci-visit ;
' cd-spy is lf-minfer-entry
T{ 400 sweep-run -> outcome-ok }T
' lf-ci-visit is lf-minfer-entry
T{ cd-asked @ 0> cd-known @ 0> cd-wrong @ -> true true 0 }T

\ ---------------------------------------------------------------------------
\ Lean's cached node data as one data word (compact-store plan step S2):
\ the skeleton memo's bits also keep whether a universe parameter occurs
\ (has_param_univ: in a Sort's level, a constant's universe arguments or
\ either child), and lf-term-data@ gives the loose range and the two bits
\ as ADR 0016 C1's data word while the caches are on.
lf-caches-clear
lf-term-reset
T{ lf-ssession-begin -> true }T
7 lf-level-param must constant cu
T{ cu csort cbits  cu csort 0 cb capp cbits
   cz cu lf-level-max must csort 1 cb lf-term-lam must cbits  cz lf-level-succ must csort cbits
   -> 2 6 6 0 }T
create cpairs 2 cells allot
: cconst ( level -- term )
  dup lf-level-identity must cpairs cell+ ! cpairs !
  0 s" cc" lf-name-str must lf-name-generation @ cpairs 1 lf-cref-new must
  lf-cterm-new must drop ;
T{ cu cconst cbits  cz cconst cbits  cu cconst 2 cb capp cbits -> 2 0 14 }T
T{ 6 lf-cd-word -> 1 true false lf-data true }T
T{ 7 lf-cd-word drop dup lf-data-loose over lf-data-params? rot lf-data-fvar?
   -> 1 true true }T
T{ lf-data-ranges 1- 2 lshift lf-cd-word -> lf-data-ranges 1- false false lf-data true }T
T{ lf-data-ranges 2 lshift lf-cd-word -> false }T
\ Since step S3 every record keeps its data word, caches on or off.
T{ false lf-caches-enable  cu csort lf-term-data@  true lf-caches-enable
   -> 0 true false lf-data true }T
\ The term store hash-conses (step S3), but never a free variable: one
\ made after the local context was emptied is a new node, and the dead
\ one does not come back as its variable.
cz csort constant ctype
lf-lctx-reset
T{ ctype lf-lctx-local nip  lf-lctx-count @ -> outcome-ok 1 }T
lf-term-count @ 1- constant cdead
lf-lctx-reset
T{ ctype lf-lctx-local swap cdead <> cdead lf-fvar-live? -> outcome-ok true false }T

\ ---------------------------------------------------------------------------
\ A broken store seal never publishes ok (review rvS12 L3). idProp, accepted
\ above, is checked with the term store's or the level store's seal broken
\ (store-faults.fs): at the root, before the check begins (lf-input-intact?,
\ read by lf-env-checking and lf-input-read; diagnostic 0, step done), and in
\ the middle, as step 8's comparison of two skeletons returns (diagnostic 27,
\ step 8). Each ends invalid, with the seal mended before the next row.
\ Several layers refuse each break (the store roots of every pass, the
\ hand-over), so disabling lf-input-intact? or lf-env-still? alone changes no
\ row (faults.toml: fx9-*, listed as equivalent); the rows pin the end result.
require ../support/store-faults.fs
variable seal-armed  \ 0 none, 1 the term seal, 2 the level seal
: seal-flip-armed ( -- )
  seal-armed @ 1 = if term-seal-flip then seal-armed @ 2 = if level-seal-flip then
  0 seal-armed ! ;
: seal-spy ( t s -- flag ) lf-cs-same? seal-flip-armed ;
: seal-hook ( -- ) ['] seal-spy is lf-dq-known-same? ;
: seal-unhook ( -- ) ['] lf-cs-same? is lf-dq-known-same? ;
: seals-mend ( -- )
  lf-terms store-sealed? 0= if term-seal-flip then
  lf-levels store-sealed? 0= if level-seal-flip then ;
: idprop-case ( -- ) fc-world
  s" check thm safe idProp 0 TYPE P S z P V 0 V 1 VALUE L S z L V 0 V 0"
  ['] fc-decl execute-parsing ;
\ kind: 0 term seal at the root, 1 level seal at the root, 2 term seal after
\ step 8, 3 level seal after step 8, 4 none (the control).
: check-with-seal ( kind -- outcome )
  idprop-case lf-input-end ok? must 64 lf-env-new ok? must dup the-env ! lf-env-use ok? must
  dup 0 = if term-seal-flip then dup 1 = if level-seal-flip then
  dup 2 = if 1 seal-armed ! then dup 3 = if 2 seal-armed ! then drop
  seal-hook ['] lf-check-declaration ['] fc-no-maker lf-env-run drop seal-unhook
  seals-mend 0 seal-armed !
  lf-env-view ok? if fc-last lf-env-outcome else -99 then env-done ;
fc-case seals
T{ 0 check-with-seal -> outcome-invalid }T
T{ 1 check-with-seal -> outcome-invalid }T
T{ 2 check-with-seal -> outcome-invalid }T
T{ 3 check-with-seal -> outcome-invalid }T
T{ 4 check-with-seal -> outcome-ok }T

\ ---------------------------------------------------------------------------
\ A check's memory limit (core/scratch-meter.fs; check --memory-per-check).
\ The bytes each record counts bound what it takes: its record, identity,
\ side columns and two 32-bit table slots.
: unit+ ( n column -- n' ) column-slab slab-unit + ;
: group-bytes ( group -- n ) 0 ['] unit+ rot columns-each ;
: record-bytes ( store group -- n ) group-bytes swap store-width @ + cell+ 8 + ;
T{ lf-terms lf-term-columns record-bytes lf-meter-term-bytes > -> false }T
T{ lf-levels lf-level-columns record-bytes lf-meter-level-bytes > -> false }T
T{ lf-crefs store-width @ cell+ 8 + lf-meter-cref-bytes > -> false }T
T{ lf-cref-pool slab-unit lf-meter-arg-bytes > -> false }T
T{ /lf-cent 8 + lf-meter-entry-bytes > -> false }T
T{ lf-lctx store-width @ cell+ lf-meter-local-bytes > -> false }T
\ The meter on a reading the test sets: no limit refuses nothing; with
\ one, a charge that fits is allowed, one that passes is refused, and so
\ is every later one of the same check, until it stops.
variable fake-bytes
: fake-used ( -- u ) fake-bytes @ ;
' fake-used is lf-meter-used
0 lf-meter-limit! lf-meter-start
T{ lf-meter-term? lf-meter-level? 3 lf-meter-cref? lf-meter-entry?
   -> true true true true }T
1000 lf-meter-limit! 900 fake-bytes ! lf-meter-start
T{ lf-meter-term? lf-meter-term? lf-meter-passed? -> true true false }T
950 fake-bytes !
T{ lf-meter-term? lf-meter-passed? lf-meter-asked@
   -> false true lf-meter-term-bytes 950 + }T
0 fake-bytes !
T{ lf-meter-entry? -> false }T
lf-meter-stop
T{ lf-meter-term? lf-meter-passed? -> true false }T
' lf-check-scratch is lf-meter-used
0 lf-meter-limit!
\ Checks under a limit of bytes, from step to most in steps: each ends full
\ with the memory limit's diagnostic below some limit and is accepted from
\ there on, never earlier; with no limit (0) it is accepted. Composition
\ (Lean accepts it) needed 1,664 bytes on a 64-bit host (2026-11-11).
variable mem-code  variable mem-first  variable mem-ok
: mem-run ( bytes -- outcome )
  lf-meter-limit! 64 lf-env-new ok? must dup the-env ! lf-env-use ok? must
  ['] lf-check-declaration ['] fc-no-maker lf-env-run ok? must lf-diag-code@ mem-code !
  lf-env-view ok? must fc-last lf-env-outcome env-done 0 lf-meter-limit! ;
: mem-full? ( outcome -- flag ) outcome-full = mem-code @ lf-diag-memory-limit = and ;
: mem-note ( bytes outcome -- )
  dup ok? if drop mem-first @ 0< if mem-first ! else drop then exit then
  mem-full? mem-first @ 0< and 0= if false mem-ok ! then drop ;
: mem-sweep ( most step -- first ok? )
  -1 mem-first ! true mem-ok !
  >r r@ begin 2dup > while dup dup mem-run mem-note r@ + repeat 2drop r> drop
  mem-first @ mem-ok @ ;
fc-case memory-composition
fc-decl check thm safe composition 0 TYPE P S z P S z P S z P P V 2 V 2 P P V 2 V 2 P V 4 V 3 VALUE L S z L S z L S z L P V 2 V 2 L P V 2 V 2 L V 4 A V 1 A V 2 V 0
lf-input-end ok? must
T{ 0 mem-run -> outcome-ok }T
T{ 20000 16 mem-sweep swap 16 > -> true true }T

cases-done
bye
