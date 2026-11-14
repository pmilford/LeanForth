\ Lean's generated recursor rebuilt for a later declaration
\ (src/kernel/generated-recursor.fs; plan task 5.2.1a; ADR 0015 decision
\ 12): files that leave T.rec out of an inductive block and then use it
\ (tests/core/check-block-cases/after.*-left-out-then-use-rec, each the
\ export pinned Lean printed, whose last declaration is T.useRec :=
\ @T.rec at the block's own universe parameters). Asked as inference asks
\ (env-signature.fs's lf-env-signature, which builds it through lf-genrec)
\ inside the check of T.useRec. Coverage classes of
\ docs/development/TEST_COVERAGE_REVIEW.md:
\ 1, 7. The type built is the recursor's type the declaration states
\    (Lean's T.rec), for a type without universe parameters (Nat), with
\    one (List, Eq: their instances substituted), the second type of a
\    mutual block (Even/Odd: another type's telescope), an indexed family.
\ 3. lf-genrec ( d pairs fuel -- fuel' outcome ) on the type's slot: ok
\    and its root; exhausted with no fuel; the universe parameters a use
\    must supply (lf-genrec-arity), the motive's first when it is large.
\ 5. Every fuel below the least exhausts the build, the least gives the
\    type; each allocation refused in turn makes it full.
\ Test-only; nothing here accepts a theorem.
require ../support/case-sweeps.fs

\ T.useRec's value @T.rec.{us}, under the lambdas of an eta-expanded one
\ (fun α p => @T.rec.{us} α p): its name, universe arguments and number.
: unlam ( node -- node' )
  begin dup lf-term-tag@ lf-tag-lam = while lf-term-second@ repeat ;
: the-value ( -- const ) cs cs-target @ cs-value-of unlam lf-whnf-head ;
: request ( const -- name pairs count ) lf-const-slot dup lf-crec-name @ swap lf-cref-pairs ;
: answer ( root identity fuel' 0 | status -- root|-1 outcome )
  dup ok? if drop drop drop outcome-ok else -1 swap then ;
: signature ( const fuel -- root|-1 outcome )
  dup lf-minfer-start-env >r request r> true lf-env-signature answer ;
\ The type the declaration states, and whether the built one equals it.
: stated ( -- node ) cs cs-target @ cs-type-of ;
: as-stated? ( root -- flag ) stated 100000 lf-expr-equal ok? and ;
\ The type's slot: T.rec's lookup gives Lean's generated recursor (-1),
\ whose block's type lf-env-genrec-of names.
: type-slot ( -- d ) the-value request 2drop lf-env-lookup ok? cs-must drop lf-env-genrec-of ;
: built ( fuel -- fuel' outcome )
  dup lf-minfer-start-env >r type-slot the-value request drop nip r> lf-genrec ;
\ The build, then the sweeps: the type as stated, ok with plenty, then
\ exhausted without fuel; the sweeps over the whole answer.
: rebuilt ( -- )
  T{ the-value cs-plenty signature swap as-stated? -> outcome-ok true }T
  T{ cs-plenty built nip lf-genrec-root as-stated? -> outcome-ok true }T
  T{ 0 built -> 0 outcome-exhausted }T
  T{ the-value ['] signature cs-pass-sweep -> true }T
  T{ the-value ['] signature cs-pass-refusals -> true }T ;
: rebuilds ( c-addr u -- ) ['] rebuilt outcome-ok cs-probe-gives ;
s" after.nat-left-out-then-use-rec" rebuilds
s" after.list-left-out-then-use-rec" rebuilds
s" after.eq-left-out-then-use-rec" rebuilds
s" after.even-odd-left-out-then-use-second-rec" rebuilds
s" after.index-left-out-then-use-rec" rebuilds
\ At other universe arguments than the block's own names (review rvI21
\ R5-1): renamed, concrete; the declaration states the type instantiated.
s" after.list-at-renamed" rebuilds
s" after.list-at-concrete" rebuilds
s" after.eq-at-applied" rebuilds

\ 3. The universe parameters a use supplies: Nat.rec.{u} 1 (its motive's,
\ Nat has none), List.rec.{u_1, u} 2, a Prop-only eliminator (Or) its
\ block's only.
: arity ( -- ) type-slot lf-genrec-arity cs-note the-value request nip nip cs-note ;
: arity-of ( c-addr u -- n count outcome errors )
  ['] arity cs-probed 0 cs-noted 1 cs-noted 2swap ;
T{ s" after.nat-left-out-then-use-rec" arity-of -> 1 1 outcome-ok 0 }T
T{ s" after.list-left-out-then-use-rec" arity-of -> 2 2 outcome-ok 0 }T
T{ s" after.or-left-out-then-use-rec" arity-of -> 0 0 outcome-ok 0 }T
bye
