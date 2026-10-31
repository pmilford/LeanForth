\ Tests for the untrusted inference experiment. Inferred indices are not
\ theorem handles; these cases do not establish soundness or Lean parity.
include ../support/tester.fs
include ../../src/experimental/infer.fs

\ Read an inferred concrete sort level, retaining a distinct failure status.
: inferred-sort ( root fuel -- level status )
  lf-infer dup if exit then drop
  lf-term-read 0= if -1 lf-infer-invalid exit then
  drop swap lf-tag-sort <> if drop -1 lf-infer-unknown exit then
  lf-infer-ok ;

\ Sort 0 is classified by Sort 1; unsupported roots and small budgets fail.
lf-term-reset
T{ 0 lf-term-sort -> 0 true }T
T{ 0 100 inferred-sort -> 1 lf-infer-ok }T
T{ 0 0 lf-infer -> -1 lf-infer-exhausted }T
T{ -1 100 lf-infer -> -1 lf-infer-invalid }T
T{ 0 -1 lf-infer -> -1 lf-infer-invalid }T

\ An unbound variable cannot be assigned a type in an empty context.
lf-term-reset
T{ 0 lf-term-bvar -> 0 true }T
T{ 0 100 lf-infer -> -1 lf-infer-invalid }T
T{ lf-term-count @ -> 1 }T

\ Prop quantification is impredicative: (P : Prop) -> P has sort zero.
lf-term-reset
T{ 0 lf-term-sort -> 0 true }T
T{ 0 lf-term-bvar -> 1 true }T
T{ 0 1 lf-term-pi -> 2 true }T
T{ 2 1000 inferred-sort -> 0 lf-infer-ok }T

\ Quantification over Type 0 into Type 0 is classified in Sort 2.
lf-term-reset
T{ 1 lf-term-sort -> 0 true }T
T{ 0 lf-term-bvar -> 1 true }T
T{ 0 1 lf-term-pi -> 2 true }T
T{ 2 1000 inferred-sort -> 2 lf-infer-ok }T

\ Construct identity over propositions and inspect its inferred Pi structure.
lf-term-reset
T{ 0 lf-term-sort -> 0 true }T
T{ 0 lf-term-bvar -> 1 true }T
T{ 1 1 lf-term-lam -> 2 true }T
T{ 0 2 lf-term-lam -> 3 true }T
T{ 3 2000 lf-infer -> 7 lf-infer-ok }T
T{ 5 lf-term-read -> lf-tag-bvar 1 0 true }T
T{ 6 lf-term-read -> lf-tag-pi 1 5 true }T
T{ 7 lf-term-read -> lf-tag-pi 0 6 true }T

\ Repeated successful checks allocate additional nodes. Earlier result indices
\ must remain readable until reset; exhaustion must restore the prior count and
\ must not corrupt either the original term or a previously returned type.
variable first-inferred-type
variable last-infer-count
variable successful-inferences
lf-term-reset
T{ 0 lf-term-sort -> 0 true }T
T{ 0 lf-term-bvar -> 1 true }T
T{ 1 1 lf-term-lam -> 2 true }T
T{ 0 2 lf-term-lam -> 3 true }T
T{ 3 2000 lf-infer -> 7 lf-infer-ok }T
7 first-inferred-type !
1 successful-inferences !
: exhaust-repeated-inference ( -- )
  lf-term-capacity 0 do
    lf-term-count @ last-infer-count !
    3 2000 lf-infer
    dup lf-infer-ok = if
      2drop 1 successful-inferences +!
      lf-term-count @ last-infer-count @ <= if -1 throw then
    else
      lf-infer-exhausted <> if -1 throw then
      -1 <> if -1 throw then
      lf-term-count @ last-infer-count @ <> if -1 throw then
      unloop exit
    then
  loop
  -1 throw ;
exhaust-repeated-inference
T{ successful-inferences @ 1 > -> true }T
T{ 3 lf-term-read -> lf-tag-lam 0 2 true }T
T{ first-inferred-type @ lf-term-read -> lf-tag-pi 0 6 true }T
T{ 6 lf-term-read -> lf-tag-pi 1 5 true }T
T{ 5 lf-term-read -> lf-tag-bvar 1 0 true }T
T{ 3 2000 lf-infer -> -1 lf-infer-exhausted }T
T{ lf-term-count @ last-infer-count @ = -> true }T

\ Every insufficient visit budget must fail closed and leave the input arena
\ intact. Successful experimental results are discarded before the next case.
lf-term-reset
T{ 0 lf-term-sort -> 0 true }T
T{ 0 lf-term-bvar -> 1 true }T
T{ 1 1 lf-term-lam -> 2 true }T
T{ 0 2 lf-term-lam -> 3 true }T
: check-inference-budgets ( -- )
  200 0 do
    3 i lf-infer
    dup if
      lf-infer-exhausted <> if -1 throw then drop
      lf-term-count @ 4 <> if -1 throw then
    else
      2drop 4 lf-term-count !
    then
  loop ;
check-inference-budgets
T{ lf-term-count @ -> 4 }T
T{ 0 lf-term-read -> lf-tag-sort 0 0 true }T
T{ 3 lf-term-read -> lf-tag-lam 0 2 true }T

\ Applying a sort cannot produce a Pi function type. The prototype reports
\ unknown; it does not claim Lean acceptance or theorem rejection.
lf-term-reset
T{ 0 lf-term-sort -> 0 true }T
T{ 0 0 lf-term-app -> 1 true }T
T{ 1 1000 lf-infer -> -1 lf-infer-unknown }T
T{ lf-term-count @ -> 2 }T

\ Even when the function is not callable, an unbound argument is malformed;
\ full scope checking must not stop at the function before seeing it.
lf-term-reset
T{ 0 lf-term-sort -> 0 true }T
T{ 0 lf-term-bvar -> 1 true }T
T{ 0 1 lf-term-app -> 2 true }T
T{ 2 1000 lf-infer -> -1 lf-infer-invalid }T
T{ lf-term-count @ -> 3 }T

\ A known mismatched argument must not be upgraded to successful inference.
lf-term-reset
T{ 0 lf-term-sort -> 0 true }T
T{ 0 lf-term-bvar -> 1 true }T
T{ 0 1 lf-term-lam -> 2 true }T
T{ 2 0 lf-term-app -> 3 true }T
T{ 3 2000 lf-infer -> -1 lf-infer-unknown }T
T{ lf-term-count @ -> 4 }T

\ A function value is not a type annotation; reject its use before traversing
\ the invalid body context, conservatively reporting unknown.
lf-term-reset
T{ 0 lf-term-sort -> 0 true }T
T{ 0 lf-term-bvar -> 1 true }T
T{ 0 1 lf-term-lam -> 2 true }T
T{ 0 lf-term-bvar -> 3 true }T
T{ 2 3 lf-term-pi -> 4 true }T
T{ 4 2000 lf-infer -> -1 lf-infer-unknown }T
T{ lf-term-count @ -> 5 }T

\ A valid beta application has an inferred sort matching its argument's type.
lf-term-reset
T{ 0 lf-term-sort -> 0 true }T
T{ 1 lf-term-sort -> 1 true }T
T{ 0 lf-term-bvar -> 2 true }T
T{ 1 2 lf-term-lam -> 3 true }T
T{ 3 0 lf-term-app -> 4 true }T
T{ 4 2000 inferred-sort -> 1 lf-infer-ok }T

\ A concrete universe successor beyond the host-cell range cannot wrap.
lf-term-reset
T{ lf-shift-cell-max lf-term-sort -> 0 true }T
T{ 0 100 lf-infer -> -1 lf-infer-exhausted }T
T{ lf-term-count @ -> 1 }T

\ Exhausted capacity or an invalid global arena count cannot leak a result.
lf-term-reset
T{ 0 lf-term-sort -> 0 true }T
: fill-infer-arena ( -- )
  begin lf-term-count @ lf-term-capacity < while
    0 lf-term-sort 0= if -1 throw then drop
  repeat ;
fill-infer-arena
T{ 0 100 lf-infer -> -1 lf-infer-exhausted }T
T{ lf-term-count @ -> lf-term-capacity }T
-1 lf-term-count !
T{ 0 100 lf-infer -> -1 lf-infer-invalid }T
T{ lf-term-count @ -> -1 }T
lf-term-reset
bye
