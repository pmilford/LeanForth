\ Nested inductive blocks (src/kernel/inductive-nested.fs; plan task
\ 5.2.5; ADR 0020): the translation into a mutual block with auxiliary
\ types, its check, and the restoration of the nested occurrences, on
\ cases of the inductive table (tests/core/check-block-cases/, each the
\ export pinned Lean printed; tests/core/check-block.fs checks their
\ verdicts, the auxiliary recursors and the tampered replays). This file
\ adds coverage class 5 of docs/development/TEST_COVERAGE_REVIEW.md inside
\ the translation and restoration passes: for nestings through List,
\ Option and Prod and in a mutual block, and rejected ones (a negative
\ occurrence inside the nesting, a local variable in the nested
\ argument), about n budgets spread from 0 to the
\ least that suffices give exhausted, that least and above the verdict
\ plenty gives; about n of the block check's allocations, each refused in
\ turn, give full; a crowded term store gives full.
\ Test-only; nothing here accepts a theorem.
include ../support/heap-watch.fs
require ../support/case-sweeps.fs

: block-swept ( c-addr u n -- fuel-ok? refusals-ok? crowded verdict )
  >r cs-load cs-block-target r> cs-sampled cs cs-normal @ cs-unload ;

T{ s" nested.tree" 23 block-swept -> true true outcome-full outcome-ok }T
T{ s" nested.option" 19 block-swept -> true true outcome-full outcome-ok }T
T{ s" nested.prod" 19 block-swept -> true true outcome-full outcome-ok }T
T{ s" nested.mutual" 11 block-swept -> true true outcome-full outcome-ok }T
T{ s" nested.non-positive" 19 block-swept -> true true outcome-full outcome-rejected }T
\ A local variable in the nested argument is rejected before the check
\ allocates anything (no refusal to sweep: false): crowded, it is still
\ rejected.
T{ s" nested.local-variable" 23 block-swept -> true false outcome-rejected outcome-rejected }T
\ An occurrence's last test (lf-nest-if-type, split out of
\ lf-nest-occurrence by cleanup-families-3): a candidate whose head is
\ not a nested inductive type is kept as it is, none and ok.
T{ false lf-nest-if-type -> lf-nest-none outcome-ok }T
\ A new constructor's record (lf-nest-grow-ctor, split by cleanup-families-3;
\ its review, M2), after nested.tree's check, whose translation left three:
\ grown past the capacity of the constructors' declarations, each numbered
\ in turn, ok, of kind constructor. With both arrays full, the growth of
\ the records' cells, then of the declarations', refused (heap-watch.fs):
\ -1 and full, the cells under the call kept, the count unchanged.
s" nested.tree" cs-load cs-block-target cs-run drop
: ctor-grown? ( -- flag ) lf-ind-ctors@ lf-nest-grow-ctor ok? -rot = and ;
: ctors-grown? ( n -- flag ) true swap 0 ?do ctor-grown? and loop ;
: ctor-kinds? ( -- flag )
  true lf-ind-ctors@ 0 ?do i lf-nest-ctor-decl lf-idecl-kind @ lf-kind-constructor = and loop ;
: past-room ( -- n ) lf-ind-ctor-decls slab-capacity lf-ind-ctors@ - 2 + ;
T{ lf-ind-ctors@ past-room ctors-grown? ctor-kinds? -> 3 true true }T
: room-of? ( slab -- flag ) slab-capacity lf-ind-ctors@ = ;
: ctors-to-room ( -- ) lf-ind-ctor-decls slab-capacity lf-ind-ctors@ - ctors-grown? drop ;
T{ ctors-to-room lf-ind-ctor-cells room-of? lf-ind-ctor-decls room-of? -> true true }T
: grow-refused ( k -- j outcome ) heap-refusals ! lf-nest-grow-ctor 0 heap-refusals ! ;
: count-kept? ( k -- j outcome flag ) lf-ind-ctors@ >r grow-refused lf-ind-ctors@ r> = ;
T{ 55 1 count-kept? 2 count-kept? -> 55 -1 outcome-full true -1 outcome-full true }T
T{ lf-ind-ctor-decls room-of? 1 ctors-grown? ctor-kinds? -> true true true }T
cs-unload
bye
