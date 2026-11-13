\ String literals in the kernel (src/kernel/string-literals.fs; Lean's
\ string_lit_to_constructor and try_string_lit_expansion, plan task
\ 5.2.3), on the cases primitive.string-* of the inductive table
\ (tests/core/check-block-cases/, each the export pinned Lean printed;
\ tests/core/check-block.fs checks their verdicts against Lean): a
\ string literal as the major premise of String.rec (reduced through its
\ constructor form) and compared with String.ofList of a list
\ (is_def_eq_core step 13), each also with a wrong claim. Coverage
\ classes of docs/development/TEST_COVERAGE_REVIEW.md:
\ 1, 7. The target's outcome with plenty of fuel: accepted, or rejected
\    for the wrong claim, as Lean.
\ 5. Resources, inside the target's check: each allocation refused in
\    turn (the expansion's names, constants, applications, code points
\    and the list) gives full, never a verdict; a crowded term store
\    gives full; every sampled budget below the least that suffices is
\    exhausted, and that budget and above give the outcome above.
\ Test-only; nothing here accepts a theorem.
require ../support/case-sweeps.fs

\ A case's target: its outcome, then every allocation refused, a
\ crowded term store and about 20 budgets (cs-fuel-sampled).
: outcome ( c-addr u -- outcome ) cs-load cs-plenty cs-at cs-unload ;
: swept ( c-addr u -- refusals-ok? crowded fuel-ok? )
  cs-load 1 cs-refusal-sweep cs-crowded 20 cs-fuel-sampled cs-unload ;
: ok-row ( c-addr u -- refusals-ok? crowded fuel-ok? outcome )
  2dup outcome >r swept r> ;

\ String.rec on a literal of two characters: its constructor form, then
\ iota; the wrong claim names the other minor premise.
T{ s" primitive.string-major-two-constructors" ok-row
   -> true outcome-full true outcome-ok }T
T{ s" primitive.string-major-two-constructors-wrong" ok-row
   -> true outcome-full true outcome-rejected }T
\ A literal and String.ofList of its characters, in both orders, and a
\ list of other characters.
T{ s" primitive.string-opaque-expansion" ok-row -> true outcome-full true outcome-ok }T
T{ s" primitive.string-opaque-expansion-reversed" ok-row
   -> true outcome-full true outcome-ok }T
T{ s" primitive.string-opaque-expansion-wrong" ok-row
   -> true outcome-full true outcome-rejected }T
bye
