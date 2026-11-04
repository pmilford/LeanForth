\ The proof outlines in LaTeX style (plan task 8.6.1), for the golden file
\ tests/present/outlines-latex.golden (compared by tests/present/
\ check_outline.py, which also compiles them when pdflatex is installed):
\ the five pinned examples, composition's rejected copy (no outline) and a
\ log truncated at step 31 (no outline). Each section is a LaTeX fragment
\ between "== NAME" lines. Test-only.
require ../support/print-outline.fs

: section ( c-addr u -- ) ." == " type cr ;
: ample ( -- ) lf-log-capacities lf-log-limits ;
: outlines ( c-addr u -- ) false po-file ;

true lf-outline-latex!
s" identity" section s" tests/reference/identity.ndjson" outlines
s" composition" section s" tests/reference/composition.ndjson" outlines
s" type-identity" section s" tests/reference/type-identity.ndjson" outlines
s" poly-identity" section s" tests/reference/poly-identity.ndjson" outlines
s" constant-fixture" section s" tests/reference/constant-fixture.ndjson" outlines
s" composition-wrong-argument" section
s" tests/core/check-declaration-cases/composition-wrong-argument.ndjson" outlines
s" composition, log truncated" section
lf-log-terms lf-log-set
30 lf-log-mark-capacity lf-log-term-capacity lf-log-level-capacity lf-log-limits
s" tests/reference/composition.ndjson" false po-run-file ample
false lf-outline-latex!
lf-log-off lf-log-set
bye
