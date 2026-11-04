\ The proof outlines of the golden file tests/present/outlines.golden
\ (plan task 2.4.4; compared by tests/present/check_outline.py): every
\ pinned export's outlines; composition's every step (detail); composition
\ with its log truncated at step 31 and with a log without formulas (no
\ outline from either); and composition with g applied to value, rejected
\ (no outline; its steps end with the rules that failed). Test-only.
require ../support/print-outline.fs

: section ( c-addr u -- ) ." == " type cr ;
: ample ( -- ) lf-log-capacities lf-log-limits ;
: outlines ( c-addr u -- ) false po-file ;
: steps ( c-addr u -- ) true po-file ;

s" identity" section s" tests/reference/identity.ndjson" outlines
s" composition" section s" tests/reference/composition.ndjson" outlines
s" type-identity" section s" tests/reference/type-identity.ndjson" outlines
s" poly-identity" section s" tests/reference/poly-identity.ndjson" outlines
s" constant-fixture" section s" tests/reference/constant-fixture.ndjson" outlines
s" composition --detail" section s" tests/reference/composition.ndjson" steps

s" composition, log truncated" section
lf-log-terms lf-log-set
30 lf-log-mark-capacity lf-log-term-capacity lf-log-level-capacity lf-log-limits
s" tests/reference/composition.ndjson" false po-run-file ample
s" composition, log without formulas" section
lf-log-steps lf-log-set s" tests/reference/composition.ndjson" false po-run-file

s" composition-wrong-argument" section
s" tests/core/check-declaration-cases/composition-wrong-argument.ndjson" outlines
s" composition-wrong-argument --detail" section
s" tests/core/check-declaration-cases/composition-wrong-argument.ndjson" steps
bye
