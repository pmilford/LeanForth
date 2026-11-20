\ The command line of exports and snapshots alone (src/load/cli-checker.fs,
\ which bin/leanforth-checker runs): an export checks as in the whole load,
\ and a LeanForth text is refused, exit 4, with a line saying where it is
\ checked, cli/leanforth.fs's default cli-text-run (cli/leanforth-text.fs,
\ which sets it, is not loaded here). make test-cli-forth.
\ Test-only; nothing here accepts a theorem outside the code under test.
include ../support/tester.fs
include ../support/checks.fs
require ../../src/load/cli-checker.fs
decimal

: composition ( -- c-addr u ) s" tests/reference/composition.ndjson" ;
: text-check ( -- code ) cli-options s" tests/author/01-identity.lf" cli-check ;
T{ [defined] lfc-library-open [defined] cli-text-report -> false false }T
T{ cli-options composition cli-check -> 0 }T
T{ text-check -> 4 }T
T{ text-check cli-options composition cli-check -> 4 0 }T
[defined] >string-execute [if]
: text-refusal ( -- c-addr u )
  s" error: bin/leanforth-checker checks exports and snapshots only; check a LeanForth text with bin/leanforth" ;
T{ ' text-check >string-execute text-refusal search nip nip -> 4 true }T
[then]
cli-options

cases-done
bye
