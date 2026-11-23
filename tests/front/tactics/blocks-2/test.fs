require ../../../support/tester.fs
include ../../../support/heap-watch.fs
include ../../../support/meta-sweeps.fs
require ../../../../src/load/checker.fs
require ../../../../src/load/front.fs
require ../../../../src/cli/check-lf.fs
require ../../../support/tactic-text.fs
decimal

4000000 lf-term-capacity! drop  100000 lf-cref-capacity! drop
T{ s" tests/front/decide-slice.ndjson" true lfc-library-open -> outcome-ok }T
T{ s" tests/front/decide-slice.elab.ndjson" lfc-elab-file! lfc-elab-read lfc-rooms
   -> outcome-ok outcome-ok }T
lf-author-begin
: hh ( -- c-addr u ) s" Nat explicit: a Nat explicit: b a b = explicit: h b a = explicit: k a b =" ;
: hk ( -- c-addr u )
  s" Nat explicit: a Nat explicit: b a b = explicit: h b a = explicit: k a b = b a = ∧" ;
: h4 ( -- c-addr u )
  s" Nat explicit: a Nat explicit: b a b = explicit: h b a = explicit: k a b = a b = ∧ a b = a b = ∧ ∧" ;
T{ hk s" by-constructor <;> by-assumption" tactic-ran -> 0 }T
T{ hk s" by-constructor by-all-goals by-assumption by-end" tactic-ran -> 0 }T
T{ h4 s" by-constructor <;> by-constructor <;> ' h by-exact" tactic-ran -> 0 }T
T{ h4 s" by-constructor <;> by-constructor ' h by-exact ' h by-exact ' h by-exact ' h by-exact" tactic-ran -> 0 }T
T{ hk s" by-constructor <;> ' h by-exact" tactic-ran lf-author-final? -> 96 true }T
T{ hk s" <;> by-assumption" tactic-ran -> 468 }T
T{ hk s" by-constructor <;>" tactic-ran -> 85 }T
T{ hk s" { by-constructor <;> by-assumption }" tactic-ran -> 0 }T
T{ hk s" by-constructor <;> { by-assumption }" tactic-ran -> 0 }T
.( blocks-2 test.fs: all tests passed) cr
