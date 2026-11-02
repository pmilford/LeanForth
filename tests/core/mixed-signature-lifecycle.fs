\ Session-local candidate signatures never become checked declarations.
\ Exercise suffix rollback and slot reuse outside any active probe call.
include ../support/tester.fs
include ../support/checks.fs
include ../../src/core/terms.fs
include ../../src/core/names.fs
include ../../src/core/levels.fs
include ../../src/core/level-scope.fs
include ../../src/core/tagged-sort-boundary.fs
include ../../src/core/symbolic-session.fs
include ../../src/core/generation-handles.fs
include ../../src/core/constant-references.fs
include ../../src/core/constant-term-boundary.fs
include ../../src/core/level-substitute.fs
include ../../src/core/mixed-level-substitute.fs
include ../../src/core/mixed-signature-probe.fs
include ../../src/core/constant-term-scope.fs
include ../../src/core/mixed-signature-audit.fs

create formals 1 cells allot
create actuals 2 cells allot
create args 2 cells allot
variable candidate variable token variable root-id variable level-id

: pair! ( level addr -- )
  >r dup r@ ! lf-level-identity 0= abort" level identity" r> cell+ ! ;
: begin-fixture ( -- )
  lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
  11 lf-lscope-context-add 0= abort" context"
  lf-ssession-begin 0= abort" session"
  0 s" candidate" lf-name-str 0= abort" name" candidate !
  11 lf-hlevel-param 0= abort" param" level-id ! drop
  11 formals ! 0 actuals pair!
  lf-msp-begin 0= abort" index" lf-msp-token 0= abort" token" token ! ;
: put-root ( index identity -- status )
  token @ candidate @ 2swap formals 1 5000 lf-msp-put ;
: specialize ( -- index identity 0 | status )
  token @ candidate @ actuals 1 5000 lf-msp-specialize ;

\ The old root identity must not revive when the same slot gets a new term.
begin-fixture
T{ 1 level-id @ lf-hterm-sort -> 0 lf-term-serial @ true }T
lf-term-serial @ root-id !
T{ 0 root-id @ put-root -> lf-msp-ok }T
0 lf-term-count !
T{ 1 level-id @ lf-hterm-sort -> 0 lf-term-serial @ true }T
T{ specialize -> lf-msp-invalid }T
T{ token @ 5000 lf-mixed-signature-audit -> lf-msp-invalid }T
T{ lf-term-count @ lf-level-count @ lf-cref-count @ -> 1 2 0 }T

\ A reused level index cannot validate the old Sort's captured level stamp.
begin-fixture
T{ 1 level-id @ lf-hterm-sort -> 0 lf-term-serial @ true }T
T{ 0 lf-term-serial @ put-root -> lf-msp-ok }T
1 lf-level-count !
T{ 11 lf-hlevel-param -> 1 lf-level-serial @ true }T
T{ specialize -> lf-msp-invalid }T
T{ token @ 5000 lf-mixed-signature-audit -> lf-msp-invalid }T
T{ lf-term-count @ lf-level-count @ lf-cref-count @ -> 1 2 0 }T

\ The same stale-level rule applies inside a captured constant argument.
begin-fixture
1 args pair!
T{ candidate @ lf-name-generation @ args 1 lf-cref-new -> 0 lf-cref-serial @ true }T
T{ 0 lf-cref-serial @ lf-cterm-new -> 0 lf-term-serial @ true }T
T{ 0 lf-term-serial @ put-root -> lf-msp-ok }T
1 lf-level-count !
T{ 11 lf-hlevel-param -> 1 lf-level-serial @ true }T
T{ specialize -> lf-msp-invalid }T
T{ token @ 5000 lf-mixed-signature-audit -> lf-msp-invalid }T
T{ lf-term-count @ lf-level-count @ lf-cref-count @ -> 1 2 1 }T

\ Malformed put and specialize requests are invalid and change nothing.
: put-with ( name count fuel -- status )
  2>r token @ swap 0 root-id @ formals 2r> ['] lf-msp-put rs-checked ;
: specialize-with ( name count fuel -- index identity 0 | status )
  2>r token @ swap actuals 2r> ['] lf-msp-specialize rs-checked ;
begin-fixture
T{ 1 level-id @ lf-hterm-sort -> 0 lf-term-serial @ true }T
lf-term-serial @ root-id !
T{ candidate @ 1 -1 put-with -> lf-msp-invalid }T
T{ candidate @ -1 5000 put-with -> lf-msp-invalid }T
T{ candidate @ lf-level-capacity 1+ 5000 put-with -> lf-msp-invalid }T
T{ 0 1 5000 put-with -> lf-msp-invalid }T
T{ 999 1 5000 put-with -> lf-msp-invalid }T
T{ lf-msp-count @ lf-term-count @ lf-level-count @ -> 0 1 2 }T
T{ candidate @ 1 5000 put-with -> lf-msp-ok }T
T{ candidate @ 1 -1 specialize-with -> lf-msp-invalid }T
T{ candidate @ -1 5000 specialize-with -> lf-msp-invalid }T
T{ candidate @ lf-level-capacity 1+ 5000 specialize-with -> lf-msp-invalid }T
T{ 0 1 5000 specialize-with -> lf-msp-invalid }T
T{ 999 1 5000 specialize-with -> lf-msp-invalid }T
T{ lf-term-count @ lf-level-count @ lf-cref-count @ -> 1 2 0 }T
T{ candidate @ 1 5000 specialize-with nip nip -> lf-msp-ok }T

\ The index holds lf-msp-capacity records. One more is exhausted and changes
\ nothing, so a capacity check cannot write past the record arrays.
: numbered ( n -- name ) 0 swap lf-name-num 0= abort" numbered name" ;
: fill-index ( -- )
  lf-msp-capacity 1 do i numbered 1 5000 put-with lf-msp-ok <> abort" fill" loop ;
fill-index
T{ lf-msp-count @ -> lf-msp-capacity }T
T{ lf-msp-capacity numbered 1 5000 put-with -> lf-msp-exhausted }T
T{ lf-msp-count @ -> lf-msp-capacity }T
T{ candidate @ 1 5000 specialize-with nip nip -> lf-msp-ok }T
T{ lf-msp-capacity 1- numbered 1 5000 specialize-with nip nip -> lf-msp-ok }T
T{ token @ 5000 lf-mixed-signature-audit -> lf-msp-ok }T
bye
