\ Session-local candidate signatures never become checked declarations.
\ Exercise suffix rollback and slot reuse outside any active probe call.
include ../support/tester.fs
include ../../src/core/terms.fs
include ../../src/experimental/names.fs
include ../../src/experimental/levels.fs
include ../../src/experimental/level-scope.fs
include ../../src/experimental/tagged-sort-boundary.fs
include ../../src/experimental/symbolic-session.fs
include ../../src/experimental/generation-handles.fs
include ../../src/experimental/constant-references.fs
include ../../src/experimental/constant-term-boundary.fs
include ../../src/experimental/level-substitute.fs
include ../../src/experimental/mixed-level-substitute.fs
include ../../src/experimental/mixed-signature-probe.fs
include ../../src/experimental/constant-term-scope.fs
include ../../src/experimental/mixed-signature-audit.fs

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
bye
