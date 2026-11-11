\ Session-local candidate signatures never become checked declarations.
\ Exercise suffix rollback and slot reuse outside any active probe call.
include ../support/tester.fs
include ../support/checks.fs
require ../../src/lib/lib.fs
require ../../src/core/constant-references.fs
require ../../src/core/constant-term-boundary.fs
require ../../src/core/generation-handles.fs
require ../../src/core/level-scope.fs
require ../../src/core/levels.fs
require ../../src/core/names.fs
require ../../src/core/symbolic-session.fs
require ../../src/core/terms.fs
require ../../src/kernel/mixed-signature-audit.fs
require ../../src/kernel/mixed-signature-probe.fs
require ../support/store-faults.fs

create formals 1 cells allot
create actuals 2 cells allot
create args 2 cells allot
variable candidate variable token variable root-id variable level-id

: pair! ( level addr -- )
  >r dup r@ ! lf-level-identity 0= abort" level identity" r> cell+ ! ;
\ Where a fixture's terms and levels begin, as store marks (lib/store.fs):
\ a test gives slots back through them, never by setting a count.
create term-start /store-mark allot   create level-start /store-mark allot
: fixture-marked ( -- )
  term-start lf-terms store-mark ok? 0= abort" term mark"
  level-start lf-levels store-mark ok? 0= abort" level mark" ;
: terms-back ( -- ) term-start lf-terms store-rollback ok? 0= abort" terms back" ;
: levels-back ( -- ) level-start lf-levels store-rollback ok? 0= abort" levels back" ;
: begin-fixture ( -- )
  lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
  fixture-marked
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
T{ 1 level-id @ lf-hterm-sort -> 0 term-serial true }T
term-serial root-id !
T{ 0 root-id @ put-root -> outcome-ok }T
terms-back
T{ 1 level-id @ lf-hterm-sort -> 0 term-serial true }T
T{ specialize -> outcome-invalid }T
T{ token @ 5000 lf-mixed-signature-audit -> outcome-invalid }T
T{ lf-term-count @ lf-level-count @ lf-cref-count @ -> 1 2 0 }T

\ A reused level index cannot validate the old Sort's captured level stamp.
begin-fixture
T{ 1 level-id @ lf-hterm-sort -> 0 term-serial true }T
T{ 0 term-serial put-root -> outcome-ok }T
levels-back
T{ 11 lf-hlevel-param -> 1 level-serial true }T
T{ specialize -> outcome-invalid }T
T{ token @ 5000 lf-mixed-signature-audit -> outcome-invalid }T
T{ lf-term-count @ lf-level-count @ lf-cref-count @ -> 1 2 0 }T

\ The same stale-level rule applies inside a captured constant argument.
begin-fixture
1 args pair!
T{ candidate @ lf-name-generation @ args 1 lf-cref-new -> 0 lf-cref-serial @ true }T
T{ 0 lf-cref-serial @ lf-cterm-new -> 0 term-serial true }T
T{ 0 term-serial put-root -> outcome-ok }T
levels-back
T{ 11 lf-hlevel-param -> 1 level-serial true }T
T{ specialize -> outcome-invalid }T
T{ token @ 5000 lf-mixed-signature-audit -> outcome-invalid }T
T{ lf-term-count @ lf-level-count @ lf-cref-count @ -> 1 2 1 }T

\ Malformed put and specialize requests are invalid and change nothing.
: put-with ( name count fuel -- status )
  2>r token @ swap 0 root-id @ formals 2r> ['] lf-msp-put rs-checked ;
: specialize-with ( name count fuel -- index identity 0 | status )
  2>r token @ swap actuals 2r> ['] lf-msp-specialize rs-checked ;
begin-fixture
T{ 1 level-id @ lf-hterm-sort -> 0 term-serial true }T
term-serial root-id !
T{ candidate @ 1 -1 put-with -> outcome-invalid }T
T{ candidate @ -1 5000 put-with -> outcome-invalid }T
T{ 0 1 5000 put-with -> outcome-invalid }T
T{ 999 1 5000 put-with -> outcome-invalid }T
T{ lf-msp-count @ lf-term-count @ lf-level-count @ -> 0 1 2 }T
T{ candidate @ 1 5000 put-with -> outcome-ok }T
T{ candidate @ 1 -1 specialize-with -> outcome-invalid }T
T{ candidate @ -1 5000 specialize-with -> outcome-invalid }T
T{ 0 1 5000 specialize-with -> outcome-invalid }T
T{ 999 1 5000 specialize-with -> outcome-invalid }T
T{ lf-term-count @ lf-level-count @ lf-cref-count @ -> 1 2 0 }T
T{ candidate @ 1 5000 specialize-with nip nip -> outcome-ok }T

\ The index has no fixed number of records (plan task 6.2.0; it held 32
\ before): 40 are kept, and the first and the last specialize.
\ (diagnostics.fs: one the heap cannot grow is full and changes nothing.)
: numbered ( n -- name ) 0 swap lf-name-num 0= abort" numbered name" ;
: fill-index ( -- )
  40 1 do i numbered 1 5000 put-with outcome-ok <> abort" fill" loop ;
fill-index
T{ lf-msp-count @ -> 40 }T
T{ candidate @ 1 5000 specialize-with nip nip -> outcome-ok }T
T{ 39 numbered 1 5000 specialize-with nip nip -> outcome-ok }T
T{ token @ 5000 lf-mixed-signature-audit -> outcome-ok }T

\ A token ends with any change to the stores or the level context it
\ captured; a new session does not revive it, and lookups through it are
\ invalid rather than unknown.
: stale? ( -- flag ) lf-msp-token if drop false else true then ;
\ A fixture whose Sort u (node 0) is not yet in the index.
: sort-fixture ( -- )
  begin-fixture 1 level-id @ lf-hterm-sort 0= abort" sort" root-id ! drop ;
: put-sort ( -- status ) 0 root-id @ put-root ;
begin-fixture
T{ stale? -> false }T
lf-term-reset
T{ stale? -> true }T
T{ lf-ssession-begin stale? -> true true }T
T{ specialize -> outcome-invalid }T
sort-fixture lf-level-reset
T{ stale? -> true }T
sort-fixture lf-lscope-context-reset
T{ stale? put-sort -> true outcome-invalid }T
sort-fixture 12 lf-lscope-context-add drop
T{ stale? put-sort -> true outcome-invalid }T
\ A failed begin (here: a corrupt reference count) also ends the lifetime;
\ repairing the store does not revive the old token.
sort-fixture
lf-cref-count @ -1 lf-cref-count !
T{ lf-msp-begin -> false }T
lf-cref-count !
T{ stale? put-sort -> true outcome-invalid }T
T{ lf-msp-count @ -> 0 }T

\ A forged or stale root identity is invalid and changes nothing.
begin-fixture
T{ 1 level-id @ lf-hterm-sort -> 0 term-serial true }T
term-serial root-id !
T{ 0 root-id @ 1+ put-root -> outcome-invalid }T
T{ 0 root-id @ 1- put-root -> outcome-invalid }T
T{ lf-msp-count @ lf-term-count @ lf-level-count @ lf-cref-count @ -> 0 1 2 0 }T

\ Zero arity: Sort u is refused (u is not a formal), Sort 0 is put, and
\ specialize gives back the identical root handle and allocates nothing; a
\ request with an argument for it is invalid.
T{ token @ candidate @ 0 root-id @ formals 0 5000 lf-msp-put -> outcome-invalid }T
T{ 0 0 lf-level-identity drop lf-hterm-sort -> 1 term-serial true }T
term-serial root-id !
T{ token @ candidate @ 1 root-id @ formals 0 5000 lf-msp-put -> outcome-ok }T
T{ token @ candidate @ actuals 0 5000 lf-msp-specialize -> 1 root-id @ outcome-ok }T
T{ token @ candidate @ actuals 1 5000 lf-msp-specialize -> outcome-invalid }T
T{ lf-term-count @ lf-level-count @ lf-cref-count @ -> 2 2 0 }T

\ Coverage refuses when the zero level is gone and keeps the caller's stack.
\ No public request reaches this guard (the token is stale first), so the
\ internal request record is filled directly.
: coverage-without-zero ( -- status )
  sort-fixture lf-msp-request >r 1 5000 r@ lf-msp-budget! formals r@ lf-sigreq-formals !
  0 root-id @ r@ lf-msp-source! lf-level-count @ 0 lf-level-count !
  r> lf-msp-coverage swap lf-level-count ! ;
T{ 777 coverage-without-zero -> 777 outcome-invalid }T

\ Generation saturation: one last begin succeeds, then begin fails for good
\ (so this case comes last).
begin-fixture
max-n 1- lf-msp-generation !
T{ lf-msp-begin -> true }T
T{ lf-msp-begin lf-msp-begin -> false false }T
T{ stale? -> true }T
bye
