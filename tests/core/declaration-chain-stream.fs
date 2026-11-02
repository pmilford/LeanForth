\ Test-only bounded u32 little-endian transport; stdin is data, never code.
\ Conditional diagnostics do not check declarations, dependencies or proofs.
include ../../src/core/terms.fs
include ../../src/core/names.fs
include ../../src/core/levels.fs
include ../../src/core/level-scope.fs
include ../../src/core/tagged-sort-boundary.fs
include ../../src/core/symbolic-session.fs
include ../../src/core/generation-handles.fs
include ../../src/core/constant-references.fs
include ../../src/core/constant-term-boundary.fs
include ../../src/core/constant-term-scope.fs
include ../../src/kernel/level-substitute.fs
include ../../src/kernel/level-value.fs
include ../../src/kernel/level-compare.fs
include ../../src/kernel/mixed-level-substitute.fs
include ../../src/kernel/mixed-signature-probe.fs
include ../../src/kernel/mixed-signature-audit.fs
include ../../src/kernel/mixed-shift.fs
include ../../src/kernel/mixed-instantiate.fs
include ../../src/kernel/mixed-beta.fs
include ../../src/kernel/mixed-compare.fs
include ../../src/kernel/mixed-convert.fs
include ../../src/kernel/mixed-infer.fs
include ../../src/kernel/mixed-definition-probe.fs
decimal
create cb 1 allot
create buf 255 allot
create names 64 cells allot
create lids 2 cells allot
create levels 2 cells allot
create tids lf-term-capacity cells allot
create args 2 cells allot
variable n variable k variable a variable b variable count-n
: byte-in ( -- u ) cb 1 stdin read-file throw 1 <> if -1 throw then cb c@ ;
: field ( -- u ) byte-in byte-in 8 lshift or byte-in 16 lshift or
  byte-in dup 128 >= if 2drop -1 throw then 24 lshift or ;
: handle ( index -- index identity ) dup n @ >= if -1 throw then dup cells tids + @ ;
: level-handle ( index -- index identity ) dup 2 >= if -1 throw then
  dup cells levels + @ swap cells lids + @ ;
: name-row ( index -- )
  field dup 255 > if 2drop -1 throw then dup >r
  0 ?do field dup 255 > if drop -1 throw then buf i + c! loop
  0 buf r> lf-name-str 0= if drop -1 throw then swap cells names + ! ;
: node ( -- )
  field n ! field k ! field a ! field b !
  n @ lf-term-count @ <> if -1 throw then
  k @ case
    1 of b @ if -1 throw then a @ level-handle lf-hterm-sort endof
    2 of b @ if -1 throw then a @ lf-hterm-bvar endof
    3 of a @ handle b @ handle lf-hterm-app endof
    4 of a @ handle b @ handle lf-hterm-lam endof
    5 of a @ handle b @ handle lf-hterm-pi endof
    7 of
      a @ dup 0= swap 8 > or if -1 throw then
      b @ level-handle args cell+ ! args !
      a @ cells names + @ lf-name-generation @ args 1 lf-cref-new
      0= if -1 throw then lf-cterm-new
    endof
    -1 throw
  endcase
  0= if -1 throw then n @ cells tids + ! n @ <> if -1 throw then ;
\ This private harness emits diagnostic observations only. No theorem is accepted.
create formals 1 cells allot
variable mark-t variable mark-l variable mark-c variable mark-s
variable step-type variable step-value variable step-name variable step-arity
variable result-code variable pair-fuel variable step-index
create stage-fuels 3 cells allot
create saved-names lf-msp-capacity cells allot
create saved-roots lf-msp-capacity cells allot
create saved-ids lf-msp-capacity cells allot
create saved-arities lf-msp-capacity cells allot
create saved-formals lf-msp-capacity lf-level-capacity * cells allot
: bytes-equal? ( first second count -- flag ) >r r@ swap r> compare 0= ;
: save-prefix ( source destination -- ) mark-s @ cells move ;
: marks ( -- )
  lf-term-count @ mark-t ! lf-level-count @ mark-l !
  lf-cref-count @ mark-c ! lf-msp-count @ mark-s !
  lf-msp-names saved-names save-prefix lf-msp-roots saved-roots save-prefix
  lf-msp-ids saved-ids save-prefix lf-msp-arities saved-arities save-prefix
  lf-msp-formals saved-formals mark-s @ lf-level-capacity * cells move ;
: prefix-unchanged ( -- flag )
  lf-msp-names saved-names mark-s @ cells bytes-equal?
  lf-msp-roots saved-roots mark-s @ cells bytes-equal? and
  lf-msp-ids saved-ids mark-s @ cells bytes-equal? and
  lf-msp-arities saved-arities mark-s @ cells bytes-equal? and
  lf-msp-formals saved-formals mark-s @ lf-level-capacity * cells bytes-equal? and ;
: unchanged ( -- flag )
  lf-term-count @ mark-t @ = lf-level-count @ mark-l @ = and
  lf-cref-count @ mark-c @ = and lf-msp-count @ mark-s @ = and
  prefix-unchanged and ;
: staged-as-requested ( -- flag )
  mark-s @ cells lf-msp-names + @ step-name @ cells names + @ =
  mark-s @ cells lf-msp-roots + @ step-type @ = and
  mark-s @ cells lf-msp-ids + @ step-type @ cells tids + @ = and
  mark-s @ cells lf-msp-arities + @ step-arity @ = and
  mark-s @ lf-msp-formals-at formals step-arity @ cells bytes-equal? and ;
: report ( step phase status -- ) >r >r . r> . r> . lf-msp-count @ . cr ;
\ Status 0 is conditional diagnostic success, never declaration authority.
\ Every result must preserve the arena marks; a failed put preserves the index.
: do-step ( step type value name arity -- flag )
  step-arity ! step-name ! step-value ! step-type ! step-index !
  marks lf-msp-token 0= if -1 throw then
  step-type @ handle step-value @ handle pair-fuel @ lf-mixed-definition-probe
  result-code ! unchanged 0= if -1 throw then
  step-index @ 1 result-code @ report
  result-code @ if false exit then
  marks lf-msp-token 0= if -1 throw then
  step-name @ cells names + @ step-type @ handle
  formals step-arity @ step-index @ 1- cells stage-fuels + @ lf-msp-put result-code !
  lf-term-count @ mark-t @ <> lf-level-count @ mark-l @ <> or
  lf-cref-count @ mark-c @ <> or if -1 throw then
  result-code @ if lf-msp-count @ mark-s @ <> if -1 throw then
    prefix-unchanged 0= if -1 throw then
    step-index @ 2 result-code @ report false exit then
  lf-msp-count @ mark-s @ 1+ <> if -1 throw then
  prefix-unchanged staged-as-requested and 0= if -1 throw then
  step-index @ 2 result-code @ report true ;
: check-name ( i addr len -- )
  0 -rot lf-name-str 0= if -1 throw then
  swap cells names + @ <> if -1 throw then ;
: run ( -- )
  lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
  \ Test-only budgets: one for pairs, then one staging budget per step.
  field pair-fuel ! 3 0 do field i cells stage-fuels + ! loop
  field 8 <> if -1 throw then 9 1 do i name-row loop
  1 s" fixtureId" check-name 2 s" u" check-name
  5 s" fixturePoly" check-name 6 s" fixtureUse" check-name
  2 cells names + @ lf-lscope-context-add 0= if -1 throw then
  lf-hlevel-zero 0= if -1 throw then lids ! levels !
  2 cells names + @ lf-hlevel-param 0= if -1 throw then lids cell+ ! levels cell+ !
  lf-ssession-begin 0= if -1 throw then
  field count-n ! count-n @ 19 <> if -1 throw then
  count-n @ 0 do node loop
  cb 1 stdin read-file throw 0<> if -1 throw then count-n @ n !
  \ Preaudit every root before any inference can allocate and revive a handle.
  4 handle 0 50000 lf-constant-term-scope lf-repr-ok <> if -1 throw then
  6 handle 0 50000 lf-constant-term-scope lf-repr-ok <> if -1 throw then
  11 handle 0 50000 lf-constant-term-scope lf-repr-ok <> if -1 throw then
  13 handle 0 50000 lf-constant-term-scope lf-repr-ok <> if -1 throw then
  18 handle 0 50000 lf-constant-term-scope lf-repr-ok <> if -1 throw then
  lf-msp-begin 0= if -1 throw then
  2 cells names + @ formals !
  1 4 6 1 1 do-step 0= if -2 throw then
  2 4 11 5 1 do-step 0= if -2 throw then
  3 13 18 6 0 do-step 0= if -2 throw then ;
: main ( -- ) ['] run catch if 1 (bye) then ;
main bye
