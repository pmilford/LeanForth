\ Test-only bounded u32 little-endian transport; stdin is data, never code.
\ Conditional diagnostics do not check declarations, dependencies or proofs.
require ../../src/lib/lib.fs
require ../../src/core/constant-references.fs
require ../../src/core/constant-term-boundary.fs
require ../../src/core/constant-term-scope.fs
require ../../src/core/generation-handles.fs
require ../../src/core/level-scope.fs
require ../../src/core/levels.fs
require ../../src/core/names.fs
require ../../src/core/scratch-marks.fs
require ../../src/core/symbolic-session.fs
require ../../src/core/tagged-sort-boundary.fs
require ../../src/core/terms.fs
require ../../src/kernel/mixed-convert.fs
require ../../src/kernel/mixed-definition-probe.fs
require ../../src/kernel/mixed-infer.fs
require ../../src/kernel/mixed-signature-probe.fs
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
create formals 1 cells allot
variable expected-tag variable expected-a variable expected-b
create infer-mark /lf-scratch allot   \ the stores before the inferences
: infer-marked ( -- ) infer-mark lf-scratch-mark ok? 0= if -1 throw then ;
: infer-rolled-back ( -- ) infer-mark lf-scratch-rollback ok? 0= if -1 throw then ;
\ Require the exported binder/application links used by this fixture test.
: expect-node ( index tag first second -- )
  expected-b ! expected-a ! expected-tag !
  lf-term-read 0= if -1 throw then
  expected-b @ <> if -1 throw then
  expected-a @ <> if -1 throw then
  expected-tag @ <> if -1 throw then ;
\ Check the application function but leave its argument to inference.
: expect-app-head ( index first -- )
  expected-a ! lf-term-read 0= if -1 throw then
  drop expected-a @ <> if drop -1 throw then
  lf-tag-app <> if -1 throw then ;
: run ( -- )
  lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
  field 8 <> if -1 throw then 9 1 do i name-row loop
  2 cells names + @ lf-lscope-context-add 0= if -1 throw then
  lf-hlevel-zero 0= if -1 throw then lids ! levels !
  2 cells names + @ lf-hlevel-param 0= if -1 throw then lids cell+ ! levels cell+ !
  lf-ssession-begin 0= if -1 throw then
  field count-n ! count-n @ 19 <> if -1 throw then
  count-n @ 0 do node loop
  cb 1 stdin read-file throw 0<> if -1 throw then
  count-n @ n !
  \ fixturePoly is lambda A, lambda x, (fixtureId A) x. Check links before
  \ using the corresponding handles; a different valid graph must not pass.
  0 lf-tag-symbolic-sort 1 0 expect-node
  1 lf-tag-bvar 0 0 expect-node
  2 lf-tag-bvar 1 0 expect-node
  3 lf-tag-pi 1 2 expect-node
  4 lf-tag-pi 0 3 expect-node
  11 lf-tag-lam 0 10 expect-node
  10 lf-tag-lam 1 9 expect-node
  \ Node 9's argument is checked by conditional inference below, so a
  \ well-scoped but ill-typed mutation reaches the inference path.
  8 lf-tag-app 7 2 expect-node
  18 lf-tag-lam 12 17 expect-node
  17 lf-tag-lam 1 16 expect-node
  16 15 expect-app-head
  15 lf-tag-app 14 2 expect-node
  7 lf-term-read 0= if -1 throw then
  rot lf-tag-constant <> if 2drop -1 throw then lf-cterm-pair
  2dup lf-cref-read 0= if 2drop -1 throw then
  1 <> if 2drop 2drop -1 throw then
  lf-name-generation @ <> if 2drop drop -1 throw then
  1 cells names + @ <> if 2drop -1 throw then
  0 lf-cref-level 0= if -1 throw then
  lids cell+ @ <> if drop -1 throw then
  levels cell+ @ <> if -1 throw then
  14 lf-term-read 0= if -1 throw then
  rot lf-tag-constant <> if 2drop -1 throw then lf-cterm-pair
  2dup lf-cref-read 0= if 2drop -1 throw then
  1 <> if 2drop 2drop -1 throw then
  lf-name-generation @ <> if 2drop drop -1 throw then
  1 cells names + @ <> if 2drop -1 throw then
  0 lf-cref-level 0= if -1 throw then
  lids @ <> if drop -1 throw then levels @ <> if -1 throw then
  \ Check scope on the exported declaration roots before any diagnostic
  \ allocates. This does not establish that their types or dependencies hold.
  4 handle 0 50000 lf-constant-term-scope outcome-ok <> if -1 throw then
  6 handle 0 50000 lf-constant-term-scope outcome-ok <> if -1 throw then
  11 handle 0 50000 lf-constant-term-scope outcome-ok <> if -1 throw then
  13 handle 0 50000 lf-constant-term-scope outcome-ok <> if -1 throw then
  18 handle 0 50000 lf-constant-term-scope outcome-ok <> if -1 throw then
  \ fixturePoly's application refers to both binders: it is scoped under
  \ two binders, but must be rejected when only one is available.
  9 handle 2 50000 lf-constant-term-scope outcome-ok <> if -1 throw then
  9 handle 1 50000 lf-constant-term-scope outcome-invalid <> if -1 throw then
  \ Conditional inference of fixturePoly, using fixtureId's staged signature
  \ as an unchecked assumption. No declaration or theorem is accepted.
  infer-marked
  lf-msp-begin 0= if -1 throw then
  2 cells names + @ formals !
  lf-msp-token 0= if -1 throw then
  1 cells names + @ 4 handle formals 1 50000 lf-msp-put
  outcome-ok <> if -1 throw then
  \ Check pairs first so negative fixtures must reach this diagnostic.
  lf-msp-token 0= if -1 throw then
  4 handle 11 handle 50000 lf-mixed-definition-probe
  dup outcome-ok <> if
    dup outcome-unknown = if s" definition pair inconclusive" stderr write-file throw then
    dup outcome-rejected = if s" definition pair rejected" stderr write-file throw then
    drop -1 throw
  then drop
  lf-msp-token 0= if -1 throw then
  13 handle 18 handle 50000 lf-mixed-definition-probe
  dup outcome-ok <> if
    dup outcome-unknown = if s" theorem pair inconclusive" stderr write-file throw then
    dup outcome-rejected = if s" theorem pair rejected" stderr write-file throw then
    drop -1 throw
  then drop
  lf-msp-token 0= if -1 throw then
  11 handle 50000 lf-mixed-infer dup outcome-ok <> if
    dup outcome-unknown = if s" definition inference inconclusive" stderr write-file throw then
    drop 2drop -1 throw
  then drop
  4 handle 50000 lf-mixed-convert outcome-ok <> if -1 throw then
  infer-rolled-back
  \ The theorem value also uses fixtureId, specialized at universe zero.
  \ This remains conditional inference, not proof or declaration acceptance.
  lf-msp-token 0= if -1 throw then
  18 handle 50000 lf-mixed-infer dup outcome-ok <> if
    dup outcome-unknown = if s" theorem inference inconclusive" stderr write-file throw then
    drop 2drop -1 throw
  then drop
  13 handle 50000 lf-mixed-convert outcome-ok <> if -1 throw then
  infer-rolled-back
  \ Probe the fixtureId type/value pair with an empty signature index. Even a
  \ successful diagnostic is not declaration registration or a theorem.
  lf-msp-begin 0= if -1 throw then
  lf-msp-token 0= if -1 throw then
  4 handle 6 handle 50000 lf-mixed-definition-probe
  dup outcome-ok <> if
    dup outcome-unknown = if s" fixtureId pair inconclusive" stderr write-file throw then
    dup outcome-rejected = if s" fixtureId pair rejected" stderr write-file throw then
    drop -1 throw
  then drop
  s" fixture ok" type cr ;
run bye
