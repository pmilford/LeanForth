\ Test-only bounded u32 little-endian transport; stdin is data, never code.
\ Structural results do not check declarations, dependencies, types or proofs.
require ../../src/lib/lib.fs
require ../../src/core/constant-references.fs
require ../../src/core/constant-term-boundary.fs
require ../../src/core/generation-handles.fs
require ../../src/core/level-scope.fs
require ../../src/core/levels.fs
require ../../src/core/names.fs
require ../../src/core/symbolic-session.fs
require ../../src/core/terms.fs
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
  count-n @ 0 do
    i . i lf-term-read 0= if -1 throw then >r >r . r> . r> . cr
  loop
  \ Inspect the name and first level of each constant reference.
  7 lf-term-read 0= if -1 throw then rot drop
  2dup lf-cref-read 0= if -1 throw then drop drop .
  0 lf-cref-level 0= if -1 throw then drop . cr
  14 lf-term-read 0= if -1 throw then rot drop
  2dup lf-cref-read 0= if -1 throw then drop drop .
  0 lf-cref-level 0= if -1 throw then drop . cr
  count-n @ n !
  4 handle 50000 lf-cterm-check . 6 handle 50000 lf-cterm-check .
  4 handle 50000 lf-cterm-check . 11 handle 50000 lf-cterm-check .
  13 handle 50000 lf-cterm-check . 18 handle 50000 lf-cterm-check . cr ;
run bye
