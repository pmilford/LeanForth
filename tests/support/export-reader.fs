\ Test-only bounded reader for one exported declaration: stdin is data,
\ never code. It stages universe parameters, level records and expression
\ records as handle terms in a fresh session. Used by
\ tests/core/export-definition-stream.fs and export-signature-stream.fs;
\ tests/support/export_definition.py writes the input. Requires the kernel's
\ entry, src/load/kernel.fs.
\ Protocol, every field a nonnegative signed 32-bit little-endian value:
\   P, then P parameter names (length, then one field per byte);
\   L, then L level records (tag first second): 0 zero (record 0 only),
\     1 succ, 2 max, 3 imax of earlier records, 4 param (first = position);
\   N, then N nodes (index tag first second): 1 Sort (first = level record),
\     2 bvar, 3 app, 4 lam, 5 Pi (children are earlier nodes);
\   claim, value, S (0 or P), S level records that replace the parameters
\   in order, and the fuel. Malformed or truncated input or trailing data
\   throws before anything is printed.
decimal
4 constant max-params
create cb 1 allot
create name-buf 255 allot
create params max-params cells allot            \ parameter name IDs
create actuals max-params 2* cells allot        \ replacement level pairs
create level-map lf-level-capacity cells allot  \ level record -> level
create node-map lf-term-capacity 2* cells allot \ node -> index identity
variable param-count
variable level-count
variable node-count
variable subst-count
variable claim-index variable claim-id variable value-index variable value-id

: must ( flag -- ) 0= if -1 throw then ;
: byte-in ( -- u ) cb 1 stdin read-file throw 1 = must cb c@ ;
\ One field; a high byte with its sign bit set is outside the protocol.
: u32 ( -- u ) byte-in byte-in 8 lshift or byte-in 16 lshift or
  byte-in dup 128 < must 24 lshift or ;
\ A field that must be below limit.
: u32< ( limit -- u ) u32 tuck > must ;
: pair! ( index identity addr -- ) tuck cell+ ! ! ;

\ Universe parameters are interned names, added to the session context.
: read-name ( -- id )
  256 u32< dup >r 0 ?do 256 u32< name-buf i + c! loop
  0 name-buf r> lf-name-str must ;
: read-param ( position -- )
  read-name tuck swap cells params + ! lf-lscope-context-add must ;
: read-params ( -- ) max-params 1+ u32< dup param-count ! 0 ?do i read-param loop ;

\ Level record r may only refer to earlier records.
: level-at ( record -- level ) cells level-map + @ ;
: earlier-level ( r child -- level ) tuck > must level-at ;
: two-levels ( r first second -- l1 l2 )
  >r over swap earlier-level swap r> earlier-level ;
: zero-level ( r first second -- level ) or or 0= must 0 ;
: succ-level ( r first second -- level ) 0= must earlier-level lf-level-succ must ;
: param-level ( r first second -- level )
  0= must nip dup param-count @ u< must cells params + @ lf-level-param must ;
: level-record ( r tag first second -- level )
  rot case
    0 of zero-level endof
    1 of succ-level endof
    2 of two-levels lf-level-max must endof
    3 of two-levels lf-level-imax must endof
    4 of param-level endof
    -1 throw
  endcase ;
: read-levels ( -- )
  lf-level-capacity 1+ u32< dup level-count ! dup must
  0 ?do i u32 u32 u32 level-record i cells level-map + ! loop
  0 level-at 0= must ;
: level-handle ( record -- index identity )
  level-count @ over > must level-at dup lf-level-identity must ;

\ Node i may only refer to earlier nodes; each becomes a handle term.
: node-at ( n -- index identity ) 2* cells node-map + 2@ ;
: earlier-node ( i child -- index identity ) tuck > must node-at ;
: two-nodes ( i first second -- a aid b bid )
  >r over swap earlier-node rot r> earlier-node ;
: sort-node ( i first second -- index identity true | false )
  0= must nip level-handle lf-hterm-sort ;
: bvar-node ( i first second -- index identity true | false ) 0= must nip lf-hterm-bvar ;
: node-record ( i tag first second -- index identity )
  rot case
    1 of sort-node endof
    2 of bvar-node endof
    3 of two-nodes lf-hterm-app endof
    4 of two-nodes lf-hterm-lam endof
    5 of two-nodes lf-hterm-pi endof
    -1 throw
  endcase must ;
: read-node ( i -- )
  u32 over = must dup u32 u32 u32 node-record rot 2* cells node-map + 2! ;
: read-nodes ( -- ) lf-term-capacity 1+ u32< dup node-count ! 0 ?do i read-node loop ;
: read-root ( -- index identity ) node-count @ u32< node-at ;

\ Replacements: none, or one level record per parameter.
: read-actual ( position -- )
  level-count @ u32< level-handle rot 2* cells actuals + pair! ;
: read-actuals ( -- )
  u32 dup subst-count ! dup 0= over param-count @ = or must 0 ?do i read-actual loop ;
: no-trailing-data ( -- ) cb 1 stdin read-file throw 0= must ;

\ Read a whole stream into a fresh session; leaves the fuel field.
: read-export ( -- fuel )
  lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
  read-params read-levels lf-ssession-begin must read-nodes
  read-root claim-id ! claim-index ! read-root value-id ! value-index !
  read-actuals u32 no-trailing-data ;

\ Lean-style shape of a term whose levels are all concrete: s<level value>,
\ v<index>, a(fn,arg), l(domain,body), p(domain,body).
: emit-level ( level -- ) 50000 lf-level-value ok? must ." s" 0 .r ;
: emit-shape ( index -- )
  lf-term-read must rot case
    lf-tag-symbolic-sort of drop emit-level endof
    lf-tag-bvar of drop ." v" 0 .r endof
    lf-tag-app of ." a(" swap recurse ." ," recurse ." )" endof
    lf-tag-lam of ." l(" swap recurse ." ," recurse ." )" endof
    lf-tag-pi of ." p(" swap recurse ." ," recurse ." )" endof
    -1 throw
  endcase ;
