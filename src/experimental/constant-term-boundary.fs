\ Untrusted constant syntax boundary. Load terms, names, levels, level-scope,
\ tagged-sort-boundary, symbolic-session, generation-handles and
\ constant-references first. No lookup, typing, binder scope or proof checking.
\ Global scratch is single-threaded and non-reentrant. Exclude raw mutation,
\ module reload and concurrent access; identities are forgeable, instance-local
\ diagnostics, not capabilities. Memory layout is not a serialization format.
\ Existing binary constructors capture indices, not child identities: their
\ safety relies on backward edges and no raw mutation or arbitrary count edits.
\ A reset invalidates the session; allocation identities prevent resurrection
\ of captured roots, constants, Sort levels and constant references on reuse.

7 constant lf-tag-constant
create lf-cterm-stamps lf-term-capacity cells allot
lf-cterm-stamps lf-term-capacity cells erase
create lf-cterm-work lf-term-capacity cells allot
variable lf-cterm-pending
variable lf-cterm-fuel
variable lf-cterm-node
variable lf-cterm-tag
variable lf-cterm-first
variable lf-cterm-second
variable lf-cterm-ref
variable lf-cterm-ref-id
variable lf-cterm-count

\ Allocate a constant node only for a live reference in the active session.
\ Payload contains the full reference pair; the side stamp binds it to this
\ exact term allocation. Failure leaves the term arena unchanged.
: lf-cterm-new ( cref identity -- term identity true | false )
  lf-ssession-current? 0= if 2drop false exit then
  2dup lf-cref-valid? 0= if 2drop false exit then
  lf-tag-constant -rot lf-term-add lf-hterm-result
  dup if over 3 pick cells lf-cterm-stamps + ! then ;

: lf-cterm-push ( index -- flag )
  lf-cterm-pending @ lf-term-capacity >= if drop false exit then
  lf-cterm-pending @ cells lf-cterm-work + !
  1 lf-cterm-pending +! true ;

\ Check a level graph in the current context, charging the shared budget.
: lf-cterm-level ( index -- status )
  lf-cterm-fuel @ lf-lscope-check lf-lscope-fuel @ lf-cterm-fuel !
  case
    lf-lscope-ok of lf-repr-ok endof
    lf-lscope-invalid of lf-repr-invalid endof
    lf-lscope-exhausted of lf-repr-exhausted endof
    drop lf-repr-invalid 0
  endcase ;

\ The reference accessors revalidate all captured identities on every call.
: lf-cterm-reference ( -- status )
  lf-cterm-first @ lf-cterm-ref ! lf-cterm-second @ lf-cterm-ref-id !
  lf-cterm-node @ lf-term-identity 0= if lf-repr-invalid exit then
  lf-cterm-node @ cells lf-cterm-stamps + @ <> if lf-repr-invalid exit then
  lf-cterm-ref @ lf-cterm-ref-id @ lf-cref-read 0= if lf-repr-invalid exit then
  lf-cterm-count ! 2drop
  lf-cterm-count @ 0 ?do
    lf-cterm-ref @ lf-cterm-ref-id @ i lf-cref-level 0= if
      lf-repr-invalid unloop exit
    then
    drop lf-cterm-level ?dup if unloop exit then
  loop lf-repr-ok ;

: lf-cterm-child? ( index -- flag )
  dup 0< 0= swap lf-cterm-node @ < and ;

\ Inspect one node; children must precede their parent. Sorts must have been
\ constructed by lf-hterm-sort and retain their captured level identity.
: lf-cterm-visit ( -- status )
  lf-cterm-node @ lf-term-read 0= if lf-repr-invalid exit then
  lf-cterm-second ! lf-cterm-first ! lf-cterm-tag !
  lf-cterm-tag @ lf-tag-constant = if lf-cterm-reference exit then
  lf-cterm-tag @ lf-tag-bvar = if
    lf-cterm-first @ 0< lf-cterm-second @ 0<> or
    if lf-repr-invalid else lf-repr-ok then exit
  then
  lf-cterm-tag @ lf-tag-symbolic-sort = if
    lf-cterm-first @ 0< lf-cterm-second @ 0<> or if lf-repr-invalid exit then
    lf-cterm-node @ lf-term-identity 0= if lf-repr-invalid exit then
    lf-cterm-node @ cells lf-hsort-term-identities + @ <> if lf-repr-invalid exit then
    lf-cterm-first @ lf-level-identity 0= if lf-repr-invalid exit then
    lf-cterm-node @ cells lf-hsort-level-identities + @ <> if lf-repr-invalid exit then
    lf-cterm-first @ lf-cterm-level exit
  then
  lf-cterm-tag @ lf-tag-app = lf-cterm-tag @ lf-tag-lam = or
  lf-cterm-tag @ lf-tag-pi = or 0= if lf-repr-invalid exit then
  lf-cterm-first @ lf-cterm-child? lf-cterm-second @ lf-cterm-child? and 0= if
    lf-repr-invalid exit
  then
  lf-cterm-first @ lf-cterm-push 0= if lf-repr-exhausted exit then
  lf-cterm-second @ lf-cterm-push 0= if lf-repr-exhausted exit then
  lf-repr-ok ;

\ Validate a live root and reachable mixed symbolic graph. Each term and level
\ visit costs one fuel unit, including repeated DAG visits; bounded context and
\ cref identity scans are unmetered. Negative fuel is invalid; zero exhausts.
\ Success is structural evidence only, never authority to accept a theorem.
: lf-cterm-check ( index identity fuel -- status )
  dup 0< if drop 2drop lf-repr-invalid exit then lf-cterm-fuel !
  2dup lf-hterm-valid? 0= if 2drop lf-repr-invalid exit then
  drop 0 lf-cterm-pending !
  lf-cterm-push 0= if lf-repr-exhausted exit then
  begin lf-cterm-pending @ 0> while
    lf-cterm-fuel @ 0= if lf-repr-exhausted exit then
    -1 lf-cterm-fuel +! -1 lf-cterm-pending +!
    lf-cterm-pending @ cells lf-cterm-work + @ lf-cterm-node !
    lf-cterm-visit ?dup if exit then
  repeat lf-repr-ok ;
