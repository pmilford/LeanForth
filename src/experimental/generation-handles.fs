\ Untrusted allocation-identity handle experiment; not a capability system,
\ kernel interface, portable serialization, or theorem checker. Load terms,
\ levels, level-scope, tagged-sort-boundary and symbolic-session first.
\ Handles are two stack cells: index followed by its allocation identity.
\ Identities detect reuse after reset or rollback, but are forgeable and do not
\ distinguish arena kinds. Callers must prevent concurrent mutation, raw
\ writes and cross-arena confusion. Sort references created here retain a
\ level allocation identity; raw symbolic Sorts cannot pass lf-hterm-check.
\ All underlying storage and scratch state remain global and non-reentrant.

variable lf-hterm-tag
create lf-hsort-term-identities lf-term-capacity cells allot
create lf-hsort-level-identities lf-term-capacity cells allot
lf-hsort-term-identities lf-term-capacity cells erase
lf-hsort-level-identities lf-term-capacity cells erase
create lf-href-work lf-term-capacity cells allot
variable lf-href-pending
variable lf-href-fuel
variable lf-href-node
variable lf-href-tag
variable lf-href-first
variable lf-href-second

\ Test a level pair against the current slot identity and allocation range.
\ This does not check level graph shape, context scope or handle provenance.
: lf-hlevel-valid? ( index identity -- flag )
  swap lf-level-identity if = else drop false then ;

\ Test a term pair against the active session and term identity. The result says
\ nothing about the node's syntax or its level graph.
: lf-hterm-valid? ( index identity -- flag )
  swap lf-term-identity if = else drop false then lf-ssession-current? and ;

\ Convert the raw allocator's optional result to an allocation-identity pair.
: lf-hlevel-result ( index true | false -- index identity true | false )
  if dup lf-level-identity 0= if drop false else true then else false then ;
: lf-hterm-result ( index true | false -- index identity true | false )
  if dup lf-term-identity 0= if drop false else true then else false then ;

\ Produce handles to zero, an opaque parameter, or a successor of a live level.
\ Parameters are still required to be in the session context when checked.
: lf-hlevel-zero ( -- index identity true | false )
  0 lf-level-valid? if 0 dup lf-level-identity else false then ;
: lf-hlevel-param ( name-id -- index identity true | false )
  lf-level-param lf-hlevel-result ;
: lf-hlevel-succ ( index identity -- index identity true | false )
  2dup lf-hlevel-valid? 0= if 2drop false exit then
  drop lf-level-succ lf-hlevel-result ;

\ Construct tagged symbolic Sort syntax only from a current level pair, while
\ the destination term session is active. Level scope is checked separately.
: lf-hterm-sort ( level-index level-identity -- index identity true | false )
  lf-ssession-current? 0= if 2drop false exit then
  2dup lf-hlevel-valid? 0= if 2drop false exit then
  >r lf-term-symbolic-sort lf-hterm-result
  dup if
    2 pick cells lf-hsort-level-identities + r> swap !
    over 3 pick cells lf-hsort-term-identities + !
  else r> drop then ;

\ Construct a variable in the active session; binding scope is not checked.
: lf-hterm-bvar ( depth -- index identity true | false )
  lf-ssession-current? 0= if drop false exit then
  lf-term-bvar lf-hterm-result ;

\ Construct binary syntax after validating both handle identities. The raw
\ constructor checks child indices and supported tags, but not typing or scope.
: lf-hterm-binary ( left lid right rid tag -- index identity true | false )
  lf-hterm-tag !
  2over lf-hterm-valid? >r 2dup lf-hterm-valid? r> and 0= if
    2drop 2drop false exit
  then
  drop swap drop lf-hterm-tag @ lf-term-binary lf-hterm-result ;
: lf-hterm-app ( left lid right rid -- index identity true | false )
  lf-tag-app lf-hterm-binary ;
: lf-hterm-lam ( domain did body bid -- index identity true | false )
  lf-tag-lam lf-hterm-binary ;
: lf-hterm-pi ( domain did body bid -- index identity true | false )
  lf-tag-pi lf-hterm-binary ;

\ Push a reachable term index into a bounded audit stack.
: lf-href-push ( index -- flag )
  lf-href-pending @ lf-term-capacity >= if drop false exit then
  lf-href-pending @ cells lf-href-work + ! 1 lf-href-pending +! true ;

\ Audit one structurally checked term. A Sort must have a stamp for this exact
\ term allocation and its referenced level must still have the captured ID.
\ Term and level children point backwards, so count rollback cannot preserve a
\ parent while removing its child in the same arena. Raw mutation is excluded.
: lf-href-visit ( node -- status )
  dup lf-href-node ! lf-term-read 0= if lf-repr-invalid exit then
  lf-href-second ! lf-href-first ! lf-href-tag !
  lf-href-tag @ lf-tag-symbolic-sort = if
    lf-href-node @ lf-term-identity 0= if lf-repr-invalid exit then
    lf-href-node @ cells lf-hsort-term-identities + @ <> if lf-repr-invalid exit then
    lf-href-first @ lf-level-identity 0= if lf-repr-invalid exit then
    lf-href-node @ cells lf-hsort-level-identities + @ <>
    if lf-repr-invalid else lf-repr-ok then exit
  then
  lf-href-tag @ lf-tag-bvar = if lf-repr-ok exit then
  lf-href-tag @ lf-tag-app = lf-href-tag @ lf-tag-lam = or
  lf-href-tag @ lf-tag-pi = or 0= if lf-repr-invalid exit then
  lf-href-first @ lf-href-push 0= if lf-repr-exhausted exit then
  lf-href-second @ lf-href-push 0= if lf-repr-exhausted exit then
  lf-repr-ok ;

\ Internal helper: audit structurally validated terms with nonnegative fuel.
: lf-href-check ( root fuel -- status )
  lf-href-fuel ! 0 lf-href-pending !
  lf-href-push 0= if lf-repr-exhausted exit then
  begin lf-href-pending @ 0> while
    lf-href-fuel @ 0= if lf-repr-exhausted exit then
    -1 lf-href-fuel +! -1 lf-href-pending +!
    lf-href-pending @ cells lf-href-work + @ lf-href-visit
    ?dup if exit then
  repeat lf-repr-ok ;

\ Check a live pair's reachable symbolic syntax, levels and Sort identities.
\ This gives structural and level-parameter-scope evidence only; term binder
\ scope, typing and theorem validity are not checked.
: lf-hterm-check ( index identity fuel -- status )
  >r 2dup lf-hterm-valid? 0= if 2drop r> drop lf-repr-invalid exit then
  drop dup r> lf-ssession-check ?dup if nip exit then
  lf-ssession-fuel @ lf-href-check ;
