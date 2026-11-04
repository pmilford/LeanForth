\ Global nonallocating preflight for the untrusted mixed signature index.
\ Signatures are unchecked type assumptions: this checks neither types,
\ declaration lookup, dependency closure nor proofs. Constant names/handles
\ are validated, not resolved to index records; arities of referenced
\ declarations are unknown. Universe formal IDs are opaque positive IDs, not
\ name-table handles. Used parameters must belong both to the copied formals
\ and the current session scope; unused formals need not occur in the
\ session scope.
\
\ No reset, insertion, raw writes or callback during a call. The token fixes
\ an index lifetime, not a content revision; the caller must keep the index
\ and session fixed for the whole call and any subsequent use requires a
\ fresh audit. Scratch of the called auditors changes. No term, level or
\ reference is allocated, even on failure; counts and serials are
\ unchanged. Handles are forgeable, instance-local diagnostics.
\ State: one record, lf-msa-state, holding the fuel the last audit left; a
\ member of the checker context (lib/context.fs). The level audit is
\ mixed-level-substitute's lf-mls-audit-formals, given its root, formal
\ list and fuel on the stack. Single-threaded within one context.

require ../lib/lib.fs
require ../core/constant-term-scope.fs
require ../core/diagnostics.fs
require ../core/level-scope.fs
require ../core/levels.fs
require ./mixed-level-substitute.fs
require ./mixed-signature-probe.fs

begin-structure /lf-audit
  field: lf-audit-left   \ fuel left by the last audit with nonnegative fuel
end-structure
/lf-audit context-record: lf-msa-state

\ Fuel left after an audit; mixed-infer and the definition probe continue
\ with it. On failure it holds the fuel left where the audit stopped.
: lf-msa-fuel ( -- addr ) lf-msa-state lf-audit-left ;

\ Validate a record's bounded metadata before using it as a pointer or loop
\ bound: a live positive name not used by an earlier record, an arity of
\ at least 0 whose formals lie in the pool, and positive, pairwise distinct
\ formal IDs.
: lf-msa-name? ( position -- flag )
  dup lf-msp-name@ dup lf-msp-name? if swap lf-msp-find 0< else 2drop false then ;
: lf-msa-arity? ( position -- flag )
  dup lf-msp-arity@ dup 0< if 2drop false exit then
  swap lf-msp-offset@ dup 0< if 2drop false exit then
  + lf-msp-formal-pool slab-capacity > 0= ;
: lf-msa-formal? ( addr i -- flag )
  2dup cells + @ dup 0> if -rot lf-msp-cell-index 0< else drop 2drop false then ;
: lf-msa-formals? ( addr count -- flag )
  0 ?do dup i lf-msa-formal? 0= if drop false unloop exit then loop drop true ;
: lf-msa-formal-list ( position -- formals count )
  dup lf-msp-formals-at swap lf-msp-arity@ ;
: lf-msa-metadata? ( position -- flag )
  dup lf-msa-name? over lf-msa-arity? and
  if lf-msa-formal-list lf-msa-formals? else drop false then ;

\ Each check takes the fuel left and returns the fuel it leaves, even on
\ failure. lf-constant-term-scope and lf-mls-audit-formals report only ok,
\ invalid, exhausted or full; outcome-sane passes any outcome on unchanged (so
\ rejected or unsupported too, once ADR 0008 step 3 lets helpers return
\ them; still not ok) and makes anything else invalid.
: lf-msa-root ( position -- root identity ) dup lf-msp-root@ swap lf-msp-id@ ;
: lf-msa-scope ( position fuel -- fuel' status )
  >r lf-msa-root 0 r> lf-constant-term-scope lf-cts-fuel @ swap outcome-sane ;
: lf-msa-levels ( position fuel -- fuel' status )
  >r dup lf-msp-root@ swap lf-msa-formal-list r> lf-mls-audit-formals outcome-sane ;

\ One record: metadata, binder scope at outer depth zero, then every level
\ against the copied formals.
: lf-msa-checked ( position fuel -- fuel' status )
  over swap lf-msa-scope dup ok? if drop lf-msa-levels else rot drop then ;
: lf-msa-record ( position fuel -- fuel' status )
  over lf-msa-metadata? if lf-msa-checked else nip outcome-invalid then ;
: lf-msa-records ( fuel -- fuel' status )
  lf-msp-count @ 0 ?do i swap lf-msa-record dup ok? 0= if unloop exit then drop loop
  outcome-ok ;
: lf-msa-site ( -- site ) c" mixed-signature-audit lf-mixed-signature-audit" ;
\ Zero fuel is exhausted and negative fuel invalid; both are recorded as
\ diagnostics.
: lf-msa-dry ( fuel -- fuel status ) dup lf-msa-site lf-diag-exhausted outcome-exhausted ;
: lf-msa-run ( token fuel -- fuel' status )
  swap lf-msp-current? lf-lscope-context-valid? and 0= if outcome-invalid exit then
  dup 0= if lf-msa-dry else lf-msa-records then ;
: lf-msa-negative ( token fuel -- status )
  nip 0 lf-msa-site lf-diag-bad-argument lf-diag-note outcome-invalid ;

\ Validate every live record, including complete root identity, reachable
\ constant references, session level scope, copied formals, structural
\ syntax and term binder scope at outer depth zero. One shared budget
\ charges each term and level occurrence on each traversal, including
\ repeated DAG edges. Index/name/formal/context and reference identity scans
\ are bounded additional work; a full work stack is full, independently of
\ fuel. Negative fuel or malformed/stale data is invalid; zero fuel is
\ exhausted, including for an empty index. No lookup, specialization or
\ inference is done.
: lf-mixed-signature-audit ( token fuel -- status )
  dup 0< if lf-msa-negative exit then lf-msa-run swap lf-msa-fuel ! ;
