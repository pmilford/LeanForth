\ Global nonallocating preflight for the untrusted mixed signature index.
\ Load mixed-signature-probe.fs and constant-term-scope.fs first. Signatures
\ are unchecked type assumptions: this checks neither types, declaration lookup,
\ dependency closure nor proofs. Constant names/handles are validated, not
\ resolved to index records; arities of referenced declarations are unknown.
\ Universe formal IDs are opaque positive IDs, not name-table handles. Used
\ parameters must belong both to the copied formals and the current session
\ scope; unused formals need not occur in the session scope.
\
\ No reset, insertion, raw writes or callback during a call. The token fixes
\ an index lifetime, not a content revision; the caller must keep the index
\ and session fixed for the whole call and any subsequent use requires a
\ fresh audit. Scratch of the called auditors changes. No term, level or
\ reference is allocated, even on failure; counts and serials are
\ unchanged. Handles are forgeable, instance-local diagnostics.
\ State: one record, lf-msa-state, holding the fuel the last audit left.
\ The level audit is mixed-level-substitute's lf-mls-audit, which reads its
\ root and fuel from that module's cells and the formal list from
\ level-substitute's; this module sets them just before each call. Not
\ re-entrant and single-threaded.

begin-structure /lf-msa
  field: lf-msa-left     \ fuel left by the last audit with nonnegative fuel
end-structure
create lf-msa-state /lf-msa allot
lf-msa-state /lf-msa erase

\ Fuel left after an audit; mixed-infer and the definition probe continue
\ with it. On failure it holds the fuel left where the audit stopped.
: lf-msa-fuel ( -- addr ) lf-msa-state lf-msa-left ;

\ Validate a record's bounded metadata before using it as a pointer or loop
\ bound: a live positive name not used by an earlier record, an arity of
\ 0..lf-level-capacity, and positive, pairwise distinct formal IDs.
: lf-msa-name? ( position -- flag )
  dup lf-msp-name@ dup lf-msp-name? if swap lf-msp-find 0< else 2drop false then ;
: lf-msa-arity? ( position -- flag ) lf-msp-arity@ lf-level-capacity upto? ;
: lf-msa-formal? ( addr i -- flag )
  2dup cells + @ dup 0> if -rot lf-msp-cell-index 0< else drop 2drop false then ;
: lf-msa-formals? ( addr count -- flag )
  0 ?do dup i lf-msa-formal? 0= if drop false unloop exit then loop drop true ;
: lf-msa-metadata? ( position -- flag )
  dup lf-msa-name? over lf-msa-arity? and
  if dup lf-msp-formals-at swap lf-msp-arity@ lf-msa-formals? else drop false then ;

\ Each check takes the fuel left and returns the fuel it leaves, even on
\ failure. lf-constant-term-scope and lf-mls-audit report only ok, invalid
\ or exhausted.
: lf-msa-root ( position -- root identity ) dup lf-msp-root@ swap lf-msp-id@ ;
: lf-msa-scope ( position fuel -- fuel' status )
  >r lf-msa-root 0 r> lf-constant-term-scope lf-cts-fuel @ swap outcome-sane ;
: lf-msa-source! ( position -- ) lf-msa-root lf-mls-id ! lf-mls-root ! ;
: lf-msa-formals! ( position -- )
  dup lf-msp-arity@ lf-lsubst-count ! lf-msp-formals-at lf-lsubst-formals ! ;
: lf-msa-levels ( position fuel -- fuel' status )
  lf-mls-fuel ! dup lf-msa-source! lf-msa-formals!
  lf-mls-audit lf-mls-fuel @ swap outcome-sane ;

\ One record: metadata, binder scope at outer depth zero, then every level
\ against the copied formals.
: lf-msa-checked ( position fuel -- fuel' status )
  over swap lf-msa-scope dup ok? if drop lf-msa-levels else rot drop then ;
: lf-msa-record ( position fuel -- fuel' status )
  over lf-msa-metadata? if lf-msa-checked else nip outcome-invalid then ;
: lf-msa-records ( fuel -- fuel' status )
  lf-msp-count @ 0 ?do i swap lf-msa-record dup ok? 0= if unloop exit then drop loop
  outcome-ok ;
: lf-msa-run ( token fuel -- fuel' status )
  swap lf-msp-current? lf-lscope-context-valid? and 0= if outcome-invalid exit then
  dup 0= if outcome-exhausted else lf-msa-records then ;

\ Validate every live record, including complete root identity, reachable
\ constant references, session level scope, copied formals, structural
\ syntax and term binder scope at outer depth zero. One shared budget
\ charges each term and level occurrence on each traversal, including
\ repeated DAG edges. Index/name/formal/context and reference identity scans
\ are bounded additional work; work-stack capacity can independently exhaust.
\ Negative fuel or malformed/stale data is invalid; zero fuel is exhausted,
\ including for an empty index. No lookup, specialization or inference is done.
: lf-mixed-signature-audit ( token fuel -- status )
  dup 0< if 2drop outcome-invalid exit then lf-msa-run swap lf-msa-fuel ! ;
