\ Untrusted scope audit for mixed constant-bearing symbolic terms: every
\ bound variable must point inside the binders around it. Load
\ constant-term-boundary.fs and its dependencies first. This does not check
\ types, declarations, dependencies or proofs. Handles are forgeable
\ diagnostics.
\ State: one paired walk record, lf-cts-walker, whose items are a node and
\ the number of binders available at it. Not re-entrant and
\ single-threaded; raw mutation and lifecycle changes during a call are
\ excluded.

lf-term-capacity walk2: lf-cts-walker

\ Fuel left after an audit; kernel passes continue with it.
: lf-cts-fuel ( -- addr ) lf-cts-walker walk-fuel ;

\ Visiting a node at the depth in walk-context. Pi and lambda bind in their
\ body (second child) only, so a node shared under different binders is
\ revisited at each depth. A depth that cannot grow is exhaustion.
: lf-cts-bvar ( first second walk -- outcome ) nip walk-context @ < flag>outcome ;
: lf-cts-leaf ( first second walk -- outcome ) drop 2drop outcome-ok ;
: lf-cts-inner ( depth tag -- depth' true | false )
  lf-tag-app = if true exit then dup max-n = if drop false else 1+ true then ;
: lf-cts-binary ( first second walk tag -- outcome )
  over walk-context @ swap lf-cts-inner
  if swap walk-children-at else drop 2drop outcome-exhausted then ;
: lf-cts-dispatch ( first second walk tag -- outcome )
  dup lf-term-binary-tag? if lf-cts-binary exit then
  case lf-tag-bvar of lf-cts-bvar endof
    lf-tag-symbolic-sort of lf-cts-leaf endof
    lf-tag-constant of lf-cts-leaf endof walk-bad-tag endcase ;
: lf-cts-visit ( walk -- outcome ) lf-terms ['] lf-cts-dispatch walk-visit ;
: lf-cts-run ( root depth -- outcome ) ['] lf-cts-visit lf-cts-walker walk-run-pair ;

\ The whole graph is first validated by lf-cterm-check; the scope walk then
\ continues with the fuel it leaves. On a failed validation lf-cts-fuel
\ keeps the fuel given.
: lf-cts-audit ( index identity -- outcome )
  lf-cts-fuel @ lf-cterm-check dup ok? if lf-cterm-fuel @ lf-cts-fuel ! then ;
: lf-cts-scope ( index identity depth -- outcome )
  >r over >r lf-cts-audit r> r> rot dup ok? if drop lf-cts-run else nip nip then ;

\ Check a live root whose outer depth (binders available around it) is
\ between 0 and the term capacity; the walk may enter further binders. Each
\ visit costs one unit of fuel, including repeated DAG visits. Negative
\ fuel or an out-of-range depth is invalid. Unknown names and declaration
\ types are not examined; nothing is allocated and nothing is accepted.
: lf-cts-depth? ( depth -- flag ) lf-term-capacity upto? ;
: lf-constant-term-scope ( index identity depth fuel -- status )
  lf-cts-walker walk-budget 0= if 2drop drop outcome-invalid exit then
  dup lf-cts-depth? if lf-cts-scope else drop 2drop outcome-invalid then ;
