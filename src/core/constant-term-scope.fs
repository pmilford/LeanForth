\ Untrusted scope audit for mixed constant-bearing symbolic terms: every
\ bound variable must point inside the binders around it. This does not
\ check types, declarations, dependencies or proofs. Handles are forgeable
\ diagnostics.
\ State: one paired walk record, lf-cts-walker, whose items are a node and
\ the number of binders available at it; a member of the checker context
\ (lib/context.fs); its marks are constant-term-boundary.fs's.
\ Single-threaded within one context; raw mutation and lifecycle changes
\ during a call are excluded.

require ../lib/lib.fs
require ./constant-term-boundary.fs
require ./diagnostics.fs
require ./tagged-sort-boundary.fs
require ./terms.fs

lf-walk-room context-walk2: lf-cts-walker

\ Fuel left after an audit; kernel passes continue with it.
: lf-cts-fuel ( -- addr ) lf-cts-walker walk-fuel ;
: lf-cts-site ( -- site ) c" constant-term-scope lf-constant-term-scope" ;

\ Visiting a node at the depth in walk-context. Pi and lambda bind in their
\ body (second child) only, so a node shared under different binders is
\ checked again only at a smaller depth than any it was checked at (the
\ marks of constant-term-boundary.fs). A depth that cannot grow (max-n) is
\ full, like a push without room, whatever fuel is left (ADR 0008). An
\ unbound variable and a full binder depth are recorded as diagnostics.
: lf-cts-unbound ( index depth -- outcome )
  lf-cts-site lf-diag-out-of-scope lf-diag-note outcome-invalid ;
: lf-cts-bvar ( first second walk -- outcome )
  nip walk-context @ 2dup < if 2drop outcome-ok else lf-cts-unbound then ;
: lf-cts-leaf ( first second walk -- outcome ) drop 2drop outcome-ok ;
: lf-cts-inner ( depth tag -- depth' true | false )
  lf-tag-app = if true exit then dup max-n = if drop false else 1+ true then ;
: lf-cts-deep ( -- outcome )
  max-n dup lf-cts-site lf-diag-binders-full lf-diag-note outcome-full ;
: lf-cts-binary ( first second walk tag -- outcome )
  over walk-context @ swap lf-cts-inner
  if swap walk-children-at else drop 2drop lf-cts-deep then ;
: lf-cts-dispatch ( first second walk tag -- outcome )
  dup lf-term-binary-tag? if lf-cts-binary exit then
  case lf-tag-bvar of lf-cts-bvar endof
    lf-tag-symbolic-sort of lf-cts-leaf endof
    lf-tag-constant of lf-cts-leaf endof
    lf-tag-proj of lf-cts-leaf endof  lf-tag-lit of lf-cts-leaf endof
    lf-tag-str of lf-cts-leaf endof
    lf-tag-let of lf-cts-leaf endof  walk-bad-tag endcase ;
: lf-cts-once ( first second walk tag -- outcome ) ['] lf-cts-dispatch lf-walk-once ;
: lf-cts-visit ( walk -- outcome ) ['] lf-cts-once lf-term-visit ;
: lf-cts-run ( root depth -- outcome )
  lf-cts-walker lf-walk-marking
  ['] lf-cts-visit lf-cts-walker walk-run-pair lf-cts-walker lf-cts-site lf-diag-walk ;

\ The whole graph is first validated by lf-cterm-check; the scope walk then
\ continues with the fuel it leaves. On a failed validation lf-cts-fuel
\ keeps the fuel given.
: lf-cts-audit ( index identity -- outcome )
  lf-cts-fuel @ lf-cterm-check dup ok? if lf-cterm-fuel @ lf-cts-fuel ! then ;
: lf-cts-scope ( index identity depth -- outcome )
  >r over >r lf-cts-audit r> r> rot dup ok? if drop lf-cts-run else nip nip then ;

\ Check a live root whose outer depth (binders available around it) is
\ nonnegative (no fixed limit: plan task 6.2.0); the walk may enter
\ further binders. Each visit costs one unit of fuel, a repeated DAG visit
\ too, though a node is checked again only at a smaller depth. Negative
\ fuel or a negative depth is invalid. Unknown names and declaration
\ types are not examined; nothing is allocated and nothing is accepted.
: lf-cts-depth? ( depth -- flag ) 0< 0= ;
: lf-constant-term-scope ( index identity depth fuel -- status )
  lf-cts-walker walk-budget 0= if 2drop drop outcome-invalid exit then
  dup lf-cts-depth? if lf-cts-scope else drop 2drop outcome-invalid then ;
