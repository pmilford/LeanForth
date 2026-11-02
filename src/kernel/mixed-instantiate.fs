\ Untrusted capture-avoiding single-binder instantiation of mixed terms.
\ Load mixed-shift.fs and its dependencies first. This is syntax
\ transformation, not type checking or theorem acceptance.
\ State: one frame record, lf-minst-frames (fuel, nesting, the binder depth
\ as its context, the replacement, the starting term count). The
\ replacement is shifted on mixed-shift's record. Not re-entrant and
\ single-threaded; callers must not mutate the stores concurrently.

outcome-ok constant lf-minst-ok
outcome-invalid constant lf-minst-invalid
outcome-exhausted constant lf-minst-exhausted
lf-term-capacity frames: lf-minst-frames

\ Fuel left after an instantiation; mixed-beta and mixed-infer continue
\ with it.
: lf-minst-fuel ( -- addr ) lf-minst-frames frame-fuel ;
: lf-minst-replacement ( -- addr ) lf-minst-frames frame-arg ;
: lf-minst-start ( -- addr ) lf-minst-frames frame-mark ;
: lf-minst-depth ( -- depth ) lf-minst-frames frame-context @ ;

\ Only nodes of the original input, below the starting count, are visited,
\ and a child must precede its parent.
: lf-minst-old? ( index -- flag ) dup 0< 0= swap lf-minst-start @ < and ;
: lf-minst-child? ( child node -- flag ) over > swap lf-minst-old? and ;
: lf-minst-children? ( node first second -- node flag )
  rot tuck lf-minst-child? >r tuck lf-minst-child? r> and ;

\ Bound variables at binder depth d: a local one (index below d) is kept;
\ the target (index d) becomes the replacement shifted by d, with the
\ remaining shared fuel; outer ones are lowered by one. A negative index or
\ a nonzero second field is malformed.
: lf-minst-replace ( -- result outcome )
  lf-minst-replacement @ lf-minst-depth lf-minst-frames lf-mshift-inside ;
: lf-minst-lower ( index -- result outcome ) 1- lf-term-bvar lf-mshift-allocated ;
: lf-minst-outer ( index -- result outcome )
  dup lf-minst-depth = if drop lf-minst-replace else lf-minst-lower then ;
: lf-minst-variable ( node index -- result outcome )
  dup lf-minst-depth < if drop outcome-ok else nip lf-minst-outer then ;
: lf-minst-bvar ( node first second -- result outcome )
  0<> over 0< or if 2drop lf-rebuild-invalid else lf-minst-variable then ;

\ Visiting one source node. Application, lambda and Pi nodes are rebuilt;
\ any other tag is malformed. Each visit costs one unit of fuel.
: lf-minst-binary ( node first second -- result outcome )
  lf-minst-children?
  if lf-minst-frames lf-rebuild-binary else drop lf-rebuild-invalid then ;
: lf-minst-dispatch ( node first second tag -- result outcome )
  dup lf-term-binary-tag? if drop lf-minst-binary exit then
  dup lf-tag-bvar = if drop lf-minst-bvar exit then
  lf-rebuild-leaf? if lf-rebuild-keep else 2drop drop lf-rebuild-invalid then ;
: lf-minst-visit ( node -- result outcome )
  dup lf-minst-old? 0= if drop lf-rebuild-invalid exit then
  dup lf-term-read if rot lf-minst-dispatch else drop lf-rebuild-invalid then ;

\ Validate both complete handles with one fuel budget before allocating, even
\ when the replacement is unused. Roll back term allocations on every failure;
\ allocation serials are intentionally never rewound. Constant and Sort nodes
\ are reused with their stamps. Identities are session-local; resets
\ invalidate handles. Child indices rely on backward edges and no raw
\ mutation or count edits during their lifetime. Fuel charges both audits,
\ source visits and each replacement shift visit. No type, scope, proof, or
\ executable-program correctness is established. Negative fuel and a failed
\ validation leave zero remaining fuel as a conservative bound.
: lf-minst-audit ( source sid replacement rid -- source sid replacement rid outcome )
  2over lf-minst-frames lf-rebuild-audit
  dup ok? if drop 2dup lf-minst-frames lf-rebuild-audit then ;
: lf-minst-refuse ( source sid replacement rid outcome -- -1 0 outcome )
  >r 2drop 2drop r> lf-rebuild-none ;
: lf-minst-unfueled ( source sid replacement rid -- -1 0 status )
  0 lf-minst-fuel ! outcome-invalid lf-minst-refuse ;
: lf-mixed-instantiate ( source sid replacement rid fuel -- result id status )
  lf-minst-frames frame-budget 0= if lf-minst-unfueled exit then
  lf-minst-audit dup ok? 0= if lf-minst-refuse exit then
  2drop lf-minst-replacement ! drop 0 ['] lf-minst-visit lf-minst-frames lf-rebuild-run ;
