\ Untrusted conservative beta conversion for mixed terms. This is not a
\ trusted kernel or proof checker. Both inputs are audited; beta
\ normalization and comparison share fuel. Sorts use a conservative symbolic
\ level comparator. Other differences are unknown. The audit checks universe
\ parameter scope, not term binder scope or typing; callers must establish
\ those independently before using a conversion result.
\ State: one paired walk record, lf-mconvert-walker, whose items are a left
\ and a right term; reduction and level comparison run in mixed-beta and
\ level-compare with this walk's fuel. Not re-entrant and single-threaded;
\ no raw or concurrent mutation is safe.

require ../lib/lib.fs
require ../core/constant-term-boundary.fs
require ../core/levels.fs
require ../core/tagged-sort-boundary.fs
require ../core/terms.fs
require ./level-compare.fs
require ./mixed-beta.fs
require ./mixed-compare.fs

lf-term-capacity walk2: lf-mconvert-walker

\ Former status names, still used by tests.
outcome-ok constant lf-mconvert-equal
outcome-invalid constant lf-mconvert-invalid
outcome-exhausted constant lf-mconvert-exhausted
outcome-unknown constant lf-mconvert-unknown

\ Fuel left after a conversion; mixed-infer continues with it. Negative
\ fuel and a failed audit leave zero.
: lf-mconvert-fuel ( -- addr ) lf-mconvert-walker walk-fuel ;

\ Reduce one node to weak head normal form, or compare two levels, with the
\ walk's fuel, continuing with the fuel each leaves. A node's identity is
\ checked first; no failure can authorize equality.
: lf-mconvert-beta ( node identity -- node' outcome )
  lf-mconvert-fuel @ lf-mixed-beta lf-mbeta-fuel @ lf-mconvert-fuel ! nip outcome-sane ;
: lf-mconvert-whnf ( node -- node' outcome )
  dup lf-term-identity if lf-mconvert-beta else drop -1 outcome-invalid then ;
: lf-mconvert-levels ( left right -- outcome )
  lf-mconvert-fuel @ lf-level-compare lf-lcmp-fuel @ lf-mconvert-fuel ! outcome-sane ;

\ Reduce the pair being visited in place, left first.
: lf-mconvert-reduce ( addr -- outcome ) dup @ lf-mconvert-whnf >r swap ! r> ;
: lf-mconvert-reduce-pair ( walk -- outcome )
  dup walk-node lf-mconvert-reduce ok-then? if walk-context lf-mconvert-reduce then ;

\ Compare reduced heads. Symbolic Sorts need equal second fields and levels
\ that compare equal; bound variables must match exactly; constants need
\ equal arity, names and levels; binary nodes compare both children pairs,
\ each reduced when visited. Other constructors are invalid; distinct valid
\ syntax is unknown, not a proof of inequality.
: lf-mconvert-sort ( a b walk -- outcome )
  drop 2dup lf-mcompare-seconds = if lf-mcompare-firsts lf-mconvert-levels
  else 2drop outcome-invalid then ;
: lf-mconvert-bvar ( a b walk -- outcome )
  drop 2dup lf-mcompare-seconds = >r lf-mcompare-firsts = r> and lf-mcompare-verdict ;
: lf-mconvert-args ( slot slot -- outcome )
  lf-mcompare-arrays 0 ?do 2dup i lf-mcompare-arg lf-mconvert-levels
    dup ok? 0= if nip nip unloop exit then drop loop 2drop outcome-ok ;
: lf-mconvert-constant ( a b walk -- outcome )
  >r lf-mcompare-crefs r> lf-mcompare-heads if lf-mconvert-args then ;
: lf-mconvert-dispatch ( a b walk tag -- outcome )
  dup lf-term-binary-tag? if drop lf-mcompare-children exit then
  case lf-tag-symbolic-sort of lf-mconvert-sort endof
    lf-tag-constant of lf-mconvert-constant endof
    lf-tag-bvar of lf-mconvert-bvar endof walk-bad-tag endcase ;
\ Each visit costs one unit of fuel before its reductions. The reduced
\ heads along one path are distinct term nodes (a reduct holds only nodes
\ below the redex or new ones), so the work stack, with at most one pending
\ pair per node on the path, cannot outgrow the term capacity; a full stack
\ would be full, as the former frame bound was.
: lf-mconvert-visit ( walk -- outcome )
  dup lf-mconvert-reduce-pair ok-then?
  if lf-terms ['] lf-mconvert-dispatch lf-mcompare-visit-pair then ;

\ Compare after both audits; the term and level counts are restored on every
\ result, discarding all temporary allocations (serials never rewind).
: lf-mconvert-marks ( -- terms levels ) lf-term-count @ lf-level-count @ ;
: lf-mconvert-restore ( terms levels -- ) lf-level-count ! lf-term-count ! ;
: lf-mconvert-run ( left right -- outcome )
  lf-mconvert-marks 2>r ['] lf-mconvert-visit lf-mconvert-walker walk-run-pair
  2r> lf-mconvert-restore ;

\ ( left left-id right right-id fuel -- status )
\ Validate both complete graphs, then compare; restore all temporary term
\ allocations on every result. Failed preflight conservatively leaves zero fuel.
: lf-mixed-convert ( left lid right rid fuel -- status )
  lf-mconvert-walker tuck walk-budget 0= if lf-mcompare-refused exit then
  lf-mcompare-roots ok-then? if lf-mconvert-run else nip then ;
