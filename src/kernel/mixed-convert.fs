\ Untrusted conservative beta conversion for mixed terms. This is not a
\ trusted kernel or proof checker. Both inputs are audited; beta
\ normalization and comparison share fuel. Sorts use a conservative symbolic
\ level comparator. Other differences are unknown. The audit checks universe
\ parameter scope, not term binder scope or typing; callers must establish
\ those independently before using a conversion result.
\ State: one paired walk record, lf-mconvert-walker, whose items are a left
\ and a right term and whose argument cell says whether level comparisons
\ keep their fuel when undecided, a member of the checker context
\ (lib/context.fs); reduction and level comparison run in mixed-beta and
\ level-compare with this walk's fuel. Single-threaded within one context;
\ no raw or concurrent mutation is safe.

require ../lib/lib.fs
require ../core/constant-term-boundary.fs
require ../core/derivation-log.fs
require ../core/diagnostics.fs
require ../core/levels.fs
require ../core/local-context.fs
require ../core/tagged-sort-boundary.fs
require ../core/terms.fs
require ./level-compare.fs
require ./mixed-beta.fs
require ./mixed-compare.fs

lf-walk-room context-walk2: lf-mconvert-walker

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
: lf-mconvert-keep ( -- addr ) lf-mconvert-walker walk-arg ;
: lf-mconvert-levels ( left right -- outcome )
  lf-mconvert-fuel @ lf-mconvert-keep @ lf-level-compare-run
  lf-lcmp-fuel @ lf-mconvert-fuel ! outcome-sane ;

\ Reduce the pair being visited in place, left first.
: lf-mconvert-reduce ( addr -- outcome ) dup @ lf-mconvert-whnf >r swap ! r> ;
: lf-mconvert-reduce-pair ( walk -- outcome )
  dup walk-node lf-mconvert-reduce ok-then? if walk-context lf-mconvert-reduce then ;

\ Compare reduced heads. Symbolic Sorts need equal second fields and levels
\ that compare equal; bound variables, and free variables (by number, one
\ node per local-context entry), must match exactly; constants need equal
\ arity, names and levels; binary nodes compare both children pairs, each
\ reduced when visited. Other constructors are invalid; distinct valid
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
    lf-tag-constant of lf-mconvert-constant endof  lf-tag-bvar of lf-mconvert-bvar endof
    lf-tag-fvar of lf-mconvert-bvar endof walk-bad-tag endcase ;
\ Each visit costs one unit of fuel before its reductions. The reduced
\ heads along one path are distinct term nodes (a reduct holds only nodes
\ below the redex or new ones), so the work stack, with at most one pending
\ pair per node on the path, outgrows its room only when the term capacity
\ is raised above it; a full stack is full, as the former frame bound was.
: lf-mconvert-visit ( walk -- outcome )
  dup lf-mconvert-reduce-pair ok-then?
  if lf-terms ['] lf-mconvert-dispatch lf-mcompare-visit-pair then ;

\ Compare after both audits; the term and level counts are restored on every
\ result, discarding all temporary allocations (serials never rewind).
: lf-mconvert-marks ( -- terms levels ) lf-term-count @ lf-level-count @ ;
: lf-mconvert-restore ( terms levels -- ) lf-level-count ! lf-term-count ! ;
: lf-mconvert-site ( -- site ) c" mixed-convert lf-mixed-convert" ;
: lf-mconvert-walk ( left right -- outcome )
  ['] lf-mconvert-visit lf-mconvert-walker walk-run-pair
  lf-mconvert-walker lf-mconvert-site lf-diag-walk ;
: lf-mconvert-run ( left right -- outcome )
  lf-mconvert-marks 2>r lf-mconvert-walk 2r> lf-mconvert-restore ;

\ ( left left-id right right-id fuel -- status )
\ Validate both complete graphs, then compare; restore all temporary term
\ allocations on every result. Failed preflight conservatively leaves zero fuel.
\ lf-mixed-convert-keeping differs only in the fuel left after an undecided
\ level comparison (lf-level-compare-keeping): mixed-infer uses it, so that
\ its rejection analysis (ADR 0011) can go on after an undecided step.
: lf-mconvert-pass ( left lid right rid fuel -- status )
  lf-mconvert-walker tuck walk-budget 0= if lf-mcompare-refused exit then
  lf-mcompare-roots ok-then? if lf-mconvert-run else nip then ;
\ The derivation log (ADR 0013): with it on, a conversion is one defeq
\ step of left and right; both paths run the same pass.
: lf-mconvert-logged ( left lid right rid fuel -- status )
  4 pick 3 pick lf-rule-defeq lf-log-open lf-mconvert-pass lf-log-decided ;
: lf-mconvert-checked ( left lid right rid fuel -- status )
  lf-log? if lf-mconvert-logged else lf-mconvert-pass then ;
: lf-mixed-convert ( left lid right rid fuel -- status )
  false lf-mconvert-keep ! lf-mconvert-checked ;
: lf-mixed-convert-keeping ( left lid right rid fuel -- status )
  true lf-mconvert-keep ! lf-mconvert-checked ;
