\ Projections (plan task 5.2.2; ADR 0015 rules J1, J2): Lean's
\ Expr.proj S i e, field i of e, a value of the structure S. LeanForth
\ stores it as the application of a projection leaf to e: the leaf, tag
\ lf-tag-proj, holds S's name ID (first) and i (second); the application
\ is an ordinary node (terms.fs). So every pass that does not look at
\ projections treats one as an application of an opaque head, as Lean's
\ do (instantiate, lift_loose_bvars, abstract, has_loose_bvars,
\ instantiate_lparams: one child, no binder, no level); the places where
\ Lean treats Expr.proj specially find the leaf at the head of a spine
\ with at least one argument, e the first: inference (infer_proj,
\ kernel/mixed-infer.fs), reduction (reduce_proj in whnf_core,
\ kernel/iota.fs behind whnf.fs's hook), comparison and printing. A
\ projection applied to more arguments, (e.i) a, is the same spine with
\ them after e. A leaf is never a term of its own: a pass that meets one
\ outside a spine's head treats it as malformed (invalid).
\ Untrusted [import][kernel] data; nothing here checks types.
\ State: none of its own; the leaves go into the term store.

require ../lib/lib.fs
require ./generation-handles.fs
require ./names.fs
require ./terms.fs

10 constant lf-tag-proj
\ A leaf for field idx of the structure named name (a name ID of this
\ context), as a handle: (index identity true), or false for a negative
\ name or index, a full store or a spent serial.
: lf-hterm-proj ( name idx -- index identity true | false )
  2dup or 0< if 2drop false exit then
  lf-tag-proj -rot lf-term-add lf-hterm-result ;
\ Whether node is a projection leaf; its structure's name and its index.
: lf-proj-leaf? ( node -- flag ) lf-term-tag@ lf-tag-proj = ;
: lf-proj-name ( leaf -- name ) lf-term-first@ ;
: lf-proj-idx ( leaf -- i ) lf-term-second@ ;
\ A leaf's fields as a graph check reads them: a name of this context and
\ an index that is no negative cell (walk-visit's first and second).
: lf-proj-fields? ( first second -- flag ) 0< 0= swap lf-name-valid? and ;
: lf-proj-check ( first second walk -- outcome ) drop lf-proj-fields? flag>outcome ;
