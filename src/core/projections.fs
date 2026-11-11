\ Projections (plan task 5.2.2; ADR 0015 rules J1, J2; compact-store
\ plan step S5): Lean's Expr.proj S i e, field i of e, a value of the
\ structure S. LeanForth stores it as a binary node of its own,
\   PROJECTION (leaf, e)
\ tag lf-tag-projection (core/terms.fs), whose first child is a
\ projection leaf, tag lf-tag-proj, holding S's name ID (first) and i
\ (second). So every pass that does not look at projections treats one as
\ a node with a closed leaf and e as children, as Lean's do treat
\ Expr.proj (instantiate, lift_loose_bvars, abstract, has_loose_bvars,
\ instantiate_lparams: one child, no binder, no level). An input proj
\ record (C1: the name, e and i) is read in place in this shape
\ (core/terms.fs's input view). The places where Lean treats Expr.proj
\ specially find the node by its tag (lf-proj?), alone or at the head of
\ a spine (applied to more arguments, (e.i) a): inference (infer_proj,
\ kernel/mixed-infer.fs), reduction (reduce_proj in whnf_core,
\ kernel/iota.fs behind whnf.fs's hook), comparison and printing. A leaf
\ is never a term of its own: a pass that meets one other than as a
\ projection's first child treats it as malformed (invalid).
\ Untrusted [import][kernel] data; nothing here checks types.
\ State: none of its own; the nodes go into the term store.

require ../lib/lib.fs
require ./generation-handles.fs
require ./names.fs
require ./terms.fs

10 constant lf-tag-proj
\ An input proj record carries its leaf, a leaf of the view's table
\ (core/terms.fs's input view).
lf-tag-proj lf-tin-proj-leaf tag-proj lf-term-input-leaf-twin
\ A leaf for field idx of the structure named name (a name ID of this
\ context), as a handle: (index identity true), or false for a negative
\ name or index, a full store or a spent serial.
: lf-hterm-proj ( name idx -- index identity true | false )
  2dup or 0< if 2drop false exit then
  lf-tag-proj -rot lf-term-add lf-hterm-result ;
\ The projection of a leaf and e, from live handles.
: lf-hterm-projection ( leaf lid e eid -- index identity true | false )
  lf-tag-projection lf-hterm-binary ;
\ Lean's mk_proj(S, i, e): the projection of field i of the structure
\ named name of e, a new node; full without room.
: lf-proj-of ( e name i -- node outcome )
  lf-hterm-proj 0= if drop -1 outcome-full exit then
  drop swap lf-tag-projection lf-term-binary if outcome-ok else -1 outcome-full then ;
\ Whether node is a projection; whether it is a projection leaf; a leaf's
\ structure name and index.
: lf-proj? ( node -- flag ) lf-term-tag@ lf-tag-projection = ;
: lf-proj-leaf? ( node -- flag ) lf-term-tag@ lf-tag-proj = ;
: lf-proj-name ( leaf -- name ) lf-term-first@ ;
: lf-proj-idx ( leaf -- i ) lf-term-second@ ;
\ A projection's leaf and its structure term e. Unchecked: lf-proj? holds.
: lf-proj-leaf ( node -- leaf ) lf-term-first@ ;
: lf-proj-struct ( node -- e ) lf-term-second@ ;
\ A leaf's fields as a graph check reads them: a name of this context and
\ an index that is no negative cell (walk-visit's first and second).
: lf-proj-fields? ( first second -- flag ) 0< 0= swap lf-name-valid? and ;
: lf-proj-check ( first second walk -- outcome ) drop lf-proj-fields? flag>outcome ;
