\ Let terms (plan task 4.2.3; ADR 0014 Q7; compact-store plan step S5):
\ Lean's Expr.letE x T v b, "let x : T := v; b". LeanForth stores one as
\ a binary node of its own over v and the binder of its body:
\   LET (v, fun x : T => b)
\ tag lf-tag-let, or lf-tag-let-nondep when Lean's nonDep flag is set,
\ which Lean's == compares (Expr.eqv; binder names are dropped, as Lean's
\ == ignores them). So every pass that does not look at let terms treats
\ one as a node with two children at its own depth, the second a lambda,
\ as Lean's do treat Expr.letE's children (instantiate, lift_loose_bvars,
\ abstract, has_loose_bvars, instantiate_lparams): T and v at the let's
\ own depth, b one binder deeper -- exactly the lambda's domain and body.
\ An input letE record (C1: type, value, and a second record holding the
\ body) is read in place in this shape (core/terms.fs's input view). The
\ places where Lean treats Expr.letE specially find the let node by its
\ tag (lf-let?): the spine (Lean's get_app_fn stops at a let,
\ kernel/mixed-head.fs: a let is no application), inference (infer_let,
\ kernel/mixed-infer.fs), whnf_core (zeta, kernel/whnf.fs), == (the tag,
\ kernel/mixed-compare.fs) and the derivation log. A let whose second
\ child is no lambda (lf-let-well?) is malformed: invalid where a pass
\ interprets it.
\ Words: lf-let?, lf-let-well?, lf-let-value, lf-let-binder, lf-let-type,
\ lf-let-body, lf-let-nondep, lf-let-tag (the tags are core/terms.fs's),
\ lf-hterm-let and lf-let-make (constructors).
\ Example: with handles v and fun x : T => b, ( v vid lam lid 0 )
\ lf-hterm-let is let x : T := v; b.
\ Untrusted [import][kernel] data; nothing here checks types.
\ State: none of its own; the nodes go into the term store (terms.fs).

require ../lib/lib.fs
require ./generation-handles.fs
require ./terms.fs

\ Whether node is a let term. Unchecked: node is valid (its children
\ then are).
: lf-let? ( node -- flag ) lf-let-tags lf-term-in? ;

\ The parts of a let term (lf-let? holds): v, fun x : T => b, T, b and
\ the nonDep flag; well formed when the second child is a lambda.
: lf-let-value ( let -- v ) lf-term-first@ ;
: lf-let-binder ( let -- lam ) lf-term-second@ ;
: lf-let-type ( let -- T ) lf-let-binder lf-term-first@ ;
: lf-let-body ( let -- b ) lf-let-binder lf-term-second@ ;
: lf-let-nondep ( let -- flag ) lf-term-tag@ lf-tag-let-nondep = ;
: lf-let-well? ( let -- flag ) lf-let-binder lf-term-lam? ;

\ Constructors: the let of value v and lam = fun x : T => b, the tag
\ from the flag (any true flag is nonDep). From live handles; or from
\ live nodes the caller checked (inference's results). A failed
\ allocation (full store, spent serial) gives false.
: lf-let-tag ( nondep -- tag ) if lf-tag-let-nondep else lf-tag-let then ;
: lf-hterm-let ( v vid lam lid nondep -- index identity true | false )
  lf-let-tag lf-hterm-binary ;
: lf-let-make ( v lam nondep -- let true | false ) lf-let-tag lf-term-binary ;
