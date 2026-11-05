\ Let terms (plan task 4.2.3; ADR 0014 Q7): Lean's Expr.letE x T v b,
\ "let x : T := v; b". LeanForth stores one as the application of a let
\ leaf to v, applied in turn to fun x : T => b:
\   app (app LEAF v) (lam T b)
\ The leaf, tag lf-tag-let, holds Lean's nonDep flag (first field 0 or 1,
\ second 0), which Lean's == compares (Expr.eqv; binder names are
\ dropped, as Lean's == ignores them). So every pass that does not look at
\ let terms treats one as an application of an opaque head, as Lean's do
\ treat Expr.letE's children (instantiate, lift_loose_bvars, abstract,
\ has_loose_bvars, instantiate_lparams): T and v at the let's own depth,
\ b one binder deeper -- exactly the lambda's domain and body. The places
\ where Lean treats Expr.letE specially find the let term itself, the
\ outer application (lf-let?): the spine (Lean's get_app_fn stops at a
\ let, kernel/mixed-head.fs), inference (infer_let, kernel/mixed-infer.fs),
\ whnf_core (zeta, kernel/whnf.fs), == (the leaf's flag,
\ kernel/mixed-compare.fs) and the derivation log. A leaf anywhere else,
\ or a let term whose second argument is no lambda (lf-let-well?), is
\ malformed: invalid where a pass interprets it.
\ Words: lf-tag-let, lf-let-leaf?, lf-let?, lf-let-well?, lf-let-value,
\ lf-let-binder, lf-let-type, lf-let-body, lf-let-nondep, lf-let-check
\ (the audit's), lf-hterm-let-fn and lf-let-make (constructors).
\ Example: with handles v and fun x : T => b, ( v vid 0 ) lf-hterm-let-fn
\ then ( lam lid ) lf-hterm-app is let x : T := v; b.
\ Untrusted [import][kernel] data; nothing here checks types.
\ State: none of its own; the nodes go into the term store (terms.fs).

require ../lib/lib.fs
require ./generation-handles.fs
require ./terms.fs

12 constant lf-tag-let

\ Whether node is a let leaf; whether it is a let term: an application
\ whose function is the application of a let leaf (to the value).
\ Unchecked: node is valid (its children then are).
: lf-let-leaf? ( node -- flag ) lf-term-tag@ lf-tag-let = ;
: lf-let-app? ( node -- flag ) lf-term-tag@ lf-tag-app = ;
: lf-let-fn? ( node -- flag )
  dup lf-let-app? if lf-term-first@ lf-let-leaf? else drop false then ;
: lf-let? ( node -- flag )
  dup lf-let-app? if lf-term-first@ lf-let-fn? else drop false then ;

\ The parts of a let term (lf-let? holds): v, fun x : T => b, T, b and
\ the nonDep flag; well formed when the second argument is a lambda.
: lf-let-value ( let -- v ) lf-term-first@ lf-term-second@ ;
: lf-let-binder ( let -- lam ) lf-term-second@ ;
: lf-let-type ( let -- T ) lf-let-binder lf-term-first@ ;
: lf-let-body ( let -- b ) lf-let-binder lf-term-second@ ;
: lf-let-nondep ( let -- flag ) lf-term-first@ lf-term-first@ lf-term-first@ 0<> ;
: lf-let-well? ( let -- flag ) lf-let-binder lf-term-tag@ lf-tag-lam = ;

\ A leaf's fields as the audit (core/constant-term-boundary.fs) reads
\ them: the flag 0 or 1, and 0.
: lf-let-check ( first second walk -- outcome ) drop 0= swap 0 2 within and flag>outcome ;

\ Constructors. A leaf for the flag (any true flag is 1); the application
\ of it to the value v (a handle), which applied to fun x : T => b is the
\ let term; a failed allocation (full store, spent serial) gives false.
: lf-let-leaf ( nondep -- index true | false ) 0<> 1 and lf-tag-let swap 0 lf-term-add ;
: lf-hterm-let-fn ( v vid nondep -- index identity true | false )
  lf-let-leaf lf-hterm-result 0= if 2drop false exit then 2swap lf-hterm-app ;
\ The let term of value v and lam = fun x : T => b, from live nodes the
\ caller checked (inference's results): the leaf, then the two
\ applications.
: lf-let-make ( v lam nondep -- let true | false )
  lf-let-leaf 0= if 2drop false exit then
  rot lf-term-app 0= if drop false exit then swap lf-term-app ;
