\ Terms without a data word in the checker's passes (core/terms.fs: a
\ bound variable of index lf-data-unknown or more, a concrete Sort leaf,
\ and every term above one; ADR 0016 C1, compact-store plan step S3).
\ Where Lean reads a node's cached flags (has_loose_bvars, has_fvar),
\ such a node asks the caches' memo (kernel/caches.fs's hook
\ lf-whnf-known, which knows nothing of it) and is then walked
\ (whnf.fs's scans, paid from the frames' fuel). Run inside the check of
\ a case of tests/core/check-block-cases/ (tests/support/case-sweeps.fs),
\ each in an inference job of its own whose scratch is rolled back.
\ Coverage classes of docs/development/TEST_COVERAGE_REVIEW.md:
\ 1, 7. has_loose_bvars: a variable beyond the binders around it is
\    loose, one bound inside is not, a leaf is not; has_fvar: a free
\    variable or a loose bound one counts, a closed term does not. The
\    answers with the caches on and off are the same.
\ 1, 7. whnf_core's zeta of a let whose value has no data word: the
\    value put for the variable (a closed value), lifted (an open one).
\ 5. The walks' fuel: none left is exhausted, with the diagnostic.
\ Test-only; nothing here accepts a theorem.
require ../support/case-sweeps.fs

\ Nodes, made in the job's scratch.
: var-u ( -- node ) lf-data-unknown lf-term-bvar cs-must ;
: var ( i -- node ) lf-term-bvar cs-must ;
: sort-c ( -- node ) 0 lf-term-sort cs-must ;
: lam ( T b -- node ) lf-term-lam cs-must ;
: app ( f a -- node ) lf-term-app cs-must ;
: dead-fvar ( -- node ) lf-tag-fvar 1000 0 lf-term-add cs-must ;
\ fun _ : Sort 0 => #0, closed; fun _ : Sort 0 => #1, open; f (Sort 0).
: closed-lam ( -- node ) sort-c 0 var lam ;
: open-lam ( -- node ) sort-c 1 var lam ;
: free-app ( -- node ) dead-fvar sort-c app ;
\ A job of its own; the answer of xt ( node frames -- flag outcome ) on
\ the node xt' ( -- node ) makes, the scratch rolled back after.
: job ( -- ) cs-plenty lf-minfer-start-env ;
: unjob ( -- ) outcome-ok lf-minfer-rollback drop ;
: asked ( xt' xt -- flag outcome ) job swap execute lf-minfer-frames rot execute unjob ;
: loose ( xt' -- flag outcome ) ['] lf-whnf-loose? asked ;
: free-of ( xt' -- flag outcome ) ['] lf-whnf-free? asked ;
: no-data? ( xt' -- flag ) job execute lf-term-data@ dup if nip then 0= unjob ;

: scans ( -- )
  T{ ['] var-u no-data? ['] closed-lam no-data? ['] free-app no-data? -> true true true }T
  T{ ['] var-u loose ['] open-lam loose ['] closed-lam loose ['] sort-c loose
     -> true outcome-ok true outcome-ok false outcome-ok false outcome-ok }T
  T{ ['] free-app free-of ['] open-lam free-of ['] closed-lam free-of
     -> true outcome-ok true outcome-ok false outcome-ok }T ;
\ The caches off: the hook answers nothing, the same walks run.
: scans-uncached ( -- ) false lf-caches-enable scans true lf-caches-enable ;
\ No fuel left: the walk is exhausted, with the scan's diagnostic.
: dry ( xt' xt -- flag outcome code )
  lf-diag-clear job swap execute lf-minfer-frames 0 over frame-fuel ! rot execute unjob
  lf-diag-code@ ;
: dry-scans ( -- )
  T{ ['] closed-lam ['] lf-whnf-loose? dry -> false outcome-exhausted lf-diag-fuel }T
  T{ ['] free-app ['] lf-whnf-free? dry -> false outcome-exhausted lf-diag-fuel }T ;
s" proj.data" ' scans outcome-ok cs-probe-gives
s" proj.data" ' scans-uncached outcome-ok cs-probe-gives
s" proj.data" ' dry-scans outcome-ok cs-probe-gives

\ ---------------------------------------------------------------------------
\ Zeta: let x : Sort 0 := v; #0 is v. A closed v (its scan finds no
\ loose variable) is put for #0 as it is: the result is v's own node; an
\ open one (v = #U, its scan stops at the loose variable) is put through
\ instantiate's lift, by no binder here: the variable #U again.
: let-of ( v -- node ) sort-c 0 var lam lf-tag-let lf-term-binary cs-must ;
: whnf ( node -- node' outcome ) lf-minfer-frames lf-whnf-on ;
: zeta ( -- )
  T{ job closed-lam dup let-of whnf -rot = unjob -> outcome-ok true }T
  T{ job var-u let-of whnf over lf-term-tag@ rot lf-term-first@ unjob
     -> outcome-ok lf-tag-bvar lf-data-unknown }T ;
s" proj.data" ' zeta outcome-ok cs-probe-gives

\ ---------------------------------------------------------------------------
\ Beta: (fun x : Prop => x #(U+1)) P is P #U. The body has no data word,
\ so instantiate (mixed-open.fs) asks the caches' hook whether it can be
\ kept, which knows nothing of it (or is off), and walks it: x becomes P
\ and the loose variable comes down by one.
variable beta-arg
: prop ( -- node ) 0 lf-term-symbolic-sort cs-must ;
: beta-of ( P -- node ) prop 0 var lf-data-unknown 1+ var app lam swap app ;
: beta-run ( -- node' outcome ) job prop dup beta-arg ! beta-of whnf ;
: parts ( node -- first tag index )
  dup lf-term-first@ swap lf-term-second@ dup lf-term-tag@ swap lf-term-first@ ;
: beta ( -- )
  T{ beta-run swap parts unjob -> outcome-ok beta-arg @ lf-tag-bvar lf-data-unknown }T
  false lf-caches-enable
  T{ beta-run swap parts unjob -> outcome-ok beta-arg @ lf-tag-bvar lf-data-unknown }T
  true lf-caches-enable ;
s" proj.data" ' beta outcome-ok cs-probe-gives
bye
