\ LeanForth's side of tests/front/check_whnf.py's build cases (plan slice
\ a2-i, the tactic library): tests/front/whnf-cases.fs's slice, variables
\ and printer, with src/front/app-builder.fs and the free variables
\ e : a = b, u v : Nat -> Nat and w : u = v besides (in pinned Lean's setup they come
\ before the metavariables; no build case reads a metavariable's
\ context). build-run ( xt -- ) prints the term the xt's builder makes, or
\ "rejected" for Lean's AppBuilder exception (the rejected outcome),
\ "unsupported" or the outcome's name otherwise. Kept apart from
\ whnf-cases.fs, which unit tests load, so that their heap and store
\ state stays as it was. Test support only.

require ./whnf-cases.fs
require ../../src/front/app-builder.fs

: eq1 ( α a b -- t ) >r >r lv1 1 s" Eq" cn swap app r> app r> app ;
nat fa fb eq1 char e local constant fe
nat nat tpi char u local constant fu   nat nat tpi char v local constant fv
nat nat tpi fu fv eq1 char w local constant fw
: .built ( outcome -- ) dup outcome-rejected = if drop ." rejected" else .outcome then ;
: build-run ( xt -- ) 0 1 lf-meta-catch dup ok? if drop .t else nip .built then cr ;
\ Plan S3a: the metavariable ?r := 2 (after w, as in pinned Lean's
\ setup), whnfD's cases (reduceNat?), and decide (10 < 20)'s terms.
nat mv-natural lf-mvar-new made constant ?r  ?r char r named
0 ?r 2 nat-lit lf-mvar-assign made drop
: whnfd-run ( term -- ) lf-meta-whnf-d dup ok? if drop .t else nip .outcome then cr ;
: lt-10-20 ( -- t ) l0 1 s" LT.lt" cn nat app 0 s" instLTNat" cn app 10 nat-lit app 20 nat-lit app ;
: declt-10-20 ( -- t ) 0 s" Nat.decLt" cn 10 nat-lit app 20 nat-lit app ;
