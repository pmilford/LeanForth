\ LeanForth's side of tests/front/check_whnf.py's build cases (plan slice
\ a2-i, the tactic library): tests/front/whnf-cases.fs's slice, variables
\ and printer, with src/front/app-builder.fs and the free variables
\ e : a = b and u v : Nat -> Nat besides (in pinned Lean's setup they come
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
: .built ( outcome -- ) dup outcome-rejected = if drop ." rejected" else .outcome then ;
: build-run ( xt -- ) 0 1 lf-meta-catch dup ok? if drop .t else nip .built then cr ;
