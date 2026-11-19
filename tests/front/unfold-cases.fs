\ LeanForth's side of tests/front/check_unfold.py (plan FE1c): for each
\ declaration named, one line as tests/front/unfold-cases.lean prints it
\ with pinned Lean: the name, its kind, its reducibility status, whether
\ getUnfoldableConst? gives it and whether canUnfold holds under each of
\ the six transparency modes (all, default, reducible, instances, none,
\ implicit; 1 or 0), and the facts matcher, projection function,
\ auxiliary recursor and smart unfolding (1, 0, or ? for unsupported).
\ Any other outcome prints "error" and the outcome. Test-only.
\   gforth tests/front/unfold-cases.fs -e 's" Nat.add" ucase bye'

require ./menv-slice.fs
menv-load

create uc-kinds
  s" none" counted, s" definition" counted, s" theorem" counted, s" axiom" counted,
  s" opaque" counted, s" quotient" counted, s" inductive" counted,
  s" constructor" counted, s" recursor" counted, 0 0 counted,
create uc-statuses
  s" semireducible" counted, s" reducible" counted, s" irreducible" counted,
  s" implicit_reducible" counted, s" instance_reducible" counted, 0 0 counted,
: uc-nth ( k table -- c-addr u ) swap counted-nth count ;
: uc-error ( outcome -- ) ." error " . ;
: uc-bit ( flag outcome -- )
  dup ok? if drop if ." 1" else ." 0" then exit then
  dup outcome-unsupported = if 2drop ." ?" else nip uc-error then ;
: uc-status ( d -- )
  lf-menv-status dup ok? if drop uc-statuses uc-nth type else nip uc-error then ;
: uc-modes ( d xt -- )
  space lf-tr-modes 0 ?do 2dup i swap execute uc-bit loop 2drop ;
: uc-unfoldable ( d mode -- flag outcome ) swap lf-menv-name swap lf-menv-unfoldable rot drop ;
: uc-fact ( d xt -- ) space execute uc-bit ;
: uc-facts ( d -- )
  dup ['] lf-menv-matcher? uc-fact dup ['] lf-menv-proj-fn? uc-fact
  dup ['] lf-menv-aux-recursor? uc-fact ['] lf-menv-smart? uc-fact ;
: ucase ( c-addr u -- )
  2dup type space menv-decl dup lf-menv-kind uc-kinds uc-nth type space dup uc-status
  dup ['] uc-unfoldable uc-modes dup ['] lf-menv-can-unfold uc-modes uc-facts cr ;
