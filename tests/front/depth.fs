\ Test support: one metavariable depth deeper and back, as Lean's
\ withNewMCtxDepth (allowLevelAssignments false), through mvars.fs's
\ depth scopes (S1 §3): deeper opens one, shallower closes the latest,
\ rolling back what was assigned inside. depth-reset forgets them with
\ lf-mctx-reset. A refused scope aborts the test. Test-only.

require ../../src/front/mvars.fs

create depth-scopes 64 cells allot
variable #depth-scopes
: depth-top ( -- addr ) depth-scopes #depth-scopes @ cells + ;
: deeper ( -- )
  false lf-mctx-depth{ ok? 0= abort" deeper" depth-top ! 1 #depth-scopes +! ;
: shallower ( -- )
  -1 #depth-scopes +! depth-top @ }lf-mctx-depth ok? 0= abort" shallower" ;
: depth-reset ( -- ) lf-mctx-reset 0 #depth-scopes ! ;
