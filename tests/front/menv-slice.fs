\ Test support for the front end's environment view (plan FE1c;
\ src/front/meta-env.fs): tests/front/whnf-slice.ndjson, a slice of
\ pinned Lean's Init export (scripts/export-slice.py: Nat.add, HAdd.hAdd,
\ instHAdd, id, Nat.div, Nat.zero_add, Quot.lift, Eq.ndrec, ... and their
\ closure), staged with its manifest, its elaboration data
\ (tests/front/whnf-slice.elab.ndjson, scripts/export-elab.sh: format 3.2,
\ with the smart-unfolding bodies of the slice's definitions and seven
\ binder_kinds records) read
\ against the stage, sealed and fed to this context. menv-load does it
\ all and names the stage to meta-env.fs; menv-name ( c-addr u -- name )
\ gives the name of a dotted text, string parts only, looked up through
\ the context's scratch tier of names, which finds the stage's (a part no
\ name has aborts). Test-only.

require ../../src/front/meta-env.fs
require ../../src/import/feed.fs

create menv-lib /stage allot
create menv-feed /feed allot
: menv-slice ( -- c-addr u ) s" tests/front/whnf-slice.ndjson" ;
\ The elaboration data menv-load reads; a test may name another first.
defer menv-data ( -- c-addr u )
:noname ( -- c-addr u ) s" tests/front/whnf-slice.elab.ndjson" ; is menv-data
: menv-digest ( -- sha ) menv-lib stage-manifest manifest-digest ;
: menv-must ( outcome -- ) ok? 0= abort" menv-slice: a loading step failed" ;
: menv-read ( -- ) menv-data menv-lib menv-digest elab-read menv-must ;
: menv-load ( -- )
  14 menv-lib stage-init menv-must menv-slice menv-lib stage-read menv-must menv-read
  menv-lib stage-seal menv-must menv-lib menv-feed lf-feed menv-must menv-lib lf-menv-stage! ;

: menv-part ( n c-addr u -- n' )
  lf-name-tier name-seek-str menv-must dup 0< abort" menv-slice: no such name" ;
: menv-split ( c-addr u -- part-addr part-u rest-addr rest-u )
  2dup s" ." search if 2swap 2 pick - 2swap 1 /string else 2drop 0 0 then ;
: menv-name ( c-addr u -- name )
  0 -rot begin dup while menv-split 2>r menv-part 2r> repeat 2drop ;
: menv-decl ( c-addr u -- d ) menv-name lf-menv-find menv-must ;

