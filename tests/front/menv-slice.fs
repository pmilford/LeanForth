\ Test support for the front end's environment view (plan FE1c;
\ src/front/meta-env.fs): tests/front/whnf-slice.ndjson, a slice of
\ pinned Lean's Init export (scripts/export-slice.py: Nat.add, HAdd.hAdd,
\ instHAdd, id, Nat.div, Nat.zero_add, Quot.lift, Eq.ndrec, ... and their
\ closure), staged with its manifest, its elaboration data
\ (tests/front/whnf-slice.elab.ndjson, scripts/export_elab.py) read
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
: menv-data ( -- c-addr u ) s" tests/front/whnf-slice.elab.ndjson" ;
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

\ The slice's smart-unfolding facts, until the elaboration data carries
\ them (plan S2 merge A; src/front/meta-env.fs, lf-menv-sunfold-source):
\ pinned Lean 4.35.0 (env.contains (mkSmartUnfoldingNameFor f), over all
\ 207 definitions of the slice, 2026-11-13) finds a `_sunfold` for these
\ 13 and none for the rest; tests/front/check_unfold.py compares the
\ answer with Lean's for its names. menv-sunfolds! installs it (after
\ menv-load). Test-only.
13 constant #menv-sunfolds
create menv-sunfolds #menv-sunfolds cells allot
: menv-sunfold-names ( -- c-addr1 u1 .. c-addr13 u13 )
  s" Nat.add" s" Nat.mul" s" Nat.pow" s" List.concat" s" List.toByteArray.loop"
  s" List.append" s" List.flatten" s" List.map" s" Nat.ble" s" Nat.beq" s" Nat.sub"
  s" Nat.modCore.go" s" Nat.div.go" ;
: menv-sunfold? ( d -- flag outcome )
  false #menv-sunfolds 0 ?do over menv-sunfolds i cells + @ = or loop nip outcome-ok ;
: menv-sunfolds! ( -- )
  menv-sunfold-names #menv-sunfolds 0 ?do menv-decl menv-sunfolds i cells + ! loop
  ['] menv-sunfold? is lf-menv-sunfold-source ;
