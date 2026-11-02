\ Experimental inference contract tests. Candidate signatures are assumptions;
\ a successful inference is not a checked theorem or declaration.
include ../../src/core/terms.fs
include ../../src/experimental/names.fs
include ../../src/experimental/levels.fs
include ../../src/experimental/level-scope.fs
include ../../src/experimental/tagged-sort-boundary.fs
include ../../src/experimental/symbolic-session.fs
include ../../src/experimental/generation-handles.fs
include ../../src/experimental/constant-references.fs
include ../../src/experimental/constant-term-boundary.fs
include ../../src/experimental/level-substitute.fs
include ../../src/experimental/mixed-level-substitute.fs
include ../../src/experimental/mixed-signature-probe.fs
include ../../src/experimental/constant-term-scope.fs
include ../../src/experimental/mixed-signature-audit.fs
include ../../src/experimental/mixed-compare.fs
include ../../src/experimental/mixed-shift.fs
include ../../src/experimental/mixed-instantiate.fs
include ../../src/experimental/mixed-beta.fs
include ../../src/experimental/level-value.fs
include ../../src/experimental/level-compare.fs
include ../../src/experimental/mixed-convert.fs
include ../../src/experimental/mixed-infer.fs


\ Finite comparisons only. Candidate signature is assumed, not a declaration.
decimal
create ids 64 cells allot
create actuals 2 cells allot
create formals 1 cells allot
variable token variable id-name variable missing-name variable universe-level
: save ( index identity true | false -- ) 0= abort" allocation" swap cells ids + ! ;
: h ( index -- index identity ) dup cells ids + @ ;
: new-name ( addr len -- id ) 0 -rot lf-name-str 0= abort" name" ;
: actual ( level -- ) dup actuals ! lf-level-identity 0= abort" level id" actuals cell+ ! ;
: fixture-constant ( name -- index identity true | false )
  lf-name-generation @ actuals 1 lf-cref-new 0= abort" reference" lf-cterm-new ;
: setup ( universe -- )
  universe-level ! lf-name-reset lf-level-reset lf-term-reset
  lf-lscope-context-reset lf-cref-reset
  42 lf-lscope-context-add 0= abort" context"
  42 lf-level-param 0= abort" parameter" drop
  lf-ssession-begin 0= abort" session"
  s" fixtureId" new-name id-name ! s" missing" new-name missing-name !
  42 formals !
  1 dup lf-level-identity 0= abort" parameter id" lf-hterm-sort save \ 0 Sort parameter
  0 lf-hterm-bvar save                                            \ 1 v0
  1 lf-hterm-bvar save                                            \ 2 v1
  1 h 2 h lf-hterm-pi save                                       \ 3
  0 h 3 h lf-hterm-pi save                                       \ 4 signature
  0 universe-level @ 0 ?do lf-level-succ 0= abort" level successor" loop
  dup actual
  dup lf-level-identity 0= abort" level id" lf-hterm-sort save  \ 5 Sort u
  id-name @ fixture-constant save                                        \ 6 id.{u}
  6 h 2 h lf-hterm-app save                                      \ 7 id A
  7 h 1 h lf-hterm-app save                                      \ 8 id A x
  7 h 8 h lf-hterm-app save                                      \ 9 id A (id A x)
  1 h 8 h lf-hterm-lam save 5 h 10 h lf-hterm-lam save          \ 11 poly
  1 h 9 h lf-hterm-lam save 5 h 12 h lf-hterm-lam save           \ 13 nested
  5 h 3 h lf-hterm-pi save                                       \ 14 expected poly
  actuals @ lf-level-succ 0= abort" successor" actual
  id-name @ fixture-constant save                                        \ 15 id.{u+1}
  15 h 5 h lf-hterm-app save 16 h 1 h lf-hterm-app save
  5 h 17 h lf-hterm-lam save                                     \ 18 fun A => id (Sort u) A
  5 h 5 h lf-hterm-pi save                                       \ 19 expected type
  6 h 5 h lf-hterm-app save                                      \ 20 wrong universe
  missing-name @ fixture-constant save                                   \ 21 missing
  1 h 1 h lf-hterm-lam save                                      \ 22 open domain
  lf-msp-begin 0= abort" index" lf-msp-token 0= abort" token" token !
  token @ id-name @ 4 h formals 1 50000 lf-msp-put lf-msp-ok <> abort" signature" ;
: infer ( root -- type identity status ) h token @ -rot 50000 lf-mixed-infer ;
: positive ( root expected -- )
  >r infer lf-minfer-ok <> abort" expected inference success"
  r> h 50000 lf-mixed-convert lf-mconvert-equal <> abort" inferred type differs" ;
: negative ( root status -- )
  >r infer r> <> abort" unexpected status"
  0<> abort" failure identity" -1 <> abort" failure root" ;
: emit-cases ( -- )
  3 0 do
    i setup
    i . 0 . 6 14 positive ." OK" cr
    i . 1 . 11 14 positive ." OK" cr
    i . 2 . 13 14 positive ." OK" cr
    i . 3 . 18 19 positive ." OK" cr
    i . 4 . 20 lf-minfer-unknown negative ." UNKNOWN" cr
    i . 5 . 21 lf-minfer-unknown negative ." UNKNOWN" cr
    i . 6 . 22 lf-minfer-invalid negative ." INVALID" cr
  loop ;
emit-cases bye
