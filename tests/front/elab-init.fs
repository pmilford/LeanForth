\ LeanForth's side of the comparison with pinned Lean on all of Init
\ (tests/front/elab-init.sh; plan row FE1d): Init's export read into a
\ stage with its manifest, its elaboration data read and checked against
\ it (src/front/elab-data.fs), then printed as tests/reference/
\ elab-data-counts.lean prints Lean's: the records of each kind, the
\ declarations of each reducibility status, and the same samples, found
\ here by name in the data read. Usage:
\   gforth tests/front/elab-init.fs -e 's" EXPORT" s" DATA" elab-init-report bye'
require ../../src/front/elab-data.fs

create init /stage allot
: part ( n c-addr u -- n' ) init stage-tier name-seek-str drop ;
: decl ( n -- d ) init stage-find 0= if -1 then ;
: top ( c-addr u -- d ) 0 -rot part decl ;
: nat ( c-addr u -- d ) 0 s" Nat" part -rot part decl ;
: .n ( n -- ) 0 .r ;
: line ( c-addr u n -- ) >r type space r> .n cr ;
: kinds. ( -- )
  s" instance" elab-instance elab-count line
  s" default_instance" elab-default elab-count line
  s" eliminator" elab-eliminator elab-count line
  s" reducibility" elab-reducibility elab-count line ;
\ The declarations of status s.
: with-status ( s -- n )
  0 init stage-decls 0 ?do over i elab-status = - loop nip ;
: statuses. ( -- )
  s" status implicit_reducible" elab-implicit-reducible with-status line
  s" status instance_reducible" elab-instance-reducible with-status line
  s" status irreducible" elab-irreducible with-status line
  s" status reducible" elab-reducible with-status line ;
\ The priority of instance inst of class, of default instance inst of
\ class, as the data read says; Nat's eliminator of a kind.
: instance? ( inst class -- prio true | false )
  swap elab-instance-of 0= if drop false exit then
  elab-instance@ >r nip = r> swap if true else drop false then ;
: default? ( class inst -- prio true | false )
  elab-default elab-count 0 ?do
    2dup i elab-default@ >r d= if 2drop r> true unloop exit then r> drop
  loop 2drop false ;
: found? ( kind c-addr u -- flag )
  nat >r s" Nat" top swap elab-eliminator-for
  if elab-eliminator@ nip r> = else r> drop false then ;
: priority. ( prio true | false -- ) if .n else ." none" then cr ;
: instance. ( inst-addr inst-u class-addr class-u -- )
  ." sample instance " 2over type space 2dup type space
  top -rot top swap instance? priority. ;
: default. ( class-addr class-u inst-addr inst-u -- )
  ." sample default " 2over type space 2dup type space
  2swap top -rot top default? priority. ;
: eliminator. ( kind c-addr u -- )
  ." sample eliminator " 2 pick elab-induction = if ." induction" else ." cases" then
  ."  Nat " 2dup 2>r found? if ." Nat." 2r> type else 2r> 2drop ." ?" then cr ;
: samples. ( -- )
  s" instAddNat" s" Add" instance. s" instOfNatNat" s" OfNat" instance.
  s" HAdd" s" instHAdd" default. s" OfNat" s" instOfNatNat" default.
  elab-cases s" casesAuxOn" eliminator. elab-induction s" recAux" eliminator. ;
: elab-init-report ( export-addr export-u data-addr data-u -- )
  12 init stage-init drop 2swap init stage-read ." export " .n cr
  init init stage-manifest manifest-digest elab-read dup ." read " .n cr
  ok? if kinds. statuses. samples. else elab-error type ."  at line " .n cr then ;
