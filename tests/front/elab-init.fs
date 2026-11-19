\ LeanForth's side of the comparison with pinned Lean on all of Init
\ (tests/front/elab-init.sh; plan rows FE1d and FE1e1): Init's export read
\ into a stage with its manifest, its elaboration data read and checked
\ against it (src/front/elab-data.fs), then printed as tests/reference/
\ elab-data-counts.lean prints Lean's: the records of each kind, the
\ declarations of each reducibility status, and the same samples, found
\ here by name in the data read (instances, default instances, keys,
\ HAdd's out-parameters, tags, a matcher, a projection, Nat's
\ eliminators). Usage:
\   gforth tests/front/elab-init.fs -e 's" EXPORT" s" DATA" elab-init-report bye'
require ../../src/front/elab-data.fs

create init /stage allot
: tier ( -- tier ) init stage-tier ;
: part ( n c-addr u -- n' ) tier name-seek-str drop ;
: decl ( n -- d ) init stage-find 0= if -1 then ;
: top ( c-addr u -- d ) 0 -rot part decl ;
: nat ( c-addr u -- d ) 0 s" Nat" part -rot part decl ;
\ A dotted name of string parts, its declaration.
: next-part ( c-addr u -- c-addr' u' part-addr part-u )
  2dup [char] . scan 2swap 2 pick - >r >r dup if 1 /string then r> r> ;
: dotted ( c-addr u -- d )
  0 -rot begin dup while next-part 2>r rot 2r> part -rot repeat 2drop decl ;
: .n ( n -- ) 0 .r ;
: line ( c-addr u n -- ) >r type space r> .n cr ;
\ A tier name and a declaration's name, dotted, as Lean prints them unescaped.
: .part ( n -- )
  dup tier name-tag@ tag-name-str = if tier name-text@ type else tier name-number@ .n then ;
: .dotted ( n -- ) dup tier name-prefix@ ?dup if recurse ." ." then .part ;
: .decl ( d -- ) init staged-name@ .dotted ;
: kinds. ( -- )
  s" instance" elab-instance elab-count line
  s" instance_left_out" elab-left-out elab-count line
  s" class" elab-class elab-count line
  s" default_instance" elab-default elab-count line
  s" eliminator" elab-eliminator elab-count line
  s" reducibility" elab-reducibility elab-count line
  s" tag" elab-tag elab-count line
  s" matcher" elab-matcher elab-count line
  s" projection" elab-projection elab-count line
  s" sunfold" elab-sunfold elab-count line
  s" binder_kinds" elab-binders elab-count line ;
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
\ Keys as the Lean side prints them: NAME/ARITY, NAME#IDX/ARITY, digits,
\ "text", *, other, arrow.
: .key-decl ( k -- ) dup elab-key-decl .decl ;
: .key ( k -- )
  dup elab-key-tag case
    elab-key-const of .key-decl ." /" elab-key-arity .n endof
    elab-key-proj of .key-decl ." #" dup elab-key-idx .n ." /" elab-key-arity 1- .n endof
    elab-key-lit of elab-key-text type endof
    elab-key-str of [char] " emit elab-key-text type [char] " emit endof
    elab-key-star of drop ." *" endof
    elab-key-other of drop ." other" endof
    elab-key-arrow of drop ." arrow" endof
    swap drop ." foreign"
  endcase ;
: keys. ( c-addr u -- )
  ." sample keys " 2dup type ." :" dotted elab-instance-of
  if elab-instance-keys over + swap ?do space i .key loop then cr ;
: .commas ( addr n -- ) 0 ?do i if ." ," then dup i cells + @ .n loop drop ;
: class. ( -- )
  ." sample class HAdd " s" HAdd" top elab-class-of drop dup elab-class-out-params .commas
  space elab-class-out-levels .commas cr ;
create tag-names
  s" elab_as_elim" counted, s" elab_without_expected_type" counted, s" aux_recursor" counted,
  s" no_confusion" counted, s" cases_on" counted, s" rec_on" counted, s" brec_on" counted,
: tag-name ( tag -- c-addr u ) tag-names swap 0 ?do key-next loop count ;
: tags. ( c-addr u -- )
  ." sample tags " 2dup type ." :" dotted
  7 0 do dup i elab-tagged? if space i tag-name type then loop drop cr ;
: alts. ( m -- ) elab-matcher-alts 0 ?do i if ." ," then dup i + elab-alt@ 2drop .n loop drop ;
: matcher. ( -- )
  ." sample matcher Nat.add.match_1 " s" Nat.add.match_1" dotted elab-matcher-of drop
  dup elab-matcher@ rot drop swap .n space .n space
  dup elab-matcher-elim if .n else ." none" then space alts. cr ;
: projection. ( -- )
  ." sample projection Add.add " s" Add.add" dotted elab-projection-of drop
  dup elab-projection@ rot .decl space swap .n space .n space
  elab-projection-class? if ." true" else ." false" then cr ;
: samples. ( -- )
  s" instAddNat" s" Add" instance. s" instOfNatNat" s" OfNat" instance.
  s" HAdd" s" instHAdd" default. s" OfNat" s" instOfNatNat" default.
  elab-cases s" casesAuxOn" eliminator. elab-induction s" recAux" eliminator.
  s" instOfNatNat" keys. s" Lean.Grind.instIsCharPUInt64OfNatNat" keys.
  s" Lean.TSyntax.instCoeStrLitTerm" keys. s" Decidable.predToBool" keys.
  s" boolToProp" keys. s" ShareCommon.instInhabitedState" keys.
  class. s" Nat.casesOn" tags. s" Nat.brecOn" tags. s" Nat.rec" tags. s" Eq.ndrec" tags.
  matcher. projection. ;
: elab-init-report ( export-addr export-u data-addr data-u -- )
  12 init stage-init drop 2swap init stage-read ." export " .n cr
  init init stage-manifest manifest-digest elab-read dup ." read " .n cr
  ok? if kinds. statuses. samples. else elab-error type ."  at line " .n cr then ;
