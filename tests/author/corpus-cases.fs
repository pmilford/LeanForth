\ The round trip over the term printer's cases (plan task 8.1.2): every
\ term of tests/present/print-case-list.fs, built as Lean builds the
\ expression of the same name (tests/reference/printer-cases.lean), is
\ printed as LeanForth words and run in a new context as the statement of
\ an axiom, after an import stub for each constant it names and with a
\ universe line for each universe parameter it uses; the terms (dump.fs)
\ and the printed words must be the same. Prints one line per case:
\ case NAME: round trip: ...
\ Test-only; not a public interface.
require ../present/build.fs
require ./report.fs

\ The constants and universe parameters a term uses.
16 constant most
create consts most 2* cells allot  variable consts#
create params most cells allot  variable params#
: const@ ( i -- name count ) 2* cells consts + 2@ ;
: has-const? ( name -- flag )
  consts# @ 0 ?do dup i const@ drop = if drop true unloop exit then loop drop false ;
: add-const ( name count -- )
  over has-const? if 2drop exit then consts# @ 2* cells consts + 2! 1 consts# +! ;
: has-param? ( name -- flag )
  params# @ 0 ?do dup i cells params + @ = if drop true unloop exit then loop drop false ;
: add-param ( name -- ) dup has-param? if drop exit then params# @ cells params + ! 1 params# +! ;
: scan-term-level ( l -- )
  dup lf-level-tag@ case
    lf-level-tag-param of lf-level-first@ add-param endof
    lf-level-tag-succ of lf-level-first@ recurse endof
    lf-level-tag-max of dup lf-level-first@ recurse lf-level-second@ recurse endof
    lf-level-tag-imax of dup lf-level-first@ recurse lf-level-second@ recurse endof
    nip endcase ;
: scan-term-levels ( addr n -- ) 0 ?do dup i lf-cref-pair@ drop scan-term-level loop drop ;
: scan-term-const ( term -- )
  lf-term-first@ dup lf-cref-current 2dup lf-cref-read 0= abort" corpus: reference"
  nip add-const lf-cref-levels drop scan-term-levels ;
: scan-term ( term -- )
  dup lf-term-tag@ case
    lf-tag-constant of scan-term-const endof
    lf-tag-symbolic-sort of lf-term-first@ scan-term-level endof
    lf-tag-app of dup lf-term-first@ recurse lf-term-second@ recurse endof
    lf-tag-lam of dup lf-term-first@ recurse lf-term-second@ recurse endof
    lf-tag-pi of dup lf-term-first@ recurse lf-term-second@ recurse endof
    nip endcase ;

\ The text to run: the stubs, then axiom corpus_case with the universes
\ and the term's words (words1), then end.
create src-buf 8192 allot  variable src-buf#
: src ( c-addr u -- ) tuck src-buf src-buf# @ + swap move src-buf# +! ;
: src-name ( id -- ) ['] src lf-print-unicode lf-print-setup lf-print-name ok? 0= abort" name" ;
: src# ( n -- ) 0 <# #s #> src ;
: stub ( name count -- )
  s" import-stub " src over src-name 0 ?do s"  universe s" src i src# loop
  s"  end " src src-name s"  " src ;
: stubs ( -- ) consts# @ 0 ?do i const@ stub loop ;
: universes ( -- ) params# @ 0 ?do s"  universe " src i cells params + @ src-name loop ;
: axiom-text ( -- c-addr u )
  0 src-buf# ! stubs s" axiom corpus_case" src universes s"  " src
  words1 words1# @ src s"  end corpus_case" src src-buf src-buf# @ ;

\ The round trip of term t.
variable the-term
: case-words ( -- outcome ) to-capture the-term @ print-fuel lf-print-forth-term ;
: case-dump ( -- ) the-term @ dump-term ;
: last-type ( -- term ) lf-author-count 1- lf-author-decl lf-fdecl-type @ ;
: case-second ( -- outcome )
  lf-author-begin lf-author-kernel src-buf src-buf# @ lf-author-text dup ok? 0= if exit then
  drop
  last-type the-term ! words2 words2# capture-into case-words dup ok? 0= if exit then drop
  dump2 dump2# capture-into case-dump outcome-ok ;
: case-trip ( t -- )
  dup the-term ! 0 consts# ! 0 params# ! scan-term
  words1 words1# capture-into case-words ok? 0= abort" corpus: print failed"
  dump1 dump1# capture-into case-dump axiom-text 2drop
  ['] case-second in-new-context ['] type lf-print-unicode lf-print-setup
  dup ok? 0= if ." round trip: the printed words did not run (" outcome-text type ." )" cr
    exit then drop
  ." round trip: terms, names, kinds, labels and notes "
  dump1 dump1# @ dump2 dump2# @ same? .same
  ." ; printed text " words1 words1# @ words2 words2# @ same? .same cr ;

: uni ( xt c-addr u -- ) ." case " type ." : " fresh execute case-trip ;
: univ ( xt c-addr u -- ) uni ;
require ../present/print-case-list.fs
bye
