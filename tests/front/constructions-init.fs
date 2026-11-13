\ LeanForth's generated definitions against Lean's own (plan row FE6;
\ tests/front/constructions-init.sh): an export read into a stage with its
\ manifest; for every inductive type of it whose T.casesOn or T.recOn
\ Lean generated, the definition built by src/front/constructions.fs is
\ compared node for node with Lean's (type, value, universe parameters).
\ Prints the different and unsupported ones by name (with the reason),
\ then per construction the types with one in the export and how many
\ were equal, equal but for binder names (the kernel ignores them, and
\ Lean's exporter shares terms equal but for them, so an export's names
\ need not be the generator's), different and unsupported. Usage:
\   gforth tests/front/constructions-init.fs -e 's" EXPORT" fe6-report bye'
require ../../src/front/ctor-idx.fs
require ../../src/front/cases-several.fs

create init /stage allot
create job /aux allot
\ A compact name, its parts joined by dots (recursive: names are shallow).
: part. ( n -- )
  dup init stage-tier name-tag@ tag-name-str = if init stage-tier name-text@ type
  else init stage-tier name-number@ 0 .r then ;
: name. ( n -- )
  dup 0= if drop exit then
  dup init stage-tier name-prefix@ dup if recurse ." ." else drop then
  part. ;
\ The tallies of each construction k: generated, equal, alike, different,
\ unsupported.
5 constant columns
3 constant kinds
create tallies kinds columns * cells allot
: tally ( k col -- addr ) swap columns * + cells tallies + ;
: bump ( k col -- ) tally 1 swap +! ;
: kind? ( d -- flag ) init staged-kind@ kind-type = ;
: lean-decl ( c-addr u -- d true | false ) job aux-named ;
: why. ( -- ) job aux-why @ ?dup if count type else ." (no reason)" then ;
: suffix. ( k -- )
  case 0 of ." casesOn" endof 1 of ." recOn" endof ." ctorIdx" endcase ;
: which. ( k -- ) job type-name name. ." ." suffix. ;
: compared ( d' k -- )
  over job aux-same? if 1 bump drop exit then
  swap job aux-alike? if 2 bump exit then
  dup 3 bump ." different " which. cr ;
: verdict ( d' outcome k -- )
  dup 0 bump swap ok? if compared exit then
  nip dup 4 bump ." unsupported " which. ." : " why. cr ;
: try-one ( d xt c-addr u k -- )
  >r 2>r over job aux-type ! 2r> lean-decl 0= if 2drop r> drop exit then
  -rot job swap execute r> verdict ;
: count. ( k col -- ) tally @ 0 .r ;
: line. ( k -- )
  dup suffix. ."  generated " dup 0 count. ."  equal " dup 1 count.
  ."  equal-up-to-binders " dup 2 count. ."  different " dup 3 count.
  ."  unsupported " 4 count. cr ;
: each-type ( -- )
  init stage-decls 0 ?do i kind? if
    i ['] aux-cases-on-any s" casesOn" 0 try-one i ['] aux-rec-on s" recOn" 1 try-one
    i ['] aux-ctor-idx s" ctorIdx" 2 try-one then
  loop ;
: fe6-report ( export-addr export-u -- )
  tallies kinds columns * cells erase
  12 init stage-init drop init stage-load dup ok? 0= if ." export " 0 .r cr exit then drop
  init job aux-init dup ok? 0= if ." job " 0 .r cr exit then drop
  each-type 0 line. 1 line. 2 line. job aux-free ;
