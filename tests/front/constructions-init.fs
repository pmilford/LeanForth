\ LeanForth's generated definitions against Lean's own (plan row FE6;
\ tests/front/constructions-init.sh): an export read into a stage with its
\ manifest; for every inductive type of it whose T.casesOn, T.recOn or
\ T.ctorIdx Lean generated, the definition built by src/front/ is
\ compared node for node with Lean's (type, value, universe parameters).
\ Prints, for each one built, its binders in pre-order ("sig NAME<tab>
\ type's<tab>value's", as tests/reference/constructions-binders.lean
\ prints Lean's environment's, names without macro scopes), the
\ different and unsupported ones by name (with the reason), then per
\ construction the types with one in the export and how many were equal,
\ equal but for binder names and information (the kernel ignores them,
\ and Lean's exporter shares terms equal but for them, so an export's
\ names need not be the generator's), different and unsupported. Usage:
\   gforth tests/front/constructions-init.fs -e 's" EXPORT" fe6-report bye'
require ../../src/front/ctor-idx.fs
require ../../src/front/cases-several.fs

create init /stage allot
create job /aux allot
: tier ( -- tier ) job aux-tier ;
\ A compact name, its parts joined by dots (recursive: names are shallow).
: part. ( n -- )
  dup tier name-tag@ tag-name-str = if tier name-text@ type
  else tier name-number@ 0 .r then ;
: name. ( n -- )
  dup 0= if drop exit then
  dup tier name-prefix@ dup if recurse ." ." else drop then
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

\ ---- Binders in pre-order: binder, domain, body; function, argument.
variable first-binder
: sep ( -- ) first-binder @ if false first-binder ! else space then ;
\ A name without its macro scopes: the parts before a _@ part.
: scoped? ( n -- flag )
  dup tier name-tag@ tag-name-str =
  if tier name-text@ s" _@" compare 0= else drop false then ;
: erased ( n -- n' )
  dup begin dup while dup scoped? if nip dup tier name-prefix@ swap then
  tier name-prefix@ repeat drop ;
: binder-name. ( n -- ) erased ?dup if name. else ." [anonymous]" then ;
defer binders.
: binder. ( e -- )
  sep dup tier expr-head@ head-payload binder-name. ." :"
  dup tier expr-tag@ tag-lam - 3 and 0 .r
  dup tier expr-a@ binders. tier expr-b@ binders. ;
: let. ( e -- )
  sep dup tier expr-head@ head-payload binder-name. ." :let"
  dup tier expr-a@ binders. dup tier expr-b@ binders. tier expr-body@ binders. ;
: (binders.) ( e -- )
  dup tier expr-tag@ dup binder-tag? if drop binder. exit then
  dup let-tag? if drop let. exit then
  dup tag-app = if drop dup tier expr-a@ binders. tier expr-b@ binders. exit then
  dup tag-proj = swap tag-mdata = or if tier expr-a@ binders. else drop then ;
' (binders.) is binders.
: sig. ( e -- ) true first-binder ! binders. ;
: signature. ( k -- )
  ." sig " which. 9 emit job aux-type@ sig. 9 emit job aux-value@ sig. cr ;

: compared ( d' k -- )
  over job aux-same? if 1 bump drop exit then
  swap job aux-alike? if 2 bump exit then
  dup 3 bump ." different " which. cr ;
: verdict ( d' outcome k -- )
  dup 0 bump swap ok? if dup signature. compared exit then
  nip dup 4 bump ." unsupported " which. ." : " why. cr ;
: try-one ( d xt c-addr u k -- )
  >r 2>r over job aux-type ! 2r> lean-decl 0= if 2drop r> drop exit then
  -rot job swap execute r> verdict ;
: count. ( k col -- ) tally @ 0 .r ;
: line. ( k -- )
  dup suffix. ."  generated " dup 0 count. ."  equal " dup 1 count.
  ."  equal-up-to-binders " dup 2 count. ."  different " dup 3 count.
  ."  unsupported " 4 count. cr ;
\ A type Lean made no ctorIdx for, whose one LeanForth builds (review
\ fe6a-2 N1: Lean's other conditions are not in an export).
: extra-idx ( d -- ) job aux-ctor-idx ok? if ." extra " 2 which. cr then ;
: idx-one ( d -- )
  dup job aux-type ! s" ctorIdx" lean-decl
  if drop ['] aux-ctor-idx s" ctorIdx" 2 try-one else extra-idx then ;
: each-type ( -- )
  init stage-decls 0 ?do i kind? if
    i ['] aux-cases-on-any s" casesOn" 0 try-one i ['] aux-rec-on s" recOn" 1 try-one
    i idx-one then
  loop ;
: fe6-report ( export-addr export-u -- )
  tallies kinds columns * cells erase
  12 init stage-init drop init stage-load dup ok? 0= if ." export " 0 .r cr exit then drop
  init job aux-init dup ok? 0= if ." job " 0 .r cr exit then drop
  each-type 0 line. 1 line. 2 line. job aux-free ;
