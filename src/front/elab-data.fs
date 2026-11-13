\ Elaboration data, first slice (plan row FE1d; ADR 0021 D10): the reader
\ of the file scripts/export-elab.sh writes with pinned Lean for a Lean
\ export -- instances with their class, priority and synthesis order,
\ default instances, reducibility and the induction and cases eliminators
\ -- checked against the export's names and kept for the elaborator
\ (FE1e: instances; FE1g: eliminators). Format version 1, one JSON object
\ per line: docs/programming/ELABORATION_DATA.md and
\ schemas/elab-data-1.schema.json. Untrusted and fail-closed: the data
\ never reaches the kernel, and nothing it holds can make a declaration
\ accepted; it can change what a statement means, which is why every
\ record is checked here and every statement is printed back.
\ LeanForth-specific (Lean's attributes, the importer stage's names).
\ Requires: lib/bytes.fs, json.fs, sha256.fs, htab.fs, hash32.fs, and
\ import/stage.fs (and through it import/manifest.fs's JSON helpers).
\
\ elab-read ( c-addr u stage sha -- outcome ) reads the file c-addr u
\ against a stage that holds the library export, read and not yet sealed
\ (its names are looked up without adding any), and sha, the address of
\ that export's 32-byte SHA-256. The first line must be the header: this
\ format and version, the pinned Lean, the export's SHA-256 equal to sha,
\ the number of records of each kind and the SHA-256 of every later line
\ with its line feed. Every later line is one record of a known kind with
\ exactly its members; every name in it (a JSON array of string and
\ natural-number parts, root first) is the name of exactly one
\ declaration of the stage, of the right kind: an instance's or default
\ instance's class an inductive type, an instance or eliminator not one;
\ a reducibility's declaration and an eliminator's target types any
\ declaration. No instance, default instance or reducibility names a
\ declaration twice, and no two eliminators of one kind have the same
\ target types. At the end the records of each kind and the SHA-256 must
\ equal the header's, so a file cut off between two lines, or changed,
\ is refused.
\
\ Outcomes (ADR 0008): ok; invalid for anything malformed, unknown,
\ duplicated, of the wrong kind or differing from the header or from the
\ export, an unreadable file, a sealed stage, or a call while a read is in
\ progress; unsupported for another format version or Lean version, and
\ a priority or synthesis-order entry beyond 2^32 - 1 (no Lean library
\ has one; plan row FE3 lifts it if one appears); full when the heap has
\ no room or a line passes elab-line-limit bytes. A read that is not ok
\ keeps nothing: every table is empty afterwards, as after elab-reset.
\ elab-error ( -- line c-addr u ) gives the line of the failure (1 the
\ header; after the last line, the number of lines read; 0 before the
\ file is open) and why: elab-error-line and elab-error-why apart.
\
\ The data kept, numbered from 0 in file order, its declarations the
\ stage's declaration numbers: elab-count ( kind -- n );
\ elab-instance@ ( i -- d class priority ), elab-instance-order
\ ( i -- addr n ) (cells), elab-instance-of ( d -- i true | false );
\ elab-default@ ( i -- class d priority ); elab-status ( d -- status )
\ (elab-semireducible when no record names d); elab-eliminator@
\ ( i -- kind d ), elab-eliminator-types ( i -- addr n ) (cells),
\ elab-eliminator-for ( d kind -- i true | false ) (the eliminator whose
\ one target type is d). elab-loaded? says whether the last read was ok.
\
\ Example (the export read but not sealed, its manifest checked):
\   create lib /stage allot   12 lib stage-init drop
\   s" tests/author/init-slice.ndjson" lib stage-read drop
\   s" tests/front/init-slice.elab.ndjson" lib
\   lib stage-manifest manifest-digest elab-read .   \ 0, ok
\   elab-instance elab-count .                        \ 3
\
\ State: one context record, elab (the read in progress: its reader,
\ JSON view and SHA-256 and the header's numbers; the eliminators' hash
\ table and its keys), and six context slabs: elab-facts (a cell per
\ declaration of the stage), the instances, their synthesis orders, the
\ default instances, the eliminators and their target types. One read
\ at a time per context; the reader and the view hold heap memory only
\ during a read, the table and the slabs until the context is freed.
\ Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/bytes.fs
require ../lib/json.fs
require ../lib/sha256.fs
require ../lib/hash32.fs
require ../lib/htab.fs
require ../import/stage.fs

\ Record kinds, in the order of the file.
0 constant elab-instance   1 constant elab-default
2 constant elab-reducibility   3 constant elab-eliminator   4 constant elab-kinds
\ Reducibility statuses (Lean's ReducibilityStatus; 0 is the default).
0 constant elab-semireducible   1 constant elab-reducible   2 constant elab-irreducible
3 constant elab-implicit-reducible   4 constant elab-instance-reducible
\ Eliminator kinds: @[induction_eliminator] and @[cases_eliminator].
0 constant elab-induction   1 constant elab-cases
1048576 constant elab-line-limit   \ longest line, in bytes
8 constant elab-depth-limit        \ deepest JSON nesting of a line
65536 constant elab-token-limit    \ most JSON tokens in one line

\ ---- State.
begin-structure /ed-inst
  field: inst-decl   field: inst-class   field: inst-priority
  field: inst-order   field: inst-order#   \ its synthesis order in elab-orders
end-structure
begin-structure /ed-dflt
  field: dflt-class   field: dflt-decl   field: dflt-priority
end-structure
begin-structure /ed-elim
  field: elim-kind   field: elim-decl
  field: elim-types   field: elim-types#   \ its target types in elab-types
end-structure
\ An eliminator's key, kind and target types (cells), as the table
\ compares it; ekey-one holds the type of a key made for one type.
begin-structure /ed-key
  field: ekey-kind   field: ekey-types   field: ekey-types#   field: ekey-one
end-structure
begin-structure /elab
  /reader +field elab-reader
  /json +field elab-json
  /sha256 +field elab-sha
  /htab +field elab-table            \ eliminators by kind and target types
  /ed-key +field elab-key            \ the key looked up
  /ed-key +field elab-probe          \ the hooks' key of an entry
  field: elab-stage                  \ during a read: the stage
  field: elab-export                 \ during a read: the export's SHA-256
  field: elab-reading                \ true during a read
  field: elab-loaded                 \ true: the last read was ok
  field: elab-why                    \ counted string: why it failed, or 0
  field: elab-at                     \ the line it failed at
  elab-kinds cells +field elab-counts     \ records read of each kind
  elab-kinds cells +field elab-expected   \ the header's numbers
  sha-digest-bytes chars +field elab-digest
  sha-digest-bytes 2* chars +field elab-hex       \ a SHA-256 as text
  sha-digest-bytes 2* chars +field elab-records   \ the header's records_sha256
end-structure
/elab context-record: elab
1 cells context-slab: elab-facts
/ed-inst context-slab: elab-insts
1 cells context-slab: elab-orders
/ed-dflt context-slab: elab-dflts
/ed-elim context-slab: elab-elims
1 cells context-slab: elab-types

: ed-view ( -- view ) elab elab-json ;
: ed-stage ( -- stage ) elab elab-stage @ ;
: elab-count ( kind -- n ) cells elab elab-counts + @ ;
: elab-loaded? ( -- flag ) elab elab-loaded @ ;

\ Failing: why, at the current line; the outcome given.
: ed-line ( -- n ) elab elab-reader reader-position nip nip ;
: ed-fail ( why outcome -- outcome ) ed-line elab elab-at ! swap elab elab-why ! ;
: ed-bad ( why -- outcome ) outcome-invalid ed-fail ;
: ed-malformed ( -- outcome ) c" malformed line" ed-bad ;
: ed-roomed ( outcome -- outcome ) dup ok? 0= if c" no room" swap ed-fail then ;
: elab-error-line ( -- line ) elab elab-at @ ;
: elab-error-why ( -- c-addr u ) elab elab-why @ ?dup if count else s" none" then ;
: elab-error ( -- line c-addr u ) elab-error-line elab-error-why ;

\ ---- Facts per declaration of the stage: bits 0-2 its reducibility
\ status, bit 3 a default instance, from bit 4 its instance's number + 1.
7 constant facts-status   8 constant facts-default   4 constant facts-shift
: ed-fact ( d -- addr ) elab-facts slab-at ;
: ed-fact@ ( d -- x ) dup elab-facts slab-count u< if ed-fact @ else drop 0 then ;
: ed-facts-made ( n -- outcome )
  dup elab-facts slab-claim ed-roomed ok-then? if ed-fact swap cells erase outcome-ok
  else nip then ;
: elab-status ( d -- status ) ed-fact@ facts-status and ;
: elab-instance-of ( d -- i true | false ) ed-fact@ facts-shift rshift +1>number ;

\ ---- The records kept.
: ed-inst ( i -- addr ) elab-insts slab-at ;
: ed-dflt ( i -- addr ) elab-dflts slab-at ;
: ed-elim ( i -- addr ) elab-elims slab-at ;
: ed-types ( first n -- addr n ) swap elab-types slab-at swap ;
: elab-instance@ ( i -- d class priority )
  ed-inst dup inst-decl @ over inst-class @ rot inst-priority @ ;
: elab-instance-order ( i -- addr n )
  ed-inst dup inst-order @ swap inst-order# @ swap elab-orders slab-at swap ;
: elab-default@ ( i -- class d priority )
  ed-dflt dup dflt-class @ over dflt-decl @ rot dflt-priority @ ;
: elab-eliminator@ ( i -- kind d ) ed-elim dup elim-kind @ swap elim-decl @ ;
: elab-eliminator-types ( i -- addr n )
  ed-elim dup elim-types @ swap elim-types# @ ed-types ;

\ ---- The eliminators' table (lib/htab.fs): entries are eliminator
\ numbers, keyed by kind and target types; the hooks make an entry's key
\ in elab-probe, never in the key being looked up.
: ed-key! ( i key -- )
  >r dup elab-eliminator@ drop r@ ekey-kind ! elab-eliminator-types r@ ekey-types# !
  r> ekey-types ! ;
: ed-key-cells ( key -- addr u ) dup ekey-types @ swap ekey-types# @ cells ;
: ed-key-hash ( key -- h )
  dup ekey-kind @ hash-fmix swap ed-key-cells bounds ?do i @ hash-step 1 cells +loop ;
: ed-same-key? ( key1 key2 -- flag )
  2dup ekey-kind @ swap ekey-kind @ = >r ed-key-cells rot ed-key-cells compare 0= r> and ;
: ed-probe ( n -- key ) elab elab-probe tuck ed-key! ;
: ed-rehash ( n htab -- h ) drop ed-probe ed-key-hash ;
: ed-same ( n key htab -- flag ) drop swap ed-probe ed-same-key? ;
create ed-hooks /htab-hooks allot  ' ed-rehash ' ed-same ed-hooks htab-hooks!
: ed-table ( -- htab ) elab elab-table ;
:noname ( -- ) 4 ed-hooks ed-table htab-init drop ; context-setup
:noname ( -- ) ed-table htab-free ; context-teardown
: ed-key-find ( key -- n true | i false ) dup ed-key-hash ed-table htab-find ;
: elab-eliminator-for ( d kind -- i true | false )
  elab elab-key tuck ekey-kind ! tuck ekey-one ! dup ekey-one over ekey-types !
  1 over ekey-types# ! ed-key-find dup 0= if nip then ;

\ ---- Forgetting: every table empty, the counts zero, nothing loaded.
: ed-slabs-clear ( -- )
  elab-facts slab-clear elab-insts slab-clear elab-orders slab-clear
  elab-dflts slab-clear elab-elims slab-clear elab-types slab-clear ;
: elab-reset ( -- )
  ed-slabs-clear ed-table htab-clear false elab elab-loaded !
  elab elab-counts elab-kinds cells erase ;

\ ---- Tables of keys: counted strings ending with an empty one
\ (import/manifest.fs's exact-keys? reads them). ed-key-index finds a
\ text's place in one.
: ed-key-index ( c-addr u table -- k true | false )
  -rot 2>r 0 swap begin dup count nip while
    dup count 2r@ compare 0= if drop 2r> 2drop true exit then key-next swap 1+ swap
  repeat 2drop 2r> 2drop false ;
create kind-names
  s" instance" counted, s" default_instance" counted, s" reducibility" counted,
  s" eliminator" counted, 0 0 counted,
create status-names
  s" reducible" counted, s" irreducible" counted, s" implicit_reducible" counted,
  s" instance_reducible" counted, 0 0 counted,
create elim-names  s" induction" counted, s" cases" counted, 0 0 counted,
: ed-kind-name ( kind -- c-addr ) kind-names swap 0 ?do key-next loop ;

\ ---- Members of the object value: shape? holds when it has exactly the
\ table's keys; ed-member gives a key's value, -1 when absent.
: ed-member ( value key -- index ) swap ed-view json-find 0= if -1 then ;
: ed-shape? ( value table -- flag ) swap ed-view exact-keys? ;
: ed-text ( index -- c-addr u true | false ) ed-view string-value ;
: ed-text= ( index c-addr u -- flag ) rot ed-text if compare 0= else 2drop false then ;
: ed-array? ( index -- flag ) json-array ed-view json-items-of dup if nip then ;
\ A natural number of at most 32 bits.
: ed-u32 ( index -- u outcome )
  ed-view json-u 0= if 0 ed-malformed exit then
  dup u32-mask u> if c" a number beyond 2^32 - 1" outcome-unsupported ed-fail exit then
  outcome-ok ;
\ One of the table's texts: its place.
: ed-choice ( index table -- k outcome )
  >r ed-text if r> ed-key-index if outcome-ok exit then else r> drop then 0 ed-malformed ;
\ xt ( item -- outcome ) on each element of an array in turn, while ok.
: ed-next ( item -- item' ) ed-view json-next ;
: ed-items ( end first xt -- outcome )
  >r begin 2dup > while
    dup r@ execute ok-then? 0= if nip r> drop exit then ed-next
  repeat 2drop r> drop outcome-ok ;
: ed-array-items ( index xt -- outcome )
  over ed-array? 0= if 2drop ed-malformed exit then
  swap ed-view json-contents rot ed-items ;

\ ---- Names: a JSON array of parts, root first, each a string or a
\ natural number, looked up in the stage's tier without adding anything
\ (-1: no such name; a part beyond 32 bits names none).
: ed-tier ( -- tier ) ed-stage stage-tier ;
: ed-looked ( n outcome -- n outcome )
  dup ok? 0= if c" name lookup failed" swap ed-fail then ;
: ed-part-text ( prefix item -- n outcome )
  ed-view json-text@ ed-tier name-seek-str ed-looked ;
: ed-part-number ( prefix item -- n outcome )
  ed-view json-u 0= if drop -1 ed-malformed exit then
  dup u32-mask u> if 2drop -1 outcome-ok exit then ed-tier name-seek-num ed-looked ;
: ed-part ( prefix item -- n outcome )
  dup ed-view json-kind@ json-string = if ed-part-text exit then
  dup ed-view json-kind@ json-integer = if ed-part-number exit then
  2drop -1 ed-malformed ;
\ The parts from first to end in turn, each under the name before it.
: ed-parts ( end first -- n outcome )
  0 -rot begin 2dup > while
    rot over ed-part ok-then? 0= if nip nip -1 swap exit then
    dup 0< if nip nip outcome-ok exit then -rot ed-next
  repeat 2drop outcome-ok ;
: ed-name-array? ( index -- flag )
  json-array ed-view json-items-of if 0> else false then ;
: ed-name ( index -- n outcome )
  dup ed-name-array? 0= if drop -1 ed-malformed exit then ed-view json-contents ed-parts ;
\ The one declaration of tier name n.
: ed-decls ( n -- u true | false )
  dup 0< if drop false exit then ed-stage 2dup stage-by-name slab-count u<
  if resolution else 2drop false then ;
: ed-name-decl ( n -- d outcome )
  ed-decls 0= if 0 c" unknown name" ed-bad exit then
  +1>number if outcome-ok else 0 c" a name several declarations have" ed-bad then ;
: ed-decl ( index -- d outcome ) ed-name dup ok? if drop ed-name-decl then ;
\ The same, of the kind wanted: an inductive type, or any but one.
: ed-type? ( d -- flag ) ed-stage staged-kind@ kind-type = ;
: ed-kind-bad ( d -- d outcome ) c" a declaration of the wrong kind" ed-bad ;
: ed-a-type ( index -- d outcome )
  ed-decl dup ok? 0= if exit then drop dup ed-type? if outcome-ok else ed-kind-bad then ;
: ed-no-type ( index -- d outcome )
  ed-decl dup ok? 0= if exit then drop dup ed-type? if ed-kind-bad else outcome-ok then ;

\ ---- Fields. A record's fields are steps ( value i -- outcome ), run in
\ turn while ok; ed-put stores x in a field of record addr when ok.
: ed-step ( value i outcome xt -- value i outcome )
  over ok? 0= if drop exit then nip >r 2dup r> execute ;
: ed-steps ( value i table -- outcome )
  outcome-ok swap begin dup @ while dup cell+ >r @ ed-step r> repeat drop nip nip ;
: ed-put ( addr x outcome xt -- outcome )
  over ok? 0= if drop nip nip exit then nip rot swap execute ! outcome-ok ;
: ed-claim ( slab -- i outcome ) 1 swap slab-claim ed-roomed ;
: ed-push ( x slab -- outcome )
  tuck ed-claim ok-then? if rot slab-at ! outcome-ok else nip nip then ;

\ ---- Instances: name, class, priority, synthesis order.
create inst-keys
  s" class" counted, s" name" counted, s" priority" counted, s" synth_order" counted,
  0 0 counted,
: ed-inst-fact ( d i -- outcome )
  over elab-instance-of if 2drop drop c" an instance named twice" ed-bad exit then
  1+ facts-shift lshift swap ed-fact +! outcome-ok ;
: ed-inst-named ( i d -- i d outcome ) 2dup swap ed-inst-fact ;
: ed-inst-decl ( value i -- outcome )
  swap c" name" ed-member ed-no-type dup ok? if drop ed-inst-named then
  rot ed-inst -rot ['] inst-decl ed-put ;
: ed-inst-class ( value i -- outcome )
  ed-inst swap c" class" ed-member ed-a-type ['] inst-class ed-put ;
: ed-inst-priority ( value i -- outcome )
  ed-inst swap c" priority" ed-member ed-u32 ['] inst-priority ed-put ;
: ed-order-item ( item -- outcome ) ed-u32 ok-then? if elab-orders ed-push then ;
: ed-order-span ( addr -- )
  elab-orders slab-count over inst-order @ - swap inst-order# ! ;
: ed-inst-order ( value i -- outcome )
  ed-inst elab-orders slab-count over inst-order ! swap c" synth_order" ed-member
  ['] ed-order-item ed-array-items swap ed-order-span ;
create inst-steps
  ' ed-inst-decl , ' ed-inst-class , ' ed-inst-priority , ' ed-inst-order , 0 ,
: ed-on-instance ( value -- outcome )
  dup inst-keys ed-shape? 0= if drop ed-malformed exit then
  elab-insts ed-claim ok-then? if inst-steps ed-steps else nip then ;

\ ---- Default instances: class, name, priority.
create dflt-keys  s" class" counted, s" name" counted, s" priority" counted, 0 0 counted,
: ed-dflt-fact ( d -- d outcome )
  dup ed-fact dup @ facts-default and
  if drop c" a default instance named twice" ed-bad exit then
  dup @ facts-default or swap ! outcome-ok ;
: ed-dflt-decl ( value i -- outcome )
  ed-dflt swap c" name" ed-member ed-no-type dup ok? if drop ed-dflt-fact then
  ['] dflt-decl ed-put ;
: ed-dflt-class ( value i -- outcome )
  ed-dflt swap c" class" ed-member ed-a-type ['] dflt-class ed-put ;
: ed-dflt-priority ( value i -- outcome )
  ed-dflt swap c" priority" ed-member ed-u32 ['] dflt-priority ed-put ;
create dflt-steps  ' ed-dflt-decl , ' ed-dflt-class , ' ed-dflt-priority , 0 ,
: ed-on-default ( value -- outcome )
  dup dflt-keys ed-shape? 0= if drop ed-malformed exit then
  elab-dflts ed-claim ok-then? if dflt-steps ed-steps else nip then ;

\ ---- Reducibility: name, status; no declaration twice.
create red-keys  s" name" counted, s" status" counted, 0 0 counted,
: ed-status-fact ( d status -- outcome )
  over elab-status if 2drop c" a reducibility named twice" ed-bad exit then
  swap ed-fact +! outcome-ok ;
: ed-on-reducibility ( value -- outcome )
  dup red-keys ed-shape? 0= if drop ed-malformed exit then
  dup c" name" ed-member ed-decl ok-then? 0= if nip exit then
  swap c" status" ed-member status-names ed-choice
  ok-then? if 1+ ed-status-fact else nip then ;

\ ---- Eliminators: kind, name, target types; one per kind and types.
create elim-keys  s" kind" counted, s" name" counted, s" types" counted, 0 0 counted,
: ed-elim-kind ( value i -- outcome )
  ed-elim swap c" kind" ed-member elim-names ed-choice ['] elim-kind ed-put ;
: ed-elim-decl ( value i -- outcome )
  ed-elim swap c" name" ed-member ed-no-type ['] elim-decl ed-put ;
: ed-type-item ( item -- outcome ) ed-decl ok-then? if elab-types ed-push then ;
: ed-types-span ( addr -- ) elab-types slab-count over elim-types @ - swap elim-types# ! ;
: ed-elim-types ( value i -- outcome )
  ed-elim elab-types slab-count over elim-types ! swap c" types" ed-member
  ['] ed-type-item ed-array-items swap ed-types-span ;
create elim-steps  ' ed-elim-kind , ' ed-elim-decl , ' ed-elim-types , 0 ,
\ Eliminator i into the table, unless one of its key is there.
: ed-twice ( i n -- outcome ) 2drop c" two eliminators for the same types" ed-bad ;
: ed-elim-insert ( i -- outcome )
  ed-table htab-ready ed-roomed dup ok? 0= if nip exit then drop
  dup elab elab-key tuck ed-key! ed-key-find
  if ed-twice else ed-table htab-put outcome-ok then ;
: ed-on-eliminator ( value -- outcome )
  dup elim-keys ed-shape? 0= if drop ed-malformed exit then
  elab-elims ed-claim ok-then? 0= if nip exit then tuck elim-steps ed-steps
  ok-then? if ed-elim-insert then ;

\ ---- Lines. Each is one JSON object with one member: the header's key
\ elab_data, or a record kind, whose value is an object.
create kind-handlers
  ' ed-on-instance , ' ed-on-default , ' ed-on-reducibility , ' ed-on-eliminator ,
: ed-one-member? ( -- flag ) 0 json-object ed-view json-items-of if 1 = else false then ;
: ed-object-value? ( -- flag ) 2 ed-view json-kind-at json-object = ;
: ed-wrapped? ( -- flag ) ed-one-member? if ed-object-value? else false then ;
: ed-tally ( kind -- ) cells elab elab-counts + 1 swap +! ;
: ed-dispatch ( value kind -- outcome ) dup ed-tally cells kind-handlers + @ execute ;
: ed-on-record ( -- outcome )
  ed-wrapped? 0= if ed-malformed exit then
  1 ed-view json-text@ kind-names ed-key-index
  0= if c" unknown record kind" ed-bad exit then
  2 swap ed-dispatch ;

\ ---- The header: its format and version first, so that another version
\ is told as such, then its shape, Lean, the export and the numbers.
create head-keys
  s" export_sha256" counted, s" format" counted, s" format_version" counted,
  s" lean_githash" counted, s" lean_version" counted, s" modules" counted,
  s" records" counted, s" records_sha256" counted, 0 0 counted,
: ed-or-bad ( flag why -- outcome ) swap if drop outcome-ok else ed-bad then ;
: ed-or-other ( flag why -- outcome )
  swap if drop outcome-ok else outcome-unsupported ed-fail then ;
: ed-head-format ( value i -- outcome )
  drop c" format" ed-member s" leanforth-elab-data" ed-text=
  c" not elaboration data" ed-or-bad ;
: ed-head-version ( value i -- outcome )
  drop c" format_version" ed-member ed-view natural-at if s" 1" compare 0= else false then
  c" another format version" ed-or-other ;
: ed-head-shape ( value i -- outcome )
  drop head-keys ed-shape? c" malformed line" ed-or-bad ;
: ed-head-lean ( value i -- outcome )
  drop dup c" lean_version" ed-member pinned-lean-version ed-text=
  swap c" lean_githash" ed-member pinned-lean-githash ed-text= and
  c" another Lean version" ed-or-other ;
: ed-export-hex ( -- c-addr u )
  elab elab-export @ elab elab-hex sha256-hex elab elab-hex sha-digest-bytes 2* ;
: ed-head-export ( value i -- outcome )
  drop c" export_sha256" ed-member ed-export-hex ed-text=
  c" elaboration data of another export" ed-or-bad ;
: ed-expected ( kind -- addr ) cells elab elab-expected + ;
: ed-expect ( object kind -- outcome )
  tuck ed-kind-name ed-member ed-view json-u if swap ed-expected ! outcome-ok
  else drop ed-malformed then ;
: ed-head-records ( value i -- outcome )
  drop c" records" ed-member dup kind-names ed-shape? 0= if drop ed-malformed exit then
  elab-kinds 0 do dup i ed-expect dup ok? 0= if nip unloop exit then drop loop
  drop outcome-ok ;
: ed-head-hash ( value i -- outcome )
  drop c" records_sha256" ed-member ed-text 0= if ed-malformed exit then
  2dup sha-digest-bytes 2* hex-text? 0= if 2drop ed-malformed exit then
  elab elab-records swap move outcome-ok ;
: ed-module-item ( item -- outcome )
  ed-view json-kind@ json-string = if outcome-ok else ed-malformed then ;
: ed-head-modules ( value i -- outcome )
  drop c" modules" ed-member ['] ed-module-item ed-array-items ;
create head-steps
  ' ed-head-format , ' ed-head-version , ' ed-head-shape , ' ed-head-lean ,
  ' ed-head-export , ' ed-head-records , ' ed-head-hash , ' ed-head-modules , 0 ,
: ed-head-key? ( -- flag ) 1 ed-view json-text@ s" elab_data" compare 0= ;
: ed-on-header ( -- outcome )
  ed-wrapped? if ed-head-key? else false then 0= if c" no header" ed-bad exit then
  2 0 head-steps ed-steps ;

\ ---- The file, line by line; each record line hashed before it is
\ parsed (parsing decodes its strings in place).
: ed-line-why ( outcome -- why )
  outcome-full = if c" a line longer than the limit" exit then
  c" no line, or a line without its line feed" ;
: ed-next-line ( -- c-addr u outcome )
  elab elab-reader reader-line dup ok? 0= if dup ed-line-why swap ed-fail then ;
: ed-parse ( c-addr u -- outcome )
  ed-view json-parse dup ok? 0= if c" not one JSON value within the limits" swap ed-fail
  then ;
: ed-header ( -- outcome )
  ed-next-line ok-then2? if ed-parse dup ok? if drop ed-on-header then then ;
: ed-record-line ( c-addr u -- outcome )
  2dup elab elab-sha sha256-line ed-parse dup ok? if drop ed-on-record then ;
: ed-more? ( -- flag ) elab elab-reader reader-more? ;
: ed-records ( -- outcome )
  begin ed-more? while
    ed-next-line ok-then2? 0= if exit then ed-record-line dup ok? 0= if exit then drop
  repeat outcome-ok ;
\ At the end: the records of each kind and their SHA-256, as the header says.
: ed-counts-same? ( -- flag )
  elab elab-counts elab-kinds cells elab elab-expected over compare 0= ;
: ed-hash-same? ( -- flag )
  elab elab-digest elab elab-sha sha256-final elab elab-digest elab elab-hex sha256-hex
  elab elab-hex sha-digest-bytes 2* elab elab-records over compare 0= ;
: ed-ends ( -- outcome )
  ed-counts-same? 0= if c" records differ in number from the header" ed-bad exit then
  ed-hash-same? c" records differ from their SHA-256" ed-or-bad ;
: ed-open ( c-addr u -- outcome )
  elab elab-reader reader-open
  dup ok? 0= if c" file missing or unreadable" swap ed-fail then ;
: ed-steps-all ( c-addr u -- outcome )
  ed-open dup ok? if drop ed-header then dup ok? if drop ed-records then
  dup ok? if drop ed-ends then ;

\ ---- The read: started with every table empty, its reader and view
\ freed on every path (a THROW passes on after that), and everything
\ forgotten when it is not ok.
: ed-views ( -- outcome )
  4096 elab-line-limit elab elab-reader reader-init dup ok? 0= if exit then drop
  elab-depth-limit ed-view json-init
  dup ok? if elab-token-limit ed-view json-token-limit ! then ;
: ed-sealed ( stage -- outcome )
  drop c" the library's stage is sealed: its names cannot be looked up" ed-bad ;
: ed-start ( stage sha -- outcome )
  elab-reset 0 elab elab-why ! 0 elab elab-at ! elab elab-export ! dup elab elab-stage !
  elab elab-sha sha256-init dup stage-sealed? if ed-sealed exit then
  stage-decls ed-facts-made dup ok? if drop ed-views ed-roomed then ;
: ed-close ( outcome -- outcome )
  elab elab-reader dup reader-close drop reader-free ed-view json-free
  false elab elab-reading ! dup ok? dup elab elab-loaded ! 0= if elab-reset then ;
: ed-caught ( c-addr u -- outcome code )
  ['] ed-steps-all catch dup if nip nip outcome-invalid swap then ;
: ed-busy ( c-addr u stage sha -- outcome ) 2drop 2drop c" a read in progress" ed-bad ;
: elab-read ( c-addr u stage sha -- outcome )
  elab elab-reading @ if ed-busy exit then
  ed-start ok-then2? if true elab elab-reading ! ed-caught else 0 then
  >r ed-close r> throw ;

base !   \ the BASE this file was loaded with
