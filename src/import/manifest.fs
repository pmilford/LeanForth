\ Export manifests (plan task 3.2.6, owner decision of 2026-11-03): reading
\ a Lean export checked against the manifest that LeanForth's export step
\ wrote beside it (scripts/export.sh, scripts/export_manifest.py). Lean's
\ export carries no checksum, so a file cut off cleanly between two lines
\ would otherwise read as a shorter, valid library. LeanForth-specific;
\ untrusted and fail-closed, like the reader. Format, outcomes and
\ measurements: docs/development/NDJSON_READER.md, "Manifests".
\ Requires: import/ndjson.fs (and through it lib/json.fs, lib/bytes.fs,
\ lib/lib.fs) and lib/sha256.fs.
\ State: none of its own. Every word takes a manifest record made by
\ manifest:, which holds the export it checks, the SHA-256 in progress,
\ the manifest's text and its JSON view; one record is single-threaded.
\ The tables below are constant after loading.
\
\ manifest-read ( c-addr u m -- outcome ) reads the export file c-addr u
\ with export-read, so with the export's handlers, and checks it against
\ its manifest: "<c-addr u>.manifest.json", or the file manifest-use
\ named for this read. Before reading the export it checks the manifest
\ whole: one JSON object with exactly the members of format version 1
\ (and perhaps elab_records_sha256, kept for manifest-elab-sha),
\ each of its type, and the exporter, export format and Lean versions
\ equal to the pinned ones the reader requires (when the export reads
\ any version, export-any-version!, only the export format). During the
\ read the export's tap gives every line, then its line feed, to SHA-256,
\ once and as it is read. After an ok read it compares the file's lines, bytes,
\ records of each kind handed over, and SHA-256 with the manifest's.
\ Every failure about the manifest is invalid: missing, unreadable,
\ larger than manifest-size-limit, not JSON, malformed, another format
\ version, other versions, or different from the file. An outcome other
\ than ok from the read itself stays as it is. export-error gives the
\ field (empty, a manifest member, or a record kind) and the reason, and
\ line 0 for a manifest failure. Skipping the check is the caller's
\ explicit choice: export-read alone. Records reach the handlers before
\ the totals can be compared, so a consumer keeps what it built only when
\ the outcome is ok, as after any failure part-way through a file.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/bytes.fs
require ../lib/json.fs
require ../lib/decimal.fs
require ../lib/sha256.fs
require ../lib/text-run.fs
require ./ndjson.fs

4096 constant manifest-name-room     \ longest manifest file name, in characters
65536 constant manifest-size-limit   \ largest manifest file read, in bytes
8 constant manifest-depth-limit      \ deepest JSON nesting of a manifest

begin-structure /manifest
  /sha256 +field manifest-sha        \ the export's SHA-256 in progress
  /json +field manifest-json         \ the manifest, parsed
  field: manifest-export             \ the export it checks
  field: manifest-text               \ heap buffer holding the manifest's bytes, or 0
  aligned 2 cells +field manifest-count   \ bytes of the export hashed, a double
  aligned 2 cells +field manifest-given   \ a file named for the next read, or 0 0
  sha-digest-bytes chars +field manifest-digest   \ the export's digest
  sha-digest-bytes 2* chars +field manifest-hex   \ the same in hexadecimal
  manifest-name-room chars +field manifest-name   \ the default file name
  sha-digest-bytes 2* chars +field manifest-elab   \ elab_records_sha256's text
  field: manifest-elab-length        \ its length: 0 when the manifest names none
end-structure

\ Defining word: name ( -- m ), zeroed; manifest-init prepares it.
: manifest: ( "name" -- ) create /manifest store-zeroed, drop ;
\ Bind the record to an export and give it a JSON view, freeing the
\ memory of an earlier manifest-init; full when the heap has no room.
\ manifest-free releases it. A file manifest-use named stays named.
: manifest-release ( m -- ) manifest-text heap-release ;
: manifest-init ( export m -- outcome )
  dup manifest-release 0 over manifest-elab-length ! tuck manifest-export !
  manifest-depth-limit swap manifest-json json-init ;
: manifest-free ( m -- ) dup manifest-release manifest-json json-free ;
\ Name the manifest file for the next manifest-read only; the string must
\ stay unchanged until that read.
: manifest-use ( c-addr u m -- ) manifest-given 2! ;

\ Failures, all invalid: the field as a counted string (0 for none) and
\ the reason, kept in the export for export-error, with line 0.
: manifest-bad ( key why m -- outcome )
  manifest-export @ dup export-restart export-marks! outcome-invalid ;
: manifest-broken ( key m -- outcome ) c" manifest malformed" swap manifest-bad ;
: manifest-unread ( m -- outcome )
  0 c" manifest missing, unreadable or too large" rot manifest-bad ;

\ The manifest's file name: the one manifest-use named, used once, or the
\ export's name with manifest-suffix added; false when that is longer
\ than manifest-name-room.
: manifest-suffix ( -- c-addr u ) s" .manifest.json" ;
: name-part! ( c-addr u offset m -- ) manifest-name swap chars + swap chars move ;
: suffix-at! ( offset m -- ) manifest-suffix 2swap name-part! ;
: default-name ( c-addr u m -- c-addr' u' true | false )
  >r dup manifest-suffix nip + manifest-name-room > if 2drop r> drop false exit then
  tuck 0 r@ name-part!  dup r@ suffix-at!
  manifest-suffix nip + r> manifest-name swap true ;
: given? ( m -- flag ) manifest-given 2@ nip 0<> ;
: manifest-file ( c-addr u m -- c-addr' u' true | false )
  dup given? 0= if default-name exit then
  nip nip dup manifest-given 2@ rot 0 0 rot manifest-given 2! true ;

\ Reading the manifest file whole into a heap buffer, then parsing it.
\ The size of an open file, when it is at most manifest-size-limit.
: small-size ( fid -- u true | false )
  file-size if 2drop false exit then
  0= over manifest-size-limit 1+ u< and dup 0= if nip then ;
\ A heap buffer of u bytes (at least one) for the text, replacing the old.
: text-claim ( u m -- addr true | false )
  dup manifest-release swap 1 max heap-claim
  if tuck swap manifest-text ! true else drop false then ;
\ Read u bytes into the buffer: the bytes read, and true when it worked.
: text-read ( fid u m -- u' flag )
  over swap text-claim 0= if 2drop 0 false exit then swap rot read-file 0= ;
\ The whole file: its size, and true when all of it was read.
: file-text ( fid m -- u flag )
  over small-size 0= if 2drop 0 false exit then
  swap over >r text-read swap r@ = and r> swap ;
: manifest-parse ( u m -- outcome )
  >r r@ manifest-text @ swap r@ manifest-json json-parse ok?
  if r> drop outcome-ok else 0 c" manifest is not valid JSON" r> manifest-bad then ;
: manifest-opened ( fid m -- outcome )
  >r dup r@ file-text rot close-file 0= and
  if r> manifest-parse else drop r> manifest-unread then ;
: manifest-load ( c-addr u m -- outcome )
  >r r/o bin open-file if drop r> manifest-unread else r> manifest-opened then ;

\ Reading the parsed manifest. Tables of keys are counted strings that end
\ with an empty one.
: key-next ( c-addr -- c-addr' ) count + aligned ;
: keys-size ( table -- n )
  0 swap begin dup count nip while key-next swap 1+ swap repeat drop ;
: has-key? ( key index view -- flag ) json-find dup if nip then ;
\ Whether test ( key index view -- flag ) holds for every key of the table.
: keys-all? ( table index view test -- flag )
  -rot 2>r swap begin dup count nip while
    dup 2r@ 4 pick execute 0= if 2drop 2r> 2drop false exit then key-next
  repeat 2drop 2r> 2drop true ;
: all-keys? ( table index view -- flag ) ['] has-key? keys-all? ;   \ every key a member
: object-size ( index view -- n true | false ) >r json-object r> json-items-of ;
: members? ( n index view -- flag ) object-size if = else drop false then ;
\ The object at index has exactly the table's keys, each once: as many
\ members as keys, and every key found.
: exact-keys? ( table index view -- flag )
  2>r dup keys-size 2r@ members? if 2r> all-keys? else drop 2r> 2drop false then ;
\ The value of the member key of the manifest's object, token 0, or -1;
\ and the same with the manifest's JSON view.
: member ( key m -- value ) 0 swap manifest-json json-find 0= if -1 then ;
: member-at ( key m -- value view ) tuck member swap manifest-json ;
\ A natural number in canonical decimal: no sign, no leading zero.
: natural-at ( value view -- c-addr u true | false )
  2dup json-integer json-kind-at? 0= if 2drop false exit then
  json-text@ 2dup canonical-natural? if true else 2drop false then ;
\ Whether c is no lowercase hexadecimal digit.
: hex-odd? ( c -- flag )
  dup [char] 0 [char] 9 between? swap [char] a [char] f between? or 0= ;
\ Exactly n lowercase hexadecimal digits.
: hex-text? ( c-addr u n -- flag )
  over <> if 2drop false exit then ['] hex-odd? text-any? 0= ;

\ The members of format version 1, and the members of its records
\ object: the record kinds, in the order of their numbers.
create manifest-keys
  s" bytes" counted, s" export_format" counted, s" exporter" counted,
  s" exporter_version" counted, s" format" counted, s" format_version" counted,
  s" lean_githash" counted, s" lean_version" counted, s" lines" counted,
  s" mathlib_commit" counted, s" records" counted, s" sha256" counted, 0 0 counted,
create kind-keys
  s" meta" counted, s" name.str" counted, s" name.num" counted,
  s" level.succ" counted, s" level.max" counted, s" level.imax" counted,
  s" level.param" counted, s" expr.bvar" counted, s" expr.sort" counted,
  s" expr.const" counted, s" expr.app" counted, s" expr.lam" counted,
  s" expr.forallE" counted, s" expr.letE" counted, s" expr.proj" counted,
  s" expr.natVal" counted, s" expr.strVal" counted, s" expr.mdata" counted,
  s" decl.axiom" counted, s" decl.def" counted, s" decl.thm" counted,
  s" decl.opaque" counted, s" decl.quot" counted, s" decl.inductive" counted,
  s" inductive.type" counted, s" inductive.ctor" counted, s" inductive.recursor" counted,
  0 0 counted,
kind-keys keys-size kind-count <>
[if] .( manifest.fs: one key per record kind) cr abort [then]
: kind-member ( kind -- c-addr ) kind-keys swap 0 ?do key-next loop ;
\ The member key of the object at index as a natural number.
: natural-found? ( key index view -- flag )
  >r r@ json-find if r> natural-at dup if nip nip then else r> drop false then ;
: naturals? ( table index view -- flag )
  ['] natural-found? keys-all? ;   \ every one a natural
\ The manifest's count of kind, in the records object at index.
: recorded ( kind index view -- c-addr u true | false )
  >r swap kind-member swap r@ json-find if r> natural-at else r> drop false then ;

\ Tables of checks, one entry per member: a cell (an xt), then the
\ member's key as a counted string; a cell of 0 ends the table.
: check, ( xt "key" -- ) , parse-name counted, ;
: check-key ( entry -- key ) cell+ ;
: check-next ( entry -- entry' ) check-key count + aligned ;
\ Run xt ( entry m -- outcome ) on each entry in turn while it gives ok.
: each-check ( table m xt -- outcome )
  >r swap begin dup @ while
    2dup swap r@ execute dup ok? 0= if nip nip r> drop exit then drop check-next
  repeat 2drop r> drop outcome-ok ;

\ Checking the manifest before the export is read: its format, then the
\ type of each member, then the versions.
: manifest-name? ( m -- flag )
  c" format" swap member-at json-string-of
  if s" leanforth-export-manifest" compare 0= else false then ;
: version? ( m -- flag )
  c" format_version" swap member-at natural-at if s" 1" compare 0= else false then ;
: version-bad ( m -- outcome )
  c" format_version" c" unsupported manifest format version" rot manifest-bad ;
\ The one optional member (S1 note, M6; ADR 0021 D10): the records_sha256
\ of the elaboration data made for this export, which scripts/export-elab.sh
\ adds; elab-read then refuses any other data (cli/check-lf.fs).
: elab-key ( -- key ) c" elab_records_sha256" ;
: root-has? ( key view -- flag ) 0 swap has-key? ;          \ of the object at token 0
: root-all? ( table view -- flag ) 0 swap all-keys? ;
: root-size? ( n view -- flag ) 0 swap members? ;
: elab-named? ( m -- flag ) manifest-json elab-key swap root-has? ;
: keys-wanted ( m -- n ) elab-named? negate manifest-keys keys-size + ;
: known-keys? ( m -- flag ) manifest-json manifest-keys swap root-all? ;
: sized? ( m -- flag ) dup keys-wanted swap manifest-json root-size? ;
\ Exactly the members of format version 1, and the optional one.
: keys-check ( m -- outcome )
  dup known-keys? over sized? and if drop outcome-ok else 0 swap manifest-broken then ;
\ The name and version first, so that another version is told as such.
: format-check ( m -- outcome )
  dup 0 swap manifest-json object-size if drop else 0 swap manifest-broken exit then
  dup manifest-name? 0= if c" format" swap manifest-broken exit then
  dup version? if keys-check else version-bad then ;

\ The type of each member, ( key m -- flag ): true when well formed.
: digest? ( key m -- flag ) member-at json-string-of if 64 hex-text? else false then ;
: commit? ( key m -- flag )
  member-at 2dup json-null json-kind-at? if 2drop true exit then
  json-string-of if 40 hex-text? else false then ;
: natural-member? ( key m -- flag ) member-at natural-at dup if nip nip then ;
\ The records object: exactly the record kinds, each a natural number.
: elab-digest? ( key m -- flag ) dup elab-named? if digest? else 2drop true then ;
: records? ( key m -- flag )
  member-at kind-keys -rot 2dup 2>r exact-keys?
  if kind-keys 2r> naturals? else 2r> 2drop false then ;
create type-checks
  ' digest? check, sha256          ' commit? check, mathlib_commit
  ' natural-member? check, bytes   ' natural-member? check, lines
  ' records? check, records        ' elab-digest? check, elab_records_sha256  0 ,
: type-entry ( entry m -- outcome )
  over check-key swap 2dup 2>r rot @ execute 2r> rot
  if 2drop outcome-ok else manifest-broken then ;
: types-check ( m -- outcome ) type-checks swap ['] type-entry each-check ;

\ The versions: each member must hold a string equal to the pinned one its
\ entry's xt ( -- c-addr u ) gives: malformed when it is no string,
\ another version when it differs.
: pinned-check ( c-addr u key m -- outcome )
  2dup member-at json-string-of 0= if 2swap 2drop manifest-broken exit then
  2rot compare 0= if 2drop outcome-ok exit then
  c" manifest names another exporter or Lean version" swap manifest-bad ;
create version-checks
  ' pinned-exporter check, exporter
  ' pinned-exporter-version check, exporter_version
  ' pinned-format-version check, export_format
  ' pinned-lean-version check, lean_version
  ' pinned-lean-githash check, lean_githash  0 ,
\ When the export reads any version (export-any-version?), only the
\ format version must be the pinned one; the others need only be strings.
: string-check ( key m -- outcome )
  2dup member-at json-string-of if 2drop 2drop outcome-ok else manifest-broken then ;
: loose? ( entry m -- flag )
  manifest-export @ export-any-version? swap @ ['] pinned-format-version <> and ;
: version-entry ( entry m -- outcome )
  2dup loose? if swap check-key swap string-check exit then
  >r dup @ execute rot check-key r> pinned-check ;
: versions-check ( m -- outcome ) version-checks swap ['] version-entry each-check ;
\ Keep the optional member's text: the manifest's is released after the read.
: elab-text ( m -- c-addr u ) elab-key swap member-at json-string-of 0= if 0 0 then ;
: elab-place ( c-addr u m -- ) 2dup manifest-elab-length ! manifest-elab swap move ;
: elab-keep ( m -- ) dup elab-text rot elab-place ;
: checked-keep ( outcome m -- outcome ) over ok? if elab-keep else drop then ;
: manifest-check ( m -- outcome )
  >r r@ format-check dup ok? if drop r@ types-check then
  dup ok? if drop r@ versions-check then r> checked-keep ;
\ The records SHA-256 of the elaboration data the manifest names, as
\ text, after an ok manifest-read; 0 0 when it names none.
: manifest-elab-sha ( m -- c-addr u ) dup manifest-elab swap manifest-elab-length @ ;

\ Hashing during the read: the export's tap gives each line to SHA-256,
\ then its line feed, and counts both.
: manifest-tap ( c-addr u m -- )
  >r dup 1+ 0 r@ manifest-count 2@ d+ r@ manifest-count 2!
  r> manifest-sha sha256-line ;
: manifest-start ( m -- )
  dup manifest-sha sha256-init dup manifest-count 0 0 rot 2!
  ['] manifest-tap over manifest-export @ export-tap! ;
\ The read, with the tap removed afterwards on every path: a THROW from a
\ handler passes on after that.
: read-caught ( c-addr u export -- outcome ior )
  ['] export-read catch dup if >r 2drop drop 0 r> then ;
: manifest-export-read ( c-addr u m -- outcome )
  dup manifest-start manifest-export @ dup >r read-caught r> export-untap throw ;

\ After an ok read: compare the file with the manifest. Numbers are
\ compared as canonical decimal text, so that counts beyond a 32-bit cell
\ compare exactly.
: differs ( key m -- outcome ) c" export differs from its manifest" swap manifest-bad ;
: number= ( ud key m -- flag )
  tuck member swap manifest-json natural-at 0= if 2drop false exit then
  2>r ud>decimal 2r> compare 0= ;
: number-check ( ud key m -- outcome )
  2dup 2>r number= if 2r> 2drop outcome-ok else 2r> differs then ;
: tallied ( kind m -- c-addr u ) manifest-export @ export-kind-count 0 ud>decimal ;
: kind-same? ( kind index m -- flag )
  >r over swap r@ manifest-json recorded 0= if drop r> drop false exit then
  rot r> tallied compare 0= ;
: kinds-check ( m -- outcome )
  c" records" over member swap kind-count 0 do
    2dup i -rot kind-same? 0= if nip i kind-member swap differs unloop exit then
  loop 2drop outcome-ok ;
\ The file's digest, as hexadecimal text, against the manifest's.
: sha-same? ( m -- flag )
  >r c" sha256" r@ member r@ manifest-json json-string-of
  if r> manifest-hex sha-digest-bytes 2* compare 0= else r> drop false then ;
: sha-check ( m -- outcome )
  dup manifest-digest over manifest-sha sha256-final
  dup manifest-digest over manifest-hex sha256-hex
  dup sha-same? if drop outcome-ok else c" sha256" swap differs then ;
: compare-all ( m -- outcome )
  >r r@ manifest-export @ export-at @ 0 c" lines" r@ number-check
  dup ok? if drop r@ manifest-count 2@ c" bytes" r@ number-check then
  dup ok? if drop r@ kinds-check then
  dup ok? if drop r@ sha-check then r> drop ;
: compare-after ( outcome m -- outcome ) over ok? if nip compare-all else drop then ;

\ The whole check; the manifest's text is released on every path.
: name-too-long ( m -- outcome ) 0 c" manifest file name too long" rot manifest-bad ;
: manifest-steps ( c-addr u m -- outcome )
  >r 2dup r@ manifest-file 0= if 2drop r> name-too-long exit then
  r@ manifest-load dup ok? if drop r@ manifest-check then
  dup ok? if drop r@ manifest-export-read r> compare-after exit then
  nip nip r> drop ;
\ A handler of the export that calls it gets invalid, as from export-read,
\ and changes nothing of the read in progress.
: manifest-read ( c-addr u m -- outcome )
  dup manifest-export @ export-idle ok-then3? 0= if exit then
  dup >r ['] manifest-steps catch r> manifest-release throw ;

base !   \ the BASE this file was loaded with (not reached when loading throws)
