\ Sectioned binary files: a container of up to 62 sections of equal-size
\ units, each section checked by a SHA-256, behind a header that is itself
\ checked. A standalone library for any Forth-2012 system with the File
\ word set; it needs portability.fs, module.fs, outcome.fs, u32.fs (the
\ only module that gives 32-bit fields a byte layout) and sha256.fs. It
\ knows nothing of what the sections hold. Untrusted until reviewed; the
\ format is described in docs/programming/SECTIONED_FILES.md.
\
\   sections: sf   create fields 3 u32s allot   create bytes 12 allot
\   7 fields u32!  8 fields 1 u32s + u32!  9 fields 2 u32s + u32!
\   fields bytes 3 u32s>le                 \ the section's bytes, little-endian
\   42 5 sf sections-field! .              \ caller's header field 5 = 42; 0 = ok
\   bytes 4 3 1 sf sections-add .          \ addr unit-size count kind
\   s" out.sect" sf sections-write .       \ writes out.sect atomically
\   sf sections-init
\   s" out.sect" sf sections-open .        \ checks the header and the layout
\   create back 12 allot  back 12 0 sf sections-read .   \ addr room i
\   back 4 + u32-le@ .  sf sections-close .
\
\ prints 0 0 0 0 0 8 0 (six outcomes, ok each, and the second field, 8).
\ Writing: sections-init, up to 16 header fields (sections-field!, 32-bit
\ values), then sections-add for each section (the caller's memory, left
\ in place until sections-write), then sections-write. The file is built as
\ FILE.partial and renamed over FILE only when complete, so an old FILE
\ survives any failure; the partial is deleted by name on failure,
\ including a THROW while writing (which is then thrown again). Reading:
\ sections-init, sections-open checks everything except the section
\ contents (magic, format version, byte order, the header's SHA-256, the
\ table against the file size: truncated, outside, overlapping,
\ misaligned, length unequal to unit size times count, trailing bytes),
\ sections-info and sections-field@ report what the table says,
\ sections-read copies a section into the caller's block and checks its
\ SHA-256, sections-close closes the file.
\
\ Outcomes (ADR 0008): ok; invalid for a malformed, truncated or unreadable
\ file, a bad argument, or a failed file operation; unsupported for another
\ format version or the opposite byte order (a valid file this library does
\ not read); rejected for a SHA-256 that does not match (corruption); full
\ for a name or block that is too long or too small, or a 63rd section.
\ Every failure leaves nothing reported as ok.
\
\ Public words (word list lf-lib), each documented where it is defined:
\   /sections sections: sections-init sections-field! sections-field@
\   sections-add sections-write sections-open sections-count sections-info
\   sections-read sections-close sections-align sections-max
\ Everything else is private (lf-lib-private).
\
\ Limits: file offsets and lengths are held in cells, so a 32-bit host
\ reads files of up to 2^31-1 bytes, and a 64-bit one 2^63-1; a larger
\ 64-bit field in a file is invalid. A section is read into memory whole.
\ State: none of its own; one record (sections:) holds a file in progress,
\ and separate records are independent. One record is used by one task at
\ a time. The file loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ./portability.fs
require ./module.fs
require ./outcome.fs
require ./u32.fs
require ./sha256.fs

lf-lib-private module-open

lf-lib set-current
4096 constant sections-align   \ the header's size and every section's alignment
62 constant sections-max       \ sections one header holds
lf-lib-private set-current

16 constant sec-fields         \ caller's 32-bit header fields
96 constant sec-table          \ where the section table starts in the header
64 constant sec-slot-bytes     \ one table entry: kind, unit, count, offset, length, SHA
4064 constant sec-sum          \ where the header's own SHA-256 starts (the last 32 bytes)
1 constant sec-version
$01020304 constant sec-order   \ written little-endian; the other order reads as the next
$04030201 constant sec-order-swapped
500 constant sec-path-room     \ the longest file name; FILE.partial adds 8
: sec-magic ( -- c-addr u ) s" SECTFILE" ;

\ One table entry, in memory: the numbers, the caller's block (writing
\ only) and the section's SHA-256.
begin-structure /sec-entry
  field: sec-kind  field: sec-unit  field: sec-count
  field: sec-offset  field: sec-length  field: sec-addr
  32 +field sec-sha
end-structure

\ The record: the open file or the partial, the table, the header bytes.
begin-structure /sec-record
  field: sec-fid  field: sec-n  field: sec-filesize  field: sec-pathlen
  sec-fields u32s +field sec-user
  sections-max /sec-entry * +field sec-entries
  /sha256 +field sec-hash
  32 chars +field sec-digest
  sections-align chars +field sec-hdr
  sections-align chars +field sec-zero
  sec-path-room chars +field sec-path
  sec-path-room 8 + chars +field sec-partial
end-structure

: sec-entry ( i sf -- e ) sec-entries swap /sec-entry * + ;
\ Call xt ( e sf -- ) for each entry in turn.
: sec-each ( xt sf -- ) dup sec-n @ 0 ?do i over sec-entry over 3 pick execute loop 2drop ;
\ Walk entries from e to end with xt ( pos e -- pos' true | false ), carrying
\ a position; give the final position, or false at the first entry that fails.
: sec-walk ( xt pos e end -- pos' true | false )
  2dup = if 2drop nip true exit then
  >r dup >r 2 pick execute
  if r> /sec-entry + r> recurse else r> r> 2drop drop false then ;
: sec-walk-all ( xt pos sf -- pos' true | false )
  dup sec-entries swap sec-n @ /sec-entry * over + sec-walk ;

\ Little-endian 64-bit fields as two 32-bit ones. A value that does not fit
\ a non-negative cell reads back as -1, which no length or offset can be.
1 cells 4 > constant sec-wide?
: sec-hi ( u -- hi ) sec-wide? if 32 rshift else drop 0 then ;
: sec-le64! ( u c-addr -- )
  over u32-mask and over u32-le! swap sec-hi swap 4 chars + u32-le! ;
: sec-join ( lo hi -- u|-1 ) dup $80000000 u< if 32 lshift or else 2drop -1 then ;
: sec-narrow ( lo hi -- u|-1 ) if drop -1 else dup 0< if drop -1 then then ;
: sec-le64@ ( c-addr -- u|-1 )
  dup u32-le@ swap 4 chars + u32-le@ sec-wide? if sec-join else sec-narrow then ;

\ The next multiple of 4096 at or above u.
: sec-padded ( u -- u' ) sections-align 1- + sections-align negate and ;
\ unit*count as a length that still pads without overflow, or false.
: sec-bytes ( unit count -- u true | false )
  um* if drop false exit then
  dup sections-align 1- + 0< if drop false else true then ;
\ Entry e's length from its unit size (1 .. 2^32-1) and count, or false.
: sec-size ( e -- u true | false )
  dup sec-unit @ dup 0= over u32-mask u> or if 2drop false exit then
  swap sec-count @ sec-bytes ;
: sec-advance ( pos len -- pos' true | false )
  sec-padded + dup 0< if drop false else true then ;
\ Writing: give e the offset pos and its length; reading: check both are
\ exactly what the layout rule gives (sections follow each other from byte
\ 4096, each padded to 4096), so nothing overlaps, hides or is misaligned.
: sec-assign ( pos e -- pos' true | false )
  dup sec-size 0= if 2drop false exit then
  over sec-length ! 2dup sec-offset ! sec-length @ sec-advance ;
: sec-verify ( pos e -- pos' true | false )
  dup sec-size 0= if 2drop false exit then
  over sec-length @ <> if 2drop false exit then
  2dup sec-offset @ <> if 2drop false exit then
  sec-length @ sec-advance ;

\ SHA-256 of bytes, in the record's digest buffer.
: sec-sum-of ( c-addr u sf -- digest )
  >r r@ sec-hash sha256-init r@ sec-hash sha256-update
  r@ sec-digest r@ sec-hash sha256-final r> sec-digest ;
: sec-u32! ( u offset sf -- ) sec-hdr + u32-le! ;
: sec-u32@ ( offset sf -- u ) sec-hdr + u32-le@ ;
: sec-ior ( ior -- outcome ) if outcome-invalid else outcome-ok then ;

\ Where entry e sits in the header.
: sec-dest ( e sf -- p )
  tuck sec-entries - /sec-entry / sec-slot-bytes * sec-table + swap sec-hdr + ;
: sec-pack-entry ( e sf -- )
  2dup sec-dest nip ( e p )
  over sec-kind @ over u32-le!
  over sec-unit @ over 4 chars + u32-le!
  over sec-count @ over 8 chars + sec-le64!
  over sec-offset @ over 16 chars + sec-le64!
  over sec-length @ over 24 chars + sec-le64!
  swap sec-sha swap 32 chars + 32 chars move ;
: sec-parse-entry ( e sf -- )
  2dup sec-dest nip ( e p )
  dup u32-le@ 2 pick sec-kind !
  dup 4 chars + u32-le@ 2 pick sec-unit !
  dup 8 chars + sec-le64@ 2 pick sec-count !
  dup 16 chars + sec-le64@ 2 pick sec-offset !
  dup 24 chars + sec-le64@ 2 pick sec-length !
  32 chars + over sec-sha 32 chars move drop ;

\ The header's first 4064 bytes get their SHA-256 as the last 32.
: sec-seal ( sf -- )
  dup sec-hdr sec-sum chars 2 pick sec-sum-of
  swap sec-hdr sec-sum chars + 32 chars move ;
: sec-pack-head ( sf -- )
  >r sec-magic r@ sec-hdr swap move
  sec-version 8 r@ sec-u32!  sec-order 12 r@ sec-u32!  r@ sec-n @ 16 r@ sec-u32!
  r@ sec-user r@ sec-hdr 24 chars + sec-fields u32s>le r> drop ;
: sec-pack ( sf -- )
  dup sec-hdr sections-align chars erase
  dup sec-pack-head ['] sec-pack-entry over sec-each sec-seal ;

\ ---- writing
: sec-name! ( c-addr u sf -- outcome )
  >r dup sec-path-room u> if 2drop r> drop outcome-full exit then
  dup r@ sec-pathlen !  r@ sec-path swap move
  r@ sec-path r@ sec-partial r@ sec-pathlen @ move
  s" .partial" r@ sec-partial r@ sec-pathlen @ chars + swap move
  r> drop outcome-ok ;
: sec-final-name ( sf -- c-addr u ) dup sec-path swap sec-pathlen @ ;
: sec-partial-name ( sf -- c-addr u ) dup sec-partial swap sec-pathlen @ 8 + ;
: sec-create ( sf -- outcome )
  dup sec-partial-name w/o bin create-file if 2drop outcome-invalid exit then
  swap sec-fid ! outcome-ok ;
\ Close the file if open; the close's ior, 0 when there was none.
: sec-shut ( sf -- ior )
  >r r@ sec-fid @ ?dup if close-file else 0 then 0 r@ sec-fid ! 0 r> sec-n ! ;
: sec-discard ( sf -- ) dup sec-shut drop sec-partial-name delete-file drop ;
: sec-assign-all ( sf -- outcome )
  ['] sec-assign sections-align rot sec-walk-all if drop outcome-ok else outcome-invalid then ;
: sec-hash-entry ( e sf -- )
  over sec-addr @ 2 pick sec-length @ 2 pick sec-sum-of rot sec-sha 32 chars move drop ;
: sec-write-hdr ( sf -- outcome )
  dup sec-hdr sections-align chars rot sec-fid @ write-file sec-ior ;
: sec-put-data ( e sf -- outcome )
  over sec-addr @ 2 pick sec-length @ 2 pick sec-fid @ write-file sec-ior nip nip ;
\ Zero bytes from the end of the data to the next multiple of 4096.
: sec-put-pad ( e sf -- outcome )
  over sec-length @ dup sec-padded swap -
  over sec-zero swap rot sec-fid @ write-file sec-ior nip ;
: sec-emit-one ( e sf -- outcome )
  2dup sec-put-data ok-then2? 0= if exit then sec-put-pad ;
: sec-write-sections ( i sf -- outcome )
  2dup sec-n @ = if 2drop outcome-ok exit then
  2dup sec-entry over sec-emit-one ok-then2? 0= if exit then
  swap 1+ swap recurse ;
\ Everything between creating the partial and closing it.
: sec-fill ( sf -- outcome )
  dup sec-assign-all ok-then? 0= if exit then
  ['] sec-hash-entry over sec-each
  dup sec-pack
  dup sec-write-hdr ok-then? 0= if exit then
  0 swap sec-write-sections ;
: sec-finish ( sf -- outcome )
  dup sec-shut if drop outcome-invalid exit then
  dup sec-partial-name 2 pick sec-final-name rename-file sec-ior nip ;

\ ---- reading
: sec-check-magic ( sf -- outcome )
  sec-hdr 8 chars sec-magic compare if outcome-invalid else outcome-ok then ;
: sec-check-version ( sf -- outcome )
  8 swap sec-u32@ sec-version = if outcome-ok else outcome-unsupported then ;
: sec-check-order ( sf -- outcome )
  12 swap sec-u32@
  case sec-order of outcome-ok endof
       sec-order-swapped of outcome-unsupported endof
       outcome-invalid swap
  endcase ;
: sec-check-hash ( sf -- outcome )
  dup sec-hdr sec-sum chars 2 pick sec-sum-of
  swap sec-hdr sec-sum chars + >r 32 chars r> 32 chars compare
  if outcome-rejected else outcome-ok then ;
\ The table: its count, the caller's fields and every entry as the layout
\ rule requires, ending exactly at the end of the file.
: sec-check-table ( sf -- outcome )
  16 over sec-u32@ dup sections-max u> if 2drop outcome-invalid exit then
  over sec-n !
  dup sec-hdr 24 chars + over sec-user sec-fields le>u32s
  ['] sec-parse-entry over sec-each
  ['] sec-verify sections-align 2 pick sec-walk-all
  if over sec-filesize @ = else false then nip
  if outcome-ok else outcome-invalid then ;
: sec-check-header ( sf -- outcome )
  dup sec-check-magic ok-then? 0= if exit then
  dup sec-check-version ok-then? 0= if exit then
  dup sec-check-order ok-then? 0= if exit then
  dup sec-check-hash ok-then? 0= if exit then
  sec-check-table ;
\ Read exactly u bytes at a file offset.
: sec-read-at ( c-addr u offset sf -- outcome )
  sec-fid @ >r s>d r@ reposition-file if 2drop r> drop outcome-invalid exit then
  tuck r> read-file if 2drop outcome-invalid exit then
  = if outcome-ok else outcome-invalid then ;
: sec-measure ( sf -- outcome )
  dup sec-fid @ file-size if 2drop drop outcome-invalid exit then
  if 2drop outcome-invalid exit then
  dup sections-align u< over 0< or if 2drop outcome-invalid exit then
  swap sec-filesize ! outcome-ok ;
: sec-read-hdr ( sf -- outcome ) >r r@ sec-hdr sections-align chars 0 r> sec-read-at ;
: sec-load ( sf -- outcome )
  dup sec-measure ok-then? 0= if exit then
  dup sec-read-hdr ok-then? 0= if exit then
  sec-check-header ;
\ Where the bytes of entry e are, as ( addr len offset ) with the caller's addr.
: sec-span ( addr e -- addr len offset ) dup sec-length @ swap sec-offset @ ;
: sec-fetch ( addr e sf -- outcome )
  >r 2dup sec-span r@ sec-read-at
  dup ok? 0= if nip nip r> drop exit then drop
  swap over sec-length @ r> sec-sum-of
  swap sec-sha >r 32 chars r> 32 chars compare
  if outcome-rejected else outcome-ok then ;

lf-lib set-current
\ The record's size in address units; a named record; reset a record (also
\ closes nothing: close an open file first).
/sec-record constant /sections
: sections: ( "name" -- ) align create here /sections allot /sections erase ;
: sections-init ( sf -- ) /sections erase ;
\ Caller's header field i (0 .. 15), a 32-bit value; invalid outside that.
: sections-field! ( u i sf -- outcome )
  over sec-fields u< 0= if drop 2drop outcome-invalid exit then
  rot dup u32-mask u> if drop 2drop outcome-invalid exit then
  -rot sec-user swap u32s + u32! outcome-ok ;
: sections-field@ ( i sf -- u true | false )
  over sec-fields u< 0= if 2drop false exit then
  sec-user swap u32s + u32@ true ;
\ Add a section of count units of unit bytes (1 .. 2^32-1) at addr, with a
\ kind number (0 .. 2^32-1) the caller defines. The block must stay valid
\ until sections-write. Full after 62 sections; invalid for a bad number.
: sections-add ( addr unit count kind sf -- outcome )
  >r dup u32-mask u> if 2drop 2drop r> drop outcome-invalid exit then
  r@ sec-n @ sections-max = if 2drop 2drop r> drop outcome-full exit then
  r@ sec-n @ r@ sec-entry
  tuck sec-kind ! tuck sec-count ! tuck sec-unit ! sec-addr !
  1 r> sec-n +! outcome-ok ;
\ Write the sections added to the file named c-addr u, atomically. The
\ record keeps its table, so sections-open is not needed to read it back, but
\ a file is read with a record given to sections-init.
: sections-write ( c-addr u sf -- outcome )
  >r r@ sec-name! dup ok? 0= if r> drop exit then drop
  r@ sec-create dup ok? 0= if r> drop exit then drop
  r@ ['] sec-fill catch ?dup if nip r> sec-discard throw then
  dup ok? if drop r@ sec-finish then
  dup ok? 0= if r@ sec-discard then r> drop ;
\ Open the file named c-addr u and check the header and the table. Not ok:
\ the file is closed again and the record holds nothing.
: sections-open ( c-addr u sf -- outcome )
  >r r/o bin open-file if drop r> drop outcome-invalid exit then
  r@ sec-fid !  r@ sec-load dup ok? 0= if r@ sec-shut drop then r> drop ;
: sections-count ( sf -- n ) sec-n @ ;
\ Section i (below sections-count) as its table says: kind, unit size,
\ number of units and length in bytes.
: sections-info ( i sf -- kind unit count length )
  sec-entry >r r@ sec-kind @ r@ sec-unit @ r@ sec-count @ r> sec-length @ ;
\ Copy section i into the block at addr, of room bytes (full when smaller
\ than the section's length), and check its SHA-256 (rejected if it differs).
: sections-read ( addr room i sf -- outcome )
  >r dup r@ sections-count u< 0= if 2drop drop r> drop outcome-invalid exit then
  r@ sec-entry
  2dup sec-length @ u< if drop 2drop r> drop outcome-full exit then
  nip r> sec-fetch ;
: sections-close ( sf -- outcome ) sec-shut if outcome-invalid else outcome-ok then ;

lf-lib-private set-current
module-close
base !   \ the BASE this file was loaded with
