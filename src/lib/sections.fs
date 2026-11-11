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
\ FILE.partial, flushed, and renamed over FILE only when complete, so an
\ old FILE survives any failure; the partial is deleted by name on failure,
\ including a THROW while writing (which is then thrown again). Reading:
\ sections-init, sections-open checks everything except the section
\ contents (magic, the header's SHA-256, format version, byte order, then
\ the table: the header rebuilt from its kinds, unit sizes and counts by
\ the layout rule must equal the one read, ending exactly at the end of the
\ file, so a section cannot be truncated, outside, overlapping, misaligned
\ or of a length other than unit size times count), sections-info and
\ sections-field@ report what the table says, sections-read copies a
\ section into the caller's block and checks its SHA-256, sections-close
\ closes the file.
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
1 constant sec-version
$01020304 constant sec-order   \ written little-endian; the other order reads as the next
$04030201 constant sec-order-swapped
500 constant sec-path-room     \ the longest file name; FILE.partial adds 8
: sec-magic ( -- c-addr u ) s" SECTFILE" ;
: sec-suffix ( -- c-addr u ) s" .partial" ;

\ One table entry in the header, little-endian (offsets in address units).
begin-structure /sec-slot
  4 chars +field slot-kind  4 chars +field slot-unit
  8 chars +field slot-count  8 chars +field slot-offset  8 chars +field slot-length
  32 chars +field slot-sha
end-structure
\ The header, 4096 bytes; the spare fields and the unused slots are zero.
begin-structure /sec-head
  8 chars +field head-magic  4 chars +field head-version  4 chars +field head-order
  4 chars +field head-n  4 chars +field head-spare
  sec-fields u32s +field head-user  8 chars +field head-spare2
  sections-max /sec-slot * +field head-table
  32 chars +field head-sum       \ SHA-256 of every byte before it
end-structure
/sec-head sections-align chars <> [if] .( sections.fs: header size ) cr abort [then]

\ One table entry, in memory: the numbers, the caller's block (writing
\ only) and the section's SHA-256.
begin-structure /sec-entry
  field: sec-kind  field: sec-unit  field: sec-count
  field: sec-offset  field: sec-length  field: sec-addr
  32 +field sec-sha
end-structure

\ The record: the open file or the partial, the table, the header bytes and
\ a copy of the header as read.
begin-structure /sec-record
  field: sec-fid  field: sec-n  field: sec-filesize  field: sec-pathlen
  sec-fields u32s +field sec-user
  sections-max /sec-entry * +field sec-entries
  /sha256 +field sec-hash
  32 chars +field sec-digest
  sections-align chars +field sec-hdr
  sections-align chars +field sec-copy
  sections-align chars +field sec-zero
  sec-path-room chars +field sec-path
  sec-path-room 8 + chars +field sec-partial
end-structure

: sec-entry ( i sf -- e ) sec-entries swap /sec-entry * + ;
: sec-slot ( i sf -- p ) sec-hdr head-table swap /sec-slot * + ;
: sec-header ( sf -- c-addr u ) sec-hdr sections-align chars ;
\ Call xt ( i sf -- ) for each entry number i in turn.
: sec-each ( xt sf -- ) dup sec-n @ 0 ?do 2dup i swap rot execute loop 2drop ;
\ Run the steps ( sf -- outcome ) listed at a (0 ends the list) until one
\ is not ok; that outcome, or ok.
: sec-run ( sf a -- outcome )
  dup @ 0= if 2drop outcome-ok exit then
  2dup @ execute dup ok? 0= if nip nip exit then drop cell+ recurse ;

\ Little-endian 64-bit fields as two 32-bit ones. A value that does not fit
\ a non-negative cell reads back as -1, which the layout rule never gives.
1 cells 4 > constant sec-wide?
: sec-hi ( u -- hi ) sec-wide? if 32 rshift else drop 0 then ;
: sec-le64! ( u c-addr -- )
  over u32-mask and over u32-le! swap sec-hi swap 4 chars + u32-le! ;
1 31 lshift constant sec-sign   \ 2^31: a high word from here up does not fit a cell
: sec-join ( lo hi -- u|-1 ) dup sec-sign u< if 32 lshift or else 2drop -1 then ;
: sec-narrow ( lo hi -- u|-1 ) if drop -1 else dup 0< if drop -1 then then ;
: sec-le64@ ( c-addr -- u|-1 )
  dup u32-le@ swap 4 chars + u32-le@ sec-wide? if sec-join else sec-narrow then ;

\ ---- the layout rule
\ The next multiple of 4096 at or above u (u + 4095 must not overflow).
: sec-padded ( u -- u' ) sections-align 1- + sections-align negate and ;
\ A unit size in 1 .. 2^32-1 (also on a 32-bit host, where WITHIN wraps).
: sec-unit? ( u -- flag ) 1 u32-mask 1+ within ;
\ unit*count as a non-negative length that still pads without overflow, or
\ false (for the -1 of an unfit 64-bit field too).
: sec-bytes ( unit count -- u true | false )
  um* if drop false exit then
  dup 0< over sections-align 1- + 0< or if drop false else true then ;
\ Entry e's length from its unit size and count (never negative), or false.
: sec-size ( e -- u true | false )
  dup sec-unit @ sec-unit? 0= if drop false exit then
  dup sec-unit @ swap sec-count @ dup 0< if 2drop false exit then sec-bytes ;
: sec-advance ( pos len -- pos' true | false )
  sec-padded + dup 0< if drop false else true then ;
\ Give e the offset pos and its length: sections follow each other from
\ byte 4096, each padded to 4096, so nothing overlaps, hides or is misaligned.
: sec-assign ( pos e -- pos' true | false )
  dup sec-size 0= if 2drop false exit then
  over sec-length ! 2dup sec-offset ! sec-length @ sec-advance ;
\ Lay every entry out; the end of the last one, or false.
: sec-assign-all ( sf -- pos true | false )
  sections-align swap dup sec-n @ 0 ?do
    i over sec-entry rot swap sec-assign 0= if drop unloop false exit then swap
  loop drop true ;
: sec-layout ( sf -- outcome )
  sec-assign-all if drop outcome-ok else outcome-invalid then ;

\ ---- the header
\ SHA-256 of bytes, in the record's digest buffer.
: sec-digest-of ( sf -- digest ) dup sec-digest tuck swap sec-hash sha256-final ;
: sec-sum-of ( c-addr u sf -- digest )
  dup >r sec-hash dup sha256-init sha256-update r> sec-digest-of ;
\ The bytes the header's SHA-256 covers.
: sec-body ( sf -- c-addr u ) sec-hdr 0 head-sum ;
: sec-body-sum ( sf -- digest ) dup sec-body rot sec-sum-of ;
: sec-seal ( sf -- ) dup sec-body-sum swap sec-hdr head-sum 32 chars move ;
\ Entry e to its table slot p (writing) and slot p to entry e (reading).
: sec-pack-entry ( e p -- )
  over sec-kind @ over slot-kind u32-le!  over sec-unit @ over slot-unit u32-le!
  over sec-count @ over slot-count sec-le64!
  over sec-offset @ over slot-offset sec-le64!
  over sec-length @ over slot-length sec-le64!  swap sec-sha swap slot-sha 32 chars move ;
: sec-parse-entry ( p e -- )
  over slot-kind u32-le@ over sec-kind !  over slot-unit u32-le@ over sec-unit !
  over slot-count sec-le64@ over sec-count !
  over slot-offset sec-le64@ over sec-offset !
  over slot-length sec-le64@ over sec-length !  swap slot-sha swap sec-sha 32 chars move ;
: sec-pack-one ( i sf -- ) 2dup sec-entry -rot sec-slot sec-pack-entry ;
: sec-parse-one ( i sf -- ) 2dup sec-slot -rot sec-entry sec-parse-entry ;
: sec-pack-fixed ( hdr -- )
  sec-version over head-version u32-le!  sec-order over head-order u32-le!
  head-magic sec-magic rot swap move ;
: sec-pack-head ( sf -- )
  dup sec-hdr sec-pack-fixed  dup sec-n @ over sec-hdr head-n u32-le!
  dup sec-user swap sec-hdr head-user sec-fields u32s>le ;
\ The whole header from the record: fields, table, zeros, its SHA-256.
: sec-pack ( sf -- )
  dup sec-header erase dup sec-pack-head ['] sec-pack-one over sec-each sec-seal ;

\ ---- writing
: sec-ior ( ior -- outcome ) if outcome-invalid else outcome-ok then ;
\ Copy c-addr u to dest; the address after it.
: sec-put ( c-addr u dest -- dest' ) swap 2dup + >r move r> ;
: sec-final-name ( sf -- c-addr u ) dup sec-path swap sec-pathlen @ ;
: sec-partial-name ( sf -- c-addr u ) dup sec-partial swap sec-pathlen @ 8 + ;
: sec-name-in ( c-addr u sf -- ) 2dup sec-pathlen ! sec-path swap move ;
: sec-name-partial ( sf -- )
  dup sec-final-name rot sec-partial sec-put sec-suffix rot sec-put drop ;
: sec-name! ( c-addr u sf -- outcome )
  over sec-path-room u> if drop 2drop outcome-full exit then
  dup >r sec-name-in r> sec-name-partial outcome-ok ;
: sec-create ( sf -- outcome )
  dup sec-partial-name w/o bin create-file if 2drop outcome-invalid exit then
  swap sec-fid ! outcome-ok ;
: sec-start ( c-addr u sf -- outcome )
  dup >r sec-name! dup ok? if drop r@ sec-create then r> drop ;
\ Close the file if open and forget the table; the close's ior, 0 when
\ there was none.
: sec-forget ( sf -- ) 0 over sec-fid ! 0 swap sec-n ! ;
: sec-shut ( sf -- ior ) dup sec-fid @ ?dup if close-file else 0 then swap sec-forget ;
: sec-discard ( sf -- ) dup sec-shut drop sec-partial-name delete-file drop ;
: sec-data ( e -- addr len ) dup sec-addr @ swap sec-length @ ;
: sec-hash-entry ( e sf -- ) over sec-data rot sec-sum-of swap sec-sha 32 chars move ;
: sec-hash-one ( i sf -- ) tuck sec-entry swap sec-hash-entry ;
\ Hash every section, then build the header.
: sec-prepare ( sf -- outcome ) ['] sec-hash-one over sec-each sec-pack outcome-ok ;
: sec-write-hdr ( sf -- outcome ) dup sec-header rot sec-fid @ write-file sec-ior ;
: sec-put-data ( e sf -- outcome ) swap sec-data rot sec-fid @ write-file sec-ior ;
\ Zero bytes from the end of the data to the next multiple of 4096.
: sec-gap ( e -- u ) sec-length @ dup sec-padded swap - ;
: sec-put-pad ( e sf -- outcome )
  swap sec-gap over sec-zero swap rot sec-fid @ write-file sec-ior ;
: sec-emit-one ( e sf -- outcome )
  2dup sec-put-data ok-then2? 0= if exit then sec-put-pad ;
: sec-write-from ( i sf -- outcome )
  2dup sec-n @ = if 2drop outcome-ok exit then
  2dup sec-entry over sec-emit-one ok-then2? 0= if exit then
  swap 1+ swap recurse ;
: sec-write-data ( sf -- outcome ) 0 swap sec-write-from ;
\ Everything between creating the partial and closing it, in order.
create sec-writing
  ' sec-layout , ' sec-prepare , ' sec-write-hdr , ' sec-write-data , 0 ,
: sec-fill ( sf -- outcome ) sec-writing sec-run ;
\ Flush and close the partial, then rename it over the final name.
: sec-flush ( sf -- ior ) sec-fid @ flush-file ;
: sec-finish ( sf -- outcome )
  dup sec-flush over sec-shut or if drop outcome-invalid exit then
  dup sec-partial-name rot sec-final-name rename-file sec-ior ;
\ Fill and rename the open partial; a THROW deletes it and is thrown again.
: sec-complete ( sf -- outcome )
  dup ['] sec-fill catch ?dup if nip swap sec-discard throw then
  ok-then? if sec-finish then ;
\ Delete the partial unless the outcome is ok.
: sec-keep ( outcome sf -- outcome ) over ok? if drop else sec-discard then ;

\ ---- reading
: sec-check-magic ( sf -- outcome )
  sec-hdr head-magic 8 chars sec-magic compare if outcome-invalid else outcome-ok then ;
: sec-check-hash ( sf -- outcome )
  dup sec-body-sum 32 chars rot sec-hdr head-sum 32 chars compare
  if outcome-rejected else outcome-ok then ;
: sec-check-version ( sf -- outcome )
  sec-hdr head-version u32-le@ sec-version = if outcome-ok else outcome-unsupported then ;
: sec-check-order ( sf -- outcome )
  sec-hdr head-order u32-le@
  case sec-order of outcome-ok endof
       sec-order-swapped of outcome-unsupported endof
       outcome-invalid swap
  endcase ;
: sec-check-count ( sf -- outcome )
  dup sec-hdr head-n u32-le@ dup sections-max u> if 2drop outcome-invalid exit then
  swap sec-n ! outcome-ok ;
\ The caller's fields and every entry, from the header.
: sec-parse ( sf -- outcome )
  dup sec-hdr head-user over sec-user sec-fields le>u32s
  ['] sec-parse-one swap sec-each outcome-ok ;
\ The layout rule, applied to the entries' unit sizes and counts, ends
\ exactly at the end of the file.
: sec-ends? ( sf -- flag )
  dup sec-assign-all if swap sec-filesize @ = else drop false then ;
: sec-keep-copy ( sf -- ) dup sec-hdr swap sec-copy sections-align chars move ;
\ The header rebuilt from the record equals the one read: every offset and
\ length is what the layout rule gives (so the -1 of an unfit field never
\ passes), and the spare fields and the unused slots are zero.
: sec-same? ( sf -- flag )
  dup sec-keep-copy dup sec-pack dup sec-header rot sec-copy over compare 0= ;
: sec-check-table ( sf -- outcome )
  dup sec-ends? 0= if drop outcome-invalid exit then sec-same? flag>outcome ;
\ Read exactly u bytes at a file offset.
: sec-seek ( offset fid -- ior ) >r s>d r> reposition-file ;
: sec-read-exact ( c-addr u fid -- outcome )
  over >r read-file if r> 2drop outcome-invalid exit then r> = flag>outcome ;
: sec-read-at ( c-addr u offset sf -- outcome )
  sec-fid @ tuck sec-seek if drop 2drop outcome-invalid exit then sec-read-exact ;
\ The file's size as a non-negative cell, or false.
: sec-length-of ( fid -- u true | false )
  file-size if 2drop false exit then  if drop false exit then
  dup 0< if drop false else true then ;
: sec-measure ( sf -- outcome )
  dup sec-fid @ sec-length-of 0= if drop outcome-invalid exit then
  swap sec-filesize ! outcome-ok ;
: sec-read-hdr ( sf -- outcome ) >r r@ sec-header 0 r> sec-read-at ;
\ The checks of an opened file, in order: the header's SHA-256 before the
\ numbers it covers.
create sec-reading
  ' sec-measure , ' sec-read-hdr , ' sec-check-magic , ' sec-check-hash ,
  ' sec-check-version , ' sec-check-order , ' sec-check-count , ' sec-parse ,
  ' sec-check-table , 0 ,
: sec-load ( sf -- outcome ) sec-reading sec-run ;
: sec-open ( c-addr u sf -- outcome )
  >r r/o bin open-file if drop r> drop outcome-invalid exit then r> sec-fid ! outcome-ok ;
\ Close the file unless the outcome is ok.
: sec-shut-unless ( outcome sf -- outcome ) over ok? if drop else sec-shut drop then ;
\ Where the bytes of entry e are, as ( addr len offset ) with the caller's addr.
: sec-span ( addr e -- addr len offset ) dup sec-length @ swap sec-offset @ ;
\ The bytes at addr have e's SHA-256.
: sec-matches? ( addr e sf -- flag )
  >r tuck sec-length @ r> sec-sum-of 32 chars rot sec-sha 32 chars compare 0= ;
: sec-fetch ( addr e sf -- outcome )
  >r 2dup sec-span r@ sec-read-at ok-then2? 0= if r> drop exit then
  r> sec-matches? if outcome-ok else outcome-rejected then ;
\ Zero the section's span at addr unless the outcome is ok.
: sec-wipe ( addr e outcome -- outcome )
  dup ok? if nip nip exit then >r sec-length @ erase r> ;
: sec-take ( addr e sf -- outcome ) >r 2dup r> sec-fetch sec-wipe ;
\ Entry i, when it exists and its section fits room bytes; else an outcome.
: sec-room ( room i sf -- e true | outcome false )
  2dup sec-n @ u< 0= if 2drop drop outcome-invalid false exit then
  sec-entry tuck sec-length @ u< if drop outcome-full false else true then ;
\ Store a new section's numbers in the entry after the last; count it only
\ when they are numbers a section can have.
: sec-next ( sf -- e ) dup sec-n @ swap sec-entry ;
: sec-enter ( addr unit count kind e -- )
  tuck sec-kind ! tuck sec-count ! tuck sec-unit ! sec-addr ! ;
: sec-sized? ( e -- flag ) sec-size dup if nip then ;
: sec-entry-ok? ( e -- flag ) dup sec-sized? swap sec-kind @ u32-mask u> 0= and ;
: sec-admit ( sf -- outcome )
  dup sec-next sec-entry-ok?
  if 1 swap sec-n +! outcome-ok else drop outcome-invalid then ;

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
\ until sections-write. Full after 62 sections; invalid for a bad unit
\ size or kind, or a count that is negative or gives a length beyond a cell.
: sections-add ( addr unit count kind sf -- outcome )
  dup sec-n @ sections-max = if 2drop 2drop drop outcome-full exit then
  dup >r sec-next sec-enter r> sec-admit ;
\ Write the sections added to the file named c-addr u, atomically. The
\ record's table is forgotten afterwards: read the file back with
\ sections-init and sections-open.
: sections-write ( c-addr u sf -- outcome )
  dup >r sec-start dup ok? if drop r@ sec-complete r@ sec-keep then r> drop ;
\ Open the file named c-addr u and check the header and the table. Not ok:
\ the file is closed again and the record holds nothing.
: sections-open ( c-addr u sf -- outcome )
  dup >r sec-open dup ok? if drop r@ sec-load then r> sec-shut-unless ;
: sections-count ( sf -- n ) sec-n @ ;
\ Section i (below sections-count) as its table says: kind, unit size,
\ number of units and length in bytes.
: sections-info ( i sf -- kind unit count length )
  sec-entry >r r@ sec-kind @ r@ sec-unit @ r@ sec-count @ r> sec-length @ ;
\ Copy section i into the block at addr, of room bytes (full when smaller
\ than the section's length), and check its SHA-256 (rejected if it
\ differs). The block is untrusted unless the outcome is ok: on any other
\ outcome after the room check, the section's span of the block is zeroed.
: sections-read ( addr room i sf -- outcome )
  dup >r sec-room if r> sec-take else nip r> drop then ;
: sections-close ( sf -- outcome ) sec-shut if outcome-invalid else outcome-ok then ;

lf-lib-private set-current
module-close
base !   \ the BASE this file was loaded with
