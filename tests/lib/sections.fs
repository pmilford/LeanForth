\ Unit tests of src/lib/sections.fs (sectioned binary files): round trips
\ of 0, 1, 62 sections, empty sections and a section of 2^20 units; the
\ planted faults, each refused with its outcome: wrong magic, byte-order
\ value, format version, truncation at every boundary class, one byte
\ flipped in the header, the table and each section, a section overlapping,
\ outside the file or misaligned, length unequal to unit size times count,
\ a 64-bit length beyond the file, trailing bytes, a THROW while writing
\ (partial deleted, old file intact), a failed rename; and the argument
\ errors. tests/lib/test_sections.py checks the same format with an
\ independent reader and compares the block and field-by-field paths.
\ Run from the project root; scratch files go to /tmp.
include ../support/tester.fs
require ../../src/lib/sections.fs
lf-lib-private order+

s" /tmp/lf-sections-unit.bin" 2constant path
s" /tmp/lf-sections-unit.bin.partial" 2constant path-partial
s" /tmp/lf-sections-unit2.bin" 2constant path2

\ ---- whole-file helpers (the heap block is never freed: tests are short)
: slurp ( c-addr u -- addr n | 0 -1 )
  r/o bin open-file if drop 0 -1 exit then >r
  r@ file-size throw drop dup allocate throw swap
  2dup r@ read-file throw drop r> close-file throw ;
: spit ( addr n c-addr u -- ) w/o bin create-file throw >r r@ write-file throw r> close-file throw ;
: same? ( a1 n1 a2 n2 -- flag ) compare 0= ;
: gone? ( c-addr u -- flag ) r/o bin open-file nip 0<> ;

\ ---- the fixture: four sections (1000 x 4 bytes, an empty one, 5000 x 1,
\ 512 x 8 filling its blocks exactly) and 16 header fields
create a-nat 1000 u32s allot   create a-bytes 4000 allot
create c-bytes 5000 allot      create d-bytes 4096 allot
: pattern ( addr n -- ) 0 ?do i 31 * 251 mod over i + c! loop drop ;
: fixture-data ( -- )
  1000 0 do i i * 7 + a-nat i u32s + u32! loop a-nat a-bytes 1000 u32s>le
  c-bytes 5000 pattern d-bytes 4096 pattern ;
fixture-data
sections: sf   sections: sg
: add-fixture ( -- )
  sf sections-init
  16 0 do i 1000 * 1+ i sf sections-field! drop loop
  a-bytes 4 1000 1 sf sections-add drop
  a-bytes 1 0 2 sf sections-add drop
  c-bytes 1 5000 3 sf sections-add drop
  d-bytes 8 512 4 sf sections-add drop ;
: write-fixture ( c-addr u -- outcome ) add-fixture sf sections-write ;

T{ path write-fixture -> outcome-ok }T
path slurp 2constant orig
T{ orig nip -> 4096 4096 + 8192 + 4096 + }T
T{ path2 write-fixture -> outcome-ok }T
\ Determinism: the same sections give the same bytes.
T{ path2 slurp orig same? -> true }T
T{ path-partial gone? -> true }T

\ ---- reading the fixture back
create rbuf 8192 allot
: read-sec ( i -- outcome ) >r rbuf 8192 r> sf sections-read ;
sf sections-init
T{ path sf sections-open -> outcome-ok }T
T{ sf sections-count -> 4 }T
T{ 0 sf sections-info -> 1 4 1000 4000 }T
T{ 1 sf sections-info -> 2 1 0 0 }T
T{ 2 sf sections-info -> 3 1 5000 5000 }T
T{ 3 sf sections-info -> 4 8 512 4096 }T
T{ 5 sf sections-field@ -> 5001 true }T
T{ 16 sf sections-field@ -> false }T
T{ 0 read-sec -> outcome-ok }T
T{ rbuf 4000 a-bytes 4000 compare -> 0 }T
T{ 1 read-sec -> outcome-ok }T
T{ 2 read-sec -> outcome-ok }T
T{ rbuf 5000 c-bytes 5000 compare -> 0 }T
T{ 3 read-sec -> outcome-ok }T
T{ rbuf 4096 d-bytes 4096 compare -> 0 }T
T{ 4 read-sec -> outcome-invalid }T
T{ rbuf 100 0 sf sections-read -> outcome-full }T
T{ sf sections-close -> outcome-ok }T
T{ 0 read-sec -> outcome-invalid }T   \ closed

\ ---- planted faults: a copy of the file is changed and opened
create work 40000 allot
variable wn
: load-work ( -- ) orig dup wn ! work swap move ;
: try-open ( -- outcome )
  work wn @ path2 spit sf sections-init path2 sf sections-open ;
: attempt ( -- outcome ) try-open sf sections-close drop ;   \ closes at once
: flip ( offset -- ) work + dup c@ 1 xor swap c! ;
: poke32 ( u offset -- ) work + u32-le! ;
sha256: hasher   create dig 32 allot
: resign ( -- )
  hasher sha256-init work 4064 hasher sha256-update dig hasher sha256-final
  dig work 4064 + 32 move ;
: slot ( i field -- offset ) swap 64 * 96 + + ;   \ field: 0 kind 4 unit 8 count 16 offset 24 length

T{ load-work attempt -> outcome-ok }T
T{ load-work 0 flip attempt -> outcome-invalid }T            \ magic
T{ load-work 7 flip attempt -> outcome-invalid }T
T{ load-work $04030201 12 poke32 resign attempt -> outcome-unsupported }T   \ other byte order
T{ load-work 5 12 poke32 resign attempt -> outcome-invalid }T
T{ load-work 2 8 poke32 resign attempt -> outcome-unsupported }T     \ other format version
T{ load-work 0 8 poke32 attempt -> outcome-unsupported }T
\ Truncation: inside the header, at its end, inside a section, in the
\ padding, short by one byte at the very end, and trailing bytes.
T{ load-work 0 wn ! attempt -> outcome-invalid }T
T{ load-work 100 wn ! attempt -> outcome-invalid }T
T{ load-work 4095 wn ! attempt -> outcome-invalid }T
T{ load-work 4096 wn ! attempt -> outcome-invalid }T
T{ load-work 4096 10 + wn ! attempt -> outcome-invalid }T
T{ load-work 8192 wn ! attempt -> outcome-invalid }T
T{ load-work orig nip 4096 - wn ! attempt -> outcome-invalid }T
T{ load-work orig nip 1- wn ! attempt -> outcome-invalid }T
T{ load-work orig nip 1+ wn ! attempt -> outcome-invalid }T
\ One byte flipped in the header (field, table, digest, padding): rejected.
T{ load-work 30 flip attempt -> outcome-rejected }T
T{ load-work 16 flip attempt -> outcome-rejected }T
T{ load-work 100 flip attempt -> outcome-rejected }T
T{ load-work 130 flip attempt -> outcome-rejected }T
T{ load-work 3000 flip attempt -> outcome-rejected }T
T{ load-work 4064 flip attempt -> outcome-rejected }T
T{ load-work 4095 flip attempt -> outcome-rejected }T
\ One byte flipped in each section: the file opens, that section is rejected.
: flipped-section ( offset i -- outcome-of-i ) swap load-work flip try-open drop read-sec ;
T{ 4096 5 + 0 flipped-section -> outcome-rejected }T
T{ sf sections-close -> outcome-ok }T
T{ 8192 4999 + 2 flipped-section -> outcome-rejected }T
T{ 0 read-sec -> outcome-ok }T
T{ sf sections-close -> outcome-ok }T
T{ 16384 4095 + 3 flipped-section -> outcome-rejected }T
T{ sf sections-close -> outcome-ok }T
\ Table faults with the header's SHA-256 recomputed, so only the layout
\ checks can refuse them.
T{ load-work 4096 2 16 slot poke32 resign attempt -> outcome-invalid }T      \ overlapping
T{ load-work 1000000 2 16 slot poke32 resign attempt -> outcome-invalid }T   \ outside the file
T{ load-work 8193 2 16 slot poke32 resign attempt -> outcome-invalid }T      \ misaligned
T{ load-work 12288 2 16 slot poke32 resign attempt -> outcome-invalid }T     \ a gap
T{ load-work 3999 0 24 slot poke32 resign attempt -> outcome-invalid }T      \ length != unit*count
T{ load-work 1 0 28 slot poke32 resign attempt -> outcome-invalid }T         \ 64-bit length beyond the file
T{ load-work $80000000 0 28 slot poke32 resign attempt -> outcome-invalid }T
T{ load-work 1 2 12 slot poke32 resign attempt -> outcome-invalid }T         \ 64-bit count beyond the file
T{ load-work 0 0 4 slot poke32 resign attempt -> outcome-invalid }T          \ unit size 0
T{ load-work 63 16 poke32 resign attempt -> outcome-invalid }T               \ more sections than fit
T{ load-work 2 16 poke32 resign attempt -> outcome-invalid }T                \ fewer: file too long
T{ load-work work 40000 erase attempt -> outcome-invalid }T                  \ all zeros
T{ load-work attempt -> outcome-ok }T
T{ s" /tmp/lf-sections-missing.bin" sf sections-open -> outcome-invalid }T

\ ---- other numbers of sections
create tiny 8 allot
: write-empty ( -- outcome ) sg sections-init path2 sg sections-write ;
T{ write-empty -> outcome-ok }T
T{ path2 slurp nip -> 4096 }T
T{ path2 sf sections-open sf sections-count sf sections-close -> outcome-ok 0 outcome-ok }T
: add-many ( n -- ) 0 ?do tiny 1 1 i sg sections-add drop loop ;
T{ sg sections-init  62 add-many  tiny 1 1 9 sg sections-add -> outcome-full }T
T{ path2 sg sections-write -> outcome-ok }T
T{ path2 slurp nip -> 4096 62 4096 * + }T
T{ path2 sf sections-open sf sections-count -> outcome-ok 62 }T
T{ 61 sf sections-info -> 61 1 1 1 }T
T{ 61 read-sec -> outcome-ok }T
T{ sf sections-close -> outcome-ok }T

\ A section of 2^20 units of 4 bytes, read back through the block words.
$100000 constant big
big u32s allocate throw constant big-nat
big u32s allocate throw constant big-bytes
big u32s allocate throw constant big-back
big u32s allocate throw constant big-nat2
: fill-big big 0 do i 2654435761 * i xor big-nat i u32s + u32! loop big-nat big-bytes big u32s>le ;
fill-big
T{ sg sections-init  big-bytes 4 big 7 sg sections-add path2 sg sections-write -> outcome-ok outcome-ok }T
T{ path2 slurp nip -> 4096 big 4 * + }T
T{ path2 sf sections-open -> outcome-ok }T
T{ 0 sf sections-info -> 7 4 big big 4 * }T
T{ big-back big 4 * 0 sf sections-read -> outcome-ok }T
T{ big-back big-nat2 big le>u32s-fields  big-nat2 big u32s big-nat big u32s compare -> 0 }T
T{ sf sections-close -> outcome-ok }T

\ ---- failures while writing leave the old file intact and no partial
T{ path write-fixture -> outcome-ok }T
T{ sg sections-init  1 1 4096 1 sg sections-add -> outcome-ok }T
: bad-write ( -- ) path sg sections-write drop ;
T{ ' bad-write catch 0<> -> true }T          \ a THROW (bad address) while hashing
T{ path-partial gone? -> true }T
T{ path slurp orig same? -> true }T
\ A rename that fails: the target is a directory.
T{ sg sections-init  tiny 1 1 1 sg sections-add drop  s" tests/lib" sg sections-write -> outcome-invalid }T
T{ s" tests/lib.partial" gone? -> true }T
\ Argument errors.
create longname 501 allot
T{ sg sections-init  tiny 0 1 1 sg sections-add drop  path2 sg sections-write -> outcome-invalid }T
T{ path-partial gone? -> true }T
T{ sg sections-init  tiny 1 1 $100000000 sg sections-add -> outcome-invalid }T
T{ 1 16 sg sections-field! -> outcome-invalid }T
T{ longname 501 sg sections-write -> outcome-full }T
T{ s" /tmp/lf-sections-no-dir/x.bin" sg sections-write -> outcome-invalid }T

bye
