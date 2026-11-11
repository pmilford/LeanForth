\ Driver for tests/lib/test_sections.py. Environment: SECT_CMD is write or
\ read, SECT_PATH the file; SECT_MODE may be fields (lf-u32-fields) or
\ portable (lf-u32-portable), chosen before the library loads.
\ write: the fixture (four sections of 1000 x 4 bytes, none, 5000 x 1, 512 x 8
\ bytes; header field i = 1000 i + 1); prints the outcome.
\ read: prints "open N", then "section i N" for each section read.
: env? ( c-addr u c-addr2 u2 -- flag ) 2>r getenv dup 0= if 2drop 2r> 2drop false exit then
  2r> compare 0= ;
s" SECT_MODE" s" fields" env? [if] : lf-u32-fields ( -- ) ; [then]
s" SECT_MODE" s" portable" env? [if] : lf-u32-portable ( -- ) ; [then]
require ../../src/lib/sections.fs

create a-nat 1000 u32s allot   create a-bytes 4000 allot
create c-bytes 5000 allot      create d-bytes 4096 allot
create rbuf 8192 allot
sections: sf
: pattern ( addr n -- ) 0 ?do i 31 * 251 mod over i + c! loop drop ;
: fixture-data ( -- )
  1000 0 do i i * 7 + a-nat i u32s + u32! loop a-nat a-bytes 1000 u32s>le
  c-bytes 5000 pattern d-bytes 4096 pattern ;
: add-fixture ( -- )
  sf sections-init
  16 0 do i 1000 * 1+ i sf sections-field! drop loop
  a-bytes 4 1000 1 sf sections-add drop
  a-bytes 1 0 2 sf sections-add drop
  c-bytes 1 5000 3 sf sections-add drop
  d-bytes 8 512 4 sf sections-add drop ;
: command ( -- c-addr u ) s" SECT_CMD" getenv ;
: file-name ( -- c-addr u ) s" SECT_PATH" getenv ;
: do-write ( -- ) fixture-data add-fixture file-name sf sections-write . cr ;
: show-section ( i -- ) ." section " dup . rbuf 8192 rot sf sections-read . cr ;
: do-read ( -- )
  sf sections-init file-name sf sections-open dup ." open " . cr
  outcome-ok = if sf sections-count 0 ?do i show-section loop sf sections-close drop then ;
command s" write" compare 0= [if] do-write [then]
command s" read" compare 0= [if] do-read [then]
bye
