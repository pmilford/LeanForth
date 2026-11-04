\ Unit tests of src/import/manifest.fs, the words around the check itself
\ (tests/core/test_export_manifest.py covers every manifest and file case
\ through the counting tool): a checked read of a fixture with its
\ manifest; the tap removed and the manifest's text released after every
\ read, also after a THROW from a handler, which passes on with the file
\ closed; a manifest named with manifest-use used for one read only; a
\ file name too long for the default manifest name; the export's error
\ fields after a manifest failure; the heap blocks given back by
\ manifest-free and export-free. Loaded under HEX: loading must not
\ depend on BASE, and must leave BASE as it found it.
include ../support/tester.fs
include ../support/heap-watch.fs
hex require ../../src/import/manifest.fs base @ decimal constant base-after-load

T{ base-after-load manifest-size-limit manifest-name-room -> 16 65536 4096 }T
live-blocks @ constant blocks-at-start
export: ex
manifest: checks
T{ ex export-init ex checks manifest-init -> outcome-ok outcome-ok }T
: accept-all ( record -- outcome ) drop outcome-ok ;
: handlers ( xt -- ) kind-count 0 do dup i ex export-handler ! loop drop ;
' accept-all handlers
: why ( -- c-addr u ) ex export-error 2swap 2drop rot drop ;
: failed-field ( -- c-addr u ) ex export-error 2drop rot drop ;
: line ( -- n ) ex export-error 2drop 2drop ;
: idle? ( -- flag ) ex export-tap @ 0= checks manifest-text @ 0= and ;
: composition ( -- c-addr u ) s" tests/reference/composition.ndjson" ;
: identity ( -- c-addr u ) s" tests/reference/identity.ndjson" ;

\ A checked read: ok, every record counted, the tap gone and the text freed.
T{ composition checks manifest-read idle? line kind-thm ex export-kind-count
   -> outcome-ok true 35 1 }T
T{ checks manifest-digest checks manifest-hex digest>hex checks manifest-hex 64
   s" 7778d2ef5da2f0935fb0180c953afa9371843f4ceec2660122f8c792b9ca2fec" compare -> 0 }T
T{ checks manifest-count 2@ -> 1787 0 }T

\ A THROW from a handler passes on, with the file closed, the tap gone and
\ the text freed; then the export reads again.
: throws ( record -- outcome ) drop 55 throw ;
T{ ' throws kind-app ex export-handler ! composition checks ' manifest-read catch nip nip nip
   ex export-reader reader-fid @ idle? -> 55 0 true }T
' accept-all handlers
T{ composition checks manifest-read idle? -> outcome-ok true }T

\ A manifest named with manifest-use serves one read: identity's manifest
\ for composition differs; the next read uses the default name again.
T{ s" tests/reference/identity.ndjson.manifest.json" checks manifest-use
   composition checks manifest-read why s" export differs from its manifest" compare
   failed-field s" lines" compare line idle? -> outcome-invalid 0 0 0 true }T
T{ composition checks manifest-read checks given? -> outcome-ok false }T
T{ identity checks manifest-read -> outcome-ok }T

\ A missing manifest, and an export name too long for the default name
\ (4,096 characters with the suffix): invalid at line 0, nothing read.
create long-name 4096 allot  long-name 4096 char x fill
T{ s" tests/reference/no-such.ndjson" checks manifest-read
   why s" manifest missing, unreadable or too large" compare line idle? -> outcome-invalid 0 0 true }T
T{ long-name 4096 14 - 1+ checks manifest-read why s" manifest file name too long" compare line
   -> outcome-invalid 0 0 }T
T{ long-name 4096 14 - checks manifest-read
   why s" manifest missing, unreadable or too large" compare -> outcome-invalid 0 }T

\ manifest-free and export-free give back every heap block; manifest-init
\ again frees the old view first.
: blocks ( -- n ) live-blocks @ blocks-at-start - ;
T{ blocks ex checks manifest-init blocks -> 5 outcome-ok 5 }T
T{ checks manifest-free ex export-free blocks -> 0 }T
bye
