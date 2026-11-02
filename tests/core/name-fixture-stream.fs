\ Test-only byte stream for interning previewed Lean name records in Forth.
\ Bytes are input data, never Forth source. Export indices map to this run's
\ temporary name IDs; this is not a public format or trusted import boundary.
require ../../src/lib/lib.fs
require ../../src/core/names.fs
decimal
create ns-byte 1 allot
create ns-buffer 255 allot
create ns-map lf-name-capacity cells allot
variable ns-count
variable ns-kind
variable ns-prefix
variable ns-payload

\ Read one required byte or stop without printing a partial mapping.
: ns-byte@ ( -- byte )
  ns-byte 1 stdin read-file throw 1 <> if -1 throw then ns-byte c@ ;

\ Decode one sequential row: export index, component kind, prefix index,
\ and either byte length followed by bytes, or a one-byte numeric component.
: ns-row ( expected-index -- )
  ns-byte@ over <> if drop -1 throw then
  ns-byte@ ns-kind ! ns-byte@ dup 2 pick >= if 2drop -1 throw then
  cells ns-map + @ ns-prefix !
  ns-byte@ ns-payload !
  ns-kind @ lf-name-tag-str = if
    ns-payload @ 0 ?do ns-byte@ ns-buffer i + c! loop
    ns-prefix @ ns-buffer ns-payload @ lf-name-str
  else ns-kind @ lf-name-tag-num = if
    ns-prefix @ ns-payload @ lf-name-num
  else drop -1 throw then then
  0= if drop -1 throw then
  swap cells ns-map + ! ;

\ Print the complete export-index to interned-ID map only after full input.
: ns-run ( -- )
  lf-name-reset 0 ns-map !
  ns-byte@ dup lf-name-capacity >= if drop -1 throw then ns-count !
  ns-count @ 1+ 1 ?do i ns-row loop
  ns-byte 1 stdin read-file throw 0<> if -1 throw then
  ns-count @ 1+ 0 do i . i cells ns-map + @ . cr loop ;
ns-run
bye
