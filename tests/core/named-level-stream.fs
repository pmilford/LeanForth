\ Test-only integration of untrusted structured names and level comparison.
\ The byte stream is data, not Forth source or a public interchange format.
\ It creates no theorem, declaration, proof certificate or trusted identity.
\ All three global arenas must remain unchanged during this single process.
include ../../src/experimental/names.fs
include ../../src/experimental/levels.fs
include ../../src/experimental/level-scope.fs
include ../../src/experimental/level-value.fs
include ../../src/experimental/level-compare.fs
decimal
create nl-byte 1 allot
create nl-buffer 255 allot
create nl-name-map lf-name-capacity cells allot
variable nl-names
variable nl-levels
variable nl-context
variable nl-left
variable nl-right
variable nl-index
variable nl-kind
variable nl-first
variable nl-second

\ Read one required byte; the driver emits no output before complete parsing.
: nl-byte@ ( -- byte )
  nl-byte 1 stdin read-file throw 1 <> if -1 throw then nl-byte c@ ;

\ Resolve a validated export name index to this process's interned ID.
: nl-name@ ( export-index -- id )
  dup nl-names @ >= if drop -1 throw then cells nl-name-map + @ ;

\ Intern a name row. Prefixes are export indices strictly before this row.
: nl-name-row ( expected-index -- )
  nl-byte@ over <> if drop -1 throw then
  nl-byte@ nl-kind ! nl-byte@ dup 2 pick >= if 2drop -1 throw then
  nl-name@ nl-first ! nl-byte@ nl-second !
  nl-kind @ lf-name-tag-str = if
    nl-second @ 0 ?do nl-byte@ nl-buffer i + c! loop
    nl-first @ nl-buffer nl-second @ lf-name-str
  else nl-kind @ lf-name-tag-num = if
    nl-first @ nl-second @ lf-name-num
  else drop -1 throw then then
  0= if drop -1 throw then swap cells nl-name-map + ! ;

\ Store a level row. A parameter payload is an export name index, which is
\ resolved through the same name map used for the declaration context.
: nl-level-row ( expected-index -- )
  nl-byte@ over <> if drop -1 throw then nl-index !
  nl-byte@ nl-kind ! nl-byte@ nl-first ! nl-byte@ nl-second !
  nl-kind @ lf-level-tag-zero = if
    nl-index @ nl-first @ or nl-second @ or if -1 throw then exit
  then
  nl-kind @ case
    lf-level-tag-succ of
      nl-second @ if -1 throw then nl-first @ lf-level-succ
    endof
    lf-level-tag-param of
      nl-second @ if -1 throw then nl-first @ nl-name@ lf-level-param
    endof
    lf-level-tag-max of nl-first @ nl-second @ lf-level-max endof
    lf-level-tag-imax of nl-first @ nl-second @ lf-level-imax endof
    -1 throw
  endcase
  0= if -1 throw then nl-index @ <> if -1 throw then ;

\ Header: name count including anonymous, level count including zero, context
\ count, left root and right root; then name rows, level rows and context IDs.
\ Only after parsing the full stream is a comparison emitted. Scope validation
\ covers the two selected roots, not every disconnected staged level node.
: nl-run ( -- )
  lf-name-reset lf-level-reset lf-lscope-context-reset
  nl-byte@ nl-names ! nl-byte@ nl-levels ! nl-byte@ nl-context !
  nl-byte@ nl-left ! nl-byte@ nl-right !
  nl-names @ 1 < nl-names @ lf-name-capacity > or
  nl-levels @ 1 < or nl-levels @ lf-level-capacity > or
  nl-context @ lf-level-capacity > or if -1 throw then
  0 nl-name-map !
  nl-names @ 1 ?do i nl-name-row loop
  nl-levels @ 0 do
    i nl-level-row lf-level-count @ i 0= if 1 else i 1+ then <> if -1 throw then
  loop
  nl-context @ 0 ?do nl-byte@ nl-name@ lf-lscope-context-add 0= if -1 throw then loop
  nl-byte 1 stdin read-file throw 0<> if -1 throw then
  nl-left @ nl-right @ 50000 lf-level-compare . cr
  nl-names @ 0 do i . i cells nl-name-map + @ . cr loop ;
nl-run
bye
