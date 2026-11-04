\ Side columns of a growable store (ADR 0016 C9 step 3): per-index data
\ kept beside a store of lib/store.fs, one unit per record index, such as
\ LeanForth's stamps of constant and Sort terms or a pass's "seen" marks.
\ A column grows with its store, so that every index below the store's
\ capacity has a unit; a unit is zero until written, and a rollback or
\ reset of the store leaves units as they are (as fixed arrays would).
\ General: it knows stores and slabs (lib/slab.fs), nothing of Lean.
\ Untrusted.
\
\ A group (column-group:) belongs to one store, given as an xt ( -- store
\ ), usually a heap store. Its owner calls columns-cover (or the cheap
\ columns-ready) after the store may have grown and before a new record
\ is used; a column is added with column-add, after declaring its member,
\ an xt ( -- slab ) such as a context record (lib/context.fs):
\   store-header context-record: things          \ a heap store of 8-cell records
\   :noname ( -- ) 16 8 cells 0 things store-heap-init drop ; context-setup
\   ' things column-group: thing-columns
\   :noname ( -- ) thing-columns columns-setup ; context-setup
\   :noname ( -- ) thing-columns columns-free ; context-teardown
\   /slab context-record: thing-marks
\   1 cells ' thing-marks thing-columns column-add   \ one cell per thing
\   things store-grow drop thing-columns columns-cover drop
\   5 thing-marks column-at                          \ unit 5's address
\ A unit's address is valid until the store next grows. Outcomes: ok,
\ full (no heap, or the test hook of lib/store.fs refuses the growth: no
\ column changed, though the store's own block may already have grown,
\ which is harmless), invalid.
\
\ State: each column is its owner's member (a lib/slab.fs record,
\ heap-owning, usually a context member); the group and column
\ descriptors are laid down while loading and read-only afterwards. The
\ owner registers one setup word, which sizes every column of the group,
\ and one teardown word, which frees them. Single-threaded per member.
\ Helpers are private (ADR 0010).

require ./store.fs
require ./slab.fs
require ./outcome.fs
require ./module.fs

lf-lib-private module-open

begin-structure /column-group
  field: group-store       \ xt ( -- store )
  field: group-newest      \ the newest column descriptor, or 0
end-structure

begin-structure /column
  field: column-link       \ the column added before, or 0
  field: column-xt         \ xt ( -- slab ) of the member
  field: column-width      \ address units per unit
end-structure

: group-store@ ( group -- store ) group-store @ execute ;
lf-lib set-current
\ The store's capacity, which every column covers once columns-cover is ok.
: group-capacity ( group -- n ) group-store@ store-capacity @ ;
\ Run xt ( column -- ) for every column of the group, newest first; xt
\ may use the stack below the column.
: columns-each ( xt group -- )
  group-newest @ begin ?dup while
    2dup >r >r swap execute r> r> column-link @
  repeat drop ;
\ A column's slab.
: column-slab ( column -- slab ) column-xt @ execute ;

\ Units. Unchecked: i is below the store's capacity.
: column-at ( i slab -- addr ) slab-at ;
\ Zero every unit.
: column-erase ( slab -- ) dup 0 swap slab-at swap slab-bytes erase ;
lf-lib-private set-current

\ Growing a column to n units, the new ones zeroed.
: column-clear-from ( old slab -- )
  >r dup r@ slab-at swap r@ slab-capacity swap - r> slab-unit * erase ;
lf-lib set-current
: column-reserve ( n slab -- outcome )
  dup slab-capacity >r tuck slab-reserve dup ok? if r@ rot column-clear-from else nip then
  r> drop ;
lf-lib-private set-current
: column-short? ( n column -- flag ) column-slab slab-capacity > ;
\ Make the column's empty slab of units of its width.
: column-init ( column -- outcome )
  dup column-width @ max-n over / rot column-slab slab-init ;

\ Whether a column is shorter than the store's capacity; cover every
\ column: ok, or the first failure (the hook of lib/store.fs is asked
\ once before any column grows, as for the store's own block).
: column-shorter ( flag n column -- flag' n ) over swap column-short? rot or swap ;
: columns-short? ( group -- flag )
  false over group-capacity rot ['] column-shorter swap columns-each drop ;
: column-cover ( n column -- n outcome ) >r dup r> column-slab column-reserve ;
: column-covered ( n outcome column -- n outcome' ) over ok? if nip column-cover else drop then ;
: columns-grow ( group -- outcome )
  dup group-capacity outcome-ok rot ['] column-covered swap columns-each nip ;
lf-lib set-current
: columns-cover ( group -- outcome )
  dup columns-short? 0= if drop outcome-ok exit then
  dup group-store@ store-grow-refused? if drop outcome-full exit then columns-grow ;
\ The cheap form before each new record: mark is a cell of the owner's
\ holding the store capacity the columns last covered; only a different
\ capacity runs columns-cover. Columns never shrink, so an equal capacity
\ is still covered.
: columns-ready ( mark group -- flag )
  over @ over group-capacity = if 2drop true exit then
  dup columns-cover ok? if group-capacity swap ! true else 2drop false then ;
lf-lib-private set-current

\ Setting up and tearing down every column of a group.
: column-setup ( column -- ) column-init drop ;
lf-lib set-current
: columns-setup ( group -- )
  ['] column-setup over columns-each columns-cover ok? 0= abort" columns: no heap" ;
lf-lib-private set-current
: column-free ( column -- ) column-slab slab-free ;
lf-lib set-current
: columns-free ( group -- ) ['] column-free swap columns-each ;
lf-lib-private set-current

\ Define a group of the store xt ( -- store ). The owner then registers,
\ after its store's own setup, a setup word that runs columns-setup and a
\ teardown word that runs columns-free on the group.
lf-lib set-current
: column-group: ( xt "name" -- )
  create here /column-group allot tuck group-store ! 0 swap group-newest ! ;
lf-lib-private set-current
\ Add a column of units of width address units, the member xt ( -- slab )
\ (a slab record declared just before), to a group, and make it in the
\ current context (the main one, while loading) at once.
: column-link-in ( column group -- )
  2dup group-newest @ swap column-link ! group-newest ! ;
lf-lib set-current
: column-add ( width xt group -- )
  >r align here /column allot tuck column-xt ! tuck column-width ! dup r@ column-link-in
  dup column-setup r> group-capacity swap column-slab column-reserve
  ok? 0= abort" columns: no heap" ;

module-close
