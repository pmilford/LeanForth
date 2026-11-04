\ Side columns of a growable store (ADR 0016 C9 step 3): per-index data
\ that modules keep beside the term or level store, such as the stamps of
\ constant and Sort nodes or a pass's "seen" marks, one unit per record
\ index. A column grows with its store, so that every index below the
\ store's capacity has a unit; a unit is zero until written, and a
\ rollback or reset of the store leaves units as they are (as the fixed
\ arrays they replace did). Untrusted.
\
\ A group (column-group:) belongs to one store, given as an xt ( -- store
\ ), usually a heap store of lib/store.fs. Its owner calls columns-cover
\ after the store may have grown and before a new record is used; a
\ module adds a column with column-add, after declaring its member:
\   /slab context-record: my-marks
\   1 cells ' my-marks lf-term-columns column-add
\ Then n my-marks column-at is unit n's address, valid until the store
\ next grows. Outcomes: ok, full (no heap, or the test hook of
\ lib/store.fs refuses the growth: nothing changed), invalid.
\
\ State: each column is a checker-context member (a lib/slab.fs record,
\ heap-owning); the group and column descriptors are laid down while
\ loading and read-only afterwards. Each group registers one setup word,
\ which sizes every column of the group in a new context, and one
\ teardown word, which frees them (lib/context.fs). Single-threaded within
\ one context.

require ../lib/lib.fs
require ../lib/slab.fs

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
: group-capacity ( group -- n ) group-store@ store-capacity @ ;
\ Run xt ( column -- ) for every column of the group, newest first.
: columns-each ( xt group -- )
  group-newest @ begin ?dup while
    2dup >r >r swap execute r> r> column-link @
  repeat drop ;

\ Units. Unchecked: i is below the store's capacity.
: column-at ( i slab -- addr ) slab-at ;
\ Zero every unit.
: column-erase ( slab -- ) dup 0 swap slab-at swap slab-bytes erase ;

\ Growing a column to n units, the new ones zeroed.
: column-clear-from ( old slab -- )
  >r dup r@ slab-at swap r@ slab-capacity swap - r> slab-unit * erase ;
: column-reserve ( n slab -- outcome )
  dup slab-capacity >r tuck slab-reserve dup ok? if r@ rot column-clear-from else nip then
  r> drop ;
: column-slab ( column -- slab ) column-xt @ execute ;
: column-short? ( n column -- flag ) column-slab slab-capacity > ;
\ Make the column's empty slab of units of its width.
: column-init ( column -- outcome )
  dup column-width @ max-n over / rot column-slab slab-init ;

\ Whether a column is shorter than the store's capacity; cover every
\ column: ok, or the first failure (the hook of lib/store.fs is asked
\ once before any column grows, as for the store's own block).
: columns-short? ( group -- flag )
  false swap dup group-capacity swap
  group-newest @ begin ?dup while >r dup r@ column-short? rot or swap r> column-link @
  repeat drop ;
: column-cover ( n column -- n outcome ) >r dup r> column-slab column-reserve ;
: columns-grow ( group -- outcome )
  dup group-capacity outcome-ok rot group-newest @ begin ?dup while
    over ok? 0= if drop nip exit then
    nip >r r@ column-cover r> column-link @
  repeat nip ;
: columns-cover ( group -- outcome )
  dup columns-short? 0= if drop outcome-ok exit then
  dup group-store@ store-grow-refused? if drop outcome-full exit then columns-grow ;

\ Setting up and tearing down every column of a group in the current
\ context.
: column-setup ( column -- ) column-init drop ;
: columns-setup ( group -- )
  ['] column-setup over columns-each columns-cover ok? 0= abort" columns: no heap" ;
: column-free ( column -- ) column-slab slab-free ;
: columns-free ( group -- ) ['] column-free swap columns-each ;

\ Define a group of the store xt ( -- store ). The owner then registers,
\ after its store's own setup, a setup word that runs columns-setup and a
\ teardown word that runs columns-free on the group.
: column-group: ( xt "name" -- )
  create here /column-group allot tuck group-store ! 0 swap group-newest ! ;
\ Add a column of units of width address units, the member xt ( -- slab )
\ (a /slab context record declared just before), to a group, and make it
\ in the current (the main) context at once.
: column-link-in ( column group -- )
  2dup group-newest @ swap column-link ! group-newest ! ;
: column-add ( width xt group -- )
  >r align here /column allot tuck column-xt ! tuck column-width ! dup r@ column-link-in
  dup column-setup r> group-capacity swap column-slab column-reserve
  ok? 0= abort" columns: no heap" ;
