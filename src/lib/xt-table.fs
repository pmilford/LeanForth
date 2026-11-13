\ Tables of execution tokens indexed by a small number, for a dispatch by
\ a tag or a code that comes from data (plan task 9.4.5, the item-2 Forth
\ review's L5): a node's tag, a log step's rule. A general tool with no
\ Lean knowledge; untrusted.
\
\ xt-table: ( n default "name" -- ) makes name ( -- table ), a table of n
\ entries (n at least 1), each the default xt; a bad n aborts before
\ anything is defined. xt-table! ( xt i table -- ) sets entry i, and
\ aborts for an i outside 0 .. n-1, so filling a table while loading
\ never writes outside it. xt-table@ ( i table -- xt ) gives entry i, or
\ the default for any other i, negative or too large: an index read from
\ data needs no check of its own. Tables are filled while loading and
\ read-only afterwards, so tasks may read one table at once.
\
\ Example: a word for each of the tags 1 and 3, any other tag invalid.
\   : one ( -- ) ;   : three ( -- ) ;   : invalid ( -- ) ;
\   4 ' invalid xt-table: by-tag
\   ' one 1 by-tag xt-table!   ' three 3 by-tag xt-table!
\   3 by-tag xt-table@ execute   \ three
\   9 by-tag xt-table@ execute   \ invalid
\
\ Interface: /xt-table xt-table: xt-table! xt-table@ xt-table-size
\ xt-table-default; every other word is private (lf-lib-private; ADR 0010).
\ State: none of its own; each table is a dictionary record made by
\ xt-table:, written only while loading.

require ./portability.fs
require ./bounds.fs
require ./module.fs

lf-lib-private module-open

lf-lib set-current
begin-structure /xt-table
  field: xt-table-size       \ entries, at least 1
  field: xt-table-default    \ the xt of every entry not set, and of any other index
end-structure
lf-lib-private set-current
: xt-table-at ( i table -- addr ) /xt-table + swap cells + ;
: xt-table-in? ( i table -- flag ) xt-table-size @ index? ;
: xt-table-fill ( table -- )
  dup xt-table-size @ 0 ?do dup xt-table-default @ over i swap xt-table-at ! loop drop ;
: xt-table-room ( n -- n ) dup 1 max-n 1 cells / within 0= abort" xt-table: bad size" ;

lf-lib set-current
: xt-table: ( n default "name" -- )
  swap xt-table-room create here >r dup , swap , cells allot r> xt-table-fill ;
: xt-table! ( xt i table -- )
  2dup xt-table-in? 0= abort" xt-table!: index outside the table" xt-table-at ! ;
: xt-table@ ( i table -- xt )
  2dup xt-table-in? if xt-table-at @ else nip xt-table-default @ then ;

module-close
