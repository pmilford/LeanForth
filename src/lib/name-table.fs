\ Tables of names: read-only tables laid down while loading, each entry a
\ name and the caller's data after it, found by the name's exact bytes.
\ A standalone library for any Forth-2012 system; it needs bytes.fs
\ (counted,) and module.fs (ADR 0010).
\
\   name-table: colours
\   s" red" colours name-entry 1 ,
\   s" green" colours name-entry 2 ,
\   s" green" colours name-table-find name-entry-data @   \ 2
\   s" blue" colours name-table-find                      \ 0
\
\ name-table: ( "name" -- ) makes an empty table; the name gives its
\ address. Any two cells set to 0 serve as an empty table too, such as
\ a field of a module's own record.
\ name-entry ( c-addr u table -- ) appends an entry named c-addr
\ u (at most 255 bytes; a longer name aborts, the table unchanged) to the
\ table; the caller then lays down the entry's data, if any, in the data
\ space (`,`, `c,`, `allot`), before the next entry.
\ name-table-find ( c-addr u table -- entry | 0 ) the first entry, in the
\ order laid down, whose name is c-addr u byte for byte; 0 when none is.
\ name-entry-name ( entry -- c-addr u ) and name-entry-data ( entry --
\ a-addr ) its name and the aligned address of its data.
\ name-table-each ( table xt -- ) runs xt ( entry -- ) on each entry in
\ order; xt must leave the stack below its argument as it was.
\ An entry is a link cell to the next entry (0 for the last), then the
\ counted name, then the data; the table is two cells, its first and its
\ last entry. Entries of one table may lie apart in the data space, so
\ other definitions may come between them.
\
\ Profile (docs/development/FORTH_LIBRARY.md, "Name tables"): a linear
\ scan from the first entry, one COMPARE per entry (most stop at the
\ first byte), no memory beyond the table, no recursion; the cost grows
\ with the entries before the hit, so it suits tables of tens to a few
\ hundred names, not a dictionary of millions.
\ State: none; tables are constant after loading. Untrusted. Loads in
\ decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ./bytes.fs
require ./module.fs

lf-lib-private module-open
\ The table's last entry, where the next one is linked.
: ntab-last ( table -- a-addr ) cell+ ;
: ntab-tail ( table -- a-addr ) dup ntab-last @ ?dup if nip then ;
\ Whether entry's name is c-addr u, keeping both.
: ntab-named? ( c-addr u entry -- c-addr u entry flag )
  >r 2dup r@ cell+ count compare 0= r> swap ;

lf-lib set-current
: name-table: ( "name" -- ) create 0 , 0 , ;
: name-entry-name ( entry -- c-addr u ) cell+ count ;
: name-entry-data ( entry -- a-addr ) name-entry-name + aligned ;
: name-entry ( c-addr u table -- )
  over 255 > abort" name-entry: a name over 255 bytes"
  align here over ntab-tail ! here swap ntab-last ! 0 , counted, ;
: name-table-find ( c-addr u table -- entry | 0 )
  @ begin dup while ntab-named? if nip nip exit then @ repeat nip nip ;
: name-table-each ( table xt -- )
  swap @ begin dup while 2dup swap execute @ repeat 2drop ;

module-close
base !   \ the BASE this file was loaded with
