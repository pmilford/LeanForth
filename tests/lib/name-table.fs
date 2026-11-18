\ Unit tests of src/lib/name-table.fs, tables of names, on their own (no
\ checker loaded): the header's example; the first and the last entry,
\ a name absent, a prefix and an extension of a name, the empty name, a
\ name of 255 bytes, the first of two equal names; entries with no data
\ and with three cells, and entries laid apart; each entry visited once,
\ in order, with the stack below kept; the stack depth after every word.
include ../support/tester.fs
include ../support/checks.fs
require ../../src/lib/name-table.fs

\ The header's example.
name-table: colours
s" red" colours name-entry 1 ,
s" green" colours name-entry 2 ,
T{ s" green" colours name-table-find name-entry-data @ -> 2 }T
T{ s" red" colours name-table-find name-entry-data @ -> 1 }T
T{ s" blue" colours name-table-find -> 0 }T
T{ s" gree" colours name-table-find s" greens" colours name-table-find -> 0 0 }T
T{ s" " colours name-table-find -> 0 }T
T{ s" red" colours name-table-find name-entry-name s" red" compare -> 0 }T

\ Names alone, with no data.
name-table: keywords
s" alpha" keywords name-entry  s" beta" keywords name-entry  s" gamma" keywords name-entry
T{ s" gamma" keywords name-table-find name-entry-name s" gamma" compare -> 0 }T
T{ s" alpha" keywords name-table-find 0<> s" alphas" keywords name-table-find -> true 0 }T
T{ s" " keywords name-table-find s" keywords" keywords name-table-find -> 0 0 }T
\ An empty table; the empty name as an entry's name.
name-table: none
T{ s" alpha" none name-table-find -> 0 }T
s" " none name-entry 7 ,
T{ s" " none name-table-find name-entry-data @ s" x" none name-table-find -> 7 0 }T

\ Three data cells, a name of 255 bytes, two equal names (the first
\ found), and an entry laid after other definitions.
create long 255 allot  long 255 char z fill
name-table: wide
s" a" wide name-entry 10 , 11 , 12 ,
long 255 wide name-entry 20 , 21 , 22 ,
s" a" wide name-entry 30 , 31 , 32 ,
: between ( -- ) ;
s" b" wide name-entry 40 , 41 , 42 ,
T{ long 255 wide name-table-find name-entry-data dup @ swap cell+ 2@ -> 20 22 21 }T
T{ s" a" wide name-table-find name-entry-data @ s" b" wide name-table-find name-entry-data @
  -> 10 40 }T
T{ long 254 wide name-table-find -> 0 }T

\ Every entry once, in order, the stack below kept.
variable seen  0 seen !
: visit ( x entry -- x ) name-entry-data @ seen @ 100 * + seen ! ;
T{ 99 wide ' visit name-table-each -> 99 }T
T{ seen @ -> 10203040 }T
0 seen !
: count-names ( entry -- ) drop 1 seen +! ;
T{ keywords ' count-names name-table-each seen @ -> 3 }T
T{ name-table: empty  empty ' count-names name-table-each seen @ -> 3 }T

T{ depth -> 0 }T
cases-done
bye
