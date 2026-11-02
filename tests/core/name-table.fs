\ Emit equality of interned experimental names for pinned Lean comparisons.
\ IDs and byte strings are mutable test data, not a trusted declaration name.
include ../../src/core/names.fs
decimal

\ Require an intern operation to return an ID; failure stops the test.
: require-name ( id true | false -- id ) 0= if -1 throw then ;
lf-name-reset
0 s" u" lf-name-str require-name constant table-name-u
0 s" v" lf-name-str require-name constant table-name-v
table-name-u s" u" lf-name-str require-name constant table-name-nested
0 1 lf-name-num require-name constant table-name-num
0 s" 1" lf-name-str require-name constant table-name-string-num
0 s" é" lf-name-str require-name constant table-name-unicode
0 s" é" lf-name-str require-name constant table-name-decomposed
0 s" " lf-name-str require-name constant table-name-empty
table-name-u 1 lf-name-num require-name constant table-name-nested-num

\ Print case ID and whether the two interned IDs are identical.
: emit-name-equality ( case left right -- )
  = if 1 else 0 then swap . . cr ;
0 table-name-u 0 s" u" lf-name-str require-name emit-name-equality
1 table-name-u table-name-v emit-name-equality
2 table-name-u table-name-nested emit-name-equality
3 table-name-num table-name-string-num emit-name-equality
4 table-name-num 0 1 lf-name-num require-name emit-name-equality
5 table-name-unicode 0 s" é" lf-name-str require-name emit-name-equality
6 table-name-unicode table-name-decomposed emit-name-equality
7 table-name-empty 0 s" " lf-name-str require-name emit-name-equality
8 table-name-nested-num table-name-u 1 lf-name-num require-name emit-name-equality
bye
