\ Gforth 1.0: which translation tokens does the interpreter use for a
\ word and for a number?
s" dup" rec-forth .s cr 2drop
s" 5" rec-forth .s cr 2drop
.( translate-name: ) translate-name . cr
.( translate-cell: ) translate-cell . cr
[defined] translate-nt [if] .( ' translate-nt: ) ' translate-nt . cr [then]
[defined] translate-num [if] .( ' translate-num: ) ' translate-num . cr [then]
bye
