\ IR 0.2 probe 3 (ADR 0019 Amendment 1): the bytes EMIT writes for
\ values outside printable ASCII. Pipe the output through od to see them:
\   timeout -k 5 30 gforth p03-emit.fs </dev/null | od -An -c
\ Each value is emitted between [ and ]: 65, 0, 9, 200, 255, 256 + 65,
\ 955 (Greek small lambda, U+03BB), -1.
: one ( x -- ) [char] [ emit emit [char] ] emit ;
65 one 0 one 9 one 200 one 255 one 321 one 955 one -1 one
bye
