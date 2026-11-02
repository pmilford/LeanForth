\ Emit test-only integer fields for the reconstructed composition DAG.
\ This table is neither a term interchange format nor a proof certificate.
require ../../src/core/terms.fs
include ../support/term-cases.fs
include ../support/composition.fs
decimal

\ Print each node index, tag, first field and second field in arena order.
: emit-composition-table ( -- )
  build-composition
  lf-term-count @ 0 do
    i . i lf-term-read 0= if -1 throw then
    >r >r . r> . r> . cr
  loop ;
emit-composition-table
bye
