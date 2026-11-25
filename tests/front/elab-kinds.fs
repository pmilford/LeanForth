\ Unit tests of src/front/elab-data.fs's registry of the kinds other files
\ add (elab-add-kind), loaded with src/front/simp-data.fs, which adds
\ congr: a key another kind has aborts, whether added or one of the file's
\ own; the registry takes kinds until elab-kinds-most, then aborts; each
\ abort leaves it unchanged. This file never calls context-new, so the
\ registry stays open (tests/front/simp-data.fs tests its seal).
include ../support/tester.fs
require ../../src/front/simp-data.fs

: add-kind ( c-addr u -- ior )
  0 ['] noop 2swap ['] elab-add-kind catch dup if nip nip nip nip else nip then ;
T{ context-sealed? s" congr" add-kind s" tag" add-kind ed-added# -> false -2 -2 1 }T
T{ s" a" add-kind s" b" add-kind s" c" add-kind s" d" add-kind -> 0 0 0 0 }T
T{ s" e" add-kind s" e" ed-kind-index ed-added# -> -2 false elab-kinds-most elab-kinds - }T
T{ s" d" ed-kind-index s" congr" ed-kind-index -> elab-kinds-most 1- true simp-congr-kind true }T
T{ elab-kinds-most 1- ed-kind-name count s" d" compare -> 0 }T
bye
