\ Unit tests of src/front/elab-data.fs's registry of the kinds other files
\ add (elab-add-kind, elab-add-kind41), loaded with src/front/simp-data.fs,
\ which adds congr (format 4) and realized (format 4.1): a key another kind
\ has aborts, whether added or one of the file's own; a format-4 kind after
\ a format-4.1 kind aborts (format 4 reads the kinds before the first of
\ 4.1); the registry takes kinds until elab-kinds-most, then aborts; each
\ abort leaves it unchanged. This file never calls context-new, so the
\ registry stays open (tests/front/simp-data.fs tests its seal).
include ../support/tester.fs
require ../../src/front/simp-data.fs

: caught ( c-addr u xt -- ior ) >r 0 ['] noop 2swap r> catch dup if nip nip nip nip else nip then ;
: add-kind ( c-addr u -- ior ) ['] elab-add-kind caught ;
: add-kind41 ( c-addr u -- ior ) ['] elab-add-kind41 caught ;
T{ context-sealed? s" congr" add-kind s" tag" add-kind s" realized" add-kind41 ed-added#
   -> false -2 -2 -2 2 }T
T{ s" a" add-kind s" a" ed-kind-index ed-added# ed-added-v4# -> -2 false 2 1 }T
T{ s" a" add-kind41 s" b" add-kind41 s" c" add-kind41 s" d" add-kind41 -> 0 0 0 0 }T
T{ s" e" add-kind41 s" f" add-kind41 s" g" add-kind41 s" h" add-kind41 -> 0 0 0 0 }T
T{ s" i" add-kind41 s" j" add-kind41 s" k" add-kind41 -> 0 0 0 }T
T{ s" l" add-kind41 s" l" ed-kind-index ed-added# -> -2 false elab-kinds-most elab-kinds - }T
T{ s" k" ed-kind-index s" congr" ed-kind-index -> elab-kinds-most 1- true simp-congr-kind true }T
T{ elab-kinds-most 1- ed-kind-name count s" k" compare -> 0 }T
bye
