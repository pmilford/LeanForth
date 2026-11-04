\ Tests of src/lib/text-run.fs, outside the checker: the interpreter's
\ settings saved and restored, a whole file read, lines split, the
\ plain-text rule, and the example of the file's header. Run from the
\ repository root.
include ../support/tester.fs
require ../../src/lib/text-run.fs

\ Settings: a search order of three, another compilation word list and
\ BASE sixteen come back exactly, whatever was set in between.
wordlist constant w1
wordlist constant w2
create kept /run-settings allot
create before /run-settings allot
: odd ( -- ) forth-wordlist w1 w2 3 set-order w2 set-current hex ;
: other ( -- ) w1 1 set-order forth-wordlist set-current decimal ;
: order= ( -- flag )
  get-order 3 = >r w2 = r> and >r w1 = r> and >r forth-wordlist = r> and ;
: round-trip ( -- order? current? base? )
  before run-settings-save odd kept run-settings-save other kept run-settings-restore
  order= get-current w2 = base @ 16 = before run-settings-restore ;
T{ round-trip -> true true true }T
T{ kept run-settings-order# @ 0 kept run-settings-wid @ -> 3 w2 }T
T{ base @ get-current forth-wordlist = -> 10 true }T

\ Files: a missing file, a directory, a file in a buffer larger than it,
\ and one in a buffer it fills, which may be longer.
create file-buffer 4096 chars allot
T{ s" tests/lib/no-such-file" file-buffer 4096 file-slurp 0<> -> 0 true }T
T{ s" src" file-buffer 4096 file-slurp 0<> -> 0 true }T
T{ s" tests/program/ir/clamp.ir" file-buffer 4096 file-slurp -> 296 0 }T
T{ file-buffer 9 s" lf-ir 0.1" compare -> 0 }T
T{ s" tests/program/ir/clamp.ir" file-buffer 10 file-slurp -> 10 0 }T

\ Lines: the first line's length and whether an LF ends it; one CR
\ before it dropped.
T{ s\" ab\ncd" text-line-end -> 2 true }T
T{ s" abcd" text-line-end -> 4 false }T
T{ s\" \n" text-line-end -> 0 true }T
T{ s" " text-line-end -> 0 false }T
T{ s\" ab\r" text-cr-drop nip -> 2 }T
T{ s\" ab\r\r" text-cr-drop nip -> 3 }T
T{ s" " text-cr-drop nip -> 0 }T

\ Plain text: printable ASCII, spaces and tabs only.
T{ s\" a b\tc~" text-plain-at -> 6 }T
T{ s\" ab\x7f" text-plain-at -> 2 }T
T{ s\" a\rb" text-plain-at -> 1 }T
T{ s\" \x00" text-plain-at -> 0 }T
T{ s\" ab\xe9" text-plain-at -> 2 }T
T{ s\" \x0c" text-plain-at -> 0 }T

\ The header's example: one line of plain text with only my-words visible
\ and BASE ten; the caller's settings come back however the line ends.
create saved /run-settings allot
wordlist constant my-words
get-current my-words set-current
: seven ( -- n ) 7 ;
set-current
: run-line ( c-addr u -- code )
  2dup text-plain-at over <> if 2drop -1 exit then
  saved run-settings-save my-words 1 set-order decimal
  ['] evaluate catch dup if nip nip then saved run-settings-restore ;
hex
T{ s" seven 10" run-line -> 7 #10 0 }T
T{ s" seven dup" run-line base @ -> #-13 #16 }T
T{ s\" seven\x00" run-line -> -1 }T
decimal
T{ depth -> 0 }T
bye
