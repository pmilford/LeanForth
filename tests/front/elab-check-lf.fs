\ The elaboration data's step of `leanforth check FILE.lf`
\ (src/cli/check-lf.fs, plan row FE1d; review fe1d L2, I3): with a library
\ read without its manifest (--no-manifest), the library file is hashed
\ again and the data read against that SHA-256; when the hash's buffer
\ cannot be allocated (tests/support/heap-watch.fs refuses it), the data
\ is refused as full with error 26 at line 0, nothing loaded, and the next
\ read is ok again. tests/front/test_elab_data.py runs the rest through the
\ command line.
include ../support/tester.fs
include ../support/heap-watch.fs
require ../../src/cli/leanforth-text.fs

: slice ( -- c-addr u ) s" tests/author/init-slice.ndjson" ;
T{ slice lfc-env! s" tests/front/init-slice.elab.ndjson" lfc-elab-file! -> }T
T{ 12 ck-stage stage-init slice ck-stage stage-read-unchecked -> outcome-ok outcome-ok }T
T{ ck-importing? ck-state ck-checked-read @ -> false false }T

\ Read against the library file hashed here.
T{ lfc-elab-read elab-loaded? elab-instance elab-count -> outcome-ok true 3 }T

\ The hash's buffer refused: full, error 26, nothing kept, no block left.
: blocks ( -- n ) live-blocks @ ;
T{ blocks 1 heap-refusals ! lfc-elab-read 0 heap-refusals ! blocks rot - -> outcome-full 0 }T
T{ elab-error-code elab-error-line elab-loaded? elab-instance elab-count -> 26 0 false 0 }T
T{ elab-error-why s" the library's export could not be hashed" compare -> 0 }T
T{ lfc-elab-read elab-loaded? -> outcome-ok true }T

\ The data's line (leanforth-text.fs's cli-elab-format4 and
\ cli-elab-format41): nothing more for the init slice's format-3.2 data;
\ the simp slice's format-4.1 data adds its congruence lemmas and defeq
\ tags, then its realized congruence theorems.
create printed 200 allot  variable printed#
: grab ( c-addr u -- ) tuck printed printed# @ + swap move printed# +! ;
: said ( xt -- c-addr u )
  0 printed# ! action-of type >r ['] grab is type catch r> is type throw printed printed# @ ;
T{ ' cli-elab-format4 said nip ' cli-elab-format41 said nip -> 0 0 }T
T{ ck-stage stage-free -> }T
: simp ( -- c-addr u ) s" tests/front/simp-slice.ndjson" ;
T{ simp lfc-env! s" tests/front/simp-slice.elab.ndjson" lfc-elab-file! -> }T
T{ 12 ck-stage stage-init simp ck-stage stage-read-unchecked -> outcome-ok outcome-ok }T
T{ lfc-elab-read ' cli-elab-format4 said s" , 9 congruence lemmas, 33 defeq tags" compare
   -> outcome-ok 0 }T
T{ ' cli-elab-format41 said s" , 5 realized congruence theorems" compare -> 0 }T
T{ ck-stage stage-free -> }T
bye
