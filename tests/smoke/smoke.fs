include ../../src/leanforth.fs

: smoke-check ( -- )
  21 lf-double 42 <> if -1 throw then
  -7 lf-double -14 <> if -1 throw then ;

smoke-check
bye
