require test/ttester.fs
include ../../src/leanforth.fs
T{ 21 lf-double -> 42 }T
T{ -7 lf-double -> -14 }T
: finish-tests #errors @ if -1 throw then ;
finish-tests
bye
