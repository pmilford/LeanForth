\ The tester must accept a passing suite; bad-value.fs and bad-depth.fs
\ check that it rejects failures (see check.sh).
include ../support/tester.fs
: double ( n -- 2n ) dup + ;
T{ 21 double -> 42 }T
T{ -7 double -> -14 }T
bye
