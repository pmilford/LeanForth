require test/ttester.fs
T{ 1 2 + -> 4 }T
: finish-tests #errors @ if -1 throw then ;
finish-tests
bye
