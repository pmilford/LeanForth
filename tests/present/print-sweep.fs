\ Every exit of the printer on every golden case, in all three modes:
\ with each fuel level below what the print needs it is exhausted, leaves
\ no fuel and the data stack as it was; with exactly that fuel it is ok
\ and prints what it prints with ample fuel. With each visit limit from 1
\ to 24 it is ok or exhausted, again with the stack balanced. So every
\ failure path is reached at least once per case without a stack error.
require ./build.fs

variable need   variable prints
: no-sink ( c-addr u -- ) 2drop ;
: balanced ( depth -- ) depth 1- <> abort" sweep: stack not balanced" ;
: counted ( -- ) 1 prints +! ;
: used ( t -- n ) fuel lf-print-term must-ok fuel lf-print-fuel @ - ;
: exhausted-at ( t f -- )
  depth 2 - >r lf-print-term outcome-exhausted <> abort" sweep: fuel not exhausted"
  lf-print-fuel @ abort" sweep: fuel left" r> balanced counted ;
: fuel-sweep ( t -- ) need @ 0 ?do dup i exhausted-at loop drop ;
\ Exactly the fuel needed prints the same text as ample fuel.
create full-text 4096 allot
variable full-len
: keep ( -- ) cap full-len ! full-text full-len @ move ;
: same-text ( t options -- )
  dup mode cap-reset over fuel lf-print-term must-ok keep
  mode cap-reset need @ lf-print-term must-ok full-text full-len @ expect-text counted ;
: ok-or-full ( outcome -- ) dup ok? swap outcome-full = or must ;
: limit-at ( t limit -- )
  lf-print-limit! must depth 1- >r fuel lf-print-term ok-or-full r> balanced counted ;
: limit-sweep ( t -- )
  25 1 do dup i limit-at loop drop lf-print-default-limit lf-print-limit! must ;
: sweep-mode ( t options -- )
  2dup ['] no-sink swap lf-print-setup used need !
  2dup same-text ['] no-sink swap lf-print-setup dup fuel-sweep limit-sweep ;
: run-case ( xt c-addr u options -- )
  >r 2drop fresh execute r> 3 0 do 2dup i or sweep-mode loop 2drop ;
: uni ( xt c-addr u -- ) 0 run-case ;
: univ ( xt c-addr u -- ) lf-print-universes run-case ;

include ./print-case-list.fs
.( print-sweep: ) prints @ . .( prints checked) cr
bye
