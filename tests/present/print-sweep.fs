\ Every exit of the printer on every golden case, in all three modes:
\ with each fuel level below what the print needs it is exhausted, leaves
\ no fuel and the data stack as it was; with exactly that fuel it is ok
\ and prints what it prints with ample fuel. With each visit limit from 1
\ to 24 it is ok or full, again with the stack balanced. So every failure
\ path is reached at least once per case without a stack error. Every
\ print runs above a return-stack marker (rs-checked).
\ Then, against the sink rules, a sink calls lf-print-reset at each of its
\ calls in turn: every such print ends invalid, with both stacks balanced
\ and the printer idle, which is evidence for the defence in depth of
\ print-job.fs (no endless loop, no address outside the printer's memory).
\ After every print the frames its visits ran on are empty again.
require ./build.fs
require ../support/checks.fs

variable need   variable prints   variable resets
: no-sink ( c-addr u -- ) 2drop ;
: frames-empty ( -- )
  lf-pp-frames dup frame-used @ over frame-context @ or swap frame-depth @ or
  abort" sweep: frames not empty" ;
: balanced ( depth -- ) depth 1- <> abort" sweep: stack not balanced" frames-empty ;
: counted ( -- ) 1 prints +! ;
: print ( t fuel -- outcome ) ['] lf-print-term rs-checked ;
: used ( t -- n ) fuel print must-ok fuel lf-print-fuel @ - ;
: exhausted-at ( t f -- )
  depth 2 - >r print outcome-exhausted <> abort" sweep: fuel not exhausted"
  lf-print-fuel @ abort" sweep: fuel left" r> balanced counted ;
: fuel-sweep ( t -- ) need @ 0 ?do dup i exhausted-at loop drop ;
\ Exactly the fuel needed prints the same text as ample fuel.
create full-text 4096 allot
variable full-len
: keep ( -- ) cap full-len ! full-text full-len @ move ;
: same-text ( t options -- )
  dup mode cap-reset over fuel print must-ok keep
  mode cap-reset need @ print must-ok full-text full-len @ expect-text counted ;
: ok-or-full ( outcome -- ) dup ok? swap outcome-full = or must ;
: limit-at ( t limit -- )
  lf-print-limit! must depth 1- >r fuel print ok-or-full r> balanced counted ;
: limit-sweep ( t -- )
  25 1 do dup i limit-at loop drop lf-print-default-limit lf-print-limit! must ;

\ The reset sweep: a sink that calls lf-print-reset at its n-th call.
variable calls   variable reset-at
: reset-sink ( c-addr u -- )
  2drop 1 calls +! calls @ reset-at @ = if lf-print-reset then ;
: sink-calls ( t options -- n )
  ['] reset-sink swap lf-print-setup 0 reset-at ! 0 calls ! fuel print must-ok calls @ ;
: reset-at-call ( t n -- )
  reset-at ! 0 calls ! depth 1- >r fuel print
  outcome-invalid <> abort" sweep: reset not invalid"
  lf-pp-busy? abort" sweep: busy after a reset" r> balanced 1 resets +! ;
: reset-sweep ( t options -- )
  over swap sink-calls 1+ 1 ?do dup i reset-at-call loop drop ;

: sweep-mode ( t options -- )
  2dup ['] no-sink swap lf-print-setup used need !
  2dup same-text 2dup reset-sweep
  ['] no-sink swap lf-print-setup dup fuel-sweep limit-sweep ;
: sweep-case ( xt c-addr u options -- )
  >r 2drop fresh execute r> 3 0 do 2dup i or sweep-mode loop 2drop ;
: uni ( xt c-addr u -- ) 0 sweep-case ;
: univ ( xt c-addr u -- ) lf-print-universes sweep-case ;

include ./print-case-list.fs
.( print-sweep: ) prints @ . .( prints checked) cr
.( print-sweep: ) resets @ . .( prints reset from the sink) cr
bye
