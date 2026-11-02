\ Run: .tools/gforth/bin/gforth tests/program/program-depth.fs
include ../support/tester.fs
require ../../src/program/program-depth.fs

\ Typed tags only; no Forth code from the arrays is executed.
create ops-dup-add lf-depth-dup , lf-depth-add ,
create ops-push-add lf-depth-push , lf-depth-add ,
create ops-add-push lf-depth-add , lf-depth-push ,
create ops-adds lf-depth-add , lf-depth-add , lf-depth-add ,
create ops-bad lf-depth-push , -1 , lf-depth-add ,
create ops-unknown 3 ,

T{ 0 0 0 0 lf-program-required-depth -> 0 true }T
T{ ops-dup-add 2 2 2 lf-program-required-depth -> 1 true }T
T{ ops-push-add 2 2 2 lf-program-required-depth -> 1 true }T
T{ ops-add-push 2 2 2 lf-program-required-depth -> 2 true }T
T{ ops-adds 3 3 3 lf-program-required-depth -> 4 true }T
T{ ops-dup-add 2 1 1 lf-program-required-depth -> 1 true }T
T{ ops-push-add 2 1 1 lf-program-required-depth -> 0 true }T
T{ ops-bad 3 3 3 lf-program-required-depth -> 0 false }T
T{ ops-unknown 1 1 1 lf-program-required-depth -> 0 false }T
T{ ops-dup-add -1 0 0 lf-program-required-depth -> 0 false }T
T{ ops-dup-add 2 -1 2 lf-program-required-depth -> 0 false }T
T{ ops-dup-add 2 2 -1 lf-program-required-depth -> 0 false }T
T{ ops-dup-add 1 2 2 lf-program-required-depth -> 0 false }T
T{ ops-dup-add 2 2 1 lf-program-required-depth -> 0 false }T
T{ 0 1 1 1 lf-program-required-depth -> 0 false }T
T{ ops-dup-add 1+ 1 1 1 lf-program-required-depth -> 0 false }T
T{ -1 cells 2 2 2 lf-program-required-depth -> 0 false }T
T{ ops-dup-add lf-depth-max lf-depth-max lf-depth-max lf-program-required-depth -> 0 false }T
T{ lf-depth-max lf-depth-add lf-depth-step -> 0 false }T
T{ lf-depth-max 1- lf-depth-add lf-depth-step -> lf-depth-max true }T
T{ lf-depth-max lf-depth-dup lf-depth-step -> lf-depth-max 1- true }T
T{ lf-depth-max lf-depth-push lf-depth-step -> lf-depth-max 1- true }T
T{ -1 lf-depth-push lf-depth-step -> 0 false }T
T{ 0 -1 lf-depth-step -> 0 false }T
\ A failed call must not contaminate the next call's scratch state.
T{ ops-dup-add 2 2 2 lf-program-required-depth -> 1 true }T
T{ 0 lf-depth-dup lf-depth-step -> 1 true }T

\ Zero-filled storage: a misaligned read here would decode as a valid PUSH
\ tag, so only the alignment check can reject it. (The ops-dup-add 1+ case
\ above would also fail on an unknown tag, even without an alignment check.)
create ops-zeros lf-depth-push , lf-depth-push ,
T{ ops-zeros 2 2 2 lf-program-required-depth -> 0 true }T
T{ ops-zeros 1+ 1 1 1 lf-program-required-depth -> 0 false }T
\ The smallest count whose byte size exceeds the largest signed cell, with
\ matching capacity and fuel. Unless the storage lies in the upper half of
\ the address space, its end address does not wrap, so only the size check
\ rejects it.
T{ ops-zeros lf-depth-max 1 cells / 1+ dup dup
   lf-program-required-depth -> 0 false }T
\ A negative count whose byte size wraps to exactly zero, so the address-wrap
\ check cannot reject it; only the negative-size check does.
T{ ops-zeros 2 lf-depth-max invert 2 lf-program-required-depth -> 0 false }T
bye
