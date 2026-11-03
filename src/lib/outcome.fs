\ One outcome vocabulary for every walker and checker (ADR 0008). Values
\ 0-3 are the ones all modules already used. An outcome is a status, not a
\ flag: 0 means success here but false for a flag, so test an outcome with
\ ok? or compare it with a named outcome, never with IF directly. Running
\ out of fuel (exhausted: more time would help) and running out of room
\ (full: more memory or a larger limit would help) are distinct, and
\ neither is ever ok.
\ No state, no dependencies.

0 constant outcome-ok           \ succeeded; for a comparison, shown equal
1 constant outcome-invalid      \ malformed input or corrupted state
2 constant outcome-exhausted    \ out of fuel: the processing budget ran out
3 constant outcome-unknown      \ supported, but this cautious rule cannot decide
4 constant outcome-rejected     \ shown wrong: ill-typed or definitely different
5 constant outcome-unsupported  \ uses a feature LeanForth does not implement yet
6 constant outcome-full         \ out of room: a store, stack, depth or size limit

: outcome? ( n -- flag ) outcome-ok outcome-full 1+ within ;
: ok? ( outcome -- flag ) outcome-ok = ;
\ Any value outside the vocabulary becomes invalid, so a corrupted or
\ unexpected status can never read as success.
: outcome-sane ( n -- outcome ) dup outcome? 0= if drop outcome-invalid then ;
\ A validity flag as an outcome: only a true flag (all bits set) is ok;
\ false, or a status passed by mistake, is invalid.
: flag>outcome ( flag -- outcome ) true = if outcome-ok else outcome-invalid then ;
\ A room flag as an outcome: only a true flag is ok; false, or a status
\ passed by mistake, is full.
: room>outcome ( flag -- outcome ) true = if outcome-ok else outcome-full then ;
\ Whether a visit bounded by fuel and by room (a frame, a depth or a level)
\ can go ahead: no fuel left (zero or a corrupted negative fuel) is
\ exhausted whatever the room, so the fuel decides when both are short;
\ otherwise no room is full.
: visit-outcome ( fuel room? -- outcome )
  swap 0> if room>outcome else drop outcome-exhausted then ;
\ Continue only on ok: keep x and give true, or replace x by the failing
\ outcome and give false.
: ok-then? ( x outcome -- x true | outcome false )
  dup ok? if drop true else nip false then ;
\ The same for a step that gives a result, with one or two values kept
\ below it for the next step: keep them and give true, or drop them, keep
\ the result beside the failing outcome and give false.
: ok-keep? ( x result outcome -- x result true | result outcome false )
  dup ok? if drop true else rot drop false then ;
: ok-keep2? ( x1 x2 result outcome -- x1 x2 result true | result outcome false )
  dup ok? if drop true else 2swap 2drop false then ;
\ A failure that has no result: -1 in the result's place.
: no-result ( outcome -- -1 outcome ) -1 swap ;
\ The outcome's name, as diagnostics write it. A value outside the
\ vocabulary is named "invalid", as outcome-sane reads it.
: outcome-text ( outcome -- c-addr u )
  outcome-sane case
    outcome-ok of s" ok" endof  outcome-invalid of s" invalid" endof
    outcome-exhausted of s" exhausted" endof  outcome-unknown of s" unknown" endof
    outcome-rejected of s" rejected" endof  outcome-unsupported of s" unsupported" endof
    s" full" rot endcase ;
\ Drop an argument and report invalid input.
: drop-invalid ( x -- outcome ) drop outcome-invalid ;
