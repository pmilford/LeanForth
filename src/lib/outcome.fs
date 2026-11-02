\ One outcome vocabulary for every walker and checker (ADR 0008). Values
\ 0-3 are the ones all modules already used. An outcome is a status, not a
\ flag: 0 means success here but false for a flag, so test an outcome with
\ ok? or compare it with a named outcome, never with IF directly.
\ No state, no dependencies.

0 constant outcome-ok           \ succeeded; for a comparison, shown equal
1 constant outcome-invalid      \ malformed input or corrupted state
2 constant outcome-exhausted    \ a fuel, capacity or depth limit was reached
3 constant outcome-unknown      \ supported, but this cautious rule cannot decide
4 constant outcome-rejected     \ shown wrong: ill-typed or definitely different
5 constant outcome-unsupported  \ uses a feature LeanForth does not implement yet

: outcome? ( n -- flag ) outcome-ok outcome-unsupported 1+ within ;
: ok? ( outcome -- flag ) outcome-ok = ;
\ Any value outside the vocabulary becomes invalid, so a corrupted or
\ unexpected status can never read as success.
: outcome-sane ( n -- outcome ) dup outcome? 0= if drop outcome-invalid then ;
\ A validity flag as an outcome: only a true flag (all bits set) is ok;
\ false, or a status passed by mistake, is invalid.
: flag>outcome ( flag -- outcome ) true = if outcome-ok else outcome-invalid then ;
\ Continue only on ok: keep x and give true, or replace x by the failing
\ outcome and give false.
: ok-then? ( x outcome -- x true | outcome false ) dup ok? if drop true else nip false then ;
\ Drop an argument and report invalid input.
: drop-invalid ( x -- outcome ) drop outcome-invalid ;
