\ The command line's exit codes and verdict counts (plan task 3.4.2), shared
\ by its text and JSON reports (cli/leanforth.fs, cli/check-json.fs). Exit
\ codes: 0 all accepted (or the command done), 1 something rejected, 2
\ unsupported or unknown, 3 a resource limit (out of fuel or room), 4
\ malformed input (also a malformed command line, or a file that cannot be
\ opened or created), 5 an internal fault. When outcomes differ, the most
\ severe wins, in the order 5, 4, 1, 3, 2, 0 (docs/user/COMMAND_LINE.md).
\ The counts are the declarations by verdict: the seven outcomes (ADR
\ 0008), not-checked (a run that stopped before them) and, apart,
\ not-proved: accepted declarations whose axiom set is not empty, which
\ the owner's rule labels NOT PROVED and never counts as proved (owner,
\ 2026-11-04; the first checker accepts no axiom, so none occurs yet).
\ LeanForth-specific; untrusted (it reports, it decides no verdict).
\ State: one record in the checker context, cli-tally-state (the code so
\ far and the counts).

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs

0 constant exit-accepted     \ every declaration accepted, or the command done
1 constant exit-rejected     \ something rejected
2 constant exit-undecided    \ unsupported or unknown
3 constant exit-limit        \ a resource limit: out of fuel or room
4 constant exit-malformed    \ malformed input or command line
5 constant exit-fault        \ an internal fault
\ Indexed by outcome: ok, invalid, exhausted, unknown, rejected,
\ unsupported, full; the table must end at HERE, otherwise the load stops.
create cli-codes
  exit-accepted , exit-malformed , exit-limit , exit-undecided , exit-rejected ,
  exit-undecided , exit-limit ,
here cli-codes - outcome-full 1+ cells <>
[if] .( tally.fs: one code per outcome) cr abort [then]
: outcome>code ( outcome -- code )
  dup outcome? if cells cli-codes + @ else drop exit-fault then ;
\ Severity, by code: 0 < 2 < 3 < 1 < 4 < 5. The more severe of two codes.
create cli-severity  0 , 3 , 1 , 2 , 4 , 5 ,
: code-severity ( code -- n ) cells cli-severity + @ ;
: worse-code ( code1 code2 -- code )
  2dup code-severity swap code-severity > if nip else drop then ;

7 constant not-checked     \ the count after the outcomes': declarations not reached
begin-structure /cli-tally
  field: tallied-worst                         \ the exit code so far
  not-checked 1+ cells +field tallied-counts  \ declarations by verdict
  field: tallied-not-proved                   \ accepted, with an axiom
end-structure
/cli-tally context-record: cli-tally-state
: cli-worst ( -- addr ) cli-tally-state tallied-worst ;
: cli-count-of ( k -- addr ) cells cli-tally-state tallied-counts + ;
: cli-not-proved ( -- addr ) cli-tally-state tallied-not-proved ;
\ A command's start: nothing counted, nothing failed.
: cli-start ( -- ) cli-tally-state /cli-tally erase exit-accepted cli-worst ! ;
: cli-code! ( code -- ) cli-worst @ worse-code cli-worst ! ;
\ Count a verdict, and its code.
: cli-tally ( outcome -- ) dup outcome>code cli-code! cli-count-of 1 swap +! ;
\ Whether a verdict with the axiom set bits is NOT PROVED: accepted, and
\ depending on an axiom. The first checker's allowlist (version 0) names
\ none, so any axiom counts (an axiom outside propext, Classical.choice
\ and Quot.sound, the owner's rule).
: not-proved? ( outcome bits -- flag ) 0<> swap ok? and ;
: cli-tally-proved ( outcome bits -- ) not-proved? if 1 cli-not-proved +! then ;

base !   \ the BASE this file was loaded with
