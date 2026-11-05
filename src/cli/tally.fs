\ The command line's exit codes and verdict counts (plan task 3.4.2), shared
\ by its text and JSON reports (cli/leanforth.fs, cli/check-json.fs). Exit
\ codes: 0 all accepted (or the command done), 1 something rejected, 2
\ unsupported or unknown, 3 a resource limit (out of fuel or room), 4
\ malformed input (also a malformed command line, or a file that cannot be
\ opened or created), 5 an internal fault, 6 every declaration accepted,
\ but some NOT PROVED: they depend on an axiom, only under
\ --strict-axioms (cli-strict-axioms!). By default a NOT PROVED
\ declaration keeps Lean's code, 0 when everything is accepted, and is
\ only counted and marked (owner, 2026-11-04, "0 like Lean, flag for 6";
\ docs/project/OWNER_DECISIONS.md). When codes differ, the most severe
\ wins, in the order 5, 4, 1, 3, 2, 6, 0 (docs/user/COMMAND_LINE.md): any
\ rejected, undecided, resource or malformed code takes precedence over 6.
\ The counts are the declarations by verdict, in the order reports show
\ them (verdict-order): the seven outcomes (ADR 0008), not-checked (a run
\ that stopped before them) and, apart, not-proved: accepted declarations
\ whose axiom set is not empty. The first checker accepts no axiom, so
\ none occurs yet. LeanForth-specific; untrusted (it reports, it decides
\ no verdict).
\ State: one record in the checker context, cli-tally-state (the code so
\ far, the counts and whether NOT PROVED gives code 6).

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs

0 constant exit-accepted     \ every declaration accepted, or the command done
1 constant exit-rejected     \ something rejected
2 constant exit-undecided    \ unsupported or unknown
3 constant exit-limit        \ a resource limit: out of fuel or room
4 constant exit-malformed    \ malformed input or command line
5 constant exit-fault        \ an internal fault
6 constant exit-not-proved   \ accepted, but some NOT PROVED (--strict-axioms)
\ Indexed by outcome: ok, invalid, exhausted, unknown, rejected,
\ unsupported, full; the table must end at HERE, otherwise the load stops.
create cli-codes
  exit-accepted , exit-malformed , exit-limit , exit-undecided , exit-rejected ,
  exit-undecided , exit-limit ,
here cli-codes - outcome-full 1+ cells <>
[if] .( tally.fs: one code per outcome) cr abort [then]
: outcome>code ( outcome -- code )
  dup outcome? if cells cli-codes + @ else drop exit-fault then ;
\ Severity, by code 0 to 6: 0 < 6 < 2 < 3 < 1 < 4 < 5; the table must
\ end at HERE, otherwise the load stops. The more severe of two codes.
create cli-severity  0 , 4 , 2 , 3 , 5 , 6 , 1 ,
here cli-severity - exit-not-proved 1+ cells <>
[if] .( tally.fs: one rank per exit code) cr abort [then]
: code-severity ( code -- n ) cells cli-severity + @ ;
: worse-code ( code1 code2 -- code )
  2dup code-severity swap code-severity > if nip else drop then ;

\ The verdicts reports count, in their order: accepted (ok), rejected,
\ unknown, unsupported, invalid, exhausted, full, not checked.
7 constant not-checked     \ the count after the outcomes': declarations not reached
create verdict-order
  outcome-ok , outcome-rejected , outcome-unknown , outcome-unsupported ,
  outcome-invalid , outcome-exhausted , outcome-full , not-checked ,
here verdict-order - 1 cells / constant verdict-kinds
verdict-kinds not-checked 1+ <>
[if] .( tally.fs: one entry per verdict) cr abort [then]
: verdict-kind ( k -- verdict ) cells verdict-order + @ ;
\ A verdict as reports name it: accepted for ok, not-checked, or the
\ outcome's name.
: verdict-name ( verdict -- c-addr u )
  case outcome-ok of s" accepted" endof not-checked of s" not-checked" endof
    dup outcome-text rot endcase ;

begin-structure /cli-tally
  field: tallied-worst                         \ the exit code so far
  not-checked 1+ cells +field tallied-counts   \ declarations by verdict
  field: tallied-not-proved                    \ accepted, with an axiom
  field: tallied-strict                        \ true: NOT PROVED gives code 6
end-structure
/cli-tally context-record: cli-tally-state
: cli-worst ( -- addr ) cli-tally-state tallied-worst ;
: cli-count-of ( k -- addr ) cells cli-tally-state tallied-counts + ;
: cli-not-proved ( -- addr ) cli-tally-state tallied-not-proved ;
\ A command's start: nothing counted, nothing failed, NOT PROVED with
\ Lean's code.
: cli-start ( -- ) cli-tally-state /cli-tally erase exit-accepted cli-worst ! ;
\ --strict-axioms, set after cli-start: whether NOT PROVED gives code 6.
: cli-strict-axioms! ( flag -- ) cli-tally-state tallied-strict ! ;
: cli-strict-axioms? ( -- flag ) cli-tally-state tallied-strict @ ;
: cli-code! ( code -- ) cli-worst @ worse-code cli-worst ! ;
\ Count a verdict, and its code.
: cli-tally ( outcome -- ) dup outcome>code cli-code! cli-count-of 1 swap +! ;
\ Whether a verdict with the axiom set bits is NOT PROVED: accepted, and
\ depending on an axiom. The first checker's allowlist (version 0) names
\ none, so any axiom counts (an axiom outside propext, Classical.choice
\ and Quot.sound, the owner's rule).
: not-proved? ( outcome bits -- flag ) 0<> swap ok? and ;
\ Count a NOT PROVED declaration apart; under --strict-axioms, with code 6.
: cli-not-proved-code ( -- ) cli-strict-axioms? if exit-not-proved cli-code! then ;
: cli-tally-proved ( outcome bits -- )
  not-proved? if 1 cli-not-proved +! cli-not-proved-code then ;

base !   \ the BASE this file was loaded with
