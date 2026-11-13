\ Unit tests of Lean's generated definitions built in LeanForth (plan row
\ FE6; src/front/constructions.fs and expr-remap.fs): T.casesOn and
\ T.recOn for the types of tests/front/constructions.ndjson (pinned
\ Lean's export of a slice of Init: Nat, And, Eq, Acc, Prod, Or, List,
\ Exists, Equivalence) compared with Lean's own, exactly or up to binder
\ names and information; the structure case (And, Equivalence); every
\ refusal (a mutual and a nested type, no recursor, the rp out of fuel,
\ a letE) with its reason; the renumbering rp alone (shift, swap,
\ refusal, erasing, depth under binders); a job reused after a failure.
\ All of Init is tests/front/constructions-init.sh. Every T{ }T checks
\ the data stack's depth. Nothing here checks or accepts a theorem.
require ../support/tester.fs
require ../../src/front/constructions.fs

create lib /stage allot
create job /aux allot
T{ 12 lib stage-init -> outcome-ok }T
T{ s" tests/front/constructions.ndjson" lib stage-load -> outcome-ok }T
T{ lib job aux-init -> outcome-ok }T
: tier ( -- tier ) job aux-tier ;
: top ( c-addr u -- n ) 0 -rot tier name-find-str drop ;
: ind ( c-addr u -- d ) top lib stage-find drop ;
: cases-of ( c-addr u -- outcome ) ind job aux-cases-on ;
: recon-of ( c-addr u -- outcome ) ind job aux-rec-on ;
: lean-cases-of ( -- d ) s" casesOn" job aux-named drop ;
: lean-recon-of ( -- d ) s" recOn" job aux-named drop ;
\ 2: equal node for node; 1: equal up to binder names and information.
: grade ( d -- n ) dup job aux-same? if drop 2 exit then job aux-alike? 1 and ;
: why ( -- c-addr u ) job aux-why @ count ;

\ ---- Equal to Lean's, every type of the slice.
T{ s" Nat" cases-of lean-cases-of grade -> outcome-ok 2 }T
T{ s" Nat" recon-of lean-recon-of grade -> outcome-ok 2 }T
T{ s" Eq" cases-of lean-cases-of grade -> outcome-ok 2 }T
T{ s" Eq" recon-of lean-recon-of grade -> outcome-ok 2 }T
T{ s" Acc" cases-of lean-cases-of grade -> outcome-ok 2 }T
T{ s" Acc" recon-of lean-recon-of grade -> outcome-ok 2 }T
T{ s" List" cases-of lean-cases-of grade -> outcome-ok 2 }T
T{ s" List" recon-of lean-recon-of grade -> outcome-ok 2 }T
T{ s" Or" cases-of lean-cases-of grade -> outcome-ok 2 }T
T{ s" Or" recon-of lean-recon-of grade -> outcome-ok 2 }T
T{ s" Exists" cases-of lean-cases-of grade -> outcome-ok 2 }T
T{ s" Exists" recon-of lean-recon-of grade -> outcome-ok 2 }T
\ The structure case: casesOn from projections, recOn is casesOn.
T{ s" And" cases-of lean-cases-of grade -> outcome-ok 2 }T
T{ s" And" recon-of lean-recon-of grade -> outcome-ok 2 }T
T{ s" And" ind job aux-rec-on drop job aux-value@ tier expr-tag@ -> tag-const }T
T{ s" Equivalence" cases-of lean-cases-of grade -> outcome-ok 2 }T
T{ s" Equivalence" recon-of lean-recon-of grade -> outcome-ok 2 }T
T{ s" Prod" cases-of lean-cases-of grade -> outcome-ok 2 }T
T{ s" Prod" recon-of lean-recon-of grade -> outcome-ok 2 }T
\ In all of Init's export, Prod.casesOn's minor premise has the binder
\ names of another term the exporter shared it with: equal but for them
\ (tests/front/constructions-init.sh). Here, two binders that differ in
\ name and information only.
: binder-a ( -- e ) 7 1 level-zero tier expr-sort drop 0 tier expr-bvar drop
  2swap lam-head -rot tier expr-make drop ;
: binder-b ( -- e ) 0 0 level-zero tier expr-sort drop 0 tier expr-bvar drop
  2swap lam-head -rot tier expr-make drop ;
T{ binder-a binder-b = binder-a binder-b job alike? -> false true }T
T{ binder-a 1 tier expr-bvar drop job alike? -> false }T
\ A wrong definition is neither: Nat's recOn against Lean's casesOn.
T{ s" Nat" recon-of lean-cases-of grade -> outcome-ok 0 }T
\ Building again gives the same numbers.
: built ( -- type value ) s" Nat" cases-of drop job aux-type@ job aux-value@ ;
T{ built built rot = >r = r> -> true true }T

\ ---- Refusals, each with its reason.
\ No recursor: a constructor is no type.
0 s" Nat" tier name-find-str drop s" zero" tier name-find-str drop lib stage-find drop
  constant nat-zero
T{ nat-zero job aux-cases-on why s" no recursor" compare -> outcome-invalid 0 }T
T{ nat-zero job aux-rec-on why s" no recursor" compare -> outcome-invalid 0 }T
\ Out of fuel: Acc's domains need more than one visit; then the job is
\ used again with its fuel back.
T{ 1 job aux-remap remap-fuel! s" Acc" cases-of -> outcome-exhausted }T
T{ why s" the renumbering pass refused a domain" compare -> 0 }T
T{ s" Acc" recon-of -> outcome-exhausted }T
T{ remap-fuel job aux-remap remap-fuel! s" Acc" cases-of lean-cases-of grade -> outcome-ok 2 }T
\ A nested type (tests/cli/nested.ndjson): its recursor has several
\ motives, so casesOn is unsupported; recOn is built.
create nested /stage allot
create job2 /aux allot
T{ 12 nested stage-init -> outcome-ok }T
T{ s" tests/cli/nested.ndjson" nested stage-load -> outcome-ok }T
T{ nested job2 aux-init -> outcome-ok }T
: rv ( c-addr u -- d )
  0 s" RvNest" job2 aux-tier name-find-str drop -rot job2 aux-tier name-find-str drop
  nested stage-find drop ;
T{ s" R" rv job2 aux-cases-on -> outcome-unsupported }T
T{ job2 aux-why @ count s" several motives (a mutual or nested type)" compare -> 0 }T
T{ s" VT" rv job2 aux-cases-on -> outcome-unsupported }T
T{ s" R" rv job2 aux-rec-on job2 aux-motives @ 1 > -> outcome-ok true }T
job2 aux-free  nested stage-free

\ ---- The renumbering rp alone, in the scratch tier.
create rp /remap allot
tier rp remap-init
: var ( i -- e ) tier expr-bvar drop ;
: app ( f a -- e ) tier expr-app drop ;
: sort0 ( -- e ) level-zero tier expr-sort drop ;
: lam ( name info type body -- e ) 2swap lam-head -rot tier expr-make drop ;
: run ( e cutoff -- e' outcome ) rp remap-at ;
\ Shift: drop 1, lift 0 lowers #2 to #1 and refuses #0.
T{ 1 0 rp remap-shift! 2 var 0 run -> 1 var outcome-ok }T
T{ 0 var 0 run -> -1 outcome-unsupported }T
T{ 2 var 0 var app 0 run -> -1 outcome-unsupported }T
\ Lift 3 at cutoff 1: #0 stays, #1 becomes #4; under a binder, its own
\ variable stays.
T{ 0 3 rp remap-shift! 0 var 1 var app 1 run -> 0 var 4 var app outcome-ok }T
T{ 0 0 sort0 0 var 1 var app lam 0 run -> 0 0 sort0 0 var 4 var app lam outcome-ok }T
\ Closed terms are kept: the same number, no visit.
T{ sort0 5 run -> sort0 outcome-ok }T
\ Swap 1 and 2: #0 -> #2, #1 -> #0, #2 -> #1, #3 stays.
T{ 1 2 rp remap-swap! 0 var 0 run 1 var 0 run 2 var 0 run 3 var 0 run
   -> 2 var outcome-ok 0 var outcome-ok 1 var outcome-ok 3 var outcome-ok }T
\ Erasing: names and binder information go, variables stay.
T{ true rp remap-erase! 0 0 rp remap-shift! 7 1 sort0 2 var lam 0 run
   -> 0 0 sort0 2 var lam outcome-ok }T
T{ false rp remap-erase! -> }T
\ A letE with a variable to renumber is unsupported; out of fuel, exhausted.
: let0 ( -- e ) 0 false let-head sort0 sort0 3 var tier expr-let drop ;
T{ 0 1 rp remap-shift! let0 0 run -> -1 outcome-unsupported }T
T{ 1 rp remap-fuel! 0 var 1 var app 0 run -> -1 outcome-exhausted }T
rp remap-free

job aux-free  lib stage-free
bye
