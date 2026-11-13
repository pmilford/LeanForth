\ Unit tests of Lean's generated definitions built in LeanForth (plan row
\ FE6; src/front/constructions.fs, ctor-idx.fs and expr-remap.fs):
\ T.casesOn, T.recOn and T.ctorIdx for the types of
\ tests/front/constructions.ndjson (pinned Lean's export of a slice of
\ Init: Nat, And, Eq, Acc, Prod, Or, List, Exists, Equivalence) compared
\ with Lean's own, exactly or up to binder names and information; the
\ structure case (And, Equivalence); every refusal (a nested type, no
\ recursor, the pass out of fuel, an mdata record, no ctorIdx for a Prop)
\ with its reason; the renumbering pass alone (shift, swap, refusal,
\ erasing, letE, depth under binders); a job reused after a failure.
\ All of Init is tests/front/constructions-init.sh. Every T{ }T checks
\ the data stack's depth. Nothing here checks or accepts a theorem.
require ../support/tester.fs
require ../../src/front/ctor-idx.fs
require ../../src/front/cases-several.fs

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
\ ctorIdx: Lean names the arrow's binder afresh, so equal up to names.
: idx-of ( c-addr u -- outcome ) ind job aux-ctor-idx ;
: lean-idx ( -- d ) s" ctorIdx" job aux-named drop ;
T{ s" Nat" idx-of lean-idx grade -> outcome-ok 1 }T
T{ s" List" idx-of lean-idx grade -> outcome-ok 1 }T
\ Its parameters are implicit (binder information the comparison above
\ ignores).
T{ s" List" idx-of job aux-type@ tier expr-tag@ -> outcome-ok tag-pi 1+ }T
T{ job aux-value@ tier expr-tag@ -> tag-lam 1+ }T
\ Its universe parameters are the type's, not the recursor's.
T{ s" List" idx-of lean-idx job params-same? -> outcome-ok true }T
\ One constructor: the value is the literal 0 under the funs.
T{ s" Prod" idx-of lean-idx grade -> outcome-ok 1 }T
: under-funs ( e n -- e' ) 0 ?do tier expr-b@ loop ;
T{ job aux-value@ job xs-count 1+ under-funs tier expr-tag@ -> tag-nat }T
\ Lean makes none for a Prop.
T{ s" Eq" idx-of why s" Lean makes no ctorIdx for a Prop" compare
   -> outcome-unsupported 0 }T
T{ s" And" idx-of -> outcome-unsupported }T
\ Alike types, different values (review L2): Or's casesOn applies
\ fun h => inl h where Lean's Or.recOn applies inl.
T{ s" Or" cases-of lean-recon-of dup job type-alike? swap job aux-alike?
   -> outcome-ok true false }T
\ A wrong definition is neither: Nat's recOn against Lean's casesOn.
T{ s" Nat" recon-of lean-cases-of grade -> outcome-ok 0 }T
\ Building again gives the same numbers.
: built ( -- type value ) s" Nat" cases-of drop job aux-type@ job aux-value@ ;
: same-pair? ( a b c d -- flag ) rot = -rot = and ;
T{ built built same-pair? -> true }T

\ ---- Refusals, each with its reason.
\ No recursor: a constructor is no type.
0 s" Nat" tier name-find-str drop s" zero" tier name-find-str drop lib stage-find drop
  constant nat-zero
T{ nat-zero job aux-cases-on why s" no recursor" compare -> outcome-invalid 0 }T
T{ nat-zero job aux-rec-on why s" no recursor" compare -> outcome-invalid 0 }T
\ Out of fuel: Acc's domains need more than one visit; then the job is
\ used again with its fuel back.
T{ 1 job aux-remap remap-fuel! s" Acc" cases-of -> outcome-exhausted }T
T{ why s" the renumbering pass ran out of fuel" compare -> 0 }T
T{ s" Acc" recon-of -> outcome-exhausted }T
T{ remap-fuel job aux-remap remap-fuel! -> }T
T{ s" Acc" cases-of lean-cases-of grade -> outcome-ok 2 }T
\ A nested type (tests/cli/nested.ndjson): its recursor has several
\ motives, so the one-motive casesOn is unsupported, the any-motive one
\ (src/front/cases-several.fs) equals Lean's; recOn is built.
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
: grade2 ( d -- n ) dup job2 aux-same? if drop 2 exit then job2 aux-alike? 1 and ;
: lean-cases2 ( -- d ) s" casesOn" job2 aux-named drop ;
T{ s" R" rv job2 aux-cases-on-any lean-cases2 grade2 -> outcome-ok 1 }T
T{ s" VT" rv job2 aux-cases-on-any lean-cases2 grade2 -> outcome-ok 2 }T
T{ job2 aux-main @ job2 aux-motives @ 1 > -> 0 true }T
\ A mutual block with a parameter and an index (tests/front/several.lean,
\ review fe6a-2 N3): the other motive's binders and the index move.
create mutual /stage allot
create job4 /aux allot
T{ 12 mutual stage-init -> outcome-ok }T
T{ s" tests/front/several.ndjson" mutual stage-load -> outcome-ok }T
T{ mutual job4 aux-init -> outcome-ok }T
: fe6 ( c-addr u -- d )
  0 s" FE6" job4 aux-tier name-find-str drop -rot job4 aux-tier name-find-str drop
  mutual stage-find drop ;
: grade4 ( d -- n ) dup job4 aux-same? if drop 2 exit then job4 aux-alike? 1 and ;
: lean4 ( c-addr u -- d ) job4 aux-named drop ;
T{ s" Even" fe6 job4 aux-cases-on-any s" casesOn" lean4 grade4 -> outcome-ok 2 }T
T{ job4 aux-motives @ job4 aux-params @ job4 aux-indices @ job4 aux-kept @ -> 2 1 1 2 }T
T{ s" Odd" fe6 job4 aux-cases-on-any s" casesOn" lean4 grade4 -> outcome-ok 2 }T
T{ job4 aux-main @ job4 aux-kept @ -> 1 1 }T
T{ s" Even" fe6 job4 aux-rec-on s" recOn" lean4 grade4 -> outcome-ok 2 }T
T{ s" Odd" fe6 job4 aux-rec-on s" recOn" lean4 grade4 -> outcome-ok 2 }T
T{ s" Even" fe6 job4 aux-ctor-idx s" ctorIdx" lean4 grade4 -> outcome-ok 1 }T
T{ s" Odd" fe6 job4 aux-ctor-idx s" ctorIdx" lean4 grade4 -> outcome-ok 1 }T
\ The renumbering table refuses the other motive (slot 0 of Even's two;
\ Even's own is slot 1), whatever the table held before.
T{ s" Even" fe6 job4 aux-cases-on-any 0 5 job4 motive-table -> outcome-ok }T
T{ 0 job4 aux-tier expr-bvar drop job4 aux-remap remap-run -> -1 outcome-unsupported }T
T{ 1 job4 aux-tier expr-bvar drop job4 aux-remap remap-run
   -> 5 job4 aux-tier expr-bvar drop outcome-ok }T
job4 aux-free  mutual stage-free
\ One motive: the any-motive casesOn is the one-motive one.
T{ s" Nat" ind job aux-cases-on-any lean-cases-of grade -> outcome-ok 2 }T
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
\ Table: #0 refused, #1 -> #5, past the table + 7.
create two-cells -1 , 5 ,
T{ two-cells 2 rp remap-table! 7 rp remap-delta! 1 var 0 run 2 var 0 run
   -> 5 var outcome-ok 9 var outcome-ok }T
T{ 0 var 1 var app 0 run -> -1 outcome-unsupported }T
\ Erasing: names and binder information go, variables stay.
T{ true rp remap-erase! 0 0 rp remap-shift! 7 1 sort0 2 var lam 0 run
   -> 0 0 sort0 2 var lam outcome-ok }T
T{ false rp remap-erase! -> }T
\ A letE: its body is under its binder; erased, it loses its name only.
: let-of ( name nondep? body -- e ) >r let-head sort0 sort0 r> tier expr-let drop ;
T{ 0 1 rp remap-shift! 0 false 3 var let-of 0 run -> 0 false 4 var let-of outcome-ok }T
T{ 0 false 0 var 3 var app let-of 0 run -> 0 false 0 var 4 var app let-of outcome-ok }T
T{ true rp remap-erase! 0 0 rp remap-shift! 7 true 3 var let-of 0 run
   -> 0 true 3 var let-of outcome-ok }T
T{ false rp remap-erase! -> }T
\ An mdata record with a variable to renumber is unsupported; out of
\ fuel, exhausted.
T{ 0 1 rp remap-shift! 3 var tier expr-mdata drop 0 run -> -1 outcome-unsupported }T
T{ 1 rp remap-fuel! 0 var 1 var app 0 run -> -1 outcome-exhausted }T
rp remap-free

\ ---- Running out (review L1). Every fuel from 1 to 40 ends ok or
\ exhausted, with the stack as it was, whichever renumbering it stops in.
: survives? ( d xt fuel -- flag )
  job aux-remap remap-fuel! job swap execute
  dup outcome-ok = swap outcome-exhausted = or ;
variable swept
: sweep ( d xt -- n )
  0 swept ! 41 1 do 2dup i survives? if 1 swept +! then loop 2drop swept @ ;
T{ s" Nat" ind ' aux-cases-on sweep -> 40 }T
T{ s" Acc" ind ' aux-cases-on sweep -> 40 }T
T{ s" Eq" ind ' aux-rec-on sweep -> 40 }T
T{ s" List" ind ' aux-ctor-idx sweep -> 40 }T
T{ s" And" ind ' aux-cases-on-any sweep -> 40 }T
T{ remap-fuel job aux-remap remap-fuel! -> }T
T{ s" Nat" cases-of lean-cases-of grade -> outcome-ok 2 }T
\ A scratch tier that can hold nothing more: each construction refuses,
\ never ok, with the stack as it was.
create job3 /aux allot
T{ lib job3 aux-init -> outcome-ok }T
T{ job3 aux-tier tier-seal -> outcome-ok }T
T{ s" Nat" ind job3 aux-cases-on-any ok? -> false }T
T{ s" Nat" ind job3 aux-rec-on ok? -> false }T
T{ s" Nat" ind job3 aux-ctor-idx ok? -> false }T
job3 aux-free

job aux-free  lib stage-free
bye
