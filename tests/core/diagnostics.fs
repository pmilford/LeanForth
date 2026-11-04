\ Diagnostics (src/core/diagnostics.fs, docs/programming/DIAGNOSTICS.md):
\ the record and its first-failure rule; every site that reports full or
\ exhausted records the right code, site and numbers (white-box where a
\ 64-node store cannot reach the limit); the invalid and undecided sites
\ record theirs; and over random checker work (tests/support/
\ checker-trial.fs), cleared before every check, each outcome is explained
\ by a code of its own family: none after ok, fuel after exhausted, a room
\ code after full, and an input or undecided code (or none) after invalid
\ or unknown. That diagnostics never change an outcome, a result or fuel
\ is shown by the differentials against the code before them (DIAGNOSTICS.md).
\ Each case runs in a new context, so no state needs restoring.
include ../support/tester.fs
include ../support/checks.fs
require ../../src/lib/task.fs
require ../../src/kernel/mixed-definition-probe.fs
include ../support/plain-terms.fs
include ../support/plain-cases.fs
include ../support/checker-trial.fs

: begin-check ( -- ) context-new throw context-use fresh-session open-index ;
: end-check ( -- ) lf-context @ context-main context-use context-free throw ;
\ The numbers and code recorded, and whether the site's name is text.
: diag ( -- n1 n2 code ) lf-diag@ nip ;
: at? ( c-addr u -- flag )
  lf-diagnostic lf-diag-site @ ?dup if count compare 0= else 2drop false then ;
: test-site ( -- site ) c" tests diagnostics" ;
create cells4 4 cells allot

\ The record: clear in a new context, first failure wins until cleared,
\ one record per context, printing.
begin-check
T{ lf-diag-clear? diag -> true 0 0 lf-diag-none }T
T{ 1 2 test-site lf-diag-terms-full lf-diag-note diag -> 1 2 lf-diag-terms-full }T
T{ 3 4 test-site lf-diag-fuel lf-diag-note diag -> 1 2 lf-diag-terms-full }T
T{ s" tests diagnostics" at? -> true }T
T{ lf-diag-clear lf-diag-clear? diag -> true 0 0 lf-diag-none }T
T{ 3 4 test-site lf-diag-fuel lf-diag-note diag -> 3 4 lf-diag-fuel }T
lf-context @ constant first-context
context-new throw dup context-use
T{ lf-diag-clear? -> true }T
first-context context-use
T{ diag -> 3 4 lf-diag-fuel }T
context-main context-use context-free throw
first-context context-use
." example: " lf-diag. cr
end-check
\ Every code of the catalogue has a name.
create codes 1 , 2 , 3 , 4 , 5 , 6 , 7 , 8 , 9 , 10 , 11 , 12 , 13 , 14 , 15 , 16 ,
  20 , 21 , 22 , 23 , 24 , 25 , 26 , 27 , 28 , 29 , 30 , 31 , 32 , 33 , 34 , 35 , 36 ,
  40 , 41 , 42 , 43 , 50 , 51 , 52 , 53 , 54 , 55 , 56 , 57 , 58 , 59 , 60 , 61 ,
  62 , 63 , 64 , 65 , 66 , 67 , 68 , 69 , 70 , 71 , 72 , 73 , 74 , 75 ,
here codes - 1 cells / constant code-count
: named? ( code -- flag ) lf-diag-name s" unknown code" compare 0<> ;
: all-named? ( -- flag ) true code-count 0 ?do i cells codes + @ named? and loop ;
T{ all-named? 0 named? -> true false }T
T{ lf-diag-fuel lf-diag-name s" fuel exhausted" compare -> 0 }T
\ The catalogue table lists exactly these codes, in this order, and ends
\ with the entry that names every other code.
: listed? ( entry i -- entry' flag )
  cells codes + @ over lf-diag-entry-code = swap lf-diag-entry-next swap ;
: catalogue-codes? ( -- flag )
  lf-diag-catalogue true code-count 0 ?do swap i listed? rot and loop
  swap lf-diag-entry-code lf-diag-none = and ;
T{ catalogue-codes? -> true }T
T{ 99 lf-diag-name s" unknown code" compare -> 0 }T

\ Stores: full, a spent serial, and a store that fails its own checks.
: fill-terms ( -- ) lf-term-capacity lf-term-count @ ?do 0 lf-term-bvar must drop loop ;
begin-check fill-terms lf-diag-clear
T{ 0 lf-term-bvar diag -> false 64 64 lf-diag-terms-full }T
T{ s" terms lf-term-add" at? -> true }T
end-check
begin-check lf-term-reset max-n lf-term-serial ! lf-diag-clear
T{ 0 lf-term-bvar diag -> false max-n 1 lf-diag-serial-spent }T
end-check
begin-check -1 lf-term-count ! lf-diag-clear
T{ 0 lf-term-bvar diag -> false -1 64 lf-diag-corrupted }T
end-check
: chain ( -- level ) lf-level-reset 0 63 0 ?do lf-level-succ must loop ;
begin-check chain drop lf-diag-clear
T{ 0 lf-level-succ diag -> false 64 64 lf-diag-levels-full }T
T{ s" levels lf-level-add" at? -> true }T
end-check
: fill-names ( -- ) lf-name-capacity lf-name-count @ ?do 0 i lf-name-num must drop loop ;
begin-check fill-names lf-diag-clear
T{ 0 999 lf-name-num diag -> false 64 64 lf-diag-names-full }T
T{ s" names lf-name-intern" at? -> true }T
end-check
create big 2048 allot  big 2048 char a fill
begin-check 0 big 2000 lf-name-str must drop lf-diag-clear
T{ 0 big 100 lf-name-str diag -> false 2102 2048 lf-diag-name-bytes-full }T
end-check
: x-name ( -- name generation ) 0 s" x" lf-name-str must lf-name-generation @ ;
: zero-pair ( -- ) 0 dup lf-level-identity must 0 pair! ;
: new-ref ( -- flag ) x-name pairs 1 lf-cref-new dup if nip nip then ;
: fill-refs ( -- ) lf-cref-capacity 0 ?do new-ref must loop ;
begin-check zero-pair fill-refs lf-diag-clear
T{ new-ref diag -> false 32 32 lf-diag-references-full }T
T{ s" constant-references lf-cref-new" at? -> true }T
end-check
: sort0 ( -- node identity ) 0 make-sort handle ;
: put ( name -- status ) >r token r> sort0 formals 0 1000 lf-msp-put ;
: fill-index ( -- ) lf-msp-capacity 0 ?do 0 i 1+ lf-name-num must put ok? must loop ;
begin-check fill-index lf-diag-clear
T{ 0 99 lf-name-num must put diag -> outcome-full 32 32 lf-diag-signatures-full }T
T{ s" mixed-signature-probe lf-msp" at? -> true }T
end-check

\ Walks and recursive passes running out of fuel: over every fuel up to a
\ bound, some runs end exhausted at the pass's own site, and every
\ exhausted run records the fuel code.
2variable want
variable hits
variable wrong
: exhausted-check ( outcome -- )
  outcome-exhausted = if lf-diag-code@ lf-diag-fuel <> if 1 wrong +! then
  want 2@ at? if 1 hits +! then then ;
: sweep ( xt max c-addr u -- hits wrong )
  want 2! 0 hits ! 0 wrong ! 0 ?do lf-diag-clear i over execute exhausted-check loop
  drop hits @ 0> wrong @ ;
\ Fixtures in the current session: app(#0, #0) at 2; Sort u and Sort v at
\ 3 and 4; fun _ : Sort 0 => #0 applied to Sort 0, at 8.
: pair-app ( -- node ) 0 make-var 0 make-var make-app ;
: sorts ( -- ) level-u make-sort drop level-v make-sort drop ;
: redex ( -- node ) 0 make-sort 0 make-var make-lam 0 make-sort make-app ;
: samples ( -- ) pair-app drop sorts redex drop ;
: f-cterm ( fuel -- outcome ) >r 2 handle r> lf-cterm-check ;
: f-scope ( fuel -- outcome ) >r 2 handle 1 r> lf-constant-term-scope ;
: f-hterm ( fuel -- outcome ) >r 3 handle r> lf-hterm-check ;
: f-session ( fuel -- outcome ) 3 swap lf-ssession-check ;
: f-repr ( fuel -- outcome ) 2 lf-repr-symbolic rot lf-repr-check ;
: f-lscope ( fuel -- outcome ) level-u swap lf-lscope-check ;
: f-compare ( fuel -- outcome ) >r 3 handle 3 handle r> lf-mixed-compare ;
: f-convert ( fuel -- outcome ) >r 9 handle 5 handle r> lf-mixed-convert ;
: f-beta ( fuel -- outcome ) >r 9 handle r> lf-mixed-beta nip nip ;
: f-shift ( fuel -- outcome ) >r 2 handle 0 1 r> lf-mixed-shift nip nip ;
: f-inst ( fuel -- outcome ) >r 2 handle 3 handle r> lf-mixed-instantiate nip nip ;
: f-infer ( fuel -- outcome ) >r token 7 handle r> lf-mixed-infer nip nip ;
: f-value ( fuel -- outcome ) 4 swap lf-level-value nip ;
: f-lcompare ( fuel -- outcome ) >r 4 3 r> lf-level-compare ;
: f-audit ( fuel -- outcome ) token swap lf-mixed-signature-audit ;
: u-formal ( -- formals ) u-name formals ! formals ;
: f-lsubst ( fuel -- outcome )
  >r 4 u-formal 0 cells4 ! cells4 1 r> lf-lsubst dup ok? if nip then ;
: f-mls ( fuel -- outcome )
  >r 3 handle u-formal zero-pair pairs 1 r> lf-mixed-level-substitute
  dup ok? if drop 2drop outcome-ok then ;
begin-check samples
T{ ' f-cterm 10 s" constant-term-boundary lf-cterm-check" sweep -> true 0 }T
T{ ' f-scope 10 s" constant-term-scope lf-constant-term-scope" sweep -> true 0 }T
T{ ' f-hterm 20 s" generation-handles lf-hterm-check" sweep -> true 0 }T
T{ ' f-session 20 s" symbolic-session lf-ssession-check" sweep -> true 0 }T
T{ ' f-repr 5 s" tagged-sort-boundary lf-repr-check" sweep -> true 0 }T
T{ ' f-lscope 5 s" level-scope lf-lscope-check" sweep -> true 0 }T
T{ ' f-compare 20 s" mixed-compare lf-mixed-compare" sweep -> true 0 }T
T{ ' f-convert 60 s" mixed-convert lf-mixed-convert" sweep -> true 0 }T
T{ ' f-beta 60 s" mixed-beta lf-mixed-beta" sweep -> true 0 }T
T{ ' f-shift 20 s" mixed-shift lf-mixed-shift" sweep -> true 0 }T
T{ ' f-inst 20 s" mixed-instantiate lf-mixed-instantiate" sweep -> true 0 }T
T{ ' f-infer 80 s" mixed-infer lf-mixed-infer" sweep -> true 0 }T
T{ ' f-value 20 s" level-value lf-level-value" sweep -> true 0 }T
T{ ' f-lcompare 40 s" level-normalize lf-level-equivalent" sweep -> true 0 }T
T{ ' f-audit 5 s" mixed-signature-audit lf-mixed-signature-audit" sweep -> true 0 }T
T{ ' f-lsubst 20 s" level-substitute lf-lsubst" sweep -> true 0 }T
T{ ' f-mls 30 s" mixed-level-substitute lf-mixed-level-substitute" sweep -> true 0 }T
\ Lean's normalize (level-compare's decision) runs out of fuel by itself.
T{ lf-diag-clear 3 4 0 lf-level-equivalent diag -> false outcome-exhausted 0 0 lf-diag-fuel }T
T{ s" level-normalize lf-level-equivalent" at? -> true }T
end-check

\ Room limits that a 64-node store cannot reach, white-box: a work stack
\ of capacity 1, frames limited to 1, the depth limits, the cell maximum,
\ and full binder contexts.
begin-check samples 1 lf-cterm-walker walk-capacity ! lf-diag-clear
T{ 2 handle 10 lf-cterm-check diag -> outcome-full 1 1 lf-diag-work-stack-full }T
T{ s" constant-term-boundary lf-cterm-check" at? -> true }T
end-check
\ A walk that ends before its first visit records no node (-1), not the
\ node an earlier walk visited last: a work stack that cannot hold the
\ root (a corrupted capacity) is malformed at -1. An unpaired walk that
\ ends undecided records its node and 0, never its unused context cell.
begin-check samples 2 handle 10 lf-cterm-check drop 0 lf-cterm-walker walk-capacity !
lf-diag-clear
T{ 2 handle 10 lf-cterm-check diag -> outcome-invalid -1 0 lf-diag-malformed }T
end-check
begin-check 5 lf-cterm-walker walk-node ! 7 lf-cterm-walker walk-context ! lf-diag-clear
T{ outcome-unknown lf-cterm-walker test-site lf-diag-walk diag
  -> outcome-unknown 5 0 lf-diag-undecided }T
end-check
begin-check samples 1 lf-mbeta-frames frame-limit ! lf-diag-clear
T{ 9 handle 1000 lf-mixed-beta nip nip diag -> outcome-full 1 1 lf-diag-frame-limit }T
T{ s" mixed-beta lf-mixed-beta" at? -> true }T
end-check
begin-check samples 1 lf-mshift-frames frame-limit ! lf-diag-clear
T{ 2 handle 0 1 1000 lf-mixed-shift nip nip diag -> outcome-full 1 1 lf-diag-frame-limit }T
end-check
begin-check samples 1 lf-minst-frames frame-limit ! lf-diag-clear
T{ 2 handle 3 handle 1000 lf-mixed-instantiate nip nip diag
  -> outcome-full 1 1 lf-diag-frame-limit }T
T{ s" mixed-instantiate lf-mixed-instantiate" at? -> true }T
end-check
begin-check 10 lf-lvalue-fuel ! lf-diag-clear
T{ 0 lf-lvalue-depth-limit lf-lvalue-walk diag -> -1 outcome-full 64 64 lf-diag-depth-limit }T
T{ s" level-value lf-level-value" at? -> true }T
lf-diag-clear
T{ max-n lf-lvalue-succ+ diag -> -1 outcome-full max-n 1 lf-diag-cell-maximum }T
end-check
\ Lean's normalize flattens a max of maxes onto its argument stack: eight
\ doublings of u stand for 256 arguments, more than its 128 cells.
: doubled ( level n -- level' ) 0 ?do dup lf-level-max must loop ;
begin-check lf-diag-clear
T{ level-u level-u 8 doubled 100000 lf-level-compare diag
  -> outcome-full 128 128 lf-diag-work-stack-full }T
T{ s" level-normalize lf-level-equivalent" at? -> true }T
end-check
\ K6: specializing imax 1 (u+1) with u for u depends on object sharing in
\ Lean; level-substitute records the node.
variable shared-imax
begin-check 1 level-u lf-level-succ must lf-level-imax must shared-imax ! lf-diag-clear
T{ shared-imax @ u-formal level-u cells4 ! cells4 1 100 lf-lsubst diag
  -> outcome-unknown shared-imax @ 0 lf-diag-shared-level }T
T{ s" level-substitute lf-lsubst" at? -> true }T
end-check
begin-check 10 lf-minfer-fuel ! lf-term-capacity lf-minfer-depth ! lf-diag-clear
T{ 0 lf-minfer-walk diag -> -1 outcome-full 64 64 lf-diag-frame-limit }T
T{ s" mixed-infer lf-mixed-infer" at? -> true }T
lf-diag-clear 0 lf-minfer-depth ! lf-depth-limit lf-minfer-context-depth !
T{ 0 0 lf-minfer-bind diag -> outcome-full 64 64 lf-diag-binders-full }T
end-check
begin-check 0 lf-cts-walker walk-pending ! max-n lf-cts-walker walk-context ! lf-diag-clear
T{ 0 0 lf-cts-walker lf-tag-lam lf-cts-binary diag -> outcome-full max-n max-n lf-diag-binders-full }T
T{ s" constant-term-scope lf-constant-term-scope" at? -> true }T
end-check
\ Reachable through the public words: a shift past the largest cell, and a
\ shift whose cutoff leaves no room for one more binder.
begin-check 1 make-var drop lf-diag-clear
T{ 0 handle 0 max-n 100 lf-mixed-shift nip nip diag
  -> outcome-full 1 max-n lf-diag-cell-maximum }T
T{ s" mixed-shift lf-mixed-shift" at? -> true }T
end-check
begin-check 0 make-sort 0 make-var make-lam drop lf-diag-clear
T{ 2 handle max-n 1 100 lf-mixed-shift nip nip diag
  -> outcome-full max-n max-n lf-diag-binders-full }T
T{ s" mixed-rebuild lf-rebuild-binary" at? -> true }T
end-check
\ Universe substitution: no room in the level store for a changed node,
\ and an identity serial that would run out. Level 7 is succ u.
: succ-u ( -- ) level-u lf-level-succ must drop ;
: fill-levels ( -- ) lf-level-capacity lf-level-count @ ?do 0 lf-level-succ must drop loop ;
: substitute-u ( -- result | status ) 7 u-formal 0 cells4 ! cells4 1 1000 lf-lsubst ;
begin-check succ-u fill-levels lf-diag-clear
T{ substitute-u diag -> outcome-full 64 64 lf-diag-levels-full }T
T{ s" level-substitute lf-lsubst" at? -> true }T
end-check
begin-check succ-u max-n lf-level-serial ! lf-diag-clear
T{ substitute-u diag -> outcome-full max-n 1 lf-diag-serial-spent }T
end-check
\ A rebuilding pass that fills the term store is explained by the store.
begin-check 1 make-var 0 make-var make-app drop fill-terms lf-diag-clear
T{ 2 handle 0 1 1000 lf-mixed-shift nip nip diag -> outcome-full 64 64 lf-diag-terms-full }T
T{ s" terms lf-term-add" at? -> true }T
end-check

\ Invalid input and undecided results.
begin-check samples lf-diag-clear
T{ 0 12345 10 lf-cterm-check diag -> outcome-invalid 0 12345 lf-diag-stale-handle }T
lf-diag-clear
T{ 0 handle 0 10 lf-constant-term-scope diag -> outcome-invalid 0 0 lf-diag-out-of-scope }T
lf-diag-clear
0 s" w" lf-name-str must constant w-name
w-name lf-level-param must constant w-level
T{ w-level 10 lf-lscope-check diag -> outcome-invalid w-name 0 lf-diag-out-of-scope }T
lf-diag-clear
0 lf-term-sort must constant concrete
T{ concrete handle 10 lf-cterm-check diag -> outcome-invalid concrete 0 lf-diag-malformed }T
lf-diag-clear
T{ token 2 handle -5 lf-mixed-infer nip nip diag -> outcome-invalid -5 0 lf-diag-bad-argument }T
lf-diag-clear
T{ 0 0 -1 lf-level-compare diag -> outcome-invalid -1 0 lf-diag-bad-argument }T
lf-diag-clear
T{ 0 1 1000 lf-level-compare diag -> outcome-unknown 0 1 lf-diag-undecided }T
lf-diag-clear
T{ level-u 1000 lf-level-value nip diag -> outcome-unknown level-u 0 lf-diag-symbolic-level }T
lf-diag-clear
T{ token u-name pairs 0 1000 lf-msp-specialize diag
  -> outcome-unknown u-name 0 lf-diag-no-signature }T
\ One site per module: the signature index records both of its failures
\ at the same site.
T{ s" mixed-signature-probe lf-msp" at? -> true }T
lf-diag-clear
T{ 0 9 lf-minfer-leaf diag -> -1 outcome-unknown 9 0 lf-diag-unsupported }T
end-check
begin-check 0 make-var 1 make-var 2drop lf-diag-clear
T{ 0 handle 1 handle 100 lf-mixed-compare diag -> outcome-unknown 0 1 lf-diag-undecided }T
T{ s" mixed-compare lf-mixed-compare" at? -> true }T
end-check
\ Sort 0 applied to Sort 0: the function's type, Sort 1, is not a Pi, and
\ it is rigid, so rule F1 rejects (ADR 0011); a lambda whose domain is a
\ lambda: the domain's type, a Pi, is not a Sort, so rule S2 rejects. Each
\ rejection replaces the record of the undecided step with the rule's code
\ and the reduced type.
begin-check 0 make-sort dup make-app drop lf-diag-clear
T{ token 1 handle 1000 lf-mixed-infer nip nip diag
  -> outcome-rejected 2 0 lf-diag-function-expected }T
T{ s" mixed-infer lf-mixed-infer" at? -> true }T
end-check
begin-check 0 make-sort 0 make-var make-lam 0 make-var make-lam drop lf-diag-clear
T{ token 4 handle 1000 lf-mixed-infer nip nip lf-diag-code@ -> outcome-rejected lf-diag-domain-type }T
end-check
\ The same step when no rule applies keeps its own record: fun (f : (fun
\ X : Type => X) (Prop -> Prop)) => f Prop, whose function type is a beta
\ redex that reduces to a Pi (only a visible Pi is applied today).
begin-check 0 make-sort 0 make-sort make-pi 1 make-sort 0 make-var make-lam swap make-app
  0 make-var 0 make-sort make-app make-lam drop lf-diag-clear
T{ token 10 handle 1000 lf-mixed-infer nip nip lf-diag-code@ -> outcome-unknown lf-diag-not-pi }T
end-check

\ Random checker work: each check's outcome is explained by its family.
: room-code? ( code -- flag ) lf-diag-terms-full lf-diag-pool-full 1+ within ;
: input-code? ( code -- flag ) lf-diag-bad-argument lf-diag-publisher-fault 1+ within ;
: undecided-code? ( code -- flag )
  dup lf-diag-undecided lf-diag-dependency-undecided 1+ within
  swap lf-diag-unsupported = or ;
: or-none ( code flag -- flag ) swap lf-diag-none = or ;
: rejection-code? ( code -- flag ) lf-diag-unknown-constant lf-diag-value-apart 1+ within ;
: explained? ( outcome -- flag )
  lf-diag-code@ swap case
    outcome-ok of lf-diag-none = endof
    outcome-rejected of rejection-code? endof
    outcome-exhausted of lf-diag-fuel = endof
    outcome-full of room-code? endof
    outcome-invalid of dup input-code? or-none endof
    outcome-unknown of dup undecided-code? or-none endof
    nip false swap endcase ;
create counts 7 cells allot  counts 7 cells erase
create recorded 7 cells allot  recorded 7 cells erase
61 constant code-limit
create code-counts code-limit cells allot  code-counts code-limit cells erase
variable unexplained  0 unexplained !
: count-code ( -- ) lf-diag-code@ 0 max code-limit 1- min cells code-counts + 1 swap +! ;
: count-outcome ( outcome -- )
  dup outcome? if cells dup counts + 1 swap +!
    lf-diag-clear? if drop else recorded + 1 swap +! count-code then
  else drop then ;
: explain-check ( outcome -- outcome )
  dup explained? 0= if 1 unexplained +! then dup count-outcome ;
' lf-diag-clear is before-check
' explain-check is checked
[defined] trial-rounds 0= [if] 8 constant trial-rounds [then]
: random-trials ( -- )
  trial-rounds 0 ?do context-new throw dup context-use i 1000 0 trial-start trial-run
    context-main context-use context-free throw loop ;
random-trials
' noop is checked  ' noop is before-check
: total ( -- n ) 0 7 0 do i cells counts + @ + loop ;
: all-recorded? ( outcome -- flag ) cells dup counts + @ swap recorded + @ = ;
: report ( -- )
  ." diagnostics over random checks: " total . ." checks, " unexplained @ . ." unexplained;"
  cr ."   per outcome, checks and those with a diagnostic:"
  7 0 do space i . ." : " i cells counts + @ . i cells recorded + @ . loop cr ;
: codes-seen ( -- )
  ."   codes recorded (code: times):"
  code-limit 0 do i cells code-counts + @ ?dup if space i . ." : " . then loop cr ;
report codes-seen
T{ unexplained @ -> 0 }T
T{ total 5000 > -> true }T
T{ outcome-exhausted all-recorded? outcome-full all-recorded? -> true true }T
T{ depth -> 0 }T
bye
