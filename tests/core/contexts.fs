\ Checker contexts (ADR 0009, step 3): every module of src/core and
\ src/kernel keeps its mutable state in the current task's context
\ (src/lib/context.fs), so several checks run in one image without
\ sharing anything. This file checks that
\ - every state word gives an address inside the current context, at the
\   same offset in every context (a member left global fails);
\ - a new context holds exactly the bytes the main context held right after
\   loading (a missing set-up word fails);
\ - a trial of real checker work (the pinned fixtures of the plain and
\   definition tables, and random terms run through inference, conversion,
\   comparison, beta, shift, instantiation, the level passes, universe
\   substitution, the signature index and the definition probe), folded
\   into a digest of every outcome, result, fuel and count, gives exactly
\   its serial digest when contexts are interleaved step by step in one
\   task, and when the trials run as jobs on the pool (src/lib/task.fs:
\   threads on Gforth 1.0, cooperative on 0.7.3 with a yield every few
\   steps, serial in contexts-serial.fs), with the main context untouched;
\ - the deepest recursive passes fit the job stacks (job-stacks-cover?)
\   and give their serial results inside jobs.
\ Constants defined before this file set the stress: stress-rounds job
\ batches (default 2) of trial-jobs jobs (8) of trial-steps steps (300).
\ Nothing here checks or accepts a theorem.
include ../support/tester.fs
include ../support/checks.fs
\ The pool first, so that mixed-beta.fs's load-time guard also checks the
\ job stacks.
require ../../src/lib/task.fs
require ../../src/kernel/mixed-definition-probe.fs
include ../support/plain-terms.fs
include ../support/plain-cases.fs

[defined] stress-rounds 0= [if] 2 constant stress-rounds [then]

\ One trial's own state, a member of every context like the modules' state.
begin-structure /trial
  field: trial-seed       \ random generator state
  field: trial-hash       \ digest of every result so far
  field: trial-left       \ steps still to do
  field: trial-done       \ steps done
  field: trial-every      \ yield after every this many steps; 0 never
  field: trial-token      \ signature index token of the current session
  4 cells +field trial-formals    \ caller arrays: formal parameter IDs
  16 cells +field trial-pairs     \ (index identity) level pairs
end-structure
/trial context-record: trial
\ The stack cells the deepest passes used in this context (part c).
begin-structure /depths
  field: depths-return
  field: depths-data
end-structure
/depths context-record: depths

\ The main context right after loading, before any test changes it.
create loaded context-bytes allot
context-main loaded context-bytes move

\ Members: each state word's address lies inside the current context.
create state-words
  ' lf-terms , ' lf-levels , ' lf-names , ' lf-name-pool , ' lf-crefs ,
  ' lf-lscope-state , ' lf-lscope-walk , ' lf-cterm-stamps , ' lf-cterm-walker ,
  ' lf-cts-walker , ' lf-hsort-term-identities , ' lf-hsort-level-identities ,
  ' lf-href-walker , ' lf-ssession , ' lf-ssession-walker , ' lf-repr-walker ,
  ' lf-lvalue-state , ' lf-lcmp-state , ' lf-lsubst-walker , ' lf-lsubst-job ,
  ' lf-mshift-job , ' lf-minst-job , ' lf-mbeta-frames , ' lf-mcompare-walker ,
  ' lf-mcompare-level-walker , ' lf-mconvert-walker , ' lf-minfer-job ,
  ' lf-mls-walker , ' lf-mls-job , ' lf-mdefinition-request , ' lf-msp-index ,
  ' lf-msp-request , ' lf-msa-state ,
here state-words - 1 cells / constant state-count
: state-word ( i -- addr ) cells state-words + @ execute ;
: state-offset ( addr -- n ) lf-context @ - ;
: inside? ( addr -- flag ) state-offset 0 context-bytes within ;
: all-inside? ( -- flag ) true state-count 0 ?do i state-word inside? and loop ;
: offsets ( -- x ) 0 state-count 0 ?do 31 * i state-word state-offset + loop ;
T{ all-inside? -> true }T
context-new throw constant other
other context-use
T{ all-inside? offsets -> true context-main context-use offsets }T
\ A new context starts exactly as the main context did after loading.
T{ other loaded context-bytes tuck compare -> 0 }T
T{ other context-free -> 0 }T

\ Random numbers from the trial's own seed, the same on every cell size,
\ and the digest every result is folded into.
: seed-cell ( -- addr ) trial trial-seed ;
: choose ( n -- u )
  seed-cell @ 1103515245 * 12345 + 2147483647 and dup seed-cell ! 16 rshift swap mod ;
: mix ( x -- ) trial trial-hash dup @ 31 * rot + 2147483647 and swap ! ;
: mix-result ( index id 0 | status -- ) dup ok? if mix mix then mix ;
: mix-counts ( -- )
  lf-term-count @ mix lf-term-serial @ mix lf-level-count @ mix lf-level-serial @ mix
  lf-cref-count @ mix lf-name-count @ mix lf-msp-count @ mix ;
: mix-terms ( -- )
  lf-term-count @ 0 ?do i lf-term-read if mix mix mix else -1 mix then loop ;

\ Random choices: a term or level of the store (0 when it is empty, which
\ is invalid), a handle (identity 0 for an index the store does not hold),
\ a fuel and a level pair at a position of the trial's pair array.
: pick-node ( -- index ) lf-term-count @ ?dup if choose else 0 then ;
: pick-level ( -- index ) lf-level-count @ ?dup if choose else 0 then ;
: handle? ( index -- index identity ) dup lf-term-identity 0= if 0 then ;
: pick-handle ( -- index identity ) pick-node handle? ;
: pick-fuel ( -- n )
  8 choose case 0 of 0 endof 1 of 3 endof 2 of 20 endof 3 of 60 endof
    4 of 200 endof 5 of 2000 endof 50000 swap endcase ;
: pairs ( -- addr ) trial trial-pairs ;
: formals ( -- addr ) trial trial-formals ;
: pair! ( index identity position -- ) 2* cells pairs + >r swap r> 2! ;
: token ( -- token ) trial trial-token @ ;
: open-index ( -- ) lf-msp-begin drop lf-msp-token 0= if 0 then trial trial-token ! ;
: session ( -- ) mix-terms fresh-session open-index ;

\ Growing a random term DAG over the nodes already there; a refused
\ constructor (a full store, or an invalid child) adds nothing.
: add-sort ( -- ) pick-level dup lf-level-identity if lf-hterm-sort if 2drop then else drop then ;
: add-var ( -- ) 4 choose lf-term-bvar if drop then ;
: add-binary ( tag -- ) >r pick-node pick-node r> lf-term-binary if drop then ;
: add-constant ( -- )
  0 s" c" lf-name-str 0= if exit then lf-name-generation @
  pick-level dup lf-level-identity 0= if drop 2drop exit then 0 pair!
  pairs 1 lf-cref-new 0= if exit then lf-cterm-new if 2drop then ;
: new-level ( -- index true | false )
  4 choose case 0 of pick-level lf-level-succ endof
    1 of pick-level pick-level lf-level-max endof
    2 of pick-level pick-level lf-level-imax endof
    drop 2 choose if u-name else v-name then lf-level-param 0 endcase ;
: add-level ( -- ) new-level if drop then ;
: grow ( -- )
  8 choose case 0 of add-sort endof 1 of add-var endof 2 of lf-tag-lam add-binary endof
    3 of lf-tag-pi add-binary endof 4 of add-constant endof 5 of add-level endof
    lf-tag-app add-binary endcase ;
: build ( -- ) session 12 choose 4 + 0 ?do grow loop ;

\ Checker operations on random handles; each folds its outcome, result
\ and the fuel it left.
: op-infer ( -- ) token pick-handle pick-fuel lf-mixed-infer mix mix mix lf-minfer-fuel @ mix ;
: op-convert ( -- )
  pick-handle pick-handle pick-fuel lf-mixed-convert mix lf-mconvert-fuel @ mix ;
: op-compare ( -- )
  pick-handle pick-handle pick-fuel lf-mixed-compare mix lf-mcompare-fuel @ mix ;
: op-beta ( -- ) pick-handle pick-fuel lf-mixed-beta mix mix mix lf-mbeta-fuel @ mix ;
: op-shift ( -- )
  pick-handle 3 choose 3 choose pick-fuel lf-mixed-shift mix mix mix lf-mshift-fuel @ mix ;
: op-instantiate ( -- )
  pick-handle pick-handle pick-fuel lf-mixed-instantiate mix mix mix lf-minst-fuel @ mix ;
: op-probe ( -- )
  token pick-handle pick-handle pick-fuel lf-mixed-definition-probe mix
  lf-mdefinition-fuel @ mix ;
: op-levels ( -- )
  pick-level pick-level pick-fuel lf-level-compare mix lf-lcmp-fuel @ mix
  pick-level pick-fuel lf-level-value mix mix
  u-name 3 choose lf-lassign-add mix pick-level pick-fuel lf-level-value-assigned mix mix ;
: substitution ( -- formals pairs count )
  u-name formals ! v-name formals cell+ !
  2 0 do pick-level dup lf-level-identity 0= if 0 then i pair! loop formals pairs 2 choose 1+ ;
: op-substitute ( -- )
  pick-handle substitution pick-fuel lf-mixed-level-substitute mix-result lf-mls-fuel @ mix ;
: name-f ( -- name ) 0 s" f" lf-name-str 0= if 0 then ;
: op-signature ( -- )
  token name-f pick-handle substitution nip pick-fuel lf-msp-put mix
  token name-f substitution rot drop pick-fuel lf-msp-specialize mix-result
  token pick-fuel lf-mixed-signature-audit mix lf-msa-fuel @ mix ;

\ The pinned fixtures: the definition table's nine pairs
\ (tests/core/mixed-definition-table.fs), the composition DAG and the
\ five plain cases of the shift and instantiation tables.
: target-on ( domain -- node ) 0 make-var 1 make-var make-pi make-pi ;
: identity-on ( domain i -- node ) >r 0 make-var r> make-var make-lam make-lam ;
: beta-prop ( -- node ) 1 make-sort 0 make-var make-lam 0 make-sort make-app ;
: closed-pair ( n -- claim value )
  case
    0 of 0 make-sort target-on 0 make-sort 0 identity-on endof
    1 of 0 make-sort target-on 0 make-sort 1 identity-on endof
    2 of 0 make-sort 0 identity-on dup endof
    3 of 1 make-sort 0 make-sort endof
    beta-prop target-on 0 make-sort 0 identity-on rot endcase ;
: intern ( addr len -- id ) 0 -rot lf-name-str must ;
: constant-at-u ( addr len -- node )
  intern lf-name-generation @ pairs 1 lf-cref-new must lf-cterm-new must drop ;
: stage-id ( -- )
  u-name formals ! level-u dup lf-level-identity must 0 pair!
  token s" id" intern level-u make-sort target-on handle formals 1 50000 lf-msp-put ok? must ;
: body-with ( last addr len -- node )
  constant-at-u 1 make-var make-app swap make-var make-app
  0 make-var swap make-lam level-u make-sort swap make-lam ;
: polymorphic-pair ( n -- claim value )
  case
    0 of level-u make-sort target-on 0 s" id" body-with endof
    1 of level-u make-sort target-on 1 s" id" body-with endof
    2 of level-u make-sort 0 make-var level-u make-sort make-pi make-pi 0 s" id" body-with endof
    level-u make-sort target-on 0 s" missing" body-with rot endcase ;
: probe ( claim value -- )
  >r >r token r> handle r> handle 50000 lf-mixed-definition-probe mix lf-mdefinition-fuel @ mix ;
: infer ( node -- ) >r token r> handle 50000 lf-mixed-infer mix mix mix lf-minfer-fuel @ mix ;
: plain ( node -- )
  dup infer dup handle 50000 lf-mixed-beta mix mix mix
  dup handle 0 1 50000 lf-mixed-shift mix mix mix
  handle 0 make-sort handle 50000 lf-mixed-instantiate mix mix mix ;
: composition ( -- )
  build-composition drop open-index 20 infer 10 20 probe
  10 handle token 20 handle 50000 lf-mixed-infer mix 50000 lf-mixed-convert mix ;
15 constant fixtures
: fixture ( k -- )
  mix-terms dup 5 < if fresh-session open-index closed-pair probe exit then
  dup 9 < if fresh-session open-index stage-id 5 - polymorphic-pair probe exit then
  dup 9 = if drop composition exit then
  10 - build-plain-case open-index plain ;

\ One step: a random operation or fixture, then the counts.
: step ( -- )
  13 choose case 0 of build endof 1 of op-infer endof 2 of op-convert endof
    3 of op-compare endof 4 of op-beta endof 5 of op-shift endof
    6 of op-instantiate endof 7 of op-probe endof 8 of op-levels endof
    9 of op-substitute endof 10 of op-signature endof 11 of build endof
    drop fixtures choose fixture 0 endcase
  mix-counts 1 trial trial-done +! ;
: due? ( -- flag ) trial trial-every @ ?dup if trial trial-done @ swap mod 0= else false then ;
: step? ( -- more? )
  trial trial-left @ dup if -1 trial trial-left +! step then 0<> ;
\ A trial: job k's seed, steps and yield period, in the current context.
: trial-start ( k steps every -- )
  trial /trial erase trial trial-every ! trial trial-left ! 7919 * 1+ seed-cell ! session ;
: trial-finish ( -- ) mix-terms mix-counts ;
: trial-run ( -- ) begin step? while due? if task-yield then repeat trial-finish ;
: digest ( -- x ) trial trial-hash @ ;

\ The serial reference: each trial alone, to the end, in a fresh context.
[defined] trial-jobs [if] trial-jobs [else] 8 [then] constant jobs
[defined] trial-steps [if] trial-steps [else] 300 [then] constant steps
create serial jobs cells allot
create contexts jobs cells allot
create handles jobs cells allot
: slot ( k table -- addr ) swap cells + ;
: fresh ( -- context ) context-new throw dup context-use ;
: home ( -- ) context-main context-use ;
: serial-trial ( k -- )
  fresh swap dup steps 0 trial-start trial-run digest swap serial slot ! home
  context-free throw ;
: serial-all ( -- ) jobs 0 ?do i serial-trial loop ;
serial-all
T{ lf-context @ context-main = -> true }T
T{ depth -> 0 }T
\ Different seeds give different digests, so a mix-up would show.
: distinct? ( -- flag ) true jobs 1 ?do i serial slot @ i 1- serial slot @ <> and loop ;
T{ distinct? -> true }T

\ Job k's context, prepared with its trial; then its digest compared.
: prepare ( k every -- )
  >r fresh over contexts slot ! steps r> trial-start home ;
: wrong? ( k -- flag )
  dup contexts slot @ context-use serial slot @ digest <> home ;
: wrong-count ( -- n ) 0 jobs 0 ?do i wrong? - loop ;
: free-all ( -- failures ) 0 jobs 0 ?do i contexts slot @ context-free 0<> - loop ;

\ (a) Interleaved in one task: two contexts, then all of them, one step of
\ each in turn.
: step-in ( k -- more? ) contexts slot @ context-use step? ;
: finish-in ( k -- ) contexts slot @ context-use trial-finish ;
: round ( n -- more? ) false swap 0 ?do i step-in or loop ;
: interleave ( n -- ) begin dup round 0= until 0 ?do i finish-in loop home ;
: prepare-n ( n -- ) 0 ?do i 0 prepare loop ;
: wrong-n ( n -- count ) 0 swap 0 ?do i wrong? - loop ;
: free-n ( n -- failures ) 0 swap 0 ?do i contexts slot @ context-free 0<> - loop ;
T{ 2 prepare-n 2 interleave 2 wrong-n 2 free-n -> 0 0 }T
T{ jobs prepare-n jobs interleave jobs wrong-n jobs free-n -> 0 0 }T

\ (b) As jobs on the pool, each yielding every k mod 3 + 1 steps on the
\ cooperative host; the main context is not touched.
create main-before context-bytes allot
: main-same? ( -- flag ) context-main main-before context-bytes tuck compare 0= ;
: submit-all ( -- failures )
  0 jobs 0 ?do i i 3 mod 1+ prepare
    i contexts slot @ ['] trial-run job-submit swap i handles slot ! 0<> - loop ;
\ A refused submission was counted already and leaves no job to wait for.
: wait-all ( -- failures )
  0 jobs 0 ?do i handles slot @ ?dup if job-wait 0<> - then loop ;
: batch ( -- failures )
  context-main main-before context-bytes move
  submit-all wait-all + wrong-count + free-all + main-same? 0= - ;
: batches ( n -- failures ) 0 swap 0 ?do batch + loop ;
T{ stress-rounds batches -> 0 }T
T{ lf-context @ context-main = -> true }T
T{ depth -> 0 }T

\ (c) Recursion inside jobs. The beta, instantiate and shift passes nest
\ up to three times lf-term-capacity frames; mixed-beta.fs states the
\ cells that need, which the job stacks cover (also checked when it
\ loads). The deepest inputs known then run inside jobs, with both stacks
\ painted below the job's word to measure what they used.
T{ lf-mbeta-data-cells lf-mbeta-return-cells job-stacks-cover? -> true }T
1400 constant paint-cells
48879 constant paint-mark
: paint-span ( top -- end start ) dup paint-cells cells - ;
: paint ( top -- ) paint-span ?do paint-mark i ! 1 cells +loop ;
: used ( top -- cells )
  dup paint-span ?do i @ paint-mark <> if i - 1 cells / unloop exit then 1 cells +loop
  drop 0 ;
: tops ( -- rtop stop ) rp@ 16 cells - sp@ 16 cells - ;
: deeper ( rcells scells -- )
  depths depths-data dup @ rot max swap ! depths depths-return dup @ rot max swap ! ;
: painted ( xt -- )
  tops 2dup paint paint 2>r execute 2r> used swap used swap deeper ;
\ The deepest nesting found for a 64-node store (tests/core/mixed-beta.fs):
\ app(T, T) with T = m lambdas over bvar m-1, over one constant.
: lams ( body n -- node ) 0 ?do 0 swap make-lam loop ;
: twin ( m -- node )
  fresh-session open-index 0 s" x" lf-name-str must lf-name-generation @
  0 dup lf-level-identity must 0 pair! pairs 1 lf-cref-new must lf-cterm-new must 2drop
  dup 1- make-var swap lams dup make-app ;
: beta ( node -- ) handle 100000 lf-mixed-beta mix mix mix lf-mbeta-fuel @ mix ;
\ The deepest inference (tests/core/infer-deep.fs): fun (f : S -> S) (c : S)
\ => f (f ... (f c)) with n applications, S = Sort u.
: apps ( n -- node )
  fresh-session open-index level-u make-sort drop 0 make-var drop 0 0 make-pi drop
  1 make-var drop 1 swap 0 ?do 3 swap make-app loop 0 swap make-lam 2 swap make-lam ;
\ The deepest level nesting: 63 successors above zero.
: chain ( -- level ) lf-level-reset 0 63 0 ?do lf-level-succ must loop ;
: levels ( level -- )
  dup 1000 lf-level-value mix mix dup 1000 lf-level-compare mix lf-lcmp-fuel @ mix ;
: deep-work ( -- )
  61 twin beta 60 twin beta 26 apps infer 29 apps infer chain levels mix-counts ;
: deep-run ( -- ) ['] deep-work painted ;
variable deep-serial
: deep-reference ( -- )
  fresh 0 0 0 trial-start deep-work digest deep-serial ! home context-free throw ;
deep-reference
variable deep-context
: deep-job ( -- ior same? )
  fresh deep-context ! 0 0 0 trial-start home
  deep-context @ ['] deep-run job-submit throw job-wait
  deep-context @ context-use digest deep-serial @ = home ;
: deep-depths ( -- return-cells data-cells )
  deep-context @ context-use depths depths-return @ depths depths-data @ home ;
T{ deep-job -> 0 true }T
T{ deep-depths lf-mbeta-data-cells < swap lf-mbeta-return-cells < -> true true }T

." task host " task-host . ." (0 serial, 1 cooperative, 2 threads), "
pool-size . ." workers, " stress-rounds . ." rounds of " jobs . ." jobs of "
steps . ." steps; the deepest passes in a job used " deep-depths swap
. ." return-stack and " . ." data-stack cells" cr
T{ deep-context @ context-free -> 0 }T
T{ depth -> 0 }T
bye
