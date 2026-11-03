\ A trial of real checker work, for tests/core/contexts.fs and
\ diagnostics.fs: the pinned fixtures of the plain and definition tables,
\ and random terms run through inference, conversion, comparison, beta,
\ shift, instantiation, the level passes, universe substitution, the
\ signature index and the definition probe, each step folded into a
\ digest of every outcome, result, fuel and count. All of a trial's state
\ is in the current context (the record trial), so trials in different
\ contexts are independent. Two hooks, both noop unless a test sets them,
\ run around every checker call: before-check ( -- ) and checked
\ ( outcome -- outcome ). Include after plain-terms.fs and plain-cases.fs;
\ load src/lib/task.fs (task-yield) first. Test-only; nothing here checks
\ or accepts a theorem.

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

defer before-check ( -- )  ' noop is before-check
defer checked ( outcome -- outcome )  ' noop is checked

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
: add-sort ( -- )
  pick-level dup lf-level-identity if lf-hterm-sort if 2drop then else drop then ;
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
: op-infer ( -- )
  token pick-handle pick-fuel before-check lf-mixed-infer checked mix mix mix
  lf-minfer-fuel @ mix ;
: op-convert ( -- )
  pick-handle pick-handle pick-fuel before-check lf-mixed-convert checked mix
  lf-mconvert-fuel @ mix ;
: op-compare ( -- )
  pick-handle pick-handle pick-fuel before-check lf-mixed-compare checked mix
  lf-mcompare-fuel @ mix ;
: op-beta ( -- )
  pick-handle pick-fuel before-check lf-mixed-beta checked mix mix mix
  lf-mbeta-fuel @ mix ;
: op-shift ( -- )
  pick-handle 3 choose 3 choose pick-fuel before-check lf-mixed-shift checked mix mix mix
  lf-mshift-fuel @ mix ;
: op-instantiate ( -- )
  pick-handle pick-handle pick-fuel before-check lf-mixed-instantiate checked mix mix mix
  lf-minst-fuel @ mix ;
: op-probe ( -- )
  token pick-handle pick-handle pick-fuel before-check lf-mixed-definition-probe checked
  mix lf-mdefinition-fuel @ mix ;
: op-levels ( -- )
  pick-level pick-level pick-fuel before-check lf-level-compare checked mix
  lf-lcmp-fuel @ mix
  pick-level pick-fuel before-check lf-level-value checked mix mix
  u-name 3 choose lf-lassign-add mix
  pick-level pick-fuel before-check lf-level-value-assigned checked mix mix ;
: substitution ( -- formals pairs count )
  u-name formals ! v-name formals cell+ !
  2 0 do pick-level dup lf-level-identity 0= if 0 then i pair! loop
  formals pairs 2 choose 1+ ;
: op-substitute ( -- )
  pick-handle substitution pick-fuel before-check lf-mixed-level-substitute checked
  mix-result lf-mls-fuel @ mix ;
: name-f ( -- name ) 0 s" f" lf-name-str 0= if 0 then ;
: op-signature ( -- )
  token name-f pick-handle substitution nip pick-fuel before-check lf-msp-put checked mix
  token name-f substitution rot drop pick-fuel before-check lf-msp-specialize checked
  mix-result token pick-fuel before-check lf-mixed-signature-audit checked mix
  lf-msa-fuel @ mix ;

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
  token s" id" intern level-u make-sort target-on handle formals 1 50000
  lf-msp-put ok? must ;
: body-with ( last addr len -- node )
  constant-at-u 1 make-var make-app swap make-var make-app
  0 make-var swap make-lam level-u make-sort swap make-lam ;
: polymorphic-pair ( n -- claim value )
  case
    0 of level-u make-sort target-on 0 s" id" body-with endof
    1 of level-u make-sort target-on 1 s" id" body-with endof
    2 of level-u make-sort 0 make-var level-u make-sort make-pi make-pi
      0 s" id" body-with endof
    level-u make-sort target-on 0 s" missing" body-with rot endcase ;
: probe ( claim value -- )
  >r >r token r> handle r> handle 50000 before-check lf-mixed-definition-probe checked
  mix lf-mdefinition-fuel @ mix ;
: infer ( node -- )
  >r token r> handle 50000 before-check lf-mixed-infer checked mix mix mix
  lf-minfer-fuel @ mix ;
: plain ( node -- )
  dup infer dup handle 50000 before-check lf-mixed-beta checked mix mix mix
  dup handle 0 1 50000 before-check lf-mixed-shift checked mix mix mix
  handle 0 make-sort handle 50000 before-check lf-mixed-instantiate checked mix mix mix ;
: composition ( -- )
  build-composition drop open-index 20 infer 10 20 probe
  10 handle token 20 handle 50000 before-check lf-mixed-infer checked mix
  50000 before-check lf-mixed-convert checked mix ;
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
: due? ( -- flag )
  trial trial-every @ ?dup if trial trial-done @ swap mod 0= else false then ;
: step? ( -- more? )
  trial trial-left @ dup if -1 trial trial-left +! step then 0<> ;
\ A trial: job k's seed, steps and yield period, in the current context.
: trial-start ( k steps every -- )
  trial /trial erase trial trial-every ! trial trial-left ! 7919 * 1+ seed-cell !
  session ;
: trial-finish ( -- ) mix-terms mix-counts ;
: trial-run ( -- ) begin step? while due? if task-yield then repeat trial-finish ;
: digest ( -- x ) trial trial-hash @ ;
