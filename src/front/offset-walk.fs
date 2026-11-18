\ Memoised rebuild walks over (node, depth) pairs of the front end's terms
\ (plan FE1c; review F2 of 2026-11-18): the walk of Lean 4.35.0's
\ replace with an offset (kernel/replace_fn.cpp's replace_rec_fn, its
\ cache keyed by the node and the offset), which instantiate1, abstract
\ (front/instantiate.fs) and instantiateBetaRevRange (front/beta-inst.fs)
\ share. Each (node, depth) pair reached gets an image once: a pair the
\ walk's kept test passes is its own image; a binary node's image is the
\ node over its parts' images, the second one depth + 1 deeper under a
\ binder (lf-meta-rebuilt: the same node when its parts stay, a rebuilt
\ binder keeping its name and kind); an annotation's is the annotation
\ over its child's image under its key (lf-meta-annot-over, Lean's
\ preserved mdata); a leaf's is the walk's leaf image. A walk's own case,
\ tried before those, may handle a pair itself (beta-inst.fs's head beta).
\ The pending pairs are on a heap stack and the images in a memo
\ (lib/memo.fs), so a DAG costs its size and no depth needs the host's
\ stacks (plan task 6.2.0).
\ - ow-kind ( kept-xt leaf-xt own-xt -- kind ) lays down a kind (a
\   read-only table, kept as a constant): a walk's three words, kept
\   ( node depth -- flag ), leaf ( node depth -- image ) and own
\   ( node depth -- node depth false | true ).
\ - ow-run ( body kind w -- term outcome ): body's image at depth 0, made
\   with the walk record w (/ow, a member of the checker context, emptied
\   first); ok, or the walk's first failure with -1. Runs nest: a hook may
\   run another walk with another record.
\ - ow-free ( w -- ): the record's heap blocks given back (its teardown).
\ - lf-meta-rebuilt ( f s e -- e' outcome ): the binary node e over the
\   parts f and s: e itself when they are its own (Lean's updateApp!,
\   updateLambdaE! and updateForallE! keep e when the parts are
\   pointer-equal), else a node of e's tag whose binder keeps e's name and
\   kind (meta-spine.fs's lf-meta-named); full, with -1, when the term
\   store has no room. Also kabstract.fs's and mvars.fs's rebuild.
\ - lf-meta-annot-over ( image a -- t outcome ): the annotation a over the
\   child image: a itself when image is its child (Lean's updateMData!),
\   else a new annotation with a's key; full, with -1, as above.
\ - Inside a run (hooks and the words they call): ow-fail ( outcome -- )
\   ends the walk with the outcome (the first one stays; ok changes
\   nothing), ow-image ( node depth -- image ) gives a pair's image made
\   already, ow-push-if ( node depth -- pushed? ) puts a pair whose image
\   is not made yet on the stack, ow-done ( node depth image -- ) keeps a
\   pair's image and takes it off the stack, ow-first and ow-second
\   ( node depth -- child depth' ) give a binary node's parts.
\ Outcomes: ok; full when the memo, the stack or a store has no room; a
\ hook's failure. Untrusted.
\ State: ow-current, the record of the run under way (a member of the
\ checker context), set by ow-run and put back when it returns; every
\ record's memo and stack are made at its first run.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/slab.fs
require ../lib/memo.fs
require ../core/terms.fs
require ../core/annotations.fs
require ./meta-spine.fs

begin-structure /ow
  field: ow-words          \ the walk's words (ow-kind)
  field: ow-outcome        \ ok, or the walk's first failure
  /slab +field ow-stack    \ the pending pairs: node depth
  /memo +field ow-memo     \ (node depth) to its image
end-structure
1 cells context-record: ow-current
\ A kind, laid down from its last word: own, leaf, kept.
begin-structure /owk
  field: owk-own
  field: owk-leaf
  field: owk-kept
end-structure

: ow-kind ( kept-xt leaf-xt own-xt -- kind ) align here >r , , , r> ;
: ow ( -- w ) ow-current @ ;
: ow-fail ( outcome -- ) ow ow-outcome outcome-first! ;
: ow-hooks ( -- kind ) ow ow-words @ ;

\ Rebuilding a node over its parts' images.
: ow-parts ( e -- f s ) dup lf-term-first@ swap lf-term-second@ ;
: ow-binary ( f s e -- e' outcome )
  >r r@ lf-term-tag@ lf-term-binary if r> lf-meta-named exit then
  r> drop outcome-full no-result ;
: lf-meta-rebuilt ( f s e -- e' outcome )
  >r 2dup r@ ow-parts d= if 2drop r> outcome-ok else r> ow-binary then ;
: lf-meta-annot-over ( image a -- t outcome )
  2dup lf-annot-child = if nip outcome-ok exit then lf-annot-key lf-annot ;

\ Images: the pair itself when kept, else the memo's.
: ow-image? ( node depth -- image true | false )
  2dup ow-hooks owk-kept @ execute if drop true exit then ow ow-memo memo@ ;
: ow-ready? ( node depth -- flag ) ow-image? dup if nip then ;
: ow-image ( node depth -- image ) ow-image? drop ;
: ow-keep ( node depth image -- outcome ) -rot ow ow-memo memo! ;

\ The stack.
: ow-top ( -- node depth ) ow ow-stack slab-last 2@ ;
: ow-pop ( -- ) ow ow-stack slab-drop ;
: ow-push ( node depth -- ) ow ow-stack slab-2push ow-fail ;
: ow-push-if ( node depth -- pushed? )
  2dup ow-ready? if 2drop false else ow-push true then ;
: ow-done ( node depth image -- ) ow-keep ow-fail ow-pop ;

\ Binary nodes and annotations.
: ow-first ( node depth -- child depth ) swap lf-term-first@ swap ;
: ow-second ( node depth -- child depth' )
  over lf-term-binder? - swap lf-term-second@ swap ;
: ow-images ( node depth -- i1 i2 ) 2dup ow-second ow-image >r ow-first ow-image r> ;
: ow-pair-image ( node depth -- image ) over swap ow-images rot lf-meta-rebuilt ow-fail ;
: ow-annot-image ( node depth -- image )
  over lf-annot-child swap ow-image swap lf-meta-annot-over ow-fail ;
: ow-step-pair ( node depth -- )
  2dup ow-first ow-push-if if 2drop exit then
  2dup ow-second ow-push-if if 2drop exit then 2dup ow-pair-image ow-done ;
: ow-step-annot ( node depth -- )
  2dup ow-first ow-push-if if 2drop exit then 2dup ow-annot-image ow-done ;
: ow-step-leaf ( node depth -- ) 2dup ow-hooks owk-leaf @ execute ow-done ;

\ One step on the top pair: done already, the walk's own case, a child
\ first, or made.
: ow-step ( -- )
  ow-top 2dup ow-ready? if 2drop ow-pop exit then
  ow-hooks owk-own @ execute if exit then
  over lf-term-binary? if ow-step-pair exit then
  over lf-annot? if ow-step-annot else ow-step-leaf then ;
: ow-busy? ( -- flag ) ow ow-stack slab-count 0> ow ow-outcome @ ok? and ;
: ow-loop ( body -- term outcome )
  dup 0 ow-push begin ow-busy? while ow-step repeat
  ow ow-outcome @ dup ok? if drop 0 ow-image outcome-ok else nip no-result then ;

\ The record's stack: made at its first run, emptied at the next; its
\ memo: made afresh for each run (as the hash table it replaced, so that
\ a run's first heap request is still its table's).
: ow-stack-make ( slab -- outcome ) 2 cells dup slab-limit-max rot slab-init ;
: ow-stack-ready ( slab -- outcome )
  dup slab-live? if slab-clear outcome-ok else ow-stack-make then ;
: ow-memo-make ( memo -- outcome ) dup memo-free 2 1 rot memo-init ;
: ow-start ( kind w -- outcome )
  tuck ow-words ! outcome-ok over ow-outcome !
  dup ow-stack ow-stack-ready swap ow-memo ow-memo-make outcome-and ;
: ow-go ( body kind w -- term outcome ) ow-start ['] ow-loop ok-and ok-or-none ;
: ow-run ( body kind w -- term outcome )
  ow-current @ >r dup ow-current ! ow-go r> ow-current ! ;
: ow-free ( w -- ) dup ow-memo memo-free ow-stack slab-free ;

base !   \ the BASE this file was loaded with
