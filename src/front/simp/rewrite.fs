\ Simp's rewriting with its theorems (plan row FE9, simp slice SL1a-1 of
\ docs/design/TACTIC_SIMP.md): Lean 4.35.0's rewrite? with the index
\ (src/lean/Lean/Meta/Tactic/Simp/Rewrite.lean:207-240),
\ tryTheoremWithExtraArgs? (178) and tryTheoremCore (115).
\ - lf-simp-rewrite? ( e tree rfl-only -- e' h true | false ): the
\   candidates of getMatchWithExtra (discr-tree.fs's lf-dt-get-match-extra
\   at mkIndexConfig, lf-with-simp-index) sorted by priority, highest
\   first, stably (lib/sort.fs, Lean's insertionSort); with rfl-only those
\   without the rfl flag passed over; the first that rewrites e answers.
\   A theorem is tried one metavariable depth deeper (lf-with-new-depth):
\   its value (a declaration's constant at fresh level metavariables,
\   SimpTheorem.getValue 475; a hypothesis itself), its type's
\   forallMetaTelescopeReducing, whnf of the body (reducible, simp's
\   transparency), its left side unified with e less its extra arguments
\   at mkMetaConfig (lf-with-simp-meta); then synthesizeArgs (58,
\   lf-simp-synthesize): a metavariable left unassigned whose type is a
\   class gets the instance trySynthInstance finds (synth.fs's
\   lf-try-synth) when isDefEq at reducible and instances transparency
\   agrees; one whose type is a proposition needs the discharger (slice
\   SL2, not ported: unsupported); the proof none for an rfl theorem
\   (implicitDefEqProofs),
\   else the value applied to the metavariables, refused (none) when it
\   holds an assignable metavariable (hasAssignableMVar,
\   app-builder.fs's lf-meta-has-assignable?); the result refused when
\   it equals e (Lean's ==, term-eqv.fs); a type with binderNameHint
\   unsupported (resolveBinderNameHint, 152); the result refused when it
\   holds an assignable metavariable; then addExtraArgs
\   (simp/types.fs's lf-simp-extra-args).
\ - lf-simp-rfl-match? ( e tree -- flag ): whether a theorem with the rfl
\   flag is among e's candidates (the dsimp guard of simp/main.fs).
\ - lf-simp-synthesize ( first n slab -- flag ): synthesizeArgs of the n
\   metavariables in the cells of slab from cell first (also
\   simp/congr.fs's, for a congruence lemma): false when one is left that
\   the discharger did not prove. Each cell is read when its turn comes,
\   so the slab may grow while it runs (a discharger's nested simp).
\ - lf-simp-discharge ( x type -- flag ): the discharger's hook
\   (Methods.discharge?, Rewrite.lean:637): a proof of the proposition
\   type assigned to the metavariable x, true; false when it finds none.
\   Until the discharger is ported (slice SL2) it answers unsupported.
\ Re-entrant: each call keeps a frame of its own (srt, the newest of the
\ slab sr-frames), and its candidates and its theorem's metavariables
\ above the bases its frame records in sr-cands and sr-xs, read by
\ index, never by an address held across a step that may run simp again
\ (a discharger's nested simp, simp/main.fs's lf-simp-nested), and cut
\ back to those bases when it returns. lf-simp-rewrite-reset ( -- )
\ forgets every frame (simp/main.fs: at a run's start, after a throw).
\ Throws as meta-must.fs's words do. Untrusted: a rewrite's proof is
\ checked by the kernel. State: the context slabs sr-frames (a frame per
\ call in progress), sr-cands (the candidates, pairs) and sr-xs (the
\ telescopes' metavariables), and the sorter sr-sort (one sort's).
\ Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/slab.fs
require ../../lib/sort.fs
require ../../lib/context.fs
require ../../core/terms.fs
require ../instances.fs
require ./types.fs
require ./theorems.fs

1 cells context-slab: sr-cands   \ (theorem, extra arguments) pairs
1 cells context-slab: sr-xs      \ the theorems' metavariables, in order
/sorter context-record: sr-sort
begin-structure /srt
  field: srt-e   field: srt-n   field: srt-thm   field: srt-app   field: srt-type
  field: srt-cands   \ the call's first cell in sr-cands
  field: srt-xs      \ its theorem's first metavariable's cell in sr-xs
end-structure
/srt context-slab: sr-frames
: srt ( -- addr ) sr-frames slab-last ;
: lf-simp-rewrite-reset ( -- ) sr-frames sr-cands sr-xs 3 slabs-clear ;
\ A call's frame, its bases the slabs' counts; given back with what the
\ call put above them.
: sr-push ( -- )
  1 sr-frames slab-claim lf-must drop srt /srt erase
  sr-cands slab-count srt srt-cands !  sr-xs slab-count srt srt-xs ! ;
: sr-pop ( -- )
  srt srt-xs @ sr-xs slab-cut  srt srt-cands @ sr-cands slab-cut  sr-frames slab-drop ;

\ ---- The candidates, highest priority first.
: sr-query ( e tree -- ) sr-cands lf-dt-get-match-extra ;
: sr-prio ( a-addr -- p ) @ lf-simp-thm-prio negate ;   \ ascending: highest first
: sr-cands# ( -- n ) srt srt-cands @ sr-cands slab-since 2/ ;
: sr-sorted ( -- )
  2 cells ['] sort-signed sr-sort sorter-init lf-must ['] sr-prio sr-sort sorter-key!
  srt srt-cands @ sr-cands slab-at sr-cands# sr-sort sort-records lf-must ;
: sr-cands-of ( e tree -- n ) ['] sr-query lf-with-simp-index sr-sorted sr-cands# ;
: sr-pair ( i -- thm extra ) 2* srt srt-cands @ + sr-cands slab-at 2@ swap ;

\ ---- tryTheoremCore's term: e less its extra arguments, and those.
: srt-e@ ( -- e ) srt srt-e @ ;   : srt-n@ ( -- n ) srt srt-n @ ;
: sr-extras ( h e' -- e'' h' ) swap srt-e@ srt-n@ 2swap lf-simp-extra-args ;

\ ---- getValue and the telescope.
: sr-mvar ( app mvar kind -- app' ) drop dup sr-xs slab-push lf-must lf-mk-app ;
: sr-value ( t -- val d ) dup lf-simp-thm-proof swap lf-simp-thm-decl?
  if dup lf-meta-const-fresh lf-must swap else -1 then ;
: sr-keep ( app type -- ) lf-instantiate! lf-whnf-r! srt srt-type ! srt srt-app ! ;
: sr-open ( t -- )
  srt srt-xs @ sr-xs slab-cut sr-value >r dup lf-infer! r> ['] sr-mvar
  lf-forall-meta-telescope-reducing sr-keep ;
: sr-sides ( -- lhs rhs ) srt srt-type @ lf-simp-sides ;
: sr-e0 ( -- e ) srt-e@ srt-n@ lf-term-fns ;
: sr-unifies? ( -- flag ) sr-sides drop sr-e0 ['] lf-defeq! lf-with-simp-meta ;

\ ---- synthesizeArgs (58, with tactic.skipAssignedInstances's default):
\ an unassigned argument of a class (isClass?, instances.fs's lf-class?)
\ or of a proposition.
: sr-open? ( x -- flag ) lf-instantiate! lf-mvar? ;
: sr-class? ( type -- flag ) lf-class? lf-must dup if nip then ;
\ synthesizeInstance: trySynthInstance's instance, assigned when isDefEq
\ at reducible and instances transparency agrees.
: sr-instance? ( x type -- flag )
  lf-try-synth lf-must lf-synth-some =
  if ['] lf-defeq! lf-tr-instances lf-meta-at else 2drop false then ;
\ The discharger (Methods.discharge?): until slice SL2 unsupported.
defer lf-simp-discharge ( x type -- flag )
:noname ( x type -- flag ) 2drop lf-unported false ; is lf-simp-discharge
\ One metavariable: an instance found for a class; a proposition left to
\ the discharger, whose failure fails the theorem (false).
: sr-arg ( x -- flag )
  true swap dup sr-open? 0= if drop exit then
  dup lf-infer! dup sr-class? if 2dup sr-instance? if 2drop exit then then
  dup lf-is-prop! if rot drop lf-simp-discharge else 2drop then ;
: sr-arg-at ( slab i -- slab flag ) over slab-at @ sr-arg ;
: lf-simp-synthesize ( first n slab -- flag )
  -rot bounds ?do i sr-arg-at 0= if drop false unloop exit then loop drop true ;
: sr-synthesize ( -- flag ) srt srt-xs @ dup sr-xs slab-since sr-xs lf-simp-synthesize ;

\ ---- tryTheoremCore's go: the rewrite, or none.
: sr-rfl? ( -- flag ) srt srt-thm @ lf-simp-thm-rfl? ;
: sr-proof ( -- h true | false )
  sr-rfl? if lf-simp-none true exit then
  srt srt-app @ lf-instantiate! dup lf-meta-has-assignable? if drop false else true then ;
: sr-hint-node? ( node -- flag ) s" binderNameHint" lf-meta-const-named? ;
: sr-hint? ( type -- flag ) ['] sr-hint-node? lf-term-holds-node? lf-must ;
: sr-rhs ( -- rhs ) sr-sides nip lf-instantiate! ;
: sr-same? ( rhs -- flag ) sr-e0 lf-instantiate! lf-eqv! ;
: sr-result ( h -- e' h true | false )
  sr-rhs dup sr-same? if 2drop false exit then
  srt srt-type @ sr-hint? if lf-unported then
  dup lf-meta-has-assignable? if 2drop false exit then sr-extras true ;
: sr-go ( t -- e' h true | false )
  sr-open sr-unifies? 0= if false exit then
  sr-synthesize 0= if false exit then sr-proof dup if drop sr-result then ;
: sr-try ( e t n -- e' h true | false )
  srt srt-n ! dup srt srt-thm ! swap srt srt-e ! ['] sr-go lf-with-new-depth ;

: sr-skip? ( rfl-only t -- flag ) lf-simp-thm-rfl? 0= and ;
\ A candidate passed over (rfl-only), else checked before it is tried
\ (theorems.fs's lf-simp-thm-usable: one the library lacks unsupported).
: sr-candidate ( e rfl-only i -- e rfl-only e' h true | e rfl-only false )
  sr-pair >r 2dup sr-skip? if r> 2drop false exit then
  dup lf-simp-thm-usable >r over r> r> sr-try ;
: sr-first ( e rfl-only n -- e' h true | false )
  0 ?do i sr-candidate if 2swap 2drop true unloop exit then loop 2drop false ;
: sr-rewrite ( e tree rfl-only -- e' h true | false )
  >r over swap sr-cands-of r> swap sr-first ;
\ The call's frame given back on either answer.
: sr-popped ( x1 x2 true -- x1 x2 true | false -- false )
  dup if >r 2>r sr-pop 2r> r> else sr-pop then ;
: lf-simp-rewrite? ( e tree rfl-only -- e' h true | false ) sr-push sr-rewrite sr-popped ;
: sr-rfl-at? ( i -- flag ) sr-pair drop lf-simp-thm-rfl? ;
: sr-rfl-any? ( e tree -- flag ) sr-cands-of false swap 0 ?do i sr-rfl-at? or loop ;
: lf-simp-rfl-match? ( e tree -- flag ) sr-push sr-rfl-any? sr-pop ;

base !   \ the BASE this file was loaded with
