\ Substitutions of free variables of the tactic library (plan row TB2,
\ piece E, slice E1; docs/design/TACTIC_PATTERNS.md section 4): Lean
\ 4.35.0's Meta/Tactic/FVarSubst.lean, which old free variable became
\ which term, as Meta's induction and cases report it and rcases applies
\ it to every target still to match (Elab/Tactic/RCases.lean:276). Each
\ word throws on failure (meta-must.fs), as Lean's do.
\ A substitution is a run (lib/runs.fs) of pairs, each a run of two cells
\ (a free variable and its term), oldest first; 0 is the empty one
\ (FVarSubst.empty). Its keys are unique (insert keeps the first) and no
\ term holds a key put in after it (insert replaces the new key in the
\ terms before it), so replacing the keys one by one, oldest first, is
\ Lean's single replace walk.
\ Public words:
\   lf-replace-fvar ( e fvar v -- e' )  Expr.replaceFVar: e.abstract
\       #[fvar], then instantiate1 v (instantiate.fs)
\   lf-fsubst-get ( fs fvar -- e )  get: fvar's term, else fvar itself
\   lf-fsubst-insert ( fs fvar e -- fs' )  insert: fs itself when it maps
\       fvar already; else each of its terms with fvar replaced by e, then
\       the pair fvar e last
\   lf-fsubst-erase ( fs fvar -- fs' )  erase: every pair but fvar's
\   lf-fsubst-apply ( fs e -- e' )  apply: each key in e replaced by its
\       term (the empty substitution gives e)
\   lf-fsubst-append ( fs1 fs2 -- fs )  append (fs1 then fs2, so that
\       applying the result is applying fs1, then fs2): fs2, then each
\       pair k v of fs1, newest first as Lean's AssocList folds, inserted
\       as k and fs2 applied to v
\   lf-fsubst-pair ( fvar e -- pair )  a pair (the run of two cells)
\ Example: 0 x a lf-fsubst-insert  y b lf-fsubst-insert  x c
\   lf-fsubst-insert gives [x a] [y b]; applied to f x y it gives f a b.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: fsi-frames (insert's and erase's frames, one per call open,
\ meta-must.fs's lf-with-record) and frp-cells (replaceFVar's one cell,
\ lf-with-cells), in the checker context (ADR 0009); no other. Loads in
\ decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../lib/runs.fs
require ../lib/bounds.fs
require ../lib/slab.fs
require ../lib/find.fs
require ../lib/context.fs
require ./instantiate.fs
require ./meta-must.fs

\ ---- replaceFVar: the free variable in a cell of its own, the array of
\ one that lf-meta-abstract reads.
1 cells context-slab: frp-cells
: frp-at ( e v fvar addr -- e' )
  tuck ! rot swap 1 lf-meta-abstract lf-must swap lf-meta-instantiate1 lf-must ;
: lf-replace-fvar ( e fvar v -- e' ) swap 1 frp-cells ['] frp-at lf-with-cells ;

\ ---- Pairs, and finding a key.
: lf-fsubst-pair ( fvar e -- pair ) 0 rot lf-run+ swap lf-run+ ;
: fsb-key ( pair -- fvar ) 0 run@ ;
: fsb-val ( pair -- e ) 1 run@ ;
: fsb-is? ( fs fvar k -- fs fvar flag ) >r over r> run@ fsb-key over = ;
: fsb-index ( fs fvar -- fs k true | fs false ) over run-count ['] fsb-is? find-index ;
: lf-fsubst-get ( fs fvar -- e ) tuck fsb-index if run@ fsb-val nip else drop then ;

\ ---- apply: each pair in turn, oldest first.
: fsb-step ( e pair -- e' outcome ) dup fsb-key swap fsb-val lf-replace-fvar outcome-ok ;
: lf-fsubst-apply ( fs e -- e' ) swap ['] fsb-step run-each lf-must ;

\ ---- insert, erase and append: a frame per call (lf-with-record).
begin-structure /fsi
  field: fsi-key         \ the free variable (insert's, erase's)
  field: fsi-val         \ its term (insert's)
  field: fsi-fs1         \ append's first substitution
  field: fsi-fs2         \ and its second
end-structure
/fsi context-slab: fsi-frames
: fsi ( -- frame ) fsi-frames slab-last ;
: fsi-pair ( -- pair ) fsi fsi-key @ fsi fsi-val @ lf-fsubst-pair ;
: fsi-mapped ( out pair -- out' outcome )
  dup fsb-key swap fsb-val fsi fsi-key @ fsi fsi-val @ lf-replace-fvar lf-fsubst-pair
  lf-run+ outcome-ok ;
: fsi-new ( fs -- fs' ) 0 swap ['] fsi-mapped run-each lf-must fsi-pair lf-run+ ;
: fsi-run ( fs -- fs' ) dup fsi fsi-key @ fsb-index if 2drop exit then drop fsi-new ;
: fsi-framed ( fs fvar e -- fs' ) fsi fsi-key cell-pair! fsi-run ;
: lf-fsubst-insert ( fs fvar e -- fs' ) fsi-frames ['] fsi-framed lf-with-record ;
: fsi-other? ( pair -- flag ) fsb-key fsi fsi-key @ <> ;
: fse-framed ( fs fvar -- fs' ) fsi fsi-key ! ['] fsi-other? run-filter lf-must ;
: lf-fsubst-erase ( fs fvar -- fs' ) fsi-frames ['] fse-framed lf-with-record ;
\ append: fs2, then fs1's pairs inserted newest first, each term through fs2.
: fsa-step ( acc pair -- acc' )
  dup fsb-key swap fsb-val fsi fsi-fs2 @ swap lf-fsubst-apply lf-fsubst-insert ;
: fsa-at ( acc k -- acc' ) fsi fsi-fs1 @ swap run@ fsa-step ;
: fsa-framed ( fs1 fs2 -- fs )
  dup fsi fsi-fs2 ! swap dup fsi fsi-fs1 ! run-count
  begin ?dup while 1- tuck fsa-at swap repeat ;
: lf-fsubst-append ( fs1 fs2 -- fs ) fsi-frames ['] fsa-framed lf-with-record ;
base !   \ the BASE this file was loaded with
