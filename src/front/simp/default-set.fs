\ Simp's default set (simp group 4, step 4; plan
\ .claude/work/briefs/simp-group-4-architect.md sections 1 and 3): Lean
\ 4.35.0's getSimpTheorems and getSimprocs, the sets plain simp starts
\ from (src/lean/Lean/Elab/Tactic/Simp.lean:554-580), as format 4.1's
\ records give them (front/simp-set-data.fs), on two ranked-record
\ indexes each (front/data-index.fs).
\ - lf-simp-default ( -- ): simp/theorems.fs's set made the default set:
\   its pre and post trees indexes of the data's lemmas of each phase,
\   each root built at its first query, its values inserted in rank order
\   (so in Lean's stored order), each value a theorem record made then
\   (theorems.fs's lf-simp-data-entry); a rule added later (a bracket
\   lemma) forces its root first and goes in after the root's values, as
\   Lean inserts into the default set (Elab/Tactic/Simp.lean:434); the
\   definitions the set unfolds answer unsupported where reduceStep
\   would unfold them (simp/main.fs). Data without the default set
\   (simp-set-data.fs's simp-default?: another format, or 4.1 without
\   the simp_set record) is unsupported (a throw).
\ - The default simprocs, an index per phase over the data's simproc
\   entries, queried by getMatchWithExtra at simp's index configuration
\   (Simproc.lean:230, simprocCore): simp/main.fs's hook lf-simp-procs
\   ( e post? -- e' h step ) tries e's candidates in the index's order
\   (simp/simprocs.fs's lf-simproc-try: a port found by the record's
\   name, or its family's guard, which answers unsupported where Lean's
\   simproc may fire), the first step other than continue answering;
\   lf-simp-dprocs? ( e post? -- flag ), the dsimp guard's, is any
\   dsimproc candidate (dsimp is not ported). A set that is not the
\   default one has no simprocs.
\ A lemma the library lacks (simp_left_out) answers unsupported when the
\ rewrite reaches it in candidate order, and each data lemma's keys are
\ recomputed when it is first tried (theorems.fs's lf-simp-thm-usable).
\ Throws as meta-must.fs's words do. Untrusted: a lemma only proposes a
\ rewrite the kernel checks. State: the context records ds-proc-pre and
\ ds-proc-post (the simproc indexes, made anew by each lf-simp-default)
\ and the slab ds-out (the queries' candidates, each query's above the
\ one it runs inside; emptied by each lf-simp-default).
\ Loads in decimal whatever BASE is, then restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../../lib/lib.fs
require ../../lib/slab.fs
require ../../lib/context.fs
require ../data-index.fs
require ../simp-set-data.fs
require ../meta-config.fs
require ./theorems.fs
require ./main.fs
require ./simprocs.fs
require ./simprocs/core.fs
require ./simprocs/nat.fs

\ ---- The kinds' values: an index's list of the data (simp-set-data.fs's
\ simp-value), a tree's lemmas or a phase's simprocs.
/rix context-record: ds-proc-pre
/rix context-record: ds-proc-post
: ds-list ( rix -- post procs? )
  dup lf-simp-post-tree = over ds-proc-post = or
  swap dup ds-proc-pre = swap ds-proc-post = or ;
: ds-count ( rix -- n ) ds-list simp-values# ;
: ds-value ( k rix -- v ) ds-list simp-value ;
: ds-ok ( rix -- outcome ) drop outcome-ok ;
\ The lemma trees' kind: the theorem record made for each value when its
\ root is built; the checks run per lemma when it is tried.
' ds-count ' ds-value ' simp-lemma-count ' simp-lemma-keys ' simp-lemma-rank ' ds-ok
  ' lf-simp-data-entry rix-kind, constant ds-kind
\ The simprocs' kind: the tree holds each entry's number.
: ds-self ( p -- p outcome ) outcome-ok ;
' ds-count ' ds-value ' simp-proc-count ' simp-proc-keys ' simp-proc-rank
  ' ds-ok ' ds-self rix-kind, constant ds-proc-kind
1 cells context-slab: ds-out
:noname ( -- ) ds-proc-pre lf-rix-free ds-proc-post lf-rix-free ; context-teardown
: ds-procs-new ( -- )
  ds-proc-pre lf-rix-free ds-proc-post lf-rix-free
  ds-proc-kind ds-proc-pre lf-rix-kind! ds-proc-kind ds-proc-post lf-rix-kind! ;

: lf-simp-default ( -- )
  simp-default? 0= if lf-unported then ds-out slab-clear
  lf-simp-set-new ds-kind ds-kind lf-simp-set-data! ds-procs-new ;

\ ---- simprocCore (Simproc.lean:230; simprocArrayCore, 300, of the one
\ set): e's candidates in its phase, getMatchWithExtra's (p, extra)
\ pairs above base in ds-out, read by index (a port's nested walk asks
\ again above them), each tried (simprocs.fs's lf-simproc-try) until
\ one answers other than continue; ds-out cut back to base after.
: ds-procs ( post? -- rix ) if ds-proc-post else ds-proc-pre then ;
: ds-query ( e rix -- ) ds-out lf-rix-match lf-must ;
: ds-cands ( e post? -- e base n )
  over ds-out slab-count >r swap ds-procs ['] ds-query lf-with-simp-index
  r> dup ds-out slab-since 2/ ;
: ds-pair ( base k -- p extra ) 2* + ds-out slab-at 2@ swap ;
: ds-cand? ( e base e0 h0 step0 k -- e base e' h step flag )
  >r 2drop drop 2dup r> ds-pair lf-simproc-try dup lf-simp-continue <> ;
: ds-first ( e base n -- e' h step )
  >r over lf-simp-pass r> ['] ds-cand? any? drop >r 2swap ds-out slab-cut drop r> ;
: ds-procs-of ( e post? -- e' h step ) ds-cands ds-first ;
: ds-procs-run ( e post? -- e' h step )
  lf-simp-default? if ds-procs-of else drop lf-simp-pass then ;
' ds-procs-run is lf-simp-procs
\ dsimp's question (the dsimp guard, simp/main.fs): a dsimproc candidate.
: ds-dsimproc? ( e base k -- e base flag ) over swap ds-pair drop simp-proc-dsimproc? ;
: ds-dprocs? ( e post? -- flag )
  ds-cands ['] ds-dsimproc? any? -rot ds-out slab-cut drop ;
: ds-dprocs-run ( e post? -- flag ) lf-simp-default? if ds-dprocs? else 2drop false then ;
' ds-dprocs-run is lf-simp-dprocs?

base !   \ the BASE this file was loaded with
