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
\   (Simproc.lean:230, simprocCore): until the simprocs are ported (group
\   4, pass 2), any candidate of a term at its pre or post step, or of a
\   node the dsimp guard would keep, answers unsupported (simp/main.fs's
\   hook lf-simp-procs), never "continue": a simproc that would fire is
\   never skipped. A set that is not the default one has no simprocs.
\ A lemma the library lacks (simp_left_out) answers unsupported when the
\ rewrite reaches it in candidate order, and each data lemma's keys are
\ recomputed when it is first tried (theorems.fs's lf-simp-thm-usable).
\ Throws as meta-must.fs's words do. Untrusted: a lemma only proposes a
\ rewrite the kernel checks. State: the context records ds-proc-pre and
\ ds-proc-post (the simproc indexes, made anew by each lf-simp-default)
\ and the slab ds-out (a query's candidates).
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
  simp-default? 0= if lf-unported then
  lf-simp-set-new ds-kind ds-kind lf-simp-set-data! ds-procs-new ;

\ ---- The guard: a simproc candidate of e in its phase, unsupported.
: ds-procs ( post? -- rix ) if ds-proc-post else ds-proc-pre then ;
: ds-query ( e rix -- ) ds-out lf-rix-match lf-must ;
: ds-any? ( e post? -- flag )
  ds-out slab-clear ds-procs ['] ds-query lf-with-simp-index ds-out slab-count 0> ;
: ds-guard ( e post? -- )
  lf-simp-default? 0= if 2drop exit then ds-any? if lf-unported then ;
' ds-guard is lf-simp-procs

base !   \ the BASE this file was loaded with
