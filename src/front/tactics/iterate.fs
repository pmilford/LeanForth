\ n by-iterate tacs by-end: Lean's iterate n tacs (plan row TB2, small
\ tactics 1), a port of the macro of Lean 4.35.0's src/lean/Init/
\ TacticsExtra.lean:69-75: iterate 0 tacs is skip, iterate (n+1) tacs is
\ (tacs); iterate n tacs, so the block's tactics run n times over, in
\ the block around it (a paren: no focus, no save, recover kept; names
\ given inside it stay), and the first error is the step's, as Lean's.
\ n is a numeral (Lean's num literal; any other value is not supported,
\ 99: Lean's parser wants one). iterate with no count (try (tacs);
\ iterate tacs, until Lean's recursion depth runs out) has no form.
\ The block is a mode of the runner (tactic-run.fs's lf-block-mode): its
\ open reads n, keeps it in the frame's tfr-at (a per-goal block's place,
\ which no other use of an iterate frame reads) and skips the steps when
\ it is 0; each end counts one pass down and starts the steps again
\ (lf-tac-again) while passes are left.
\ Lean call list: the macro's expansion -> the mode tit-mode; skip ->
\ lfr-skip; the steps again -> lf-tac-again.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own (the passes left are the frame's).

require ../tactic-api.fs

\ ---- The count: the step's value, a numeral.
: tit-num ( node -- n )
  dup syn-kind@ syn-k-num = if syn-a@ exit then drop lf-tac-unported ;
: tit-count ( frame -- n ) tfr-step @ 0 lf-tac-arg tit-num ;

\ ---- The mode: n passes, none when n is 0.
: tit-open ( frame -- ) dup tit-count 2dup swap tfr-at ! 0= if lfr-skip else drop then ;
: tit-left ( frame -- frame n ) dup tfr-at @ 1- 0 max 2dup swap tfr-at ! ;
: tit-end ( frame -- ) tit-left if lf-tac-again else drop then ;
' tit-open ' tit-end 0 0 lf-block-mode constant tit-mode

1 0 0 tac-shape-block lf-tactic: by-iterate constant tac-k-iterate
s" iterate" tac-k-iterate lf-tactic-lean!
' lf-tac-all tac-k-iterate lf-tactic-action!
tit-mode tac-k-iterate lf-tactic-mode!
