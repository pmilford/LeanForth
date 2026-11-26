\ n by-iterate tacs by-end: Lean's iterate n tacs (plan row TB2, small
\ tactics 1), a port of the macro of Lean 4.35.0's src/lean/Init/
\ TacticsExtra.lean:69-75: iterate 0 tacs is skip, iterate (n+1) tacs is
\ (tacs); iterate n tacs, so the block's tactics run n times over, in
\ the block around it (a paren: no focus, no save, recover kept; names
\ given inside it stay), and the first error is the step's, as Lean's.
\ n is a numeral (Lean's num literal; any other value is not supported,
\ 99: Lean's parser wants one). iterate with no count (try (tacs);
\ iterate tacs, until Lean's recursion depth runs out) has no form.
\ The recursion depth (Forth review of small-tactics-1, finding 2, and
\ its re-check, finding 1): the macro nests one expansion per pass, so
\ Lean refuses a large count with "maximum recursion depth has been
\ reached" (maxRecDepth 512). Measured on pinned Lean (2026-11-26):
\ iterate 251 skip passes, 252 fails; two nested, counts summing to 250
\ pass, 251 fail; 101 nested iterate 1 pass, 102 fail: about 2n + 3
\ levels per open iterate of count n. So an iterate's frame weighs n + 2
\ units of two levels (tit-weight) in the runner's one bound over every
\ open block (tactic-run.fs's lf-tac-depth-most, checked whenever a
\ block opens, the blocks around an iterate and inside it included): an
\ iterate alone is supported up to a count of 234, where Lean accepts
\ up to 251.
\ The block is a mode of the runner (tactic-run.fs's lf-block-mode): its
\ open reads n, keeps it as the frame's passes left (tfr-passes) and
\ skips the steps when it is 0; each end counts one pass down and starts
\ the steps again (lf-tac-again) while passes are left.
\ Lean call list: the macro's expansion -> the mode tit-mode; skip ->
\ lfr-skip; the steps again -> lf-tac-again; maxRecDepth -> the mode's
\ weight, tit-weight.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own (the passes left are the frame's).

require ../tactic-api.fs

\ ---- The count: the step's value, a numeral (never negative: the
\ reader's lfn>syntax).
: tit-num? ( node -- n true | false )
  dup syn-kind@ syn-k-num = if syn-a@ true else drop false then ;
: tit-num ( node -- n ) tit-num? 0= if lf-tac-unported then ;
: tit-arg ( frame -- node ) tfr-step @ 0 lf-tac-arg ;
: tit-count ( frame -- n ) tit-arg tit-num ;

\ ---- The weight: its count (at most the bound, so that the sum cannot
\ wrap) and 2; a count that is no numeral weighs nothing here, as the
\ open refuses it (99).
: tit-weight ( frame -- w )
  tit-arg tit-num? if lf-tac-depth-most min 2 + else 0 then ;

\ ---- The mode: n passes, none when n is 0.
: tit-open ( frame -- )
  dup tit-count 2dup swap tfr-passes ! 0= if lfr-skip else drop then ;
: tit-left ( frame -- frame n ) dup tfr-passes @ 1- 0 max 2dup swap tfr-passes ! ;
: tit-end ( frame -- ) tit-left if lf-tac-again else drop then ;
' tit-open ' tit-end 0 0 lf-block-mode constant tit-mode
' tit-weight tit-mode lf-mode-weight!

1 0 0 tac-shape-block lf-tactic: by-iterate constant tac-k-iterate
s" iterate" tac-k-iterate lf-tactic-lean!
' lf-tac-all tac-k-iterate lf-tactic-action!
tit-mode tac-k-iterate lf-tactic-mode!
