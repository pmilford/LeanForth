\ n by-iterate tacs by-end: Lean's iterate n tacs (plan row TB2, small
\ tactics 1), a port of the macro of Lean 4.35.0's src/lean/Init/
\ TacticsExtra.lean:69-75: iterate 0 tacs is skip, iterate (n+1) tacs is
\ (tacs); iterate n tacs, so the block's tactics run n times over, in
\ the block around it (a paren: no focus, no save, recover kept; names
\ given inside it stay), and the first error is the step's, as Lean's.
\ n is a numeral (Lean's num literal; any other value is not supported,
\ 99: Lean's parser wants one). iterate with no count (try (tacs);
\ iterate tacs, until Lean's recursion depth runs out) has no form.
\ The recursion depth (Forth review of small-tactics-1, finding 2): the
\ macro nests one expansion per pass, so Lean refuses a large count with
\ "maximum recursion depth has been reached" (maxRecDepth 512). Measured
\ on pinned Lean (2026-11-26): iterate 251 skip passes, 252 fails; two
\ nested, counts summing to 250 pass (1 and 249, 249 and 1, 125 and
\ 125), 251 fail (1 and 250); three, 248 pass (1, 1, 246), 249 fail;
\ 101 nested iterate 1 pass, 102 fail: about 2n + 3 levels per open
\ iterate of count n, and 6. So each open iterate weighs its count and 2,
\ and an iterate that would make the open ones weigh more than tit-most
\ (128, under half the measured limit, which leaves room for the blocks
\ around) is not supported yet (99) when it opens, where Lean may still
\ accept it (a count up to 251).
\ The block is a mode of the runner (tactic-run.fs's lf-block-mode): its
\ open checks the weight, reads n, keeps it as the frame's passes left
\ (tfr-passes) and skips the steps when it is 0; each end counts one pass
\ down and starts the steps again (lf-tac-again) while passes are left.
\ Lean call list: the macro's expansion -> the mode tit-mode; skip ->
\ lfr-skip; the steps again -> lf-tac-again; maxRecDepth -> tit-most.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own (the passes left are the frame's).

require ../tactic-api.fs

\ ---- The count: the step's value, a numeral.
: tit-num ( node -- n )
  dup syn-kind@ syn-k-num = if syn-a@ exit then drop lf-tac-unported ;
: tit-count ( frame -- n ) tfr-step @ 0 lf-tac-arg tit-num ;

\ ---- The weight of the open iterates: the frames of this frame's mode,
\ each its count and 2 (Lean's 2n + 3 levels of recursion depth, above).
128 constant tit-most
: tit-weight ( frame k -- frame w )
  lfr-frame 2dup tfr-mode @ swap tfr-mode @ = if tit-count 2 + else drop 0 then ;
: tit-weights ( frame -- w ) 0 lfr-depth 0 ?do over i tit-weight nip + loop nip ;
: tit-bounded ( frame -- frame ) dup tit-weights tit-most > if lf-tac-unported then ;

\ ---- The mode: n passes, none when n is 0.
: tit-open ( frame -- )
  tit-bounded dup tit-count 2dup swap tfr-passes ! 0= if lfr-skip else drop then ;
: tit-left ( frame -- frame n ) dup tfr-passes @ 1- 0 max 2dup swap tfr-passes ! ;
: tit-end ( frame -- ) tit-left if lf-tac-again else drop then ;
' tit-open ' tit-end 0 0 lf-block-mode constant tit-mode

1 0 0 tac-shape-block lf-tactic: by-iterate constant tac-k-iterate
s" iterate" tac-k-iterate lf-tactic-lean!
' lf-tac-all tac-k-iterate lf-tactic-action!
tit-mode tac-k-iterate lf-tactic-mode!
