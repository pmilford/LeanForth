\ by-skip: Lean's skip (plan row TB2, small tactics 1), a port of Lean
\ 4.35.0's evalSkip (src/lean/Lean/Elab/Tactic/BuiltinTactic.lean:289):
\ nothing at all, with a goal or none.
\ Lean call list: none (pure ()).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own.

require ../tactic-api.fs

tac-shape-plain lf-tactic: by-skip constant tac-k-skip
s" skip" tac-k-skip lf-tactic-lean!
: tsk-run ( i -- ) drop ;
' tsk-run tac-k-skip lf-tactic-action!
