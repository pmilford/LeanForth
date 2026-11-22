\ by-exists[ e1 .. en ]: Lean's exists e1, .., en (plan row TB2, tactic
\ batch 3c), the macro of Lean 4.35.0's src/lean/Init/Tactics.lean:1293-
\ 1294, `(refine ⟨e1, .., en, ?_⟩; try trivial)`: the anonymous
\ constructor of the list's terms and a synthetic hole, made at the
\ step's word as the macro's syntax is (front/syntax.fs's syn-k-anon and
\ syn-k-synthetic nodes; elab-term.fs elaborates it, its errors at that
\ place), refined (tactic-core.fs's lf-tac-refine: refineCore with the
\ suffix refine), then trivial's row tried (try: a Lean error undone and
\ forgotten; trivial's not supported yet thrown on, never accepted). The
\ terms are the bracket's values (tactic-syntax.fs's tac-shape-list+), one
\ at least as Lean's term,+ (460).
\ Lean call list: refine -> lf-tac-refine in lf-lift-meta-tactic
\ (tactic-core.fs); try -> lf-tac-try-lean; trivial -> by-trivial's row
\ (tactics/trivial.fs's ttr-nested, its row on the step running).
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own (the nodes it makes are the syntax store's).

require ../tactic-api.fs
require ./trivial.fs

tac-shape-list+ lf-tactic: by-exists[ constant tac-k-exists
s" exists" tac-k-exists lf-tactic-lean!

\ ⟨ e1, .., en, ?_ ⟩ at the step's word: the hole first, then the node
\ and its slots (syntax.fs: a node's slots follow it).
: txs-node ( n kind pos -- node ) syn-node-new 0= if outcome-full lf-tac-must then ;
: txs-hole ( i -- hole ) lf-tac-step-at 0 swap syn-k-synthetic swap txs-node ;
: txs-outer ( i -- node )
  dup lf-tac-args# 1+ swap lf-tac-step-at syn-k-anon swap txs-node ;
: txs-fill ( i node -- i node )
  over lf-tac-args# 0 ?do 2dup swap i lf-tac-arg i swap syn-arg! loop ;
: txs-anon ( i -- node ) dup txs-hole swap dup txs-outer txs-fill nip swap syn-last! ;
: txs-tac ( i goal -- goals ) swap txs-anon swap lf-tac-refine ;
: txs-run ( i -- )
  dup ['] txs-tac lf-lift-meta-tactic ['] ttr-nested lf-tac-try-lean drop ;
' txs-run tac-k-exists lf-tactic-action!
