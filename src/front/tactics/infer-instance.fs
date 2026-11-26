\ by-infer-instance: Lean's infer_instance (plan row TB2, small tactics
\ 1), a port of the macro of Lean 4.35.0's src/lean/Init/Tactics.lean:518,
\ exact inferInstance: the identifier inferInstance, made at the step's
\ word as the macro's syntax is (front/syntax.fs's syn-k-const node of the
\ constant of that full name, author/groups.fs's lfa-const-named: Lean's
\ hygienic name, never the text's namespace), closed over by exact's run
\ (tactics/exact.fs's tex-term: elabTermEnsuringType against the main
\ goal's type, so @inferInstance.{u} T inst with inst T's instance). Its
\ errors are exact's and the elaborator's: no instance is 125, Lean's
\ "failed to synthesize" with the class; an instance the export left
\ out is 119, not supported yet.
\ Lean call list: exact -> lf-close-main-goal-using with tex-term
\ (tactic-core.fs, tactics/exact.fs); the identifier -> syn-new,
\ lfa-const-named.
\ Untrusted: only the kernel's check of the finished term decides.
\ State: none of its own (the node it makes is the syntax store's).

require ../tactic-api.fs
require ./exact.fs

tac-shape-plain lf-tactic: by-infer-instance constant tac-k-infer-instance
s" infer_instance" tac-k-infer-instance lf-tactic-lean!

: tii-node ( i -- node )
  syn-k-const swap lf-tac-step-at syn-new lf-made! s" inferInstance" lfa-const-named
  lf-found syn-a! ;
: tii-run ( i -- ) dup tii-node swap ['] tex-term lf-close-main-goal-using ;
' tii-run tac-k-infer-instance lf-tactic-action!
