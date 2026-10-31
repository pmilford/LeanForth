# Independent AI review of experimental inference

An independent AI subagent reviewed the experimental Forth inference work in
the worktree based on commit `cb186ce`. This was an adversarial AI review, not
human review or approval for a trusted kernel. The reviewer did not review the
subsequent fixes described below.

The review found that a malformed argument could be classified as unknown
before its unbound variable was visited, that a resource test reset the arena
before checking rollback, and that the fixture inspector accepted a Boolean
sort level and malformed name records. The follow-up adds a scope precheck,
checks rollback immediately, and tightens fixture checks with regression tests.
Further differential cases compare inference against pinned Lean, including
rejected expressions. These finite checks are evidence, not a soundness proof.

Open issues include retained intermediate allocations after successful
inference, exhaustion in the small arena, global mutable and non-reentrant
state, host recursion, stale indices, and the absence of an immutable
declaration boundary. Comparison of syntactically equal expressions does not
establish that they are well typed. The inference and conversion algorithms
and their interaction still need a soundness argument and independent human
review before they can authorize theorem validity.
