# Independent AI review of symbolic universe preview

An independent AI subagent reviewed the uncommitted preview based on `dbd2b59`
and then reviewed follow-up changes. This is not a human approval for trusted
use. The real polymorphic fixture's parameter and sort references match the
pinned Lean exporter.

The first review demonstrated that a mutated summary flag and sort could make
the test adapter encode a concretized instance instead of the original symbolic
declaration. The adapter now rejects parameters and independently recomputes
concrete level graphs and sort values. The review also found that the preview
did not reject undeclared reachable universe parameters; a bounded per-root DAG
traversal now compares structured parameter names to each declaration's list.
The follow-up review found no remaining version of those two specific issues.

The follow-up identified a conservative rejection of equivalent name indices
in theorem `all` fields; subsequent changes compare structured names instead.
Tests now cover aliases, nested reachable parameters, value-only parameters and
two declarations with separate parameter lists. The AI reviewer did not review
those latest changes. This parser and test adapter remain untrusted; consistent
mutation of the whole preview creates a different input and cannot be detected
as a provenance change. Type checking, symbolic conversion and theorem
registration remain unavailable.
