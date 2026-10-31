# Independent AI review of declaration probe

An independent AI subagent reviewed the uncommitted experimental declaration
probe based on `f0338c0`. This is not a human review or approval for trusted
use, and the reviewer did not review the subsequent changes below.

The reviewer found that type inference could allocate a node at a value index
that was invalid when supplied, and that early exit could hide an invalid value
index. Both root indices are now validated against the entry arena before any
allocation; regression tests cover an index at the original count and an
invalid value paired with a non-proposition. Comparison statuses are now mapped
explicitly instead of relying on matching numeric values. The reviewer did not
find a demonstrated false success, and these fixes do not establish soundness.

The review also requested targeted exhaustion tests for each internal stage,
more malformed and open-root tests, and a direct declaration differential test
including Lean-valid cases requiring unsupported conversion. A budget sweep and
full-arena test exist, but these additional cases and full structural validation
ordering remain open. Global mutable state, unhandled host exceptions, immutable
declaration storage and inference/conversion soundness remain unresolved.
