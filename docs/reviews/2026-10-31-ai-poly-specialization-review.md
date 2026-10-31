# Independent AI review of polymorphic fixture specialization

An independent AI subagent reviewed the uncommitted test-only specialization
pipeline based on `f891b76`. This is not a human review or approval for trusted
declaration import; it produces diagnostics for concrete instances only.

The reviewer found that a forged unknown expression tag could be silently
encoded as a Pi node, that an unused declared parameter could remain unassigned,
and that equivalent structured-name aliases were treated as different IDs.
Follow-up changes explicitly reject unknown tags, require a complete assignment
map, and map equivalent structured names to the declaration's context ID.
Regression tests exercise these cases. The reviewer also requested exact AST
comparison for every instance: the differential now compares canonical type
and value syntax with pinned Lean for all four levels, in addition to checking
the `u = 1` DAG against a separate export. The reviewer did not review these
later changes.

The stream and Python adapter are untrusted and do not authenticate provenance;
their status applies only to the supplied concrete data. The Forth probe is not
a trusted kernel and does not check the original polymorphic theorem. Additional
malformed-stream coverage, symbolic conversion, protected storage and human
review remain necessary.
