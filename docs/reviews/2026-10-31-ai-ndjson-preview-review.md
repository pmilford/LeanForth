# Independent AI review of the NDJSON development preview

An independent AI subagent reviewed the uncommitted development preview based
on `b4c5f72`. This was not human review or approval of declaration import; the
reviewer did not review the subsequent fixes described here.

The reviewer found that different name indices could denote the same Lean name,
allowing duplicate declarations. The preview now compares structured names
including prefix and component kind; a regression covers duplicate names at
different indices. Name and expression count overflows now receive a limit
diagnostic. An additional test demonstrates that successful preview can contain
an open root and remains unchecked. The reviewer confirmed that exported sort
zero is a universe index and that nonzero indices are currently unsupported.

Further testing is needed for all resource boundaries and malformed nested
records, and the current evidence covers only one real export fixture. Export
metadata is an input claim, not authentication of its origin. Preview, Forth
staging, and the experimental declaration probe do not register a theorem and
are not approved for trusted use.
