# Independent AI review of experimental structured names

An independent AI subagent reviewed the uncommitted name arena based on
`c7d5f89`. It found an input aliasing defect: a string could overlap query
scratch variables and change before being copied. The implementation now copies
the query to a bounded scratch buffer before changing those variables; tests
cover scratch and stored-byte input aliases. The reviewer inspected the initial
fix and found no recurrence in its probe; subsequent alias tests were not
independently reviewed.

The reviewer found no demonstrated stack or bounds defect under the documented
readable-memory and no-external-mutation assumptions. Bounds validation does
not protect against raw changes that create duplicate names, in-range count
corruption or stale IDs. The follow-up review also noted that the fixture
transport is one-byte and test-only, and its map is not yet connected to the
universe or declaration checker. Nested alias regression tests were added after
that review. A later test-only integration maps those IDs into an experimental
level context; it does not create a trusted declaration. This is AI feedback,
not human approval for trusted use.
