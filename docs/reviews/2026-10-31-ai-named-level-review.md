# Independent AI review of named-level integration test

An independent AI subagent reviewed the uncommitted test-only integration based
on `89b5cce`. It found that a forged preview object with conflicting fields could
make the Python encoder choose the wrong parameter silently. Follow-up changes
check exact fields, byte ranges and references, and test forged records. The
reviewer also noted that the Forth driver scope-checks only the two selected
roots, not disconnected levels; this limitation is now documented and tested.

Further tests added after review cover nested aliases and a declaration context
that names a reachable parameter through a different export index. The reviewer
did not review those later changes. This byte protocol is not a general Lean
interchange, does not authenticate input, and does not check or register a
theorem. This AI review is not human approval for trusted name identity,
universe conversion or declaration import.
