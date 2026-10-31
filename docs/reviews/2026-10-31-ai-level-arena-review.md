# Independent AI review of symbolic level arena

An independent AI subagent reviewed the uncommitted level arena and ADR 0004
based on `b3a59b9`. It found no demonstrated stack or allocation defect in
documented constructor paths. This was not a human review or approval for
trusted use; the reviewer did not review the later fixture-stream test or the
additional tests described here.

The review emphasized that constructors only validate indices and counts, not
the contents of previously allocated nodes. In-range count corruption and
reused stale indices remain undetectable. A trusted checker needs protected
ownership, full reachable-DAG validation, parameter scope and a separately
reviewed symbolic equality algorithm. The ADR now explicitly excludes level
metavariables and names the extra host words used. Follow-up tests exercise
additional invalid operands, count corruption and capacity exhaustion.

The reviewer tested Gforth 1.0 on the local host only. Additional runs on the
available Gforth 0.7.3 host are documented separately; neither run establishes
behavior on another Forth implementation or cell width.
