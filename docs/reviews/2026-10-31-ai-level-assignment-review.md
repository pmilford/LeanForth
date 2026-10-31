# Independent AI review of level assignment experiment

An independent AI subagent reviewed the uncommitted level assignment experiment
based on `8e34988`. It found that context reset and reused opaque IDs could
silently retain an old assignment. Follow-up changes bind assignment maps to
arena and context generations, validate table contents before adding or
evaluating, and make evaluation mode explicit. Tests cover reset and reuse,
corruption, missing assignments and generation saturation. The reviewer
inspected the generation follow-up and found no recurrence through normal
reset or context-extension operations.

The follow-up review observed that adding to an already corrupted context
could report success. A subsequent change checks the existing context before
adding; the reviewer did not review that final change. Generation counters and
arena contents remain mutable and can be forged or corrupted by raw writes;
they are not an integrity boundary. The 36 Lean differential cases establish
finite instance evidence, not a polymorphic proof or symbolic equality.
This AI review is not human approval for trusted use.
