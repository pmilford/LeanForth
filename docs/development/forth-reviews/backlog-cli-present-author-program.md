
## Follow-ups from the review of batches A and B (2026-11-12, plan 9.4.5)

From [2026-11-12-refactor-present.md](2026-11-12-refactor-present.md), left for a later batch:
- **L2:** log-view's merged rebuild picks levels or terms with a true/false flag tested in nine words. Pass a
  `/lv-kind` record of execution tokens and offsets instead (the review gives the sketch).
- **L3:** the tag and rule dispatches (term-printer, print-forth, log-view) are chained CASEs split at arbitrary
  points. Use tables indexed by the validated tag or rule code, and stop lf-lv-relates depending on the catalogue's
  numbering.
- **I1:** /lv-node's reversed fields for `2@`.
