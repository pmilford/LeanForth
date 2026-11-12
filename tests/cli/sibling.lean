-- A second library on top of tests/cli/inductive.lean, beside
-- dependent.lean (plan task 6.2.5, step SN4; ADR 0020 amendment 1, F5):
-- the snapshots of the two, each a layer on a snapshot of inductive.ndjson,
-- load together; both hold Eq and rfl, which the base does not. Exported
-- with scripts/export.sh; tests/cli/export-check.sh rebuilds the export and
-- its manifest and compares them with the committed files.
import LeanForthInductive

theorem Two.swap_first : Two.swap Two.first = Two.second := rfl

theorem Two.swap_second : Two.swap Two.second = Two.first := rfl

#print axioms Two.swap_first
