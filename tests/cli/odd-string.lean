-- A string literal holding two format characters above U+FFFF, U+E0041 (a
-- tag) and U+1D173 (a musical one), which Lean prints as themselves and
-- LeanForth as \u{X} (review F4 of fix-cli-present, 2026-11-18). A prelude
-- file with String and P as axioms, so that the export stays small (about
-- 1.2 KB; Init's String brings 590 KB; re-check S1). The literal between the
-- quotes below holds the two characters themselves. Exported with
-- scripts/export.sh as tests/cli/odd-string.ndjson; tests/cli/export-check.sh
-- rebuilds it and compares; test_leanforth.py's OddNames.test_print_string
-- prints it.
prelude
axiom String : Type
axiom P : String → Prop
theorem strUse (h : P "a󠁁b𝅳c") : P "a󠁁b𝅳c" := h

#print axioms strUse
