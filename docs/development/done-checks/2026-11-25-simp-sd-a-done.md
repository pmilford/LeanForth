# Done check: simp data slice SD-a

DONE CHECK: simp SD-a
Verdict: MIXED, closest to DONE. The stage reached is works end to end for the format-4 read, the count line, formats 3.2 and four of the five refusals. The "priorities rising along a run" refusal was not shown end to end by me, so the claim is not fully shown. Two documents are stale (below), so it is not "done" yet.

Claim: A user can run `bin/leanforth check --elab-data` on format-4 elaboration data (congruence lemmas and defeq tags), see their count, still read formats 3, 3.1 and 3.2, and have malformed format-4 data refused.

Commands (fresh shell, repo root, `ulimit -u 500`, `GFORTH=.tools/gforth/bin/gforth`, `nice -n 10`):
1. `bin/leanforth check --env tests/front/simp-slice.ndjson --elab-data tests/front/simp-slice.elab.ndjson tests/front/simp-data/sd-id.lf`
   - Exit 0.
   - Output: "elaboration data: 20 instances, ... 13 smart-unfolding bodies, 2 congruence lemmas, 1 defeq tags".
   - Also "sd_id: accepted", "426 declarations: 426 accepted".
   - The data file has `format_version":4`. It really holds 2 `congr` records (dite_congr, ite_congr) and 1 `defeq` tag (Nat.add_zero).
2. Format 3.2: `bin/leanforth check --env tests/front/s1-slice.ndjson --elab-data tests/front/s1-slice.elab.ndjson tests/front/s1-rfl.lf`
   - Exit 0, "548 declarations: 548 accepted".
   - The count line is the old one, with no congruence part. The data file says format "3.2".
   - I did not run formats 3 and 3.1 end to end. Only the repo fixtures plain3, plain31 and plain32 exist for them, and I did not run them.
3. Malformed files of my own, in `/tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/done-simp-sd-a/`. I built each from the simp-slice data by editing the congr lines. Each was run with the command of 1. All exited 4, with "error: invalid: the elaboration data was refused ... the LeanForth text was not checked".
   - `duplicate.ndjson` (the ite_congr line repeated): line 805, error 47, "a congruence lemma named twice".
   - `count.ndjson` (header says 5 congr, the file has 2): line 804, error 20, "records differ in number from the header".
   - `wrong-fun.ndjson` (dite_congr filed under `ite`): line 803, error 37, "numbers that do not fit the declaration's type". It is refused, but under the hyps-fit error, not a dedicated "wrong function" message.
   - `sides-differ.ndjson` (ite_congr filed under Nat.add): line 804, error 37, same message.
   - `hyps-down3.ndjson` and `prio-rising3.ndjson` (an extra lemma Eq.mpr_not under `ite`): error 37.
   - `hyps-down2.ndjson` and `prio-rising2.ndjson`: error 47. My lemma name was already used.
4. The "priorities rising along a run" refusal was NOT shown by me. My extra lemma (Eq.mpr_not) has too few binders, so even my valid-looking control files (`ctl`, `ctl0` and `ctl1` in the scratchpad) were refused with error 37 before the priority check could fire. The repo's own fixtures (`tests/front/simp-data/prio-rising.elab.ndjson`) could not be used with `simp-slice.ndjson`: error 39, manifest mismatch. I did not find the matching environment. I did not run the unit tests in `tests/front/simp-data.fs`, and the unit tests are not end-to-end evidence anyway.
   - The error 37 and error 48 text for the rising-priority and run-order cases is documented. Error 48 is "congruence lemmas out of their function's order".

Documentation gaps:
- `docs/programming/ELABORATION_DATA.md:841-842` says the format-4 counts are "Not yet printed by the check's 'elaboration data:' line ... left to the branch that owns the command line". Run 1 shows the line does print "2 congruence lemmas, 1 defeq tags". The document is stale. Corrected wording: "The check's 'elaboration data:' line ends with ', N congruence lemmas, M defeq tags' for format 4 (src/cli/leanforth-text.fs)."
- `docs/project/PLAN_DRAFT.md:756` (row FE9) says "tested alone ... on branch `simp-sd-a` ... not merged, not done" and lists SD-b.6/b.7 as tasks. On main, `git merge-base --is-ancestor simp-sd-a main` says merged, and the command is integrated. The stage text needs updating to integrated or works end to end, citing this report.
- There is no done-check report file yet for SD-a. The row needs one before anything is called done.
- Not overstated: the docs and the FE9 row say simp itself is "not started". The simp work (`by-simp`, `simp only`, simp sets and the rest) is listed as not started, and `docs/design/SIMP_DATA.md` and `docs/design/TACTIC_SIMP.md` describe SP1a to SP2a as plans. SD-b is listed as open. I found no claim of a simp tactic.
- Wording: do not call this "LeanForth proved". The slice only reads and validates data.

## After the report (coordinator, 2026-11-25 09:07)

- The one refusal the checker could not show, priorities rising along a run, was run end to end by the
  coordinator on main f9252f8d: the slice copied with its manifest's `elab_records_sha256` removed (as
  `tests/front/test_simp_data.py` does; with the bound manifest any other data file is refused first with
  error 39), and the `prio-rising` data of `tests/front/test_simp_data.py`:
  `bin/leanforth check --env COPY/slice.ndjson --elab-data prio-rising.elab.ndjson tests/front/simp-data/sd-id.lf`
  answered "the elaboration data was refused at line 4 (error 48): congruence lemmas out of their function's
  order", exit 4.
- The two stale passages were corrected in the same commit as this file: `docs/programming/ELABORATION_DATA.md`
  (the count line is printed) and plan row FE9 (merged; stage below).
- Stage: **done** for what slice SD-a claims (format 4 read, counted and validated by `leanforth check`).
  No simp tactic exists; slice SD-b is open.
