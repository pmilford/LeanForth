# Done check: the `--jobs` default of 4 and the workers' time in `--resources` (2026-11-24)

Independent done checker (Sonnet), on main 9a882569 (pushed by `scripts/push.sh`, origin/main 7e7059d8; Forth review
[2026-11-24-jobs-default.md](../forth-reviews/2026-11-24-jobs-default.md) logged with its re-check; full tier passed on
that head). The commit that added this report added to COMMAND_LINE.md what the checker missed: a text under the
default shows no workers line with `--resources`, and the JSON's times are microseconds.

DONE CHECK: jobs default and run monitoring
Verdict: DONE for claims 1-4 on small exports and LeanForth texts, stage "works end to end" on those inputs. Head was 9a882569 "Log the re-check of jobs-default". I did not check the "done" stage (CI, review log, coverage).

Commands (fresh shell at the repo root, nice -n 10, no make). Outputs are under /tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/donejobs/.
| # | Command | Expected | Observed |
| 1a | `check tests/cli/inductive.ndjson` against `--jobs 1`, diffed | same output and exit | exit 0 and 0, diff empty, "6 accepted" |
| 1b | same on tests/cli/unfold.ndjson and tests/reference/constant-fixture.ndjson | same | exit 0 and 0, diff empty (2 and 3 accepted) |
| 1c | `check --no-manifest` on tests/core/check-declaration-cases/composition-wrong-argument.ndjson (rejected; it is the COMMAND_LINE.md:711 example) | same, exit 1 | exit 1 and 1, diff empty, "1 declaration: 1 rejected", diagnostic 59 |
| 1d | same on composition-unsafe.ndjson (skipped, diagnostic 97) | same | exit 0 and 0, diff empty |
| 1e | same on tests/front/decide-slice.ndjson | same | exit 0 and 0, diff empty, "1290 accepted", axioms allowlisted |
| 2a | `check --no-manifest --resources decide-slice` | workers line, plan and run times, busy and waiting per task | present; see excerpt |
| 2b | `check --resources --jobs 2 tests/cli/unfold.ndjson` | says how the count was chosen | "workers: 2 (--jobs), on 10 cores" |
| 2c | `check --resources --json` against `--json`, on unfold | `measured.workers` only with `--resources` | present with plan, run, driver, each[4], totals; absent without. Times are microseconds in the JSON. All values are >= 0. |
| 2d | `--resources --jobs 1` | no workers lines | none printed (matches COMMAND_LINE.md:1209) |
| 3 | `check [--jobs N] --env tests/author/init-slice.ndjson tests/author/07-add-comm.lf` (the COMMAND_LINE.md:317 example) | default and `--jobs 1` serial with no note; `--jobs 2` prints the note | default exit 0, no note; `--jobs 1` exit 0, no note; `--jobs 2` exit 0, first line "note: --jobs does not apply to LeanForth text yet; checking one declaration at a time"; 60 accepted in all three |
| 4 | decide-slice, `--no-manifest`, once each | default is not slower | `--jobs 1`: 4.13 s wall. Default: 1.89 s wall. Both exit 0. |

`--resources` excerpt (decide-slice, default, gforth-fast):
  workers: 4 (the default), on 10 cores
    checks handed out 1054, run again 0, not ready 0, forced 0, workers replaced 0
    plan 0.020 s, jobs' run 1.521 s
    time (s)      busy  waiting
    driving      0.164    1.357
    worker  1    1.446    0.075
    worker  2    0.852    0.669
    worker  3    0.861    0.660
    worker  4    0.829    0.692
    total        3.989    2.098
Busy plus waiting for each task is 1.521 s, the jobs' run, so the figures are consistent. Under the JSON, the driver's 747+630 and worker 1's 539+838 each come to the run's 1377 µs.

Gaps and wording in COMMAND_LINE.md:
- Line 965 and the task text say decide-slice has 1,291 declarations, but the summary says 1290 (1291 is probably the line count). I did not find where 1,291 appears in the document.
- Lines 936-941 and 312 say a text prints no note by default. That holds. They do not say what `--resources` shows for a text under the default. I ran `--resources` on the text and it printed no workers line. The doc only says "workers: none could be made" for `--jobs N` above 1, so the default case is unstated.
- I did not look for a doc paragraph on the JSON `measured.workers` fields or their units (microseconds, `each` list). I saw no explicit statement of the units while reading lines 1189-1264.
- Case 4 was one run of each, at some load from other agents. The gap (4.13 s against 1.89 s) is large, but the "not slower" claim for the smallest exports (chain, wide60) was not re-timed.

Not checked: the figures for Init and Mathlib (the 3.5x speed-up, the load figures, the tables at lines 954-1060); `--snapshot` runs under the default; `--record` and `--progress` with the default; a machine with fewer than 4 CPUs (the "(the default 4, 2 cores)" wording); .lf runs with `--elab-data`, because I used the COMMAND_LINE.md:317 example rather than a LANGUAGE_REFERENCE.md one; CI state and the Forth review log.
