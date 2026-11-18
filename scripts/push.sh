#!/bin/bash
# The only way to push to main (owner, 2026-11-12): runs everything the rules require on HEAD, records the results in
# .claude/work/ci/<hash>-result.txt, and pushes only when all pass.
#   1. the progress check (scripts/check-progress.py: stage words, progress report, Now/next/later)
#   2. the Forth review log and style ratchet, strict (scripts/check-forth-quality.py --strict)
#   3. the suites of the change tier of origin/main..HEAD (owner, 2026-11-13, plan 9.4.6; scripts/test-tier.py), run
#      and recorded by scripts/tested-tree.py tier, which reuses a recorded pass of each target whose inputs are
#      unchanged (owner, 2026-11-17: per-target reuse). The full tier (tests/test-classes.txt): the coverage
#      ratchet of the changed source files over their unit tests (make coverage-focus), make test on Gforth 1.0,
#      make test-unit on gforth-fast and make check-rest (every pinned-Lean comparison). A push runs only its own
#      tier: a documentation push the documentation and progress checks, a code push its tier once, with the Lean
#      cache. Gforth 0.7.3 and the coverage of every file run only in make daily (owner, 2026-11-17).
#   4. the age of the last daily full run (make daily: LEAN_CACHE=0, Gforth 0.7.3 and make coverage-check, run
#      once a night and before a tag): reported, with a warning when none is recorded or it is older than 36
#      hours; a push never runs it and never refuses for it. A tag needs one for its exact tree (make tag-check).
# Usage: scripts/push.sh [--no-cache] [--full] [--dry-run]
#   --no-cache  LEAN_CACHE=0 for the suites; --full  the full tier whatever changed;
#   --dry-run   print the tier, what would run or be reused and the daily run's age, then stop: runs, records and
#               pushes nothing (also on a branch other than main, against origin/main).
# Each suite's log is .claude/work/ci/<hash>-<suite>.log and each make command's time goes to
# .claude/work/ci/<hash>-timing.txt (slowest shown). The result line, with every suite run (exit status, time) or
# reused (the record's commit and date) and those the tier did not need, the Gforth and Lean versions, is appended
# to the tracked docs/development/ci-results.log in a follow-up commit.
# JOBS (owner, 2026-11-17): JOBS=N in the environment wins; else 2 when .claude/work/CPU_MODE says "day"; else 5
# when at most two heavy processes (Gforth, Lean, leanexport) of other runs are going, 2 when more
# (LF_HEAVY_COUNT=N stands for the count, for tests). Always under ulimit -u 500. Never force-pushes.
set -u
cd "$(dirname "$0")/.." || exit 1
ulimit -u 500
CACHE=1; FULL=""; DRY=""
for a in "$@"; do
  case $a in
    --no-cache) CACHE=0 ;;
    --full) FULL=--full ;;
    --dry-run) DRY=--dry-run ;;
    *) echo "usage: scripts/push.sh [--no-cache] [--full] [--dry-run]"; exit 2 ;;
  esac
done
H=$(git rev-parse --short HEAD); D=.claude/work/ci; mkdir -p "$D"
# One push run at a time: a second run would test a tree the first is still testing.
if [ -z "$DRY" ]; then exec 9>"$D/push.lock"; flock -n 9 || { echo "push.sh: another push run is in progress"; exit 1; }; fi
[ "$(git rev-parse --abbrev-ref HEAD)" = main ] || [ -n "$DRY" ] || { echo "push.sh: not on main"; exit 1; }
[ -z "$(git status --porcelain --untracked-files=no)" ] || { echo "push.sh: uncommitted changes"; exit 1; }
[ -n "$(git rev-list origin/main..HEAD)" ] || { echo "push.sh: nothing to push (HEAD is in origin/main)"; exit 0; }
heavy=${LF_HEAVY_COUNT:-$(ps -eo comm= | grep -cE '^(gforth[-a-z0-9.]*|lean|leanexport)$')}
if [ -n "${JOBS:-}" ]; then why="JOBS from the environment"
elif [ "$(cat .claude/work/CPU_MODE 2>/dev/null)" = day ]; then JOBS=2; why="CPU mode day"
elif [ "$heavy" -le 2 ]; then JOBS=5; why="$heavy heavy processes running"
else JOBS=2; why="$heavy heavy processes running"; fi
echo "push.sh: JOBS=$JOBS ($why)"
TIER=(python3 scripts/tested-tree.py tier --base origin/main --no-progress --jobs "$JOBS" --lean-cache "$CACHE")
[ -n "$FULL" ] && TIER+=("$FULL")
DAILY=(python3 scripts/tested-tree.py daily-status --warn-hours 36)
if [ -n "$DRY" ]; then "${TIER[@]}" --dry-run; s=$?; "${DAILY[@]}"; exit $s; fi
# Gforth 0.7.3 spins forever after an error; a forgotten probe slows every test run (2026-11-12: 3 h at 100%).
ps -eo pid,etimes,args | awk '$2 > 3600 && $3 ~ /gforth/ {print "push.sh: warning: gforth running " int($2/60) " min: pid " $1}'
export LF_TIMING_LOG="$PWD/$D/$H-timing.txt"; : > "$LF_TIMING_LOG"; : > "$D/$H-suites.txt"
python3 scripts/check-progress.py origin/main; p=$?
python3 scripts/check-forth-quality.py --strict; q=$?
"${TIER[@]}" --nice 10 --log-prefix "$D/$H-" --summary "$D/$H-suites.txt"; s=$?
daily_out=$("${DAILY[@]}"); echo "$daily_out"; daily=$(head -1 <<<"$daily_out")
line="progress $p; forth-quality $q; suites exit $s: $(cat "$D/$H-suites.txt" 2>/dev/null); $daily"
echo "$line" | tee "$D/$H-result.txt"
sort -k2 -n -r "$LF_TIMING_LOG" | head -8
[ $p = 0 ] && [ $q = 0 ] && [ $s = 0 ] || { echo "push.sh: not pushed"; exit 1; }
# A tracked record of what was run (owner's rule: record commands, versions and CI status).
gv=$(.tools/gforth/bin/gforth --version 2>&1 | head -1); lv=$(.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean --version 2>&1 | head -1)
echo "$(date '+%Y-%m-%d %H:%M') $H $line; $gv; $lv" >> docs/development/ci-results.log
git add docs/development/ci-results.log && git commit -q -m "Record the local CI of $H" || exit 1
git push origin main
