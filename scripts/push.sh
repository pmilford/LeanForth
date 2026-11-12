#!/bin/bash
# The only way to push to main (owner, 2026-11-12): runs everything the rules require on HEAD, records the results in
# .claude/work/ci/<hash>-result.txt, and pushes only when all pass.
#   1. the progress check (scripts/check-progress.py: stage words, progress report, Now/next/later)
#   2. the Forth review log and style ratchet, strict (scripts/check-forth-quality.py --strict)
#   3. CI job 1: make check (Gforth 1.0, Lean 4.35.0; LEAN_CACHE=0 when the first argument is --no-cache)
#   4. the coverage ratchet (make coverage-check) when the range changes Forth source
#   5. CI job 2: make test on Gforth 0.7.3
# Each make command's time goes to .claude/work/ci/<hash>-timing.txt (slowest shown); the result line, Gforth and
# Lean versions are appended to the tracked docs/development/ci-results.log in a follow-up commit.
# JOBS follows .claude/work/CPU_MODE ("day": 2, otherwise make's default). Never force-pushes.
set -u
cd "$(dirname "$0")/.." || exit 1
ulimit -u 500
H=$(git rev-parse --short HEAD); D=.claude/work/ci; mkdir -p "$D"
# One push run at a time: a second run would test a tree the first is still testing.
exec 9>"$D/push.lock"; flock -n 9 || { echo "push.sh: another push run is in progress"; exit 1; }
[ "$(git rev-parse --abbrev-ref HEAD)" = main ] || { echo "push.sh: not on main"; exit 1; }
[ -z "$(git status --porcelain --untracked-files=no)" ] || { echo "push.sh: uncommitted changes"; exit 1; }
JOBS=8; [ "$(cat .claude/work/CPU_MODE 2>/dev/null)" = day ] && JOBS=2
# Gforth 0.7.3 spins forever after an error; a forgotten probe slows every test run (2026-11-12: 3 h at 100%).
ps -eo pid,etimes,args | awk '$2 > 3600 && $3 ~ /gforth/ {print "push.sh: warning: gforth running " int($2/60) " min: pid " $1}'
CACHE=""; [ "${1:-}" = --no-cache ] && CACHE="LEAN_CACHE=0"
export LF_TIMING_LOG="$PWD/$D/$H-timing.txt"; : > "$LF_TIMING_LOG"
python3 scripts/check-progress.py origin/main; p=$?
python3 scripts/check-forth-quality.py --strict; q=$?
nice -n 10 make check JOBS=$JOBS $CACHE > "$D/$H-check.log" 2>&1; c=$?
v=0; if git diff --name-only origin/main..HEAD | grep -q '^src/.*\.fs$'; then
  nice -n 10 make coverage-check JOBS=$JOBS > "$D/$H-coverage.log" 2>&1; v=$?; fi
nice -n 10 make test JOBS=$JOBS GFORTH="$PWD/.claude/work/A/gforth073.sh" > "$D/$H-test073.log" 2>&1; t=$?
line="progress $p; forth-quality $q; make check JOBS=$JOBS $CACHE exit $c; coverage-check exit $v; make test 0.7.3 exit $t"
echo "$line" | tee "$D/$H-result.txt"
sort -k2 -n -r "$LF_TIMING_LOG" | head -8
[ $p = 0 ] && [ $q = 0 ] && [ $c = 0 ] && [ $v = 0 ] && [ $t = 0 ] || { echo "push.sh: not pushed"; exit 1; }
# A tracked record of what was run (owner's rule: record commands, versions and CI status).
gv=$(.tools/gforth/bin/gforth --version 2>&1 | head -1); lv=$(.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean --version 2>&1 | head -1)
echo "$(date '+%Y-%m-%d %H:%M') $H $line; $gv; $lv" >> docs/development/ci-results.log
git add docs/development/ci-results.log && git commit -q -m "Record the local CI of $H" || exit 1
git push origin main
