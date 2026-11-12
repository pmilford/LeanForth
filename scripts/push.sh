#!/bin/bash
# The only way to push to main (owner, 2026-11-12): runs everything the rules require on HEAD, records the results in
# .claude/work/ci/<hash>-result.txt, and pushes only when all pass.
#   1. the progress check (scripts/check-progress.py: stage words, progress report, Now/next/later)
#   2. the Forth review log and style ratchet, strict (scripts/check-forth-quality.py --strict)
#   3. CI job 1: make check (Gforth 1.0, Lean 4.35.0; LEAN_CACHE=0 when the first argument is --no-cache)
#   4. CI job 2: make test on Gforth 0.7.3
# JOBS follows .claude/work/CPU_MODE ("day": 2, otherwise make's default). Never force-pushes.
set -u
cd "$(dirname "$0")/.." || exit 1
ulimit -u 500
H=$(git rev-parse --short HEAD); D=.claude/work/ci; mkdir -p "$D"
[ "$(git rev-parse --abbrev-ref HEAD)" = main ] || { echo "push.sh: not on main"; exit 1; }
[ -z "$(git status --porcelain --untracked-files=no)" ] || { echo "push.sh: uncommitted changes"; exit 1; }
JOBS=8; [ "$(cat .claude/work/CPU_MODE 2>/dev/null)" = day ] && JOBS=2
CACHE=""; [ "${1:-}" = --no-cache ] && CACHE="LEAN_CACHE=0"
python3 scripts/check-progress.py origin/main; p=$?
python3 scripts/check-forth-quality.py --strict; q=$?
nice -n 10 make check JOBS=$JOBS $CACHE > "$D/$H-check.log" 2>&1; c=$?
nice -n 10 make test JOBS=$JOBS GFORTH="$PWD/.claude/work/A/gforth073.sh" > "$D/$H-test073.log" 2>&1; t=$?
echo "progress $p; forth-quality $q; make check JOBS=$JOBS $CACHE exit $c; make test 0.7.3 exit $t" | tee "$D/$H-result.txt"
[ $p = 0 ] && [ $q = 0 ] && [ $c = 0 ] && [ $t = 0 ] || { echo "push.sh: not pushed"; exit 1; }
git push origin main
