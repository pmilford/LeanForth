#!/bin/sh
# Where a check spends its time (docs/development/PROFILING.md, "Where a
# check spends its time"; make profile-check EXPORT=FILE [JOBS=1]): check
# EXPORT on gforth-fast under the sampling profiler (scripts/profile-sample.py,
# with scripts/profile-symbols.fs loaded after src/main.fs), keep the JSON
# report with --resources, then print the tables of scripts/profile-summary.py
# and the slowest declarations by time (scripts/slowest-declarations.py).
#
# usage: GFORTH_FAST=PATH scripts/profile-check.sh EXPORT
#   PROFILE_JOBS      workers (default 1: only the first thread is sampled)
#   PROFILE_OUT       folder of the raw files check.prof, check.syms, check.json
#                     (default build/profile; made if missing)
#   PROFILE_INTERVAL  seconds between samples (default 0.01)
#   PROFILE_ARGS      more check options (default --no-manifest)
#   PROFILE_TOP       words and declarations listed (default 25)
# Exit status: the check's (0 when every declaration was accepted), or 2 for a
# usage error, 5 when the profiler or a table failed. A development tool, not
# part of the product: x86-64 Linux and Gforth 1.0's gforth-fast only.
export_file=$1
if [ -z "$export_file" ] || [ -z "$GFORTH_FAST" ]; then
  echo "usage: GFORTH_FAST=PATH scripts/profile-check.sh EXPORT" >&2
  exit 2
fi
root=$(cd "$(dirname "$0")/.." && pwd -P) || exit 5
out=${PROFILE_OUT:-build/profile}
mkdir -p "$out" || exit 5
syms=$out/check.syms
GFORTH_ENV=off PROF_SYMS=$syms python3 "$root/scripts/profile-sample.py" "$out/check.prof" \
  "${PROFILE_INTERVAL:-0.01}" -- "$GFORTH_FAST" "$root/src/main.fs" \
  "$root/scripts/profile-symbols.fs" -e cli-main check ${PROFILE_ARGS:---no-manifest} \
  --jobs "${PROFILE_JOBS:-1}" --resources --json "$export_file" > "$out/check.json"
status=$?
# Gforth leaves through cli-leave with 100 more than the command's status.
[ "$status" -ge 100 ] && status=$((status - 100))
python3 "$root/scripts/profile-summary.py" "$out/check.prof" "$syms" \
  --top "${PROFILE_TOP:-25}" || exit 5
echo "-- slowest declarations by time"
python3 "$root/scripts/slowest-declarations.py" -n "${PROFILE_TOP:-25}" --sum "$out/check.json" || exit 5
exit "$status"
