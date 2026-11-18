#!/bin/bash
# perf-scan: write the profile and counter summaries into the measurements folder.
cd "$(dirname "$0")/../.." || exit 1
M=docs/development/measurements/perf-scan-2026-11-18
P=build/perf
{
  echo "# check of tests/front/s1-rfl.lf against Init's snapshot with Init's elaboration data,"
  echo "# gforth-fast under tools/sample.py (10 ms); commands in PERFORMANCE_SCAN.md, Commands"
  grep -A6 '^resources' "$P/prof-run.out"
  python3 $P/inc.py $P/lf-s1rfl.prof cli-text-run cli-text-loaded ck-snapshot-import ck-lf-load ck-feed-phase \
    lfc-text it-pass-run lf-libdec-decl lf-name-storage-valid? lf-name-find-str lf-name-find-num ck-check \
    ck-import-pass cli-text-report
  python3 $P/excl.py $P/lf-s1rfl.prof cli-main lf-name-storage-valid? lf-name-find-str lf-name-find-num
  python3 $P/excl.py $P/lf-s1rfl.prof it-pass-run lf-name-storage-valid? lf-name-find-str lf-name-find-num
  python3 $P/callers.py $P/lf-s1rfl.prof lf-name-storage-valid? 4 | head -6
  python3 $P/analyze.py $P/lf-s1rfl.prof 15 | sed -n '/-- exclusive/,/-- inclusive/p'
  echo "# the snapshot tier's load (tf-load-next), exclusive"
  python3 $P/analyze.py $P/lf-s1rfl.prof 8 --under tf-load-next | sed -n '/-- exclusive/,/-- inclusive/p'
  echo "# the import pass of the 59,349 snapshot results (ck-import-pass), exclusive"
  python3 $P/analyze.py $P/lf-s1rfl.prof 8 --under ck-import-pass | sed -n '/-- exclusive/,/-- inclusive/p'
  echo
  echo "# tests/front/04-nested-ih.lf, same command"
  grep -A5 '^resources' $P/nested.out
  python3 $P/inc.py $P/lf-nested.prof it-pass-run lf-name-storage-valid? lfc-text
  python3 $P/excl.py $P/lf-nested.prof lfc-text it-pass-run lf-name-storage-valid? lf-name-find-str lf-name-find-num
  echo
  echo "# the same s1-rfl check on gforth (the checking engine), /usr/bin/time: $(cat $P/lf-gforth.time)"
  grep -A5 '^resources' $P/lf-gforth.out
} > $M/lf-check-profile.txt 2>&1
{
  echo "# counters (tools/patch.py, tools/zzcnt.fs on a scratch copy of src/), s1-rfl.lf check as above:"
  echo "# 0 storage audits, 1 entries visited by them, 2 most names, 3 lf-name-find-num calls, 4 entries visited,"
  echo "# 5 lf-name-find-str calls, 6 entries visited, 7 library declarations decoded"
  cat $P/lf-counters.txt
  echo
  echo "# p1m (Init's first 1M lines, 9,202 declarations), check --no-manifest --jobs 1, gforth-fast: $(cat $P/p1m-inst.time)"
  echo "# 10 htab-find, 11 htab compares, 12 lf-env-current, 13 replace-memo lookups, 14 their hits, 15 lf-term-cons,"
  echo "# 20+2k hits / 21+2k misses of cache k: 0 infer, 1 infer-only, 2 whnf_core, 3 whnf, 4 unfold, 5 success, 6 failure;"
  echo "# 40 allocate, 41 free, 42 resize, 43 bytes allocated"
  grep '^CNT' $P/p1m-inst.out
  grep -A4 '^resources' $P/p1m-inst.out
} > $M/counters.txt
