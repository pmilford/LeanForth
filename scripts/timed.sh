#!/bin/bash
# timed.sh TARGET COMMAND...: run COMMAND and append "TARGET SECONDS EXIT" to $LF_TIMING_LOG (Makefile's RUN).
# COMMAND gets LF_MAKE_TARGET=TARGET (make coverage attributes each Gforth run's counts to its target).
target=$1; shift
export LF_MAKE_TARGET=$target
start=$(date +%s.%N)
"$@"; rc=$?
printf '%s %.1f %s\n' "$target" "$(echo "$(date +%s.%N) - $start" | bc)" "$rc" >> "$LF_TIMING_LOG"
exit $rc
