#!/bin/bash
# timed.sh TARGET COMMAND...: run COMMAND and append "TARGET SECONDS EXIT" to $LF_TIMING_LOG (Makefile's RUN).
target=$1; shift
start=$(date +%s.%N)
"$@"; rc=$?
printf '%s %.1f %s\n' "$target" "$(echo "$(date +%s.%N) - $start" | bc)" "$rc" >> "$LF_TIMING_LOG"
exit $rc
