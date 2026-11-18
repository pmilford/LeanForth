#!/bin/bash
# perf-scan: a GFORTH that logs each Gforth run's wall and user seconds and its arguments.
# GTIME_ENGINE: the real engine; GTIME_LOG: the log file.
start=$(date +%s.%N)
/usr/bin/time -f "%e %U" -o "$GTIME_LOG.$$" "$GTIME_ENGINE" "$@"
status=$?
printf '%s %s\n' "$(cat "$GTIME_LOG.$$" 2>/dev/null | tail -1)" "$*" >> "$GTIME_LOG"
rm -f "$GTIME_LOG.$$"
exit $status
