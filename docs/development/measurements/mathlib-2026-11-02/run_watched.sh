#!/bin/bash
# Usage: run_watched.sh NAME LIMIT_KB TIMEOUT_S STDIN_FILE_OR_- cmd args...
# Runs cmd under timeout and /usr/bin/time -v, logs RSS every 2 s to
# $SP/NAME.monitor and kills cmd (by PID only) if its RSS exceeds LIMIT_KB.
# stdout -> $SP/NAME.out, stderr -> $SP/NAME.stderr, time -> $SP/NAME.time
source "$(dirname "$0")/env.sh"
NAME=$1; LIMIT_KB=$2; TMO=$3; IN=$4; shift 4
[ "$IN" = "-" ] && IN=/dev/null
date -Is > $SP/$NAME.start
timeout "$TMO" /usr/bin/time -v -o $SP/$NAME.time "$@" < "$IN" > $SP/$NAME.out 2> $SP/$NAME.stderr &
TPID=$!
CPID=""
for i in $(seq 1 100); do
  T2=$(pgrep -P "$TPID" | head -1)
  [ -n "$T2" ] && CPID=$(pgrep -P "$T2" | head -1) && [ -n "$CPID" ] && break
  sleep 0.1
done
echo "timeout pid $TPID cmd pid $CPID: $*" > $SP/$NAME.monitor
MAXKB=0
while [ -n "$CPID" ] && kill -0 "$CPID" 2>/dev/null; do
  KB=$(awk '/^VmRSS/ {print $2}' /proc/$CPID/status 2>/dev/null)
  if [ -n "$KB" ]; then
    [ "$KB" -gt "$MAXKB" ] && MAXKB=$KB
    echo "$(date +%T) rss_kb=$KB avail_kb=$(awk '/^MemAvailable/ {print $2}' /proc/meminfo)" >> $SP/$NAME.monitor
    if [ "$KB" -gt "$LIMIT_KB" ]; then
      echo "LIMIT EXCEEDED: killing pid $CPID" >> $SP/$NAME.monitor
      kill "$CPID"
    fi
  fi
  sleep 2
done
wait $TPID
echo "exit $?" >> $SP/$NAME.monitor
echo "monitor max rss_kb=$MAXKB" >> $SP/$NAME.monitor
date -Is > $SP/$NAME.end
