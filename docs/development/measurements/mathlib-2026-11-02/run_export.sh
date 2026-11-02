#!/bin/bash
# Export Mathlib with the pinned leanexport, timing it and watching RSS by PID.
# Stops the exporter (by PID only) if its RSS exceeds LIMIT_KB.
source "$(dirname "$0")/env.sh"
LIMIT_KB=18500000
M=$MROOT/mathlib4
P=$M/.lake/packages
export LEAN_PATH=$P/Cli/.lake/build/lib/lean:$P/batteries/.lake/build/lib/lean:$P/Qq/.lake/build/lib/lean:$P/aesop/.lake/build/lib/lean:$P/proofwidgets/.lake/build/lib/lean:$P/importGraph/.lake/build/lib/lean:$P/LeanSearchClient/.lake/build/lib/lean:$P/plausible/.lake/build/lib/lean:$M/.lake/build/lib/lean:$REPO/.tools/elan/toolchains/leanprover--lean4---v4.35.0/lib/lean
echo "LEAN_PATH=$LEAN_PATH" > $SP/export.env
cd $MROOT
date -Is > $SP/export.start
timeout 3600 /usr/bin/time -v -o $SP/export.time leanexport Mathlib > $MROOT/mathlib.ndjson 2> $SP/export.stderr &
TPID=$!
LPID=""
for i in $(seq 1 50); do
  LPID=$(pgrep -P "$TPID" | head -1)   # timeout's child: /usr/bin/time
  [ -n "$LPID" ] && LPID2=$(pgrep -P "$LPID" | head -1) && [ -n "$LPID2" ] && LPID=$LPID2 && break
  sleep 0.2
done
echo "timeout pid $TPID leanexport pid $LPID" > $SP/export.monitor
MAXKB=0
while kill -0 "$LPID" 2>/dev/null; do
  KB=$(awk '/^VmRSS/ {print $2}' /proc/$LPID/status 2>/dev/null)
  if [ -n "$KB" ]; then
    [ "$KB" -gt "$MAXKB" ] && MAXKB=$KB
    echo "$(date +%T) rss_kb=$KB out_bytes=$(stat -c %s $MROOT/mathlib.ndjson) avail_kb=$(awk '/^MemAvailable/ {print $2}' /proc/meminfo)" >> $SP/export.monitor
    if [ "$KB" -gt "$LIMIT_KB" ]; then
      echo "LIMIT EXCEEDED: killing leanexport pid $LPID" >> $SP/export.monitor
      kill "$LPID"
    fi
  fi
  sleep 2
done
wait $TPID
echo "exit $?" >> $SP/export.monitor
echo "monitor max rss_kb=$MAXKB" >> $SP/export.monitor
date -Is > $SP/export.end
