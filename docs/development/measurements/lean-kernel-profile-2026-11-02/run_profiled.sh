#!/bin/bash
# run_profiled.sh NAME LIMIT_MIB [--perf FREQ] [--mathlib] -- command args...
#
# Times one command with GNU time under the RSS watchdog (watch.py), optionally
# under `perf record` with DWARF stack copies (32 KiB per sample), and with
# LEAN_PATH set to the pinned Mathlib checkout (--mathlib). Uses the pinned
# toolchain binaries directly (never the elan proxies).
# Output goes to $OUT (default: ./out): NAME.{time,watch,stdout,stderr,perf.data}.
# Example: run_profiled.sh init-fresh 8000 --perf 499 -- leanchecker --fresh Init
here=$(cd "$(dirname "$0")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
tc=$root/.tools/elan/toolchains/leanprover--lean4---v4.35.0
export PATH=$tc/bin:/usr/lib/linux-tools/$(uname -r)/bin:/usr/bin:/bin
out=${OUT:-$PWD/out}
name=$1; limit=$2; shift 2
perf=()
if [ "$1" = "--perf" ]; then
  perf=(perf record -F "$2" --call-graph dwarf,32768 -o "$out/$name.perf.data" --)
  shift 2
fi
if [ "$1" = "--mathlib" ]; then
  ml=$root/.tools/mathlib/mathlib4
  LEAN_PATH=$ml/.lake/build/lib/lean
  for d in "$ml"/.lake/packages/*/.lake/build/lib/lean; do LEAN_PATH=$LEAN_PATH:$d; done
  export LEAN_PATH
  shift
fi
[ "$1" = "--" ] && shift
mkdir -p "$out"
python3 -I "$here/watch.py" "$limit" "$out/$name.watch" -- \
  /usr/bin/time -v -o "$out/$name.time" "${perf[@]}" "$@" \
  > "$out/$name.stdout" 2> "$out/$name.stderr"
status=$?
grep -E 'Elapsed|Maximum resident|User time|System time|Exit status' "$out/$name.time"
exit $status
