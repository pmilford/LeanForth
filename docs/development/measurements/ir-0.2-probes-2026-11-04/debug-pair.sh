#!/bin/bash
# IR 0.2 probe 6 (ADR 0019 Amendment 1): insert p06-debug-pair.lean into a
# copy of tests/reference/program-ir.lean, just before the end of its
# Part 3 (the first "end ProgramIR"), and check the copy with Lean.
#   bash docs/development/measurements/ir-0.2-probes-2026-11-04/debug-pair.sh LEAN
# LEAN is the pinned Lean 4.35.0 binary, for example
# .tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean.
# With a second argument "fault", `.` is planted as doing nothing to the
# stack (the pair becomes a lone `dup`), and Lean must reject the proof.
# Run from the repository root.
set -eu
lean=$(realpath "$1")
fault=${2:-}
here=$(dirname "$0")
work=$(mktemp -d)
trap 'rm -f "$work/program-ir-debug.lean"; rmdir "$work"' EXIT
python3 -I - "$here/p06-debug-pair.lean" tests/reference/program-ir.lean \
  "$work/program-ir-debug.lean" "$fault" <<'EOF'
import sys
snippet, source, target, fault = sys.argv[1:]
text = open(source, encoding="utf-8").read()
marker = "\nend ProgramIR\n"
at = text.index(marker)
insert = open(snippet, encoding="utf-8").read()
if fault == "fault":
    pair = ".prim .dup, .prim .drop,"
    assert insert.count(pair) == 1
    insert = insert.replace(pair, ".prim .dup,")
open(target, "w", encoding="utf-8").write(text[:at] + "\n" + insert + text[at:])
EOF
status=0
out=$("$lean" "$work/program-ir-debug.lean") || status=$?
echo "lean exit: $status; errors: $(grep -c 'error' <<<"$out" || true)"
grep 'clampDebug_correct' <<<"$out" || true
