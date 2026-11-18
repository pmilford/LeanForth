#!/bin/bash
# The proof set, annotated (plan S2, branch s2-steps): each theorem file of
# S1's and S2's proof set checked by `bin/leanforth check ... --steps -`,
# printed as its text, then each checked step with its goals before and
# after (the step log, docs/user/COMMAND_LINE.md "The step log"), then
# LeanForth's verdict lines and the exit status.
#
# Usage: scripts/showcase-steps.sh [FILE.lf ...]
#   With no file, the proof set: s1-rfl.lf, 03-zero-add-exact.lf,
#   01-zero-add-rw.lf, 04-nested-ih.lf, ps-*.lf and S2 merge B's midpoint
#   files 00-add-zero.lf (a term proof: no steps) and 02-add-zero-rfl.lf.
#   SHOWCASE_LIBRARY: the library options, by default S2's slice of Init
#   (--env tests/front/s2-slice.ndjson --elab-data
#   tests/front/s2-slice.elab.ndjson, a few seconds a file); for all of
#   Init through a snapshot, about 75 s a file:
#     SHOWCASE_LIBRARY="--snapshot init.lfsnap --elab-data init.elab.ndjson"
# Exit status: 0 when every file exits 0, else 1. Read-only: it writes
# nothing but standard output.
set -u
cd "$(dirname "$0")/.." || exit 1
ulimit -u 500
library=${SHOWCASE_LIBRARY:-"--env tests/front/s2-slice.ndjson --elab-data tests/front/s2-slice.elab.ndjson"}
if [ $# -eq 0 ]; then
  set -- tests/front/s1-rfl.lf tests/front/03-zero-add-exact.lf tests/front/01-zero-add-rw.lf \
    tests/front/04-nested-ih.lf tests/front/ps-succ-add.lf tests/front/ps-add-comm.lf \
    tests/front/ps-mul-add.lf tests/front/ps-length-append.lf tests/front/00-add-zero.lf \
    tests/front/02-add-zero-rfl.lf
fi
# The step lines, laid out: a declaration's name, then each step's word,
# place and parent, its goal before and its goals after, indented.
format='
import json, sys
def goal(text, lead):
    return "\n".join(lead + line for line in text.splitlines())
for line in sys.stdin:
    record = json.loads(line)
    if "tactic_steps" in record:
        head = record["tactic_steps"]
        name, count = head["declaration"], head["steps"]
        print(f"  theorem {name}: {count} checked steps")
        continue
    step, word, tactic, source = record["step"], record["word"], record["tactic"], record["source"]
    parent = record["parent"]
    inside = f", in step {parent}" if parent else ""
    print(f"  step {step}: {word} ({tactic}) at line:col {source}{inside}")
    if record["goal_before"] is not None:
        print("    before:")
        print(goal(record["goal_before"], "      "))
    after = record["goals_after"]
    print("    after: " + ("no goals" if not after else f"{len(after)} goal(s)"))
    for text in after:
        print(goal(text, "      "))
'
status=0
for file in "$@"; do
  echo "=== $file"
  grep -v '^\\' "$file" | grep -v '^ *$'
  # shellcheck disable=SC2086
  out=$(bin/leanforth check $library --steps - "$file" </dev/null 2>&1)
  code=$?
  printf '%s\n' "$out" | grep '^{' | python3 -c "$format" || status=1
  # The file's own theorems' verdicts (the library's come first), or the error.
  for name in $(grep -oE '^theorem +[^ ]+' "$file" | awk '{print $2}'); do
    printf '%s\n' "$out" | grep -F -- "$name: " | grep -v '^{' | tail -1
  done
  printf '%s\n' "$out" | grep '^error'
  echo "--- exit $code"
  [ "$code" -eq 0 ] || status=1
done
exit $status
