#!/bin/bash
# The proof set, annotated (plan S2, branch s2-steps): each theorem file of
# S1's and S2's proof set checked by `bin/leanforth check ... --steps -`, and
# for each theorem its LeanForth text, its statement as Lean prints the first
# goal, each checked step with the goal before and the goals after as the
# step log gives them (docs/user/COMMAND_LINE.md "The step log"), and its
# verdict; then the run's errors, summary line and exit status. The layout is
# scripts/showcase-steps-format.py's; tests/front/showcase.golden is the
# output on the S2 slice (make test-showcase).
#
# Usage: scripts/showcase-steps.sh [FILE.lf ...]
#   With no file, the proof set: s1-rfl.lf, 03-zero-add-exact.lf,
#   01-zero-add-rw.lf, 04-nested-ih.lf, ps-*.lf and S2 merge B's midpoint
#   files 00-add-zero.lf (a term proof: no steps) and 02-add-zero-rfl.lf.
#   SHOWCASE_LIBRARY: the library options, by default S2's slice of Init
#   (--env tests/front/s2-slice.ndjson --elab-data
#   tests/front/s2-slice.elab.ndjson, about a second a file); for all of
#   Init through a snapshot, about 80 s a file:
#     SHOWCASE_LIBRARY="--snapshot init.lfsnap --elab-data init.elab.ndjson"
#   File names are taken from the checkout's root. GFORTH names the engine
#   as for bin/leanforth.
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
status=0
for file in "$@"; do
  # shellcheck disable=SC2086
  out=$(bin/leanforth check $library --steps - "$file" </dev/null 2>&1)
  code=$?
  printf '%s\n' "$out" | python3 scripts/showcase-steps-format.py "$file" "$code" || status=1
  echo
  [ "$code" -eq 0 ] || status=1
done
exit $status
