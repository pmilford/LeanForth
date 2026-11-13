#!/usr/bin/env bash
# with-scratch.sh COMMAND [ARGUMENT]...: run COMMAND with LF_TEST_SCRATCH
# naming a new, empty folder of its own (mktemp -d), and remove that folder
# afterwards; the exit status is COMMAND's. For the Forth tests that write
# scratch files (tests/support/scratch.fs): the same test run at the same
# moment by another worktree or another make writes into another folder.
set -u
dir=$(mktemp -d "${TMPDIR:-/tmp}/lf-test-scratch.XXXXXX") || exit 1
trap 'rm -rf -- "$dir"' EXIT
LF_TEST_SCRATCH=$dir "$@"
status=$?
exit "$status"
