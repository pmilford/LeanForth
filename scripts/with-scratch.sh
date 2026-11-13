#!/usr/bin/env bash
# with-scratch.sh COMMAND [ARGUMENT]...: run COMMAND with LF_TEST_SCRATCH
# naming a new, empty folder of its own (mktemp -d), and remove that folder
# afterwards; the exit status is COMMAND's. For the Forth tests that write
# scratch files (tests/support/scratch.fs): the same test run at the same
# moment by another worktree or another make writes into another folder.
# The folder is also removed when the script is stopped by SIGTERM (make's
# timeout, which signals the command's whole process group), SIGINT or
# SIGHUP: bash runs no EXIT trap on a signal it does not trap, so each is
# trapped and turned into an exit with the shell's status for it.
set -u
dir=$(mktemp -d "${TMPDIR:-/tmp}/lf-test-scratch.XXXXXX") || exit 1
trap 'rm -rf -- "$dir"' EXIT
trap 'exit 143' TERM
trap 'exit 130' INT
trap 'exit 129' HUP
LF_TEST_SCRATCH=$dir "$@"
status=$?
exit "$status"
