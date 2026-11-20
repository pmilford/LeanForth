# Sourced by bin/leanforth and bin/leanforth-checker (bash), after they set
# root (the checkout), lf_entry (the Forth file that loads the command line:
# src/main.fs, or src/load/cli-checker.fs) and the EXIT trap, and read
# scripts/start-limit.sh, and set GFORTH_ENV=off: verify, the engine chosen,
# the arguments that name one file, the commit, the run of the command line,
# and its exit status. It was bin/leanforth's own until 2026-11-19 (branch
# layered-loads); the two launchers differ only in what they load.

# verify (plan 8.4.1c): checking a Forth word against its contract runs the driver
# scripts/program_verify.py, which needs Python 3 and the pinned Lean 4.35.0 (the owner
# allowed both for V1 only, 2026-11-13) and starts this command's check itself. Its exit
# status is the CLI's, 0 to 6; any other (Python missing, a crash of the interpreter) is
# an internal fault, 5, never a verdict.
if [ "${1:-}" = verify ]; then
  shift
  python3 -I "$root/scripts/program_verify.py" "$@" </dev/null
  status=$?
  case $status in
    0 | 1 | 2 | 3 | 4 | 5 | 6) exit "$status" ;;
    *) printf 'error: internal: leanforth verify ended with status %s\n' "$status"; exit 5 ;;
  esac
fi

# The engine of check, replay or print: an argument --fast or --checked.
# Which options take a value is known only to the Forth side
# (src/cli/leanforth.fs, cli-option-table), which also refuses both
# together; a value spelled --checked (--record --checked) only changes the
# engine, never a verdict.
fast=false
checked=false
case ${1:-} in
  check | replay | print)
    for argument in "${@:2}"; do
      case $argument in
        --fast) fast=true ;;
        --checked) checked=true ;;
      esac
    done
    ;;
esac
# Default engine: gforth-fast for every command but with --checked.
engine=gforth-fast
if $checked; then engine=gforth; fi
# The engine named, from this checkout's tools or the PATH.
find_engine() {
  if [ -x "$root/.tools/gforth/bin/$1" ]; then
    printf '%s' "$root/.tools/gforth/bin/$1"
  elif command -v "$1" >/dev/null 2>&1; then
    printf '%s' "$1"
  else
    return 1
  fi
}
no_fast() {
  printf 'leanforth: note: no %s found; checking with %s\n' "$1" "$2" >&2
}
# The fast engine beside GFORTH: the gforth-fast in its folder (for the
# Makefile's scripts/gforth-strict.sh, scripts/gforth-fast), or on PATH
# for a GFORTH without a folder; GFORTH itself when it is a gforth-fast.
beside_fast() {
  case ${GFORTH##*/} in
    gforth-fast*) printf '%s' "$GFORTH" ;;
    *) case $GFORTH in
         */*) printf '%s' "${GFORTH%/*}/gforth-fast" ;;
         *) printf '%s' gforth-fast ;;
       esac ;;
  esac
}
if [ -n "${GFORTH:-}" ]; then
  if $fast; then
    candidate=$(beside_fast)
    if command -v "$candidate" >/dev/null 2>&1; then
      GFORTH=$candidate
    else
      no_fast "$candidate" "$GFORTH"
    fi
  fi
elif GFORTH=$(find_engine "$engine"); then
  :
elif GFORTH=$(find_engine gforth); then
  if [ "$engine" = gforth-fast ]; then no_fast gforth-fast "$GFORTH"; fi
else
  printf 'leanforth: internal fault: no Gforth found; %s\n' \
    'run scripts/install-gforth.sh or set GFORTH' >&2
  exit 5
fi
LEANFORTH_ENGINE=${GFORTH##*/}
export LEANFORTH_ENGINE

# The arguments that name one existing file (test -ef: the same device and
# inode, through symbolic links and relative names), as " I:J " pairs of
# their indices, the command 0 and I < J, in LEANFORTH_SAME_FILES, and as
# " Im:J " when the manifest an export argument I would have
# (I.manifest.json, read with it) is argument J, and " Ip:J " when
# I.partial (written first by --save-snapshot I, then renamed) is argument
# J. The Forth side, which
# alone knows each option's role, refuses a file written that is one read
# or written by another argument (cli-same-file?), exit 4, before anything
# runs.
same=' '
arguments=("$@")
for ((i = 1; i < ${#arguments[@]}; i++)); do
  manifest="${arguments[i]}.manifest.json" partial="${arguments[i]}.partial"
  for ((j = 1; j < ${#arguments[@]}; j++)); do
    if [ "$j" != "$i" ] && [ -e "$manifest" ] && [ "$manifest" -ef "${arguments[j]}" ]; then
      same+="${i}m:$j "
    fi
    if [ "$j" != "$i" ] && [ -e "$partial" ] && [ "$partial" -ef "${arguments[j]}" ]; then
      same+="${i}p:$j "
    fi
    if [ "$j" -gt "$i" ] && [ -e "${arguments[i]}" ] &&
       [ "${arguments[i]}" -ef "${arguments[j]}" ]; then same+="$i:$j "; fi
  done
done
export LEANFORTH_SAME_FILES=$same

# The checkout's git commit, and whether tracked files differ from it, for
# version and for the run record (check --record, replay); none outside a
# git checkout.
commit= modified=false
case ${1:-} in
  check | replay | version | --version)
    commit=$(git -C "$root" rev-parse HEAD 2>/dev/null) || commit=
    if [ -n "$commit" ] && ! git -C "$root" diff --quiet HEAD 2>/dev/null; then
      modified=true
    fi
    ;;
esac
export LEANFORTH_COMMIT=$commit LEANFORTH_MODIFIED=$modified

"$GFORTH" "$lf_entry" -e cli-main "$@" </dev/null
status=$?
case $status in
  10[0-6]) code=$((status - 100)) ;;
  *)
    # A Gforth that never started (a wrapper's fork refused, 254; an exec
    # that failed, 126 or 127) is said as such; any other status is Gforth's.
    lf_start_report "leanforth: internal fault" "$status" ||
      printf 'leanforth: internal fault: Gforth ended with status %s\n' "$status" >&2
    exit 5
    ;;
esac

if [ "$code" -eq 0 ] && { [ "${1:-}" = version ] || [ "${1:-}" = --version ]; }; then
  if [ -z "$commit" ]; then
    printf 'commit: unknown (not a git checkout)\n'
  elif $modified; then
    printf 'commit: %s (with local changes)\n' "$commit"
  else
    printf 'commit: %s\n' "$commit"
  fi
fi
exit "$code"
