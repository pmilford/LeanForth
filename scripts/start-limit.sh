# Sourced by bin/leanforth and scripts/gforth-strict.sh (POSIX sh; nothing here
# starts a process). lf_start_report WHO STATUS explains, on standard error, a
# Gforth that could not be started: status 254 is bash's own when it could not
# fork (a process refused, normally under `ulimit -u`, which counts every
# thread of the user, other programs' job pools included), 126 and 127 an exec
# that failed. It adds the user's threads, counted from /proc with the shell's
# own READ, and the process limit, so that an intermittent refusal explains
# itself (review lib-tidy, note 9: an exit 5 seen once under coverage).
# Status 0 when it reported, 1 for any other status (nothing printed).

# lf_user_threads: sets lf_threads to the threads of the user running this
# shell, and lf_nproc to its process limit (soft), both "?" where /proc does
# not tell.
lf_user_threads() {
  lf_uid=? lf_threads=? lf_nproc=?
  [ -r /proc/self/status ] || return 0
  while read -r lf_k lf_v lf_rest; do
    if [ "$lf_k" = Uid: ]; then lf_uid=$lf_v; fi
  done </proc/self/status
  if [ -r /proc/self/limits ]; then
    while read -r lf_a lf_b lf_soft lf_rest; do
      if [ "$lf_a $lf_b" = "Max processes" ]; then lf_nproc=$lf_soft; fi
    done </proc/self/limits
  fi
  lf_threads=0
  for lf_f in /proc/[0-9]*/status; do
    lf_u= lf_t=0
    { while read -r lf_k lf_v lf_rest; do
        case $lf_k in Uid:) lf_u=$lf_v ;; Threads:) lf_t=$lf_v ;; esac
      done <"$lf_f"; } 2>/dev/null
    if [ "$lf_u" = "$lf_uid" ]; then lf_threads=$((lf_threads + lf_t)); fi
  done
  return 0
}

lf_start_report() {
  case $2 in
    254) lf_why="resource limit (a process could not be started)" ;;
    126 | 127) lf_why="exec failed (status $2)" ;;
    *) return 1 ;;
  esac
  lf_user_threads
  printf '%s: could not start Gforth: %s; the user has %s threads, process limit %s\n' \
    "$1" "$lf_why" "$lf_threads" "$lf_nproc" >&2
  return 0
}
