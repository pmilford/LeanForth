#!/usr/bin/env python3
"""Run a command, sample the summed RSS of its process tree, kill it past a limit.

Usage: watch.py LIMIT_MIB LOGFILE -- command args...
Writes peak tree RSS, wall time and exit status to LOGFILE (and stderr).
Kills only the PIDs it started (the tree below the child), one by one.
"""
import os, signal, subprocess, sys, time


def tree(root):
    kids = {}
    for p in os.listdir('/proc'):
        if not p.isdigit():
            continue
        try:
            with open(f'/proc/{p}/stat') as f:
                parts = f.read().rsplit(')', 1)[1].split()
            kids.setdefault(int(parts[1]), []).append(int(p))
        except OSError:
            pass
    out, todo = [], [root]
    while todo:
        q = todo.pop()
        out.append(q)
        todo.extend(kids.get(q, []))
    return out


def rss_kib(pid):
    try:
        with open(f'/proc/{pid}/status') as f:
            for line in f:
                if line.startswith('VmRSS:'):
                    return int(line.split()[1])
    except OSError:
        pass
    return 0


def main():
    limit = int(sys.argv[1]) * 1024
    log = sys.argv[2]
    assert sys.argv[3] == '--'
    cmd = sys.argv[4:]
    t0 = time.time()
    proc = subprocess.Popen(cmd, stdin=subprocess.DEVNULL)
    peak, peak_pid_rss, killed = 0, {}, False
    while proc.poll() is None:
        pids = tree(proc.pid)
        total = 0
        for q in pids:
            r = rss_kib(q)
            total += r
            peak_pid_rss[q] = max(peak_pid_rss.get(q, 0), r)
        peak = max(peak, total)
        if total > limit and not killed:
            killed = True
            for q in reversed(pids):
                try:
                    os.kill(q, signal.SIGKILL)
                except OSError:
                    pass
        time.sleep(0.5)
    wall = time.time() - t0
    msg = (f'cmd={" ".join(cmd)}\nexit={proc.returncode} wall_s={wall:.1f} '
           f'peak_tree_rss_kib={peak} max_single_rss_kib={max(peak_pid_rss.values() or [0])} '
           f'killed_at_limit={killed} limit_kib={limit}\n')
    with open(log, 'a') as f:
        f.write(msg)
    sys.stderr.write(msg)
    sys.exit(proc.returncode if proc.returncode >= 0 else 128 - proc.returncode)


main()
