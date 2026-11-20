"""Independent subprocess cases of a test runner, run side by side, results in order.

The slow Python runners (tests/front/check_s2.py, check_tactics.py, check_showcase.py and the
tactic runners of tests/front/tactics/) start one fresh `bin/leanforth` or Gforth process for each
.lf file, wrong proof or case. The cases do not depend on each other, so a runner builds the list
of its commands, runs them through run_all, and then reads the results one by one in the order of
the list: its messages, golden comparisons and failure reports are those of the serial run.

    from parallel_runs import run_all
    for command, done in zip(commands, run_all(commands)):
        if done.returncode != 0:
            raise Failure(...)

run_all(commands, jobs=None, run=default_run) -> an iterator of run(command), in the order of
commands:
  jobs 1     each command runs when its result is asked for, exactly as in a plain loop: a runner that
             stops at the first failure never starts the later commands.
  jobs > 1   at most jobs commands at once, all submitted up front; the result of the n-th command
             is yielded after those of the commands before it. An exception that run raised (a
             timeout, a missing program) is raised when its result is asked for, so the first
             failure in the order is the one reported, as in the serial run; when the caller stops
             early, the commands not yet started are cancelled and the running ones are waited for.
A command is whatever `run` takes, by default an argument list for subprocess.run with the
standard input closed and the output captured as text.

Only cases that share nothing belong in one run_all: no temporary file written by two of them, no
cache folder written while another reads it, no case that reads what an earlier one wrote.

job_count() is the number of jobs: the environment variable LEANFORTH_TEST_JOBS when it is a whole
number of at least 1, else min(DEFAULT_JOBS, the machine's cores). The default is 4 because each case
may itself start several processes and the runs go under `ulimit -u 500`.

Usage (from the repository root): python3 tests/scripts/test_parallel_runs.py
"""
import concurrent.futures
import os
import subprocess

DEFAULT_JOBS = 4
JOBS_VARIABLE = "LEANFORTH_TEST_JOBS"


def job_count(environ=None):
    """The number of cases to run at once: $LEANFORTH_TEST_JOBS (1 or more), else min(4, cores)."""
    text = (os.environ if environ is None else environ).get(JOBS_VARIABLE, "").strip()
    if text.isdigit() and int(text) >= 1:
        return int(text)
    return max(1, min(DEFAULT_JOBS, os.cpu_count() or 1))


def default_run(command, cwd=None, env=None, timeout=None):
    """subprocess.run of an argument list: standard input closed, output captured as text."""
    return subprocess.run(command, cwd=cwd, env=env, stdin=subprocess.DEVNULL,
                          capture_output=True, text=True, timeout=timeout)


def run_all(commands, jobs=None, run=default_run):
    """run(command) for each of commands, at most jobs at once; an iterator in input order."""
    commands = list(commands)
    jobs = job_count() if jobs is None else jobs
    if jobs <= 1 or len(commands) <= 1:
        return (run(command) for command in commands)
    return _ordered(commands, min(jobs, len(commands)), run)


def _ordered(commands, jobs, run):
    pool = concurrent.futures.ThreadPoolExecutor(max_workers=jobs)
    try:
        futures = [pool.submit(run, command) for command in commands]
        for future in futures:
            yield future.result()
    finally:
        pool.shutdown(wait=True, cancel_futures=True)
