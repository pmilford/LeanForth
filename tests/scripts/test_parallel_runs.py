"""tests/support/parallel_runs.py: results in input order, failures reported as the serial run
reports them, jobs=1 exactly a plain loop, the jobs variable.

Usage (from the repository root): python3 tests/scripts/test_parallel_runs.py
"""
import pathlib
import subprocess
import sys
import threading
import time
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tests/support"))
import parallel_runs  # noqa: E402
from parallel_runs import job_count, run_all  # noqa: E402

PYTHON = sys.executable


def sleeper(seconds, code=0, text="x"):
    """A python command that sleeps, prints text and exits with code."""
    return [PYTHON, "-c", f"import sys,time; time.sleep({seconds}); print({text!r}); sys.exit({code})"]


class Order(unittest.TestCase):
    def test_results_follow_the_input_order_not_the_finishing_order(self):
        commands = [sleeper(0.6, text="slow"), sleeper(0.0, text="fast"), sleeper(0.2, text="mid")]
        got = [done.stdout.strip() for done in run_all(commands, jobs=3)]
        self.assertEqual(got, ["slow", "fast", "mid"])

    def test_equal_to_the_serial_run_for_each_jobs(self):
        commands = [sleeper(0.0, code=n % 3, text=str(n)) for n in range(9)]
        serial = [(d.returncode, d.stdout) for d in run_all(commands, jobs=1)]
        for jobs in (2, 4, 16):
            self.assertEqual([(d.returncode, d.stdout) for d in run_all(commands, jobs=jobs)], serial)

    def test_empty_and_single(self):
        self.assertEqual(list(run_all([], jobs=4)), [])
        self.assertEqual([d.stdout for d in run_all([sleeper(0, text="one")], jobs=4)], ["one\n"])

    def test_a_custom_runner_and_commands_of_any_kind(self):
        self.assertEqual(list(run_all(range(6), jobs=3, run=lambda n: n * n)), [0, 1, 4, 9, 16, 25])

    def test_at_most_jobs_at_once_and_really_side_by_side(self):
        lock, state = threading.Lock(), {"now": 0, "peak": 0}

        def run(_):
            with lock:
                state["now"] += 1
                state["peak"] = max(state["peak"], state["now"])
            time.sleep(0.05)
            with lock:
                state["now"] -= 1

        list(run_all(range(12), jobs=3, run=run))
        self.assertEqual(state["peak"], 3)


class Failures(unittest.TestCase):
    def test_a_nonzero_exit_is_a_result_not_an_error(self):
        done = list(run_all([sleeper(0, code=7), sleeper(0, code=0)], jobs=2))
        self.assertEqual([d.returncode for d in done], [7, 0])

    def test_an_exception_is_raised_at_its_place_after_the_results_before_it(self):
        def run(n):
            if n == 2:
                raise subprocess.TimeoutExpired("cmd", 1)
            return n

        for jobs in (1, 4):
            seen = []
            with self.assertRaises(subprocess.TimeoutExpired):
                for result in run_all(range(5), jobs=jobs, run=run):
                    seen.append(result)
            self.assertEqual(seen, [0, 1], f"jobs={jobs}")

    def test_the_first_failure_in_order_wins_over_an_earlier_finishing_later_one(self):
        def run(n):
            if n == 1:
                time.sleep(0.3)
                raise ValueError("first")
            if n == 3:
                raise KeyError("later")
            return n

        with self.assertRaises(ValueError):
            list(run_all(range(5), jobs=5, run=run))

    def test_a_missing_program_raises_like_subprocess_run(self):
        for jobs in (1, 3):
            with self.assertRaises(FileNotFoundError):
                list(run_all([["/nonexistent/program-for-test"]], jobs=jobs))

    def test_stopping_early_cancels_the_commands_not_started(self):
        started = []

        def run(n):
            started.append(n)
            time.sleep(0.2)
            return n

        results = run_all(range(30), jobs=2, run=run)
        self.assertEqual(next(results), 0)
        results.close()
        self.assertLess(len(started), 30)


class Serial(unittest.TestCase):
    def test_jobs_one_runs_lazily_in_a_plain_loop(self):
        started = []

        def run(n):
            started.append(n)
            return n

        results = run_all(range(5), jobs=1, run=run)
        self.assertEqual(started, [])
        self.assertEqual(next(results), 0)
        self.assertEqual(started, [0])
        self.assertEqual(next(results), 1)
        self.assertEqual(started, [0, 1])

    def test_jobs_zero_or_negative_is_serial(self):
        self.assertEqual(list(run_all(range(3), jobs=0, run=lambda n: n)), [0, 1, 2])
        self.assertEqual(list(run_all(range(3), jobs=-5, run=lambda n: n)), [0, 1, 2])


class Jobs(unittest.TestCase):
    def test_the_variable(self):
        name = parallel_runs.JOBS_VARIABLE
        self.assertEqual(job_count({name: "1"}), 1)
        self.assertEqual(job_count({name: " 7 "}), 7)

    def test_unset_or_bad_gives_the_default_capped_by_the_cores(self):
        name = parallel_runs.JOBS_VARIABLE
        want = job_count({})
        self.assertTrue(1 <= want <= parallel_runs.DEFAULT_JOBS)
        for bad in ("", "0", "-2", "many", "2.5"):
            self.assertEqual(job_count({name: bad}), want, bad)

    def test_the_default_on_a_machine_with_few_cores(self):
        real = parallel_runs.os.cpu_count
        try:
            for cores, want in ((1, 1), (2, 2), (10, 4), (None, 1)):
                parallel_runs.os.cpu_count = lambda cores=cores: cores
                self.assertEqual(job_count({}), want, cores)
        finally:
            parallel_runs.os.cpu_count = real


class DefaultRun(unittest.TestCase):
    def test_standard_input_is_closed_and_output_is_text(self):
        done = parallel_runs.default_run([PYTHON, "-c", "import sys; print(repr(sys.stdin.read()))"])
        self.assertEqual((done.returncode, done.stdout), (0, "''\n"))

    def test_timeout_raises(self):
        with self.assertRaises(subprocess.TimeoutExpired):
            parallel_runs.default_run(sleeper(5), timeout=0.2)


if __name__ == "__main__":
    unittest.main()
