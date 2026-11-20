#!/usr/bin/env python3
"""Tests of scripts/check-layers.py and of what scripts/tested-tree.py reads through the layer
entries of src/load/ (make check-layers).

CheckLayers: the check on small trees of its own: a clean tree passes; an entry that loads a
higher layer, the checker loading more of present/ than the run records' name text, a library
loading the data model, the data model loading the kernel, src/main.fs loading a module through
no entry, a test requiring src/main.fs outside WHOLE_LOADS, a stale WHOLE_LOADS row, a Gforth
that loads a file the closure lacks and a Gforth that fails each fail, naming the file.

Tracing: on a throw-away repository shaped like LeanForth's (tests/scripts/tier_fixture.py)
whose tests load entries: a target's inputs are the closure of the entry it loads (through
the entry, the module and the module's own requires) and its test files, never the other
layers; a recorded pass of the kernel's test is reused after a front-end change and not after
a change of its module, of a file two requires down or of its entry, and the front end's test
is not reused after a front-end change."""
# inputs: fixtures only: git, the home folder and the scripts' records here are those of the
# repositories tier_fixture.Repo makes (scripts/changed-tests.py, FIXTURES_ONLY).
import importlib.util
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
import tier_fixture  # noqa: E402

spec = importlib.util.spec_from_file_location("check_layers", ROOT / "scripts" / "check-layers.py")
check_layers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check_layers)
spec = importlib.util.spec_from_file_location("test_tier", ROOT / "scripts" / "test-tier.py")
test_tier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(test_tier)

TREE = {
    "src/lib/l.fs": ": l ;\n",
    "src/core/c.fs": "require ../lib/l.fs\n",
    "src/kernel/k.fs": "require ../core/c.fs\n",
    "src/import/i.fs": "require ../core/c.fs\n",
    "src/present/name-text.fs": "require ../core/c.fs\n",
    "src/present/p.fs": "require ./name-text.fs\n",
    "src/author/a.fs": "require ../present/p.fs\n",
    "src/front/f.fs": "require ../author/a.fs\nrequire ../import/i.fs\n",
    "src/program/g.fs": "require ../lib/l.fs\n",
    "src/cli/x.fs": "require ../load/checker.fs\n",
    "src/cli/t.fs": "require ./x.fs\nrequire ../front/f.fs\n",
    "src/load/cli-checker.fs": "require ./checker.fs\nrequire ../cli/x.fs\n",
    "src/load/cli.fs": "require ../cli/x.fs\nrequire ../cli/t.fs\n",
    "src/load/kernel.fs": "require ../kernel/k.fs\n",
    "src/load/import.fs": "require ../import/i.fs\n",
    "src/load/checker.fs": "require ./kernel.fs\nrequire ./import.fs\nrequire ../present/name-text.fs\n",
    "src/load/program.fs": "require ../program/g.fs\n",
    "src/load/present.fs": "require ../present/p.fs\n",
    "src/load/front.fs": "require ../front/f.fs\n",
    "src/main.fs": "require ./load/checker.fs\nrequire ./load/program.fs\nrequire ./load/present.fs\n"
                   "require ./load/front.fs\nrequire ./load/cli.fs\n",
    "tests/core/t.fs": "require ../../src/load/kernel.fs\n",
}
TREE.update({path: "require ../../src/main.fs\n" for path in check_layers.WHOLE_LOADS})

STUB = "#!/bin/sh\n[ \"$2\" = -e ] || exit 3\necho \"$1\"\necho src/lib/l.fs\n%s\n"


class CheckLayers(unittest.TestCase):
    def setUp(self):
        self.top = tempfile.mkdtemp(prefix="lf-layers-test-")
        for name, text in TREE.items():
            self.write(name, text)

    def tearDown(self):
        shutil.rmtree(self.top, ignore_errors=True)

    def write(self, name, text):
        path = pathlib.Path(self.top, name)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def run_check(self, *args):
        return subprocess.run([sys.executable, str(ROOT / "scripts" / "check-layers.py"), "--root", self.top, *args],
                              stdin=subprocess.DEVNULL, capture_output=True, text=True)

    def fails(self, *needles, args=()):
        run = self.run_check(*args)
        self.assertEqual(run.returncode, 1, run.stdout + run.stderr)
        for needle in needles:
            self.assertIn(needle, run.stderr)
        return run.stderr

    def test_clean_tree_passes(self):
        run = self.run_check()
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertIn("8 layer entries keep to their layers", run.stdout)

    def test_kernel_loading_the_front_end_fails(self):
        self.write("src/kernel/k.fs", "require ../core/c.fs\nrequire ../front/f.fs\n")
        err = self.fails("src/load/kernel.fs loads src/front/f.fs", "src/load/checker.fs loads src/author/a.fs")
        self.assertNotIn("src/load/front.fs", err)

    def test_the_command_line_of_exports_loading_the_text_part_fails(self):
        self.write("src/load/cli-checker.fs", "require ./checker.fs\nrequire ../cli/t.fs\n")
        self.fails("src/load/cli-checker.fs loads src/front/f.fs", "src/load/cli-checker.fs loads src/author/a.fs")

    def test_a_require_in_a_comment_counts(self):
        self.write("src/program/g.fs", "require ../lib/l.fs\n\\ require ../core/c.fs\n")
        self.fails("src/load/program.fs loads src/core/c.fs")

    def test_checker_loads_only_the_name_text_of_present(self):
        self.write("src/import/i.fs", "require ../core/c.fs\nrequire ../present/p.fs\n")
        self.fails("src/load/checker.fs loads src/present/p.fs: the checker loads of present/ only",
                   "src/load/import.fs loads src/present/p.fs")

    def test_an_entry_loading_a_file_of_src_load_that_is_no_entry_fails(self):
        self.write("src/load/extra.fs", "require ../lib/l.fs\n")
        self.write("src/load/program.fs", "require ../program/g.fs\nrequire ./extra.fs\n")
        self.fails("src/load/program.fs loads src/load/extra.fs, which is no entry")

    def test_a_missing_entry_fails(self):
        os.remove(os.path.join(self.top, "src/load/present.fs"))
        self.fails("src/load/present.fs is missing")

    def test_library_and_data_model_rules(self):
        self.write("src/lib/l.fs", "require ../core/c.fs\n")
        self.write("src/core/c.fs", "require ../lib/l.fs\nrequire ../kernel/k.fs\n")
        self.fails("src/lib/l.fs loads src/core/c.fs: src/lib uses only lib",
                   "src/core/c.fs loads src/kernel/k.fs: src/core uses only core, lib")

    def test_main_loading_a_module_through_no_entry_fails(self):
        self.write("src/program/h.fs", ": h ;\n")
        self.write("src/main.fs", TREE["src/main.fs"] + "require ./program/h.fs\n")
        self.fails("src/main.fs loads src/program/h.fs through no entry")

    def test_a_test_requiring_main_outside_the_list_fails(self):
        self.write("tests/core/t.fs", "\\ a test\nrequire ../../src/main.fs\n")
        self.fails("tests/core/t.fs requires src/main.fs: require the entries")

    def test_a_stale_row_of_the_list_fails(self):
        some = sorted(check_layers.WHOLE_LOADS)[0]
        self.write(some, "require ../../src/load/kernel.fs\n")
        self.fails(f"{some} is listed in WHOLE_LOADS but is missing or does not require src/main.fs")
        os.remove(os.path.join(self.top, some))
        self.fails(f"{some} is listed in WHOLE_LOADS")

    def stub(self, extra):
        path = os.path.join(self.top, "gforth-stub")
        with open(path, "w", encoding="utf-8") as stream:
            stream.write(STUB % extra)
        os.chmod(path, 0o755)
        return path

    def test_gforth_within_the_closure_passes(self):
        run = self.run_check("--gforth", self.stub(""))
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertIn("Gforth loads each alone within its closure", run.stdout)

    def test_gforth_loading_more_than_the_closure_fails(self):
        err = self.fails("src/load/kernel.fs: Gforth loads src/front/f.fs, which its closure lacks",
                         args=("--gforth", self.stub("echo src/front/f.fs")))
        self.assertNotIn("src/load/front.fs: Gforth loads", err)

    def test_gforth_failing_or_complaining_fails(self):
        self.fails("src/load/kernel.fs: Gforth exited 4", args=("--gforth", self.stub("exit 4")))
        self.fails("Gforth exited 0", args=("--gforth", self.stub("echo redefined >&2")))

    def test_the_repository_passes(self):
        """The real tree, statically (make check-layers adds Gforth)."""
        run = subprocess.run([sys.executable, str(ROOT / "scripts" / "check-layers.py"), "--root", str(ROOT)],
                             stdin=subprocess.DEVNULL, capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)


class GlobalInputs(unittest.TestCase):
    """Every target that runs under the Lean cache reads its scripts (the variables make exports
    name them, scripts/test-tier.py's Inputs.global_files): none of them may read a source
    library, or a change of any file of src/lib would re-run every target (they once did:
    os.path.join(prefix, "lib", "lean") read as the repository's lib folders). The files are
    listed from the folder, not git, so the planted faults' copies of the tree run it too."""

    CACHE_SCRIPTS = {"scripts/lean-cache.py", "scripts/leanexport-cache.py", "scripts/lean_pin.py"}

    def test_the_lean_cache_scripts_read_no_source(self):
        files = {}
        for top, folders, names in os.walk(ROOT):
            folders[:] = [f for f in folders if f not in (".git", ".tools", "__pycache__", "build", "work")]
            for name in names:
                files[os.path.relpath(os.path.join(top, name), ROOT)] = ""
        here = os.getcwd()
        os.chdir(ROOT)
        try:
            ct = test_tier.changed_tests
            found, _ = ct.input_files(self.CACHE_SCRIPTS, files, {}, ct.file_index(files))
        finally:
            os.chdir(here)
        self.assertTrue(self.CACHE_SCRIPTS <= found)
        self.assertEqual(sorted(p for p in found if p.startswith(("src/", "tests/lib/"))), [])


FIXTURE = dict(tier_fixture.FILES)
FIXTURE.update({
    "src/kernel/k.fs": "require ../core/c.fs\n: k ;\n",
    "src/front/loaded.fs": "require ../lib/used.fs\n: loaded ;\n",
    "src/load/kernel.fs": "\\ the kernel's entry\nrequire ../kernel/k.fs\n",
    "src/load/front.fs": "require ../front/loaded.fs\n",
    "src/main.fs": "require ./load/kernel.fs\nrequire ./load/front.fs\n",
    "tests/core/c.fs": "require ../../src/load/kernel.fs\n",
    "tests/front/f.fs": "require ../../src/load/front.fs\nrequire ../../src/front/alone.fs\n",
})


class Tracing(unittest.TestCase):
    """What a target reads, and so when its recorded pass is reused, through the entries."""

    def setUp(self):
        self.repo = tier_fixture.Repo(FIXTURE)

    def tearDown(self):
        self.repo.close()

    def inputs(self, target):
        here = os.getcwd()
        saved = dict(os.environ)
        os.chdir(self.repo.path)
        os.environ.clear()
        os.environ.update(self.repo.env)
        try:
            inputs = test_tier.Inputs()
            files, reasons = inputs.files(test_tier.changed_tests.named_files(inputs.recipe(target)))
            self.assertEqual(reasons, [], target)
            self.assertIsNotNone(inputs.target(target), target)
            return files
        finally:
            os.environ.clear()
            os.environ.update(saved)
            os.chdir(here)

    def tool(self, *args):
        return self.repo.script("tested-tree.py", *args)

    def change(self, name, text):
        self.repo.write(name, text)
        self.repo.commit(f"change {name}")

    def lookup(self, target):
        run = self.tool("lookup", "--", "make", target)
        return run.returncode, run.stdout + run.stderr

    def test_inputs_are_the_closure_of_the_entry(self):
        core = self.inputs("test-core")
        for path in ("tests/core/c.fs", "src/load/kernel.fs", "src/kernel/k.fs", "src/core/c.fs", "src/lib/used.fs"):
            self.assertIn(path, core)
        for path in ("src/main.fs", "src/load/front.fs", "src/front/loaded.fs", "src/front/alone.fs"):
            self.assertNotIn(path, core)
        front = self.inputs("test-front")
        for path in ("src/load/front.fs", "src/front/loaded.fs", "src/front/alone.fs", "src/lib/free.fs"):
            self.assertIn(path, front)
        for path in ("src/main.fs", "src/load/kernel.fs", "src/kernel/k.fs"):
            self.assertNotIn(path, front)

    def test_reuse_follows_the_entries(self):
        run = self.tool("record", "--", "make", "test-core", "test-front")
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.change("src/front/loaded.fs", "require ../lib/used.fs\n: loaded 1 ;\n")
        code, out = self.lookup("test-core")
        self.assertEqual(code, 0, out)
        self.assertIn("inputs unchanged", out)
        self.assertEqual(self.lookup("test-front")[0], 1)
        for name, text in (("src/kernel/k.fs", "require ../core/c.fs\n: k 2 ;\n"),
                           ("src/lib/used.fs", ": used 3 ;\n"),
                           ("src/load/kernel.fs", "\\ the kernel's entry, edited\nrequire ../kernel/k.fs\n")):
            run = self.tool("record", "--", "make", "test-core")
            self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
            self.change(name, text)
            code, out = self.lookup("test-core")
            self.assertEqual(code, 1, f"{name}: {out}")

    def test_a_listing_of_proc_keeps_the_digest(self):
        """scripts/start-limit.sh's count of the user's threads (/proc/*/status) is no input of
        the checkout: a target whose test runs such a script is reused when nothing it reads
        changed (31 targets that run bin/leanforth had no digest from 2026-11-18 to 11-19)."""
        self.change("scripts/limit.sh", "n=0\nfor f in /proc/[0-9]*/status; do n=$((n+1)); done\n")
        self.change("tests/front/check_front.py", 'import subprocess\nsubprocess.run(["sh", "scripts/limit.sh"])\n'
                    'DATA = "tests/front/data.txt"\n')
        run = self.tool("record", "--", "make", "reference-front")
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.change("scripts/check.py", "print('unrelated')\n")
        code, out = self.lookup("reference-front")
        self.assertEqual(code, 0, out)
        self.assertIn("inputs unchanged", out)
        self.change("scripts/limit.sh", "n=0\nfor f in /proc/[0-9]*/status; do n=$((n+2)); done\n")
        self.assertEqual(self.lookup("reference-front")[0], 1, "the script itself is still an input")


class Finder(unittest.TestCase):
    """scripts/changed-tests.py's input_files on small trees of its own: the system's folders are
    no input of the checkout, and a test that declares FIXTURES_ONLY vouches for the git, home
    folder and export readings of what it runs, never for a program reached otherwise."""

    TREE = {
        "scripts/proc.sh": "for f in /proc/[0-9]*/status; do :; done\n",
        "scripts/proc.py": 'import glob, os\nos.listdir("/proc")\nglob.glob("/sys/class/*")\n',
        "scripts/mixed.sh": "for f in /proc/x tests/*; do :; done\n",
        "scripts/folder.py": "import os\nos.listdir(folder)\n",
        "scripts/git.py": 'import subprocess\nsubprocess.run(["git", "ls-files"])\n',
        "tests/scripts/marked.py": "# inputs: fixtures only: its repositories\nimport subprocess\n"
                                   'subprocess.run(["python3", "scripts/git.py"])\n',
        "tests/scripts/unmarked.py": 'import subprocess\nsubprocess.run(["python3", "scripts/git.py"])\n',
        "tests/scripts/lists.py": "# inputs: fixtures only\nimport subprocess\n"
                                  'subprocess.run(["python3", "scripts/folder.py"])\n',
        "scripts/marked.py": "# inputs: fixtures only\nimport subprocess\n"
                             'subprocess.run(["python3", "scripts/git.py"])\n',
        "scripts/tells.py": "# inputs: named only: scripts/git.py\nprint('run scripts/git.py yourself')\n",
        "scripts/tells-wrong.py": "# inputs: named only: scripts/other.py\nprint('run scripts/git.py yourself')\n",
        "tests/scripts/folder.py": 'import subprocess\n# inputs: named only: scripts\nsubprocess.run(["verify", "scripts"])\n',
        "tests/scripts/folder-read.py": 'import subprocess\nsubprocess.run(["verify", "scripts"])\n',
    }

    def setUp(self):
        self.top = tempfile.mkdtemp(prefix="lf-finder-test-")
        for name, text in self.TREE.items():
            path = pathlib.Path(self.top, name)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding="utf-8")
        self.here = os.getcwd()
        os.chdir(self.top)

    def tearDown(self):
        os.chdir(self.here)
        shutil.rmtree(self.top, ignore_errors=True)

    def found(self, *start):
        ct = test_tier.changed_tests
        tracked = {name: "0" for name in self.TREE}
        files, reasons = ct.input_files(list(start), tracked, {}, ct.file_index(tracked))
        self.assertTrue(set(start) <= files)
        return files, reasons

    def reasons(self, *start):
        return self.found(*start)[1]

    def test_a_path_named_only_is_neither_followed_nor_read(self):
        files, reasons = self.found("scripts/tells.py")
        self.assertEqual((reasons, "scripts/git.py" in files), ([], False))
        files, reasons = self.found("scripts/tells-wrong.py")
        self.assertEqual(reasons, ["scripts/git.py reads git's index or history"], "only the paths listed")
        self.assertNotIn("scripts/proc.sh", self.found("tests/scripts/folder.py")[0])
        self.assertIn("scripts/proc.sh", self.found("tests/scripts/folder-read.py")[0], "a folder named is read")

    def test_system_folders_are_no_listing(self):
        self.assertEqual(self.reasons("scripts/proc.sh"), [])
        self.assertEqual(self.reasons("scripts/proc.py"), [])

    def test_other_listings_still_count(self):
        self.assertEqual(self.reasons("scripts/mixed.sh"), ["scripts/mixed.sh lists a folder the finder cannot name"])
        self.assertEqual(self.reasons("scripts/folder.py"), ["scripts/folder.py lists a folder the finder cannot name"])

    def test_a_declared_test_vouches_for_what_it_runs(self):
        self.assertEqual(self.reasons("tests/scripts/marked.py"), [])
        self.assertEqual(self.reasons("tests/scripts/unmarked.py"), ["scripts/git.py reads git's index or history"])

    def test_a_program_reached_otherwise_still_counts(self):
        # Each order: the program reached first through the declared test, then plainly, and back.
        for pair in (("tests/scripts/marked.py", "scripts/git.py"), ("tests/scripts/marked.py", "tests/scripts/unmarked.py")):
            for start in (pair, pair[::-1]):
                self.assertEqual(self.reasons(*start), ["scripts/git.py reads git's index or history"], start)

    def test_only_a_test_declares_and_a_listing_always_counts(self):
        self.assertEqual(self.reasons("scripts/marked.py"), ["scripts/git.py reads git's index or history"])
        self.assertEqual(self.reasons("tests/scripts/lists.py"), ["scripts/folder.py lists a folder the finder cannot name"])


if __name__ == "__main__":
    unittest.main()
