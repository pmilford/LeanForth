#!/usr/bin/env python3
"""Tests of the Lean cache, scripts/lean-cache.py and leanexport-cache.py
(make test-lean-cache).

Run from the repository root: python3 tests/lean-cache/test_lean_cache.py

Each case builds a fake toolchain in a temporary folder: a `lean` and a
`leanexport` (Python scripts) that count their runs, print what they read
(the source path as given, its text, the .olean files of LEAN_PATH) and
write an .olean for -o, beside a library folder with a shared library.
Through the cache scripts it checks that a repeated call is replayed without
running the tool (same output, status and .olean), and that a change to
each input misses the cache: the source text, the module name Lean derives
from the path, an option, an imported .olean, the toolchain's binary or
library, a LEAN_* variable, the exporter's arguments. It also checks what
is never cached (IO inputs, unrecorded imports, statuses other than 0 and
1, other arguments), that LEANFORTH_LEAN_CACHE=0 stores nothing, that
verify mode fails on a run that differs from its entry, that echoed paths
are restored, that one stream keeps its order, and that the Makefile uses
the cache only when LEAN_CACHE is not 0 and CI is not set. Needs only
Python 3 and make; runs no Lean and no Forth.
"""
import os
import shutil
import stat
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
WRAPPER = ROOT / "scripts" / "lean-cache.py"
EXPORT_WRAPPER = ROOT / "scripts" / "leanexport-cache.py"

FAKE_LEAN = r'''#!/usr/bin/env python3
import os, sys
args = sys.argv[1:]
if args == ["--githash"]:
    print("fake-githash"); sys.exit(0)
if args == ["--version"]:
    print("Lean (version 4.35.0, fake)"); sys.exit(0)
with open(os.environ["FAKE_COUNT"], "a") as f:
    f.write("lean\n")
out = args[args.index("-o") + 1] if "-o" in args else None
source = [a for a in args if a.endswith(".lean")][-1]
text = open(source).read()
print(f"elaborated {source}: {text.strip()} {os.environ.get('FAKE_NOISE', '')}", flush=True)
for folder in filter(None, os.environ.get("LEAN_PATH", "").split(":")):
    for name in sorted(os.listdir(folder)):
        if name.endswith(".olean"):
            print(f"imported {name}: {open(os.path.join(folder, name)).read()}", flush=True)
if "STDERR" in text:
    sys.stderr.write("to stderr\n"); sys.stderr.flush()
    print("after stderr", flush=True)
if "ERROR" in text:
    print(f"{source}:1:0: error: planted"); sys.exit(1)
if "EXIT3" in text:
    sys.exit(3)
if out:
    open(out, "w").write(f"olean of {os.path.relpath(os.path.abspath(source))}: {text}"
                         + os.environ.get("FAKE_OLEAN_NOISE", ""))
'''

FAKE_EXPORT = r'''#!/usr/bin/env python3
import os, sys
with open(os.environ["FAKE_COUNT"], "a") as f:
    f.write("export\n")
print("export", " ".join(sys.argv[1:]))
for folder in filter(None, os.environ.get("LEAN_PATH", "").split(":")):
    for name in sorted(os.listdir(folder)):
        print(f"module {name}: {open(os.path.join(folder, name)).read()}")
'''


def executable(path, text):
    path.write_text(text)
    path.chmod(path.stat().st_mode | stat.S_IXUSR)


class CacheTest(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="lean-cache-test-")
        base = Path(self.temporary.name)
        # An elan home's layout, the only place lean_pin.py takes a Lean from.
        self.prefix = base / "toolchains" / "fake"
        (self.prefix / "bin").mkdir(parents=True)
        (self.prefix / "lib" / "lean").mkdir(parents=True)
        executable(self.prefix / "bin" / "lean", FAKE_LEAN)
        executable(self.prefix / "bin" / "leanexport", FAKE_EXPORT)
        (self.prefix / "lib" / "lean" / "libleanshared.so").write_text("library 1\n")
        (self.prefix / "lib" / "lean" / "Init.olean").write_text("init\n")
        self.work = base / "work"
        self.work.mkdir()
        self.outside = base / "outside"
        self.outside.mkdir()
        self.cache = base / "cache"
        self.count = base / "count"
        self.count.write_text("")
        self.env = {k: v for k, v in os.environ.items()
                    if not k.startswith(("LEAN_", "LEANFORTH_", "FAKE_"))}
        self.env.update(LEANFORTH_LEAN=str(self.prefix / "bin" / "lean"),
                        LEANFORTH_LEAN_CACHE="1", LEANFORTH_LEAN_CACHE_DIR=str(self.cache),
                        FAKE_COUNT=str(self.count))

    def tearDown(self):
        self.temporary.cleanup()

    def runs(self):
        return len(self.count.read_text().splitlines())

    def lean(self, *args, wrapper=WRAPPER, **env):
        done = subprocess.run([str(wrapper), *args], cwd=self.work, capture_output=True,
                              env=dict(self.env, **env), timeout=60)
        return done.returncode, done.stdout, done.stderr

    def source(self, name, text, folder=None):
        path = (folder or self.work) / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return str(path.relative_to(self.work)) if folder is None else str(path)

    def assert_cached(self, *args, **env):
        """The call runs the tool once, then is replayed identically."""
        before = self.runs()
        first = self.lean(*args, **env)
        self.assertEqual(self.runs(), before + 1, "the first call runs the tool")
        second = self.lean(*args, **env)
        self.assertEqual(self.runs(), before + 1, "the second call is replayed")
        self.assertEqual(first, second)
        return first

    def assert_runs(self, *args, **env):
        """The call runs the tool every time."""
        before = self.runs()
        first = self.lean(*args, **env)
        second = self.lean(*args, **env)
        self.assertEqual(self.runs(), before + 2, "both calls run the tool")
        return first, second

    def test_replayed(self):
        name = self.source("A.lean", "theorem a")
        status, stdout, stderr = self.assert_cached("-DwarningAsError=true", name)
        self.assertEqual((status, stderr), (0, b""))
        self.assertEqual(stdout, b"elaborated A.lean: theorem a \n")

    def test_bare_name_found_on_path(self):
        """LEANFORTH_LEAN=lean (the Makefile's default with no .tools beside the checkout) is
        the lean on PATH, cached or not (fix-batch-4: execv of a bare name failed)."""
        name = self.source("B.lean", "theorem b")
        path = str(self.prefix / "bin") + os.pathsep + os.environ.get("PATH", "")
        for mode in ("0", "1"):
            status, stdout, stderr = self.lean(name, LEANFORTH_LEAN="lean", PATH=path,
                                               LEANFORTH_LEAN_CACHE=mode)
            self.assertEqual((status, stdout, stderr), (0, b"elaborated B.lean: theorem b \n", b""))

    def test_elan_proxy_refused(self):
        """An elan proxy, by path or found on PATH, is never run (it downloads a toolchain
        without ELAN_HOME); a lean on PATH that is not 4.35.0 is refused too (review
        fix-batch Re-check 2)."""
        name = self.source("C.lean", "theorem c")
        proxies = Path(self.temporary.name) / "elan-bin"
        proxies.mkdir()
        executable(proxies / "elan", "#!/bin/sh\necho downloading >> \"$FAKE_COUNT\"\nexit 9\n")
        (proxies / "lean").symlink_to(proxies / "elan")
        path = str(proxies) + os.pathsep + os.environ.get("PATH", "")
        for env in ({"LEANFORTH_LEAN": "lean", "PATH": path},
                    {"LEANFORTH_LEAN": str(proxies / "lean")}):
            status, stdout, stderr = self.lean(name, **env)
            self.assertEqual((status, stdout), (1, b""), env)
            self.assertIn(b"lean-cache: refused: ", stderr)
            self.assertIn(b"is an elan proxy", stderr)
        # A wrapper script, a copy and a hard link of the proxy, given by path,
        # are refused by where they are, never run (review F5).
        wrapper = Path(self.temporary.name) / "wrapper-lean"
        executable(wrapper, f"#!/bin/sh\nexec '{proxies / 'elan'}' \"$@\"\n")
        copied = Path(self.temporary.name) / "copy"
        copied.mkdir()
        shutil.copy(proxies / "elan", copied / "lean")
        hard = Path(self.temporary.name) / "hard"
        hard.mkdir()
        os.link(proxies / "elan", hard / "lean")
        for lean in (wrapper, copied / "lean", hard / "lean"):
            status, stdout, stderr = self.lean(name, LEANFORTH_LEAN=str(lean))
            self.assertEqual((status, stdout), (1, b""), lean)
            self.assertIn(b"is not a Lean toolchain's binary", stderr)
        old = Path(self.temporary.name) / "toolchains" / "old"
        (old / "bin").mkdir(parents=True)
        (old / "lib" / "lean").mkdir(parents=True)
        executable(old / "bin" / "lean", "#!/bin/sh\necho 'Lean (version 4.9.0)'\n")
        status, _, stderr = self.lean(name, LEANFORTH_LEAN="lean",
                                      PATH=str(old / "bin") + os.pathsep + os.environ.get("PATH", ""))
        self.assertEqual(status, 1)
        self.assertIn(b"is not Lean 4.35.0", stderr)
        self.assertEqual(self.runs(), 0, "no proxy and no other Lean ran a file")

    def test_changed_source_misses(self):
        name = self.source("A.lean", "theorem a")
        self.assert_cached(name)
        self.source("A.lean", "theorem b")
        self.assert_cached(name)
        self.source("A.lean", "theorem a")
        self.assertEqual(self.runs(), 2)
        self.lean(name)
        self.assertEqual(self.runs(), 2, "the first text's entry is still there")

    def test_changed_module_name_misses(self):
        first = self.source("a/X.lean", "def x")
        second = self.source("b/X.lean", "def x")
        self.assert_cached(first)
        self.assert_cached(second)

    def test_changed_option_misses(self):
        name = self.source("A.lean", "def a")
        self.assert_cached("-DwarningAsError=true", name)
        self.assert_cached("-DwarningAsError=false", name)
        self.assert_cached("-DwarningAsError=true", "--run", name)

    def test_changed_toolchain_misses(self):
        name = self.source("A.lean", "def a")
        self.assert_cached(name)
        # A rebuilt library (a new size; the cache notices a change by the
        # binary's, the libraries' and the library folder's size, time and inode).
        (self.prefix / "lib" / "lean" / "libleanshared.so").write_text("library 2, rebuilt\n")
        self.assert_cached(name)
        executable(self.prefix / "bin" / "lean", FAKE_LEAN + "\n# another build\n")
        self.assert_cached(name)

    def test_changed_environment_misses(self):
        name = self.source("A.lean", "def a")
        self.assert_cached(name)
        self.assert_cached(name, LEAN_NUM_THREADS="2")

    def test_verify_logs_a_varying_olean(self):
        """Lean 4.35 may write other .olean bytes for the same source: verify
        mode logs that but fails only on a different status or output."""
        name = self.source("Dep.lean", "def dep")
        self.assert_cached("-o", "Dep.olean", name)
        log = Path(self.temporary.name) / "cache.log"
        status, _, stderr = self.lean("-o", "Dep.olean", name, LEANFORTH_LEAN_CACHE="verify",
                                      LEANFORTH_LEAN_CACHE_LOG=str(log), FAKE_OLEAN_NOISE="x")
        self.assertEqual((status, stderr), (0, b""))
        self.assertEqual(log.read_text().split()[:2], ["verified", "olean-differs"])

    def test_makefile_settings_hit(self):
        """make passes LEAN_CACHE=verify or LEAN_CACHE_DIR=... from its command
        line to the recipes; they are no input of Lean, so verify mode compares
        with the entries of ordinary runs."""
        name = self.source("A.lean", "def a")
        self.assert_cached(name)
        status, _, stderr = self.lean(name, LEAN_CACHE="verify", LEAN_CACHE_DIR="/elsewhere",
                                      LEAN_BINARY="/real/lean", LEANFORTH_LEAN_CACHE="verify",
                                      FAKE_NOISE="changed")
        self.assertEqual(status, 125, stderr)

    def test_changed_import_misses(self):
        library = self.work / "library"
        library.mkdir()
        dependency = self.source("Dep.lean", "def dep")
        user = self.source("User.lean", "import Dep")
        self.assert_cached("-o", "library/Dep.olean", dependency)
        _, stdout, _ = self.assert_cached(user, LEAN_PATH=str(library))
        self.assertIn(b"imported Dep.olean: olean of Dep.lean: def dep", stdout)
        self.source("Dep.lean", "def dep2")
        self.assert_cached("-o", "library/Dep.olean", dependency)
        self.assert_cached(user, LEAN_PATH=str(library))

    def test_olean_replayed(self):
        name = self.source("Dep.lean", "def dep")
        self.assert_cached("-o", "Dep.olean", name)
        written = (self.work / "Dep.olean").read_bytes()
        (self.work / "Dep.olean").unlink()
        self.lean("-o", "Dep.olean", name)
        self.assertEqual((self.work / "Dep.olean").read_bytes(), written)
        self.assertEqual(self.runs(), 1)

    def test_unrecorded_import_runs(self):
        library = self.work / "library"
        library.mkdir()
        (library / "Other.olean").write_text("made elsewhere")
        name = self.source("User.lean", "import Other")
        self.assert_runs(name, LEAN_PATH=str(library))

    def test_echoed_paths_restored(self):
        first = self.source("planted.lean", "ERROR", folder=self.outside / "first-copy")
        second = self.source("planted.lean", "ERROR", folder=self.outside / "second-copy")
        status, stdout, _ = self.assert_cached(first)
        self.assertEqual(status, 1)
        self.assertIn(f"{first}:1:0: error".encode(), stdout)
        status, stdout, _ = self.lean(second)
        self.assertEqual((status, self.runs()), (1, 1), "same text outside the folder: a hit")
        self.assertIn(f"{second}:1:0: error".encode(), stdout)
        self.assertNotIn(b"first-copy", stdout)

    def test_io_input_runs(self):
        name = self.source("Io.lean", "def main : IO Unit := do let _ <- IO.FS.readFile \"x\"")
        self.assert_runs(name)

    def test_initialize_command_runs(self):
        for text in ["initialize r : IO.Ref Nat <- IO.mkRef 0",
                     "def a := 1 initialize r : IO.Ref Nat <- IO.mkRef 0",
                     "/- unterminated initialize"]:
            self.assert_runs(self.source("Init.lean", text))

    def test_initialize_in_string_or_comment_is_cached(self):
        for text in ['def a := "failed to initialize quot"',
                     'def a := 1 -- initialize it\n',
                     '/- a /- nested -/ initialize -/ def a := 1',
                     'def a := "x\\" initialize"']:
            self.assert_cached(self.source("Word.lean", text))

    def test_statuses(self):
        self.assert_cached(self.source("Bad.lean", "ERROR"))
        self.assert_runs(self.source("Three.lean", "EXIT3"))

    def test_other_arguments_run(self):
        name = self.source("A.lean", "def a")
        self.assert_runs("--run", name, "argument")
        self.assert_runs("--json", name)
        before = self.runs()
        self.assertEqual(self.lean("--version")[1], b"Lean (version 4.35.0, fake)\n")
        self.assertEqual(self.runs(), before)

    def test_mode_0_stores_nothing(self):
        name = self.source("A.lean", "def a")
        self.assert_runs(name, LEANFORTH_LEAN_CACHE="0")
        self.assertFalse((self.cache / "entries").exists())

    def test_verify_finds_a_difference(self):
        name = self.source("A.lean", "def a")
        self.assert_cached(name)
        status, _, stderr = self.lean(name, LEANFORTH_LEAN_CACHE="verify")
        self.assertEqual((status, stderr), (0, b""))
        status, _, stderr = self.lean(name, LEANFORTH_LEAN_CACHE="verify", FAKE_NOISE="changed")
        self.assertEqual(status, 125)
        self.assertIn(b"differs from the cache entry", stderr)

    def test_one_stream_keeps_its_order(self):
        name = self.source("A.lean", "STDERR")
        outputs = []
        for _ in range(2):
            with open(self.work / "both.txt", "wb") as both:
                subprocess.run([str(WRAPPER), name], cwd=self.work, stdout=both, stderr=both,
                               env=self.env, timeout=60, check=True)
            outputs.append((self.work / "both.txt").read_bytes())
        self.assertEqual(self.runs(), 1)
        self.assertEqual(outputs[0], outputs[1])
        self.assertEqual(outputs[0].splitlines()[1:], [b"to stderr", b"after stderr"])

    def test_leanexport(self):
        library = self.work / "library"
        library.mkdir()
        dependency = self.source("Dep.lean", "def dep")
        self.lean("-o", "library/Dep.olean", dependency)
        _, stdout, _ = self.assert_cached("Dep", "--", "dep", wrapper=EXPORT_WRAPPER,
                                          LEAN_PATH=str(library))
        self.assertIn(b"export Dep -- dep", stdout)
        self.assert_cached("Dep", "--", "other", wrapper=EXPORT_WRAPPER, LEAN_PATH=str(library))
        self.source("Dep.lean", "def dep3")
        self.lean("-o", "library/Dep.olean", dependency)
        self.assert_cached("Dep", "--", "dep", wrapper=EXPORT_WRAPPER, LEAN_PATH=str(library))
        self.assert_runs("Dep", wrapper=EXPORT_WRAPPER, LEANFORTH_LEAN_CACHE="0")


class MakefileTest(unittest.TestCase):
    def recipe(self, *assignments):
        # A fresh make: not the variables of a make that runs this test.
        env = {k: v for k, v in os.environ.items()
               if k not in ("CI", "LEAN_CACHE", "MAKEFLAGS", "MFLAGS", "MAKELEVEL")}
        return subprocess.run(["make", "-n", "--no-print-directory", "reference-first-checker",
                               *assignments], cwd=ROOT, capture_output=True, text=True,
                              env=env, check=True, timeout=60).stdout

    def test_cache_by_default(self):
        self.assertIn("scripts/lean-cache.py", self.recipe())

    def test_no_cache_with_lean_cache_0_or_ci(self):
        for assignments in (["LEAN_CACHE=0"], ["CI=true"], ["CI=true", "LEAN_CACHE=0"]):
            self.assertNotIn("lean-cache", self.recipe(*assignments), assignments)


if __name__ == "__main__":
    unittest.main()
