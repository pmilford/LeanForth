"""A throw-away git repository shaped like LeanForth's, for the tests of scripts/test-tier.py,
scripts/tested-tree.py and scripts/push.sh (plan 9.4.6). Its Makefile has the real one's
aggregates (make check is make test plus check-rest), and every recipe only logs what it
ran: Gforth is a stub that writes its arguments to $STUB_LOG and fails when they contain
$STUB_FAIL_ON. Nothing here touches the project's own tree or records."""
import os
import pathlib
import shutil
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
TODAY = "2026-11-13"

MAKEFILE = """\
GFORTH ?= .tools/gforth/bin/gforth
NOTE = echo $@ >> $${STUB_LOG:-/dev/null}
COVERAGE_ENGINE_DIFFERS := test-cli
test-class = $(shell awk '$$1 ~ /^[a-z][a-z0-9-]*$$/ && $$2 == "$(1)" { print $$1 }' tests/test-classes.txt)
test-unit: $(call test-class,unit)
test-e2e: $(call test-class,e2e)
test: check-docs check-portable-forth check-forth-quality smoke test-lib test-front test-core test-cli
check: test check-rest
check-rest: test-differential mutants-check $(COVERAGE_ENGINE_DIFFERS)
test-differential: reference-front reference-core
check-docs check-portable-forth check-forth-quality reference-core:
\t$(NOTE)
mutants-check:
\t$(NOTE) tests/mutants/faults.toml
smoke:
\tfor f in src/*/*.fs; do $(GFORTH) $$f; done
test-lib:
\t$(GFORTH) tests/lib/a.fs
test-front:
\t$(GFORTH) tests/front/f.fs
test-core:
\t$(GFORTH) tests/core/c.fs
test-cli:
\t$(GFORTH) tests/cli/cli.fs
reference-front:
\tpython3 tests/front/check_front.py
\t$(NOTE)
coverage-check:
\t$(GFORTH) coverage-check
coverage-focus:
\t$(GFORTH) coverage-focus $(COVERAGE_FILES) over $(COVERAGE_TARGETS)
BASE ?= main
cover-changed:
\t$(GFORTH) cover-changed $(BASE)
mutants:
\t$(GFORTH) mutants $(FAULTS)
sneaky:
\techo changed >> ./docs/A.md
parallel-init:
\t$(NOTE)
.PHONY: test-unit test-e2e test check check-rest test-differential check-docs check-portable-forth check-forth-quality \\
\treference-core mutants-check smoke test-lib test-front test-core test-cli reference-front \\
\tcoverage-check coverage-focus cover-changed mutants sneaky parallel-init
"""

GFORTH_STUB = """\
#!/bin/sh
if [ "$1" = --version ]; then echo "${STUB_GFORTH_VERSION:-%s}"; exit 0; fi
[ -n "$STUB_LOG" ] && echo "%s $*" >> "$STUB_LOG"
if [ -n "$STUB_FAIL_ON" ]; then case "$*" in *"$STUB_FAIL_ON"*) exit 1 ;; esac; fi
exit 0
"""

LEAN_STUB = """\
#!/bin/sh
echo "${STUB_LEAN_VERSION:-Lean (version 4.35.0, stub)}"
"""

FAULTS = """\
[[fault]]
id = "free-one"
file = "src/lib/free.fs"
old = "free"
new = "eerf"
test = "$GFORTH tests/lib/a.fs"
reason = "stub"

[[fault]]
id = "core-one"
file = "src/core/c.fs"
old = "require"
new = "include"
test = "$GFORTH tests/core/c.fs"
reason = "stub"

[[fault]]
id = "alone-one"
file = "src/front/alone.fs"
old = "alone"
new = "enola"
test = "$GFORTH tests/front/f.fs"
reason = "stub"
"""

CLASSES = """\
# The fixture's classes, as tests/test-classes.txt
check-docs unit
check-portable-forth unit
check-forth-quality unit
smoke unit
test-lib unit
test-front unit
test-core unit
mutants-check unit
test-cli e2e
reference-front e2e
reference-core e2e
"""

FILES = {
    "Makefile": MAKEFILE,
    ".gitignore": ".tools/\n/.claude/work/\n__pycache__/\n",
    "README.md": "# stub\n",
    "./docs/A.md": "# A\n",
    "docs/development/ci-results.log": "",
    "src/main.fs": "require ./core/c.fs\nrequire ./front/loaded.fs\n",
    "src/core/c.fs": "require ../lib/used.fs\n",
    "src/lib/used.fs": ": used ;\n",
    "src/lib/free.fs": ": free-word ;\n",
    "src/front/loaded.fs": ": loaded ;\n",
    "src/front/alone.fs": "require ../lib/free.fs\n: alone ;\n",
    "src/program/p.fs": ": p ;\n",
    "tests/lib/a.fs": "require ../../src/lib/free.fs\n",
    "tests/front/f.fs": "require ../../src/front/alone.fs\n",
    "tests/front/check_front.py": 'DATA = "tests/front/data.txt"\n',
    "tests/front/data.txt": "data\n",
    "tests/core/c.fs": "require ../../src/main.fs\n",
    "tests/cli/cli.fs": "\\ the command line\n",
    "tests/mutants/faults.toml": FAULTS,
    "tests/coverage-baseline.json": "{}\n",
    "tests/test-classes.txt": CLASSES,
    "scripts/check.py": "print('stub')\n",
    "bin/tool": "#!/bin/sh\n",
}


def make_env(**extra):
    """The environment without an enclosing make's or test run's settings: under make
    coverage GFORTH names the counting wrapper, which the stub Makefile would use."""
    dropped = ("MAKEFLAGS", "MAKELEVEL", "MFLAGS", "MAKEOVERRIDES", "CI", "GFORTH", "LEAN", "LEANEXPORT", "JOBS")
    env = {k: v for k, v in os.environ.items()
           if k not in dropped and not k.startswith(("LF_", "LEANFORTH_", "LEAN_", "STUB_"))}
    env.update(GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@example.invalid", GIT_COMMITTER_NAME="t",
               GIT_COMMITTER_EMAIL="t@example.invalid", GIT_CONFIG_NOSYSTEM="1")
    env.update(extra)
    return env


class Repo:
    """A repository in a new temporary folder, committed once on branch main (tag "base")."""

    def __init__(self, files=None):
        self.top = tempfile.mkdtemp(prefix="lf-tier-test-")
        self.path = pathlib.Path(self.top) / "repo"
        self.records = pathlib.Path(self.top) / "records"
        self.log = pathlib.Path(self.top) / "stub.log"
        self.path.mkdir()
        self.env = make_env(HOME=self.top, LF_TESTED_DIR=str(self.records), LF_TESTED_NOW=f"{TODAY} 12:00:00",
                            LF_GFORTH073=str(self.path / ".tools/gforth073"),
                            LF_GFORTH_FAST=str(self.path / ".tools/gforth/bin/gforth-fast"), STUB_LOG=str(self.log))
        for name, text in (files or FILES).items():
            self.write(name, text)
        self.stub(".tools/gforth/bin/gforth", GFORTH_STUB % ("gforth 1.0.0 stub", "gforth10"))
        self.stub(".tools/gforth/bin/gforth-fast", GFORTH_STUB % ("gforth 1.0.0 stub", "gforthfast"))
        self.stub(".tools/gforth073", GFORTH_STUB % ("gforth 0.7.3", "gforth073"))
        self.stub(".tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean", LEAN_STUB)
        self.git("init", "-q", "-b", "main")
        self.commit("base")
        self.git("tag", "base")

    def stub(self, name, text):
        self.write(name, text)
        os.chmod(self.path / name, 0o755)

    def write(self, name, text):
        target = self.path / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text, encoding="utf-8")

    def remove(self, name):
        (self.path / name).unlink()

    def git(self, *args):
        return subprocess.run(["git", *args], cwd=self.path, env=self.env, capture_output=True,
                              text=True, check=True).stdout.strip()

    def commit(self, message):
        self.git("add", "-A")
        self.git("commit", "-q", "--allow-empty", "-m", message)

    def run(self, *argv, **extra):
        env = dict(self.env)
        env.update(extra)
        return subprocess.run(list(argv), cwd=self.path, env=env, capture_output=True, text=True)

    def script(self, name, *args, **extra):
        return self.run("python3", str(ROOT / "scripts" / name), *args, **extra)

    def logged(self):
        return self.log.read_text(encoding="utf-8").splitlines() if self.log.exists() else []

    def close(self):
        shutil.rmtree(self.top, ignore_errors=True)
