#!/usr/bin/env python3
"""The Gforth and Lean a test script runs (fix-batch-2, 2026-11-18).

From the environment as the Makefile passes them: GFORTH, else
LEANFORTH_GFORTH (the real Gforth, which the Makefile always exports while
its GFORTH names the strict wrapper); LEAN, else LEANFORTH_LEAN. Else the
pinned copies in this checkout's .tools, else the PATH's. A worktree
without .tools runs its tests with GFORTH=... LEAN=... set; it never links
another checkout's .tools.

Run as a script: a self-test of the order above on made-up environments.
"""
# Its texts name bin/leanforth, which its callers run.
# inputs: named only: bin/leanforth
import functools
import os
import pathlib
import shutil
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import lean_pin  # noqa: E402  (scripts/lean_pin.py)
LOCAL_GFORTH = ROOT / ".tools" / "gforth" / "bin"
LOCAL_LEAN = ROOT / ".tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean"


def gforth(engine="gforth", environ=None, root=ROOT):
    """The Gforth to run: the environment's, else engine in root's .tools, else engine."""
    environ = os.environ if environ is None else environ
    named = environ.get("GFORTH") or environ.get("LEANFORTH_GFORTH")
    if named:
        return named
    local = root / ".tools" / "gforth" / "bin" / engine
    return str(local) if local.exists() else engine


def lean_choice(environ=None, root=ROOT):
    """The Lean named: the environment's, else root's pinned 4.35.0, else lean."""
    environ = os.environ if environ is None else environ
    named = environ.get("LEAN") or environ.get("LEANFORTH_LEAN")
    if named:
        return named
    local = root / LOCAL_LEAN.relative_to(ROOT)
    return str(local) if local.exists() else "lean"


@functools.lru_cache(maxsize=None)
def checked_lean(name):
    """name, refused (SystemExit) when it, or the file PATH finds for a bare
    name, is an elan proxy or not Lean 4.35.0 (scripts/lean_pin.py): an
    elan proxy run without ELAN_HOME downloads a 3 GB toolchain. A bare name
    PATH does not find is returned as it is, to fail when run."""
    path = name if os.sep in name else shutil.which(name)
    if path is None:
        return name
    reason = lean_pin.refusal(path)
    if reason:
        raise SystemExit(f"toolchain: refused: {reason}")
    return name


def lean(environ=None, root=ROOT):
    """The Lean to run (lean_choice), checked once per process (checked_lean)."""
    return checked_lean(lean_choice(environ, root))


def gforth_env(environ=None):
    """A copy of the environment whose GFORTH names gforth()'s choice, for bin/leanforth."""
    environ = dict(os.environ if environ is None else environ)
    environ["GFORTH"] = gforth(environ=environ)
    return environ


def self_test():
    nowhere = pathlib.Path("/nonexistent-leanforth-root")
    assert gforth("gforth-fast", {}, nowhere) == "gforth-fast"
    assert gforth("gforth", {"LEANFORTH_GFORTH": "/a/gforth"}, nowhere) == "/a/gforth"
    assert gforth("gforth", {"GFORTH": "/b/gforth", "LEANFORTH_GFORTH": "/a/gforth"},
                  nowhere) == "/b/gforth"
    assert lean_choice({}, nowhere) == "lean"
    assert lean_choice({"LEANFORTH_LEAN": "/a/lean"}, nowhere) == "/a/lean"
    assert lean_choice({"LEAN": "/b/lean", "LEANFORTH_LEAN": "/a/lean"}, nowhere) == "/b/lean"
    # An elan proxy, by path or found on PATH, is refused before it runs; a
    # name PATH does not find is left to fail when run.
    with tempfile.TemporaryDirectory() as folder:
        elan = pathlib.Path(folder) / "elan"
        elan.write_text("#!/bin/sh\nexit 9\n")
        elan.chmod(0o755)
        (pathlib.Path(folder) / "lean").symlink_to(elan)
        for environ in ({"LEAN": str(pathlib.Path(folder) / "lean")},
                        {"PATH": folder}):
            saved = os.environ.get("PATH")
            os.environ["PATH"] = environ.get("PATH", saved or "")
            try:
                lean(environ if "LEAN" in environ else {}, nowhere)
                raise AssertionError("an elan proxy was not refused")
            except SystemExit as refused:
                assert "elan proxy" in str(refused), refused
            finally:
                os.environ["PATH"] = saved or ""
                checked_lean.cache_clear()
    assert checked_lean("no-such-lean-anywhere-xyz") == "no-such-lean-anywhere-xyz"
    assert gforth_env({"LEANFORTH_GFORTH": "/a/gforth"})["GFORTH"] == "/a/gforth"
    print("toolchain.py: all tests passed")


if __name__ == "__main__":
    self_test()
    sys.exit(0)
