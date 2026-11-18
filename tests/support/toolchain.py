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
import os
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
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


def lean(environ=None, root=ROOT):
    """The Lean to run: the environment's, else root's pinned 4.35.0, else lean."""
    environ = os.environ if environ is None else environ
    named = environ.get("LEAN") or environ.get("LEANFORTH_LEAN")
    if named:
        return named
    local = root / LOCAL_LEAN.relative_to(ROOT)
    return str(local) if local.exists() else "lean"


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
    assert lean({}, nowhere) == "lean"
    assert lean({"LEANFORTH_LEAN": "/a/lean"}, nowhere) == "/a/lean"
    assert lean({"LEAN": "/b/lean", "LEANFORTH_LEAN": "/a/lean"}, nowhere) == "/b/lean"
    assert gforth_env({"LEANFORTH_GFORTH": "/a/gforth"})["GFORTH"] == "/a/gforth"
    print("toolchain.py: all tests passed")


if __name__ == "__main__":
    self_test()
    sys.exit(0)
