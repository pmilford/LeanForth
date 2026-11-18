#!/usr/bin/env python3
"""Refuse a Lean binary that is an elan proxy or not the pinned Lean 4.35.0.

An elan proxy (elan's bin/lean, a link to the elan binary) run without
ELAN_HOME pointing at the toolchains downloads a 3 GB toolchain into
~/.elan (.claude/CLAUDE.md; review fix-batch Re-check 2, 2026-11-18). So a
Lean found by name on PATH, or named in the environment, is checked before
it is ever run:

  proxy(path)    -> the reason it is an elan proxy, or None: its real path
                    is the elan binary (a symbolic link), or it is the same
                    file as an `elan` beside it (a hard link, as elan makes
                    them). Nothing is run.
  version(path)  -> the reason `path --version` is not Lean 4.35.0, or
                    None. Run only after proxy(path) found none.
  refusal(path)  -> the first of the two reasons, or None.

Run as a script: a self-test on made-up files in a temporary directory.
"""
import os
import subprocess
import sys
import tempfile

PINNED = "4.35.0"


def proxy(path):
    real = os.path.realpath(path)
    if os.path.basename(real) in ("elan", "elan.exe"):
        return f"{path} is an elan proxy (it is {real})"
    for name in ("elan", "elan.exe"):
        sibling = os.path.join(os.path.dirname(real), name)
        if os.path.exists(sibling) and os.path.samefile(real, sibling):
            return f"{path} is an elan proxy (the same file as {sibling})"
    return None


def version(path):
    try:
        run = subprocess.run([path, "--version"], stdin=subprocess.DEVNULL,
                             capture_output=True, timeout=60)
    except (OSError, subprocess.TimeoutExpired) as error:
        return f"{path} --version did not run: {error}"
    text = run.stdout.decode("utf-8", "replace")
    if run.returncode != 0 or f"version {PINNED}" not in text:
        return f"{path} is not Lean {PINNED}: {text.strip() or 'no version'}"
    return None


def refusal(path):
    return proxy(path) or version(path)


def self_test():
    with tempfile.TemporaryDirectory() as folder:
        elan = os.path.join(folder, "elan")
        with open(elan, "w") as out:
            out.write("#!/bin/sh\necho 'elan would download here' >&2\nexit 9\n")
        os.chmod(elan, 0o755)
        linked = os.path.join(folder, "lean")
        os.symlink(elan, linked)
        assert proxy(linked) and "elan proxy" in proxy(linked)
        hard_dir = os.path.join(folder, "hard")
        os.mkdir(hard_dir)
        os.link(elan, os.path.join(hard_dir, "elan"))
        os.link(elan, os.path.join(hard_dir, "lean"))
        assert proxy(os.path.join(hard_dir, "lean"))
        other = os.path.join(folder, "other-lean")
        with open(other, "w") as out:
            out.write("#!/bin/sh\necho 'Lean (version 4.9.0, x86_64-unknown-linux-gnu)'\n")
        os.chmod(other, 0o755)
        assert proxy(other) is None
        assert "is not Lean 4.35.0" in version(other)
        pinned = os.path.join(folder, "pinned-lean")
        with open(pinned, "w") as out:
            out.write("#!/bin/sh\necho 'Lean (version 4.35.0, x86_64-unknown-linux-gnu, "
                      "commit 0, Release)'\n")
        os.chmod(pinned, 0o755)
        assert refusal(pinned) is None
        assert "did not run" in version(os.path.join(folder, "missing"))
    print("lean_pin.py: all tests passed")


if __name__ == "__main__":
    self_test()
    sys.exit(0)
