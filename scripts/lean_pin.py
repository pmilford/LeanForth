#!/usr/bin/env python3
"""Refuse a Lean binary that is an elan proxy or not the pinned Lean 4.35.0,
without ever running one that is not known to be safe.

An elan proxy (elan's bin/lean, a link to the elan binary) run without
ELAN_HOME pointing at the toolchains downloads a 3 GB toolchain into
~/.elan (.claude/CLAUDE.md; reviews fix-batch Re-check 2 and F5 of
fix-cli-present, 2026-11-18). Asking a candidate its version runs it, so a
candidate is first judged by where it is, and run only when that shows it
is a toolchain's own binary:

  proxy(path)    -> the reason it is an elan proxy, or None: its real path
                    is the elan binary (a symbolic link), or it is the same
                    file as an `elan` beside it (a hard link, as elan makes
                    them). Nothing is run.
  layout(path)   -> the reason it is not a toolchain's binary, or None: its
                    real path must be TOOLCHAINS/NAME/bin/lean (TOOLCHAINS a
                    folder named toolchains, an elan home's), with
                    NAME/lib/lean a folder beside it, and it must be neither
                    the same file as nor a copy of the elan of that elan
                    home (TOOLCHAINS/../bin/elan) or of its own folder. So a
                    wrapper script, a copy or a hard link of a proxy
                    anywhere else is refused. Nothing is run.
  version(path)  -> the reason `path --version` is not Lean 4.35.0, or
                    None; run with ELAN_HOME set to path's elan home. Only
                    after proxy and layout found nothing (refusal).
  refusal(path)  -> the first of the three reasons, or None.
  unrun(name, shape=True) -> the refusal found without running anything: an
                    elan proxy, and with shape one that is no toolchain's
                    binary (scripts/program_verify.py, which passes shape
                    False under its test switch for its stand-in Leans, and
                    program_receipt.py).
  checked(name)  -> the reason the Lean that name runs is refused, or None:
                    a bare name is found on PATH (None when PATH has none:
                    running it then fails by itself); this checkout's Lean
                    cache (scripts/lean-cache.py) runs LEANFORTH_LEAN, which
                    is checked instead.

  pinned_lean(name) -> the Lean every test runner runs (review fix-cli-present
                    S3, 2026-11-18): name, else $LEAN, else this checkout's
                    pinned toolchain binary (DEFAULT); SystemExit with the
                    reason when `checked` refuses it.

Command line:
  python3 scripts/lean_pin.py check LEAN   exit 0 when LEAN may be run, else
                                           1 with the reason on stderr
                                           (scripts/export.sh,
                                           scripts/export-elab.sh, the
                                           Makefile under LEAN_CACHE=0)
  python3 scripts/lean_pin.py pinned       print pinned_lean()'s Lean, or exit 1
                                           with the reason (the shell
                                           runners: profile-existing.sh,
                                           tests/front/synth-init.sh,
                                           constructions-init.sh)
  python3 scripts/lean_pin.py              a self-test on made-up files in a
                                           temporary directory: a fake elan
                                           that records every run, reached
                                           by symbolic link, wrapper, copy
                                           and hard link, is never run
"""
import filecmp
import os
import shutil
import subprocess
import sys
import tempfile

PINNED = "4.35.0"
HERE = os.path.dirname(os.path.realpath(__file__))
CACHE = os.path.join(HERE, "lean-cache.py")
ELANS = ("elan", "elan.exe")
DEFAULT = os.path.join(os.path.dirname(HERE), ".tools", "elan", "toolchains",
                       "leanprover--lean4---v4.35.0", "bin", "lean")


def proxy(path):
    real = os.path.realpath(path)
    if os.path.basename(real) in ELANS:
        return f"{path} is an elan proxy (it is {real})"
    for name in ELANS:
        sibling = os.path.join(os.path.dirname(real), name)
        if os.path.exists(sibling) and os.path.samefile(real, sibling):
            return f"{path} is an elan proxy (the same file as {sibling})"
    return None


def elan_home(real):
    """TOOLCHAINS/.. of a real path TOOLCHAINS/NAME/bin/lean."""
    return os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(real))))


def toolchain_shape(real):
    bin_dir = os.path.dirname(real)
    prefix = os.path.dirname(bin_dir)
    return (os.path.basename(real) in ("lean", "lean.exe") and os.path.basename(bin_dir) == "bin"
            and os.path.basename(os.path.dirname(prefix)) == "toolchains"
            and os.path.isdir(os.path.join(prefix, "lib", "lean")))


def elan_copy(real):
    """The elan binary real is, by inode or by content, or None."""
    homes = (os.path.join(elan_home(real), "bin"), os.path.dirname(real))
    for elan in (os.path.join(home, name) for home in homes for name in ELANS):
        if os.path.isfile(elan) and (os.path.samefile(real, elan)
                                     or filecmp.cmp(real, elan, shallow=False)):
            return elan
    return None


def layout(path):
    real = os.path.realpath(path)
    if not os.path.isfile(real):
        return f"{path} is no file"
    if not toolchain_shape(real):
        return (f"{path} is not a Lean toolchain's binary: its real path {real} is not "
                "TOOLCHAINS/NAME/bin/lean with NAME/lib/lean beside it")
    elan = elan_copy(real)
    if elan:
        return f"{path} is an elan proxy (a copy of {elan})"
    return None


def version(path):
    real = os.path.realpath(path)
    env = dict(os.environ, ELAN_HOME=elan_home(real))
    try:
        run = subprocess.run([real, "--version"], stdin=subprocess.DEVNULL, env=env,
                             capture_output=True, timeout=60)
    except (OSError, subprocess.TimeoutExpired) as error:
        return f"{path} --version did not run: {error}"
    text = run.stdout.decode("utf-8", "replace")
    if run.returncode != 0 or f"version {PINNED}" not in text:
        return f"{path} is not Lean {PINNED}: {text.strip() or 'no version'}"
    return None


def refusal(path):
    return proxy(path) or layout(path) or version(path)


def resolved(name):
    """(path, None): the file the Lean that name runs is (None when PATH has no such
    name), the Lean cache standing for LEANFORTH_LEAN; or (None, reason)."""
    path = name if os.sep in name else shutil.which(name)
    if path is None:
        return None, None
    if os.path.exists(path) and os.path.realpath(path) == os.path.realpath(CACHE):
        target = os.environ.get("LEANFORTH_LEAN")
        if not target:
            return None, f"{name} is the Lean cache, and LEANFORTH_LEAN, the Lean it runs, is not set"
        return resolved(target)
    return path, None


def checked(name):
    path, reason = resolved(name)
    return reason or (path and refusal(path))


def unrun(name, shape=True):
    """checked's refusal found without running anything: an elan proxy, and with shape a
    file that is no toolchain's binary (layout). The program verifier's test switch passes
    shape False, so that its stand-in Leans reach its own wrong-Lean messages."""
    path, reason = resolved(name)
    return reason or (path and (proxy(path) or (layout(path) if shape else None)))


def pinned_lean(name=None):
    lean = name or os.environ.get("LEAN") or DEFAULT
    reason = checked(lean)
    if reason:
        raise SystemExit(f"lean_pin: refused: {reason}")
    return lean


# ---- Self-test.

def executable(path, text):
    with open(path, "w") as out:
        out.write(text)
    os.chmod(path, 0o755)


def toolchain(home, name, binary_text=None, link_to=None, copy_of=None):
    """HOME/toolchains/NAME/bin/lean with lib/lean beside it: a script, a link or a copy."""
    prefix = os.path.join(home, "toolchains", name)
    os.makedirs(os.path.join(prefix, "bin"))
    os.makedirs(os.path.join(prefix, "lib", "lean"))
    lean = os.path.join(prefix, "bin", "lean")
    if binary_text is not None:
        executable(lean, binary_text)
    elif link_to is not None:
        os.link(link_to, lean)
    else:
        shutil.copy(copy_of, lean)
    return lean


def self_test():
    with tempfile.TemporaryDirectory() as folder:
        runs = os.path.join(folder, "elan-runs")
        open(runs, "w").close()
        home = os.path.join(folder, "home")
        os.makedirs(os.path.join(home, "bin"))
        elan = os.path.join(home, "bin", "elan")
        executable(elan, f"#!/bin/sh\necho ran >> '{runs}'\necho 'elan would download' >&2\n"
                   "exit 9\n")
        # Every way to reach the proxy: none of them runs it.
        linked = os.path.join(home, "bin", "lean")
        os.symlink(elan, linked)
        wrapper = os.path.join(folder, "wrapper-lean")
        executable(wrapper, f"#!/bin/sh\nexec '{elan}' \"$@\"\n")
        copy = os.path.join(folder, "copy", "lean")
        os.mkdir(os.path.dirname(copy))
        shutil.copy(elan, copy)
        hard = os.path.join(folder, "hard", "lean")
        os.mkdir(os.path.dirname(hard))
        os.link(elan, hard)
        in_home_copy = toolchain(home, "copied", copy_of=elan)
        in_home_hard = toolchain(home, "linked", link_to=elan)
        # A toolchain's shape, bin/lean beside lib/lean, but in no toolchains folder.
        elsewhere = os.path.join(folder, "elsewhere", "x")
        os.makedirs(os.path.join(elsewhere, "lib", "lean"))
        os.makedirs(os.path.join(elsewhere, "bin"))
        shaped = os.path.join(elsewhere, "bin", "lean")
        executable(shaped, f"#!/bin/sh\nexec '{elan}' \"$@\"\n")
        for candidate in (linked, wrapper, copy, hard, in_home_copy, in_home_hard, shaped):
            reason = refusal(candidate)
            assert reason and ("elan proxy" in reason or "not a Lean toolchain" in reason), \
                (candidate, reason)
            assert checked(candidate) == reason
        assert "elan proxy" in proxy(linked)
        assert "copy of" in layout(in_home_copy) and "copy of" in layout(in_home_hard)
        beside = os.path.join(folder, "beside")
        os.mkdir(beside)
        os.link(elan, os.path.join(beside, "elan"))
        os.link(elan, os.path.join(beside, "lean"))
        assert "the same file as" in proxy(os.path.join(beside, "lean"))
        # unrun: the same refusals with nothing run; without shape (the program
        # verifier's stand-ins), the proxies themselves only.
        for candidate in (linked, wrapper, copy, hard, in_home_copy, in_home_hard, shaped):
            assert unrun(candidate) == refusal(candidate), candidate
        assert "elan proxy" in unrun(linked, shape=False)
        assert "elan proxy" in unrun(os.path.join(beside, "lean"), shape=False)
        assert unrun(wrapper, shape=False) is None and unrun("no-such-lean-here") is None
        # The command line, and the scripts that call it, refuse them too.
        for candidate in (wrapper, copy, hard, in_home_copy):
            run = subprocess.run([sys.executable, __file__, "check", candidate],
                                 capture_output=True, text=True)
            assert run.returncode == 1 and "lean_pin: refused: " in run.stderr, run
            for script in ("export.sh", "export-elab.sh"):
                args = ["out.ndjson", "Mod"] if script == "export.sh" else ["o", "e", "Mod"]
                run = subprocess.run(["bash", os.path.join(HERE, script), *args], cwd=folder,
                                     env=dict(os.environ, LEAN=candidate),
                                     capture_output=True, text=True)
                assert run.returncode != 0 and "refused" in run.stderr, (script, run)
        run = subprocess.run([sys.executable, CACHE, "A.lean"], cwd=folder, capture_output=True,
                             text=True, env=dict(os.environ, LEANFORTH_LEAN=copy))
        assert run.returncode != 0 and "refused" in run.stderr, run
        with open(runs) as log:
            assert log.read() == "", "a proxy ran"
        # A toolchain's binary is asked its version, with ELAN_HOME set.
        other = toolchain(home, "other", "#!/bin/sh\necho 'Lean (version 4.9.0, x86)'\n")
        assert proxy(other) is None and layout(other) is None
        assert "is not Lean 4.35.0" in refusal(other) and unrun(other) is None
        pinned = toolchain(home, "pinned", "#!/bin/sh\n[ \"$ELAN_HOME\" = '" + home + "' ] && "
                           "echo 'Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit 0, "
                           "Release)'\n")
        assert refusal(pinned) is None
        assert checked(pinned) is None
        run = subprocess.run([sys.executable, __file__, "check", pinned], capture_output=True)
        assert run.returncode == 0 and run.stderr == b"", run
        # Through a symbolic link elsewhere (its real path decides), or by name on PATH.
        alias = os.path.join(folder, "alias-lean")
        os.symlink(pinned, alias)
        assert refusal(alias) is None
        saved = os.environ.get("PATH", "")
        os.environ["PATH"] = os.path.dirname(pinned)
        try:
            assert checked("lean") is None
            os.environ["PATH"] = os.path.dirname(copy)
            assert "not a Lean toolchain" in checked("lean")
            os.environ["PATH"] = folder
            assert checked("no-such-lean") is None
        finally:
            os.environ["PATH"] = saved
        # The Lean cache stands for the Lean it runs.
        saved = os.environ.pop("LEANFORTH_LEAN", None)
        try:
            assert "is not set" in checked(CACHE)
            os.environ["LEANFORTH_LEAN"] = pinned
            assert checked(CACHE) is None
            os.environ["LEANFORTH_LEAN"] = copy
            assert "not a Lean toolchain" in checked(CACHE)
        finally:
            os.environ.pop("LEANFORTH_LEAN")
            if saved is not None:
                os.environ["LEANFORTH_LEAN"] = saved
        assert "no file" in refusal(os.path.join(folder, "missing"))
        assert pinned_lean(pinned) == pinned
        # pinned_lean: a refused Lean stops the runner with the reason; $LEAN is
        # used when no name is given.
        saved = os.environ.get("LEAN")
        os.environ["LEAN"] = os.path.join(folder, "missing")
        try:
            pinned_lean()
            raise AssertionError("pinned_lean accepted a missing Lean")
        except SystemExit as stop:
            assert "refused" in str(stop) and "missing" in str(stop), stop
        finally:
            os.environ.pop("LEAN")
            if saved is not None:
                os.environ["LEAN"] = saved
    print("lean_pin.py: all tests passed")


def main(args):
    if not args:
        self_test()
        return 0
    if args == ["pinned"]:
        try:
            print(pinned_lean())
        except SystemExit as stop:
            print(stop, file=sys.stderr)
            return 1
        return 0
    if len(args) != 2 or args[0] != "check":
        print("usage: lean_pin.py [check LEAN | pinned]", file=sys.stderr)
        return 2
    reason = checked(args[1])
    if reason:
        print(f"lean_pin: refused: {reason}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
