#!/usr/bin/env python3
"""The Mathlib slice fixture: a small cut of Mathlib for the tests.

    python3 scripts/mathlib-slice.py [--export FILE] [--lake DIR] [--lean LEAN] [--cache DIR] [--build]

prints the folder that holds the fixture (docs/design/MATHLIB_FRONT.md section 6;
plan MF1): `slice.ndjson`, its manifest `slice.ndjson.manifest.json` (which names
the data's records SHA-256) and `slice.elab.ndjson`, its elaboration data. The
slice is the declarations of tests/front/mathlib-slice.roots and everything they
need (real numbers, add_zero, add_comm; about 4,906 declarations), cut from the
machine's Mathlib export by scripts/export-slice.py. The data is
scripts/export_elab.py run on that slice with Mathlib's own RAW records, which
scripts/export_elab.lean writes from pinned Lean importing all of Mathlib.

Each step is cached under the cache folder (--cache, $MATHLIB_SLICE_CACHE, else
the main checkout's .claude/work/mathlib-slice, shared by every worktree), keyed
by what it reads:
the slice by the export's size and time, the root list and the slicer; the RAW
by Lean's revision, export_elab.lean and Mathlib.olean's size and time; the data
by both and export_elab.py. A step is written in a temporary folder and renamed
into place, so a stopped run leaves no half fixture; when two runs fill the same
entry, the one that loses the rename uses the winner's folder. Without a cache the
steps take about 6 minutes (the slicer reads the whole 6 GB export) and 3 minutes
and 9 GB (Lean importing Mathlib); with it, nothing runs.

Those two cold steps run only when asked (--build or MATHLIB_SLICE_BUILD=1; review
data-bk L3): a test suite or a change tier never starts a 9 GB Mathlib import by
itself. Without the opt-in, a cold slice or RAW entry is SKIPPED, NOT A PASS: the
script says so and exits 3, and tests/front/check_mathlib_slice.py
(make reference-mathlib-slice) exits 3 too, so a tier (scripts/tested-tree.py)
counts the target as failed and records nothing for the tree. Fill the cache once,
by itself: MATHLIB_SLICE_BUILD=1 make reference-mathlib-slice. The data step (a
few seconds) always runs when its entry is missing.

The result is checked against tests/front/mathlib-slice.sha256: the slice's
SHA-256 and the data's records SHA-256. Another Mathlib, slicer or exporter gives
others: the script then stops (exit 1) and names both, and a commit that changes
the roots or the tools updates that file.

Inputs, each an option or else found: the export (--export, $MATHLIB_EXPORT, else
mathlib/mathlib.ndjson under $LEANFORTH_TOOLS, this checkout's .tools or the main
checkout's), Mathlib's .lake folder (--lake, $MATHLIB_LAKE, else
mathlib/mathlib4/.lake beside the export), the pinned Lean binary (--lean,
$LEANFORTH_LEAN, else the toolchain under the same tools folder; never an elan
proxy: scripts/lean_pin.py judges it). Reads them only; writes only the cache.
Exit 0 with the folder printed; 1 when a step or the check fails; 2 for a missing
input; 3 skipped (a cold step without the opt-in). Never part of a run of
LeanForth on all of Mathlib.
"""
import argparse
import hashlib
import json
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
ROOTS = ROOT / "tests/front/mathlib-slice.roots"
EXPECTED = ROOT / "tests/front/mathlib-slice.sha256"
TOOLCHAIN = "elan/toolchains/leanprover--lean4---v4.35.0/bin/lean"


def checkout():
    """The main checkout (a worktree's common git folder's parent), else this one."""
    out = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "--path-format=absolute",
                          "--git-common-dir"], capture_output=True, text=True)
    common = pathlib.Path(out.stdout.strip()) if out.returncode == 0 else None
    return common.parent if common and common.name == ".git" else ROOT


def tool_dirs():
    dirs = [os.environ.get("LEANFORTH_TOOLS"), ROOT / ".tools", checkout() / ".tools"]
    return [pathlib.Path(d) for d in dirs if d]


def find(option, env, relative):
    if option or os.environ.get(env):
        return pathlib.Path(option or os.environ[env])
    for d in tool_dirs():
        if (d / relative).exists():
            return d / relative
    return None


def sha_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def stamp(path):
    st = os.stat(path)
    return [st.st_size, st.st_mtime_ns]


def key(*parts):
    return hashlib.sha256(json.dumps(parts).encode()).hexdigest()[:24]


def roots():
    lines = ROOTS.read_text().splitlines()
    return [line.strip() for line in lines if line.strip() and not line.startswith("#")]


def run(argv, out=None, env=None):
    with open(out, "wb") if out else open(os.devnull, "wb") as sink:
        done = subprocess.run(argv, stdout=sink, stderr=subprocess.PIPE, env=env)
    if done.returncode != 0:
        sys.stderr.write(done.stderr.decode(errors="replace"))
        raise SystemExit(f"mathlib-slice: {argv[0]} {argv[1]} exited {done.returncode}")


SKIPPED = 3
BUILD_HINT = "MATHLIB_SLICE_BUILD=1 make reference-mathlib-slice"


class Skipped(Exception):
    """A cold step that may not run without the opt-in."""


def cached(cache, name, build, allowed=True):
    """CACHE/NAME, made by BUILD(folder) in a temporary folder first; Skipped when it
    is missing and not ALLOWED. A run that loses the rename to another run filling
    the same entry keeps the other's folder."""
    final = cache / name
    if not final.exists():
        if not allowed:
            raise Skipped(name)
        cache.mkdir(parents=True, exist_ok=True)
        work = pathlib.Path(tempfile.mkdtemp(prefix=name + ".", dir=cache))
        try:
            build(work)
            try:
                work.rename(final)
            except OSError:
                if not final.is_dir():
                    raise
        finally:
            if work.exists():
                shutil.rmtree(work)
    return final


def slice_step(export, folder):
    out = folder / "slice.ndjson"
    run([sys.executable, "-I", str(ROOT / "scripts/export-slice.py"), str(export)] + roots(), out)
    run([sys.executable, str(ROOT / "scripts/export_manifest.py"), str(out)])


def lean_path(lake):
    paths = [lake / "build/lib/lean"]
    paths += [p / ".lake/build/lib/lean" for p in sorted((lake / "packages").iterdir())]
    return ":".join(str(p) for p in paths)


def raw_step(lean, lake, folder):
    run([sys.executable, str(ROOT / "scripts/lean_pin.py"), "check", str(lean)])
    env = dict(os.environ, LEAN_PATH=lean_path(lake),
               PATH=f"{lean.parent}:{os.environ.get('PATH', '')}")
    run([str(lean), "-DwarningAsError=true", "--run", str(ROOT / "scripts/export_elab.lean"),
         "Mathlib"], folder / "mathlib.raw", env)


def data_step(sliced, raw, folder):
    for name in ("slice.ndjson", "slice.ndjson.manifest.json"):
        shutil.copyfile(sliced / name, folder / name)
    run([sys.executable, str(ROOT / "scripts/export_elab.py"), str(raw / "mathlib.raw"),
         str(folder / "slice.ndjson"), str(folder / "slice.elab.ndjson"), "--bind"])


def records_sha(data):
    with open(data) as f:
        return json.loads(f.readline())["elab_data"]["records_sha256"]


def check(fixture):
    want = dict(line.split() for line in EXPECTED.read_text().splitlines() if line.strip())
    have = {"slice": sha_file(fixture / "slice.ndjson"),
            "elab_records": records_sha(fixture / "slice.elab.ndjson")}
    wrong = [f"{k}: {have[k]}, expected {want.get(k)}" for k in have if have[k] != want.get(k)]
    if wrong:
        raise SystemExit("mathlib-slice: the fixture differs from " +
                         f"{EXPECTED.relative_to(ROOT)}: " + "; ".join(wrong))


def main(argv):
    ap = argparse.ArgumentParser(description="The Mathlib slice fixture (plan MF1).")
    ap.add_argument("--export", help="Mathlib's lean4export file (read only)")
    ap.add_argument("--lake", help="Mathlib's .lake folder, for its .olean files (read only)")
    ap.add_argument("--lean", help="the pinned Lean 4.35.0 binary")
    ap.add_argument("--cache", help="the cache folder (default: the main checkout's)")
    ap.add_argument("--build", action="store_true",
                    help="run the cold steps (slicing the export; Lean importing Mathlib, "
                         "9 GB) when their cache entry is missing; also MATHLIB_SLICE_BUILD=1")
    args = ap.parse_args(argv)
    build = args.build or os.environ.get("MATHLIB_SLICE_BUILD") == "1"
    export = find(args.export, "MATHLIB_EXPORT", "mathlib/mathlib.ndjson")
    if export is None or not export.is_file():
        sys.stderr.write("mathlib-slice: no Mathlib export (--export, $MATHLIB_EXPORT or "
                         ".tools/mathlib/mathlib.ndjson)\n")
        return 2
    lake = pathlib.Path(args.lake or os.environ.get("MATHLIB_LAKE") or
                        export.parent / "mathlib4/.lake")
    lean = find(args.lean, "LEANFORTH_LEAN", TOOLCHAIN)
    if not (lake / "build/lib/lean/Mathlib.olean").is_file() or lean is None:
        sys.stderr.write(f"mathlib-slice: no Mathlib build at {lake} or no pinned Lean\n")
        return 2
    cache = pathlib.Path(args.cache or os.environ.get("MATHLIB_SLICE_CACHE") or
                         checkout() / ".claude/work/mathlib-slice")
    scripts = [sha_file(ROOT / "scripts" / s) for s in ("export-slice.py", "export_manifest.py")]
    k_slice = key(stamp(export), roots(), scripts)
    githash = subprocess.run([str(lean), "--githash"], capture_output=True, text=True).stdout
    k_raw = key(githash.strip(), sha_file(ROOT / "scripts/export_elab.lean"),
                stamp(lake / "build/lib/lean/Mathlib.olean"))
    try:
        sliced = cached(cache, "slice-" + k_slice, lambda f: slice_step(export, f), build)
        raw = cached(cache, "raw-" + k_raw, lambda f: raw_step(lean, lake, f), build)
    except Skipped as missing:
        sys.stderr.write(f"mathlib-slice: SKIPPED, NOT A PASS: {cache}/{missing} is not cached, "
                         "and filling it slices the 6 GB export or imports all of Mathlib "
                         f"(9 GB); fill the cache once, by itself: {BUILD_HINT}\n")
        return SKIPPED
    k_data = key(k_slice, k_raw, sha_file(ROOT / "scripts/export_elab.py"))
    fixture = cached(cache, "data-" + k_data, lambda f: data_step(sliced, raw, f))
    check(fixture)
    print(fixture)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
