"""The five demos of docs/user/DEMOS.md against pinned Lean 4.35.0 and LeanForth (make check).

Usage: python3 tests/demos/test_demos.py [--write]   (from the repository root;
LEAN, LEANEXPORT and GFORTH name the toolchains, as the Makefile sets them)

For each demo (tests/demos/DemoX.lean):
1. pinned Lean compiles it, and scripts/export.sh exports the theorem;
2. `leanforth check` accepts the export (exit 0), and rejects its wrong twin
   (tests/demos/wrong_twin.py: the same proof under another statement) with
   exit 1;
3. `leanforth print` shows the statement; its Lean form must equal what pinned
   Lean's #check prints for the theorem, character for character;
4. everything the user page quotes is written to tests/demos/demos.golden and
   must equal it (--write regenerates the file; review the diff).
Then docs/user/DEMOS.md must equal what build_page.py makes of the golden file.
Finite evidence about these five statements; it never accepts a theorem.
"""
import concurrent.futures
import os
import pathlib
import subprocess
import sys
import tempfile

HERE = pathlib.Path("tests/demos")
GOLDEN = HERE / "demos.golden"
TEST_LIMIT = int(os.environ.get("TEST_TIMEOUT", "1800"))
LEAN = os.environ.get("LEAN", ".tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean")
sys.path.insert(0, str(HERE))
from build_page import DEMOS, page  # noqa: E402


class Mismatch(Exception):
    pass


def run(command, **extra):
    env = dict(os.environ)
    env.update(extra.pop("env", {}))
    done = subprocess.run(command, capture_output=True, text=True, timeout=TEST_LIMIT, env=env, **extra)
    return done.returncode, done.stdout + done.stderr


def lean_check(demo, work):
    """Pinned Lean's #check line for the demo's theorem."""
    code, text = run([LEAN, "-DwarningAsError=true", "-o", f"{work}/{demo['module']}.olean",
                      str(HERE / f"{demo['module']}.lean")])
    if code != 0:
        raise Mismatch(f"{demo['module']}: Lean failed:\n{text}")
    probe = pathlib.Path(work) / f"Probe_{demo['module']}.lean"
    probe.write_text(f"import {demo['module']}\n#check @{demo['theorem']}\n", encoding="utf-8")
    code, text = run([LEAN, "-DwarningAsError=true", str(probe)], env={"LEAN_PATH": work})
    if code != 0:
        raise Mismatch(f"{demo['module']}: Lean's #check failed:\n{text}")
    return text.strip()


def export(demo, work):
    path = f"{work}/{demo['id']}.ndjson"
    code, text = run(["bash", "scripts/export.sh", path, demo["module"], "--", demo["theorem"]],
                     env={"LEAN_PATH": work, "LEAN": LEAN})
    if code != 0:
        raise Mismatch(f"{demo['module']}: export failed:\n{text}")
    return path


def leanforth(*arguments):
    return run(["bash", "bin/leanforth", *arguments])


def header(text):
    """The statement and verdict lines of leanforth print: up to the checker's log line, the
    export's file name (it names a temporary folder) left out."""
    kept = []
    for line in text.splitlines():
        if line.startswith("  Input:"):
            continue
        kept.append(line)
        if line.startswith("  Checker log:"):
            break
    return "\n".join(kept)


def verdict(text):
    lines = text.rstrip("\n").splitlines()
    return "\n".join(lines[-2:])


def rejection(text, demo):
    """The theorem's rejection line and the reason under it."""
    lines = text.splitlines()
    for number, line in enumerate(lines):
        if line == f"{demo['theorem']}: rejected":
            return "\n".join(lines[number:number + 2])
    raise Mismatch(f"{demo['id']}: the wrong twin was not rejected by name:\n{text[-800:]}")


def prepared(demo, work):
    """The demo's own folder, made: Lean's #check line, the export and its wrong twin. Each
    demo gets its own folder: the Lean cache sizes every file on LEAN_PATH, and a demo
    running beside it would otherwise add and remove files there."""
    work = os.path.join(work, demo["id"])
    os.makedirs(work)
    lean = lean_check(demo, work)
    path = export(demo, work)
    twin = f"{work}/{demo['id']}-wrong.ndjson"
    run([sys.executable, str(HERE / "wrong_twin.py"), path, twin])
    return {"lean": lean, "export": path, "twin": twin}


def checks(demo, made):
    """The demo's three LeanForth runs, (name, arguments, cost): check, the wrong twin's
    check and print. Each only reads its files, so all of them can run side by side;
    the cost (print checks with the log on: about 1.6 times check) orders them."""
    size = os.path.getsize(made["export"])
    return [("check", ["check", made["export"]], size),
            ("wrong", ["check", "--no-manifest", made["twin"]], size),
            ("print", ["print", "--name", demo["theorem"], made["export"]], 2 * size)]


def section(demo, made, done):
    """The demo's part of the golden file from its runs (done: name -> (code, text))."""
    lean, (code, checked) = made["lean"], done["check"]
    if code != 0:
        raise Mismatch(f"{demo['id']}: leanforth check exit {code}:\n{checked[-800:]}")
    wrong_code, wrong = done["wrong"]
    if wrong_code != 1:
        raise Mismatch(f"{demo['id']}: the wrong twin gave exit {wrong_code}, not 1:\n{wrong[-800:]}")
    code, printed = done["print"]
    if code != 0:
        raise Mismatch(f"{demo['id']}: leanforth print exit {code}:\n{printed[-800:]}")
    body = header(printed)
    expected = f"{demo['theorem']} : " + next(
        line for line in body.splitlines() if line.startswith("  Statement in Lean:")
    ).split(":", 1)[1].strip()
    if lean != expected:
        raise Mismatch(f"{demo['id']}: Lean's #check and LeanForth's Lean form differ:\n"
                       f"  Lean:     {lean}\n  LeanForth: {expected}")
    return (f"== {demo['id']}\n-- lean\n{lean}\n-- check\n{verdict(checked)}\n"
            f"-- wrong twin\n{wrong_code}\n{rejection(wrong, demo)}\n-- print\n{body}\n")


SIDE_BY_SIDE = 4   # runs at once, as before: Lean's, then LeanForth's


def all_sections(work):
    """Every demo's section, in DEMOS order. The demos are independent (own module, export
    and twin files), so Lean's runs for them go side by side, then all fifteen LeanForth
    runs, the costliest first, so that no demo's three runs wait for one another."""
    with concurrent.futures.ThreadPoolExecutor(max_workers=SIDE_BY_SIDE) as pool:
        made = list(pool.map(lambda demo: prepared(demo, work), DEMOS))
        runs = sorted(((demo["id"], name, arguments, cost) for demo, m in zip(DEMOS, made)
                       for name, arguments, cost in checks(demo, m)), key=lambda r: -r[3])
        started = {(i, name): pool.submit(leanforth, *arguments) for i, name, arguments, _ in runs}
        return [section(demo, m, {name: started[demo["id"], name].result()
                                  for name in ("check", "wrong", "print")})
                for demo, m in zip(DEMOS, made)]


def main(write):
    with tempfile.TemporaryDirectory() as work:
        text = "".join(all_sections(work))
    if write:
        GOLDEN.write_text(text, encoding="utf-8")
        pathlib.Path("docs/user/DEMOS.md").write_text(page(text), encoding="utf-8")
        print(f"wrote {GOLDEN} and docs/user/DEMOS.md")
        return 0
    if GOLDEN.read_text(encoding="utf-8") != text:
        raise Mismatch(f"{GOLDEN} differs from the live run (python3 {sys.argv[0]} --write, then review)")
    if pathlib.Path("docs/user/DEMOS.md").read_text(encoding="utf-8") != page(text):
        raise Mismatch("docs/user/DEMOS.md differs from build_page.py's page")
    print(f"{len(DEMOS)} demos: accepted, wrong twins rejected, Lean forms equal Lean's #check, "
          f"golden and page as expected")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main("--write" in sys.argv[1:]))
    except Mismatch as error:
        print(error)
        sys.exit(1)
