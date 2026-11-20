#!/usr/bin/env bash
# Pre-tier check (2026-11-19).
# Every cheap whole-repository check in one keep-going pass, so that a 25-minute tier is
# never the first place a bookkeeping failure shows. Run in a checkout or worktree:
#   GFORTH=/abs/gforth [LEAN=/abs/lean] scripts/pre-tier.sh
# Exit 0 only if every check passed; prints one line per check.
set -u
G=${GFORTH:-$PWD/.tools/gforth/bin/gforth}
L=${LEAN:-$PWD/.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean}
fail=0
run() { local name=$1; shift; local out; out=$("$@" 2>&1 </dev/null); local rc=$?
  if [ $rc -eq 0 ]; then echo "ok    $name"; else echo "FAIL  $name (exit $rc)"; echo "$out" | tail -6 | sed 's/^/        /'; fail=1; fi; }
run "git tree clean"            bash -c 'test -z "$(git status --porcelain)"'
run "test classes"              python3 scripts/test-classes.py
run "duplicates"                python3 scripts/check-duplicates.py
run "new small copies"          python3 scripts/check-duplicates.py --new-words --base main
run "forth quality + review log" python3 scripts/check-forth-quality.py
run "library callers"           python3 scripts/check-lib-callers.py
run "outcome steps"             python3 scripts/check-outcome-steps.py
run "progress"                  python3 scripts/check-progress.py
run "agent sync"                python3 scripts/check-agent-sync.py
run "planted faults table"      python3 scripts/mutants.py --check   # also: no fault test names .tools/
run "layers"                    python3 scripts/check-layers.py --gforth "$G"
run "error catalogue"           env GFORTH="$G" python3 -c 'import importlib.util as u; s = u.spec_from_file_location("ca", "tests/author/check_author.py"); m = u.module_from_spec(s); s.loader.exec_module(m); m.check_catalogue()'
run "docs links"                make -s check-docs GFORTH="$G"
run "doc examples"              make -s check-doc-examples GFORTH="$G"
run "portable Forth"            make -s check-portable-forth GFORTH="$G"
run "Lean sources cited"        make -s check-lean-sources GFORTH="$G" LEAN="$L"
run "export list"               env GFORTH="$G" python3 tests/core/test_ndjson_emit.py
run "standalone libraries"      env GFORTH="$G" python3 tests/lib/test_standalone.py
run "no unguarded Lean fallback" bash -c '! grep -rn -E "\\$\\{LEAN:-lean\\}|os\\.environ\\.get\\(\"LEAN\", *\"lean\"\\)" tests scripts'
run "Python: undefined names"   python3 - <<'PY'
import ast, builtins, subprocess, sys
bad = 0
for f in subprocess.run(["git", "ls-files", "tests/*.py", "scripts/*.py"], capture_output=True, text=True).stdout.split():
    try:
        t = ast.parse(open(f).read())
    except SyntaxError as e:
        print("syntax", f, e); bad = 1; continue
    st = {n.id for n in ast.walk(t) if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store)}
    st |= {a.arg for a in ast.walk(t) if isinstance(a, ast.arg)}
    st |= {n.name for n in ast.walk(t) if isinstance(n, (ast.FunctionDef, ast.ClassDef, ast.AsyncFunctionDef))}
    for n in ast.walk(t):
        if isinstance(n, (ast.Import, ast.ImportFrom)):
            st |= {(a.asname or a.name).split(".")[0] for a in n.names}
        if isinstance(n, ast.ExceptHandler) and n.name: st.add(n.name)
        if isinstance(n, (ast.Global, ast.Nonlocal)): st |= set(n.names)
    und = {n.id for n in ast.walk(t) if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load)
           and n.id not in st and not hasattr(builtins, n.id) and n.id != "__file__"}
    # a function that both rebinds and calls a module-level function of the same name
    tops = {n.name for n in t.body if isinstance(n, ast.FunctionDef)}
    for fn in ast.walk(t):
        if isinstance(fn, ast.FunctionDef):
            stores = {n.id for n in ast.walk(fn) if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store)}
            calls = {n.func.id for n in ast.walk(fn) if isinstance(n, ast.Call) and isinstance(n.func, ast.Name)}
            for name in (stores & calls & tops) - {fn.name}:
                print("shadowed", f, fn.name, name); bad = 1
    names = [n.name for n in t.body if isinstance(n, ast.FunctionDef)]
    for name in {x for x in names if names.count(x) > 1}:
        print("defined twice", f, name); bad = 1
    if und: print("undefined", f, sorted(und)); bad = 1
sys.exit(bad)
PY
echo; [ $fail -eq 0 ] && echo "pre-tier: all checks passed" || echo "pre-tier: FAILED"
exit $fail
