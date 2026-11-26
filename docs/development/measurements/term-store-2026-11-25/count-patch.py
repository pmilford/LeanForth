#!/usr/bin/env python3
"""Insert entry counters into a scratch copy of src/ (term-store design, 2026-11-25)."""
import re, sys, pathlib
root = pathlib.Path(sys.argv[1])
C = root / "src/lib/counters.fs"
# (file, word, counter)
SITES = [
  ("src/core/terms.fs", "lf-term-tag@", "c-tag"),
  ("src/core/terms.fs", "lf-term-first@", "c-first"),
  ("src/core/terms.fs", "lf-term-second@", "c-second"),
  ("src/core/terms.fs", "lf-term-data-word", "c-data"),
  ("src/core/terms.fs", "lf-term-valid?", "c-valid"),
  ("src/core/terms.fs", "lf-term-identity", "c-ident"),
  ("src/core/terms.fs", "lf-tin-record", "c-tinrec"),
  ("src/core/terms.fs", "lf-tin-leaf", "c-tinleaf"),
  ("src/core/terms.fs", "lf-term-cons", "c-cons"),
  ("src/core/terms.fs", "lf-tin-given", "c-tingiven"),
  ("src/core/terms.fs", "lf-term-find", "c-find"),
  ("src/core/terms.fs", "lf-term-new", "c-new"),
  ("src/kernel/mixed-open.fs", "lf-open-run", "c-orun"),
  ("src/kernel/mixed-open.fs", "lf-open-visit", "c-ovisit"),
  ("src/kernel/mixed-open.fs", "lf-open-pair", "c-opair"),
  ("src/kernel/mixed-open.fs", "lf-open-again", "c-oagain"),
  ("src/kernel/mixed-open.fs", "lf-open-binary", "c-odesc"),
  ("src/kernel/mixed-open.fs", "lf-open-put", "c-oput"),
  ("src/kernel/mixed-open.fs", "lf-open-leaf", "c-oleaf"),
  ("src/lib/frame.fs", "frame-enter", "c-fenter"),
  ("src/lib/htab.fs", "htab-find", "c-hfind"),
  ("src/kernel/replace-memo.fs", "lf-rmemo@", "c-rm@"),
  ("src/kernel/replace-memo.fs", "lf-rmemo!", "c-rm!"),
  ("src/kernel/mixed-level-substitute.fs", "lf-mixed-level-substitute", "c-mls"),
  ("src/core/constant-term-boundary.fs", "lf-cterm-check", "c-audit"),
]
names = sorted({s[2] for s in SITES} | {"c-oclosed"})
C.write_text("get-current forth-wordlist set-current\n" +
  "".join(f"variable {n}  0 {n} !\n" for n in names) +
  ": .counters ( -- ) cr\n" +
  "".join(f'  ." {n} " {n} @ . cr\n' for n in names) + "  ;\nset-current\n")
done = set()
for f, w, c in SITES:
    p = root / f
    t = p.read_text()
    pat = re.compile(r"^(: " + re.escape(w) + r"\s+\([^)]*\))", re.M)
    t2, n = pat.subn(lambda m: m.group(1) + f" 1 {c} +!", t, count=1)
    if n != 1:
        sys.exit(f"not found: {w} in {f}")
    if f not in done:
        t2 = f"require {C}\n" + t2
        done.add(f)
    p.write_text(t2)
# closed roots: the root's loose range is 0 when the pass starts
p = root / "src/kernel/mixed-open.fs"
t = p.read_text()
t = t.replace(": lf-open-run ( node subst n mode -- node' outcome ) 1 c-orun +!",
  ": lf-open-run ( node subst n mode -- node' outcome ) 1 c-orun +!\n"
  "  3 pick lf-term-data-word lf-data-loose 0= if 1 c-oclosed +! then", 1)
p.write_text(t)
p = root / "src/cli/leanforth.fs"
t = p.read_text()
t2 = t.replace(": cli-leave ( code -- ) 100 + (bye) ;",
  ": cli-leave ( code -- ) ['] .counters stderr outfile-execute 100 + (bye) ;", 1)
assert t2 != t
p.write_text(f"require {C}\n" + t2)
print("patched", len(SITES), "sites")
