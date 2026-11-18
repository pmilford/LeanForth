# perf-scan: extra counters for a --jobs 1 kernel run (exec'd by patch.py; scratch copy only)
PATCHES += [
    ('src/lib/htab.fs', ": htab-find ( key h htab -- n true | i false )\n",
     ": htab-find ( key h htab -- n true | i false )\n  10 cnt+\n"),
    ('src/lib/htab.fs', ": htab-same ( n key htab -- flag ) dup htab-hooks @ hook-same @ execute ;",
     ": htab-same ( n key htab -- flag ) 11 cnt+ dup htab-hooks @ hook-same @ execute ;"),
    ('src/kernel/environment.fs', ": lf-env-current ( -- env true | false ) lf-env dup lf-env-valid? ?keep ;",
     ": lf-env-current ( -- env true | false ) 12 cnt+ lf-env dup lf-env-valid? ?keep ;"),
    ('src/kernel/replace-memo.fs', "  r> lf-rmemo-entry memo-find dup if @ true then ;",
     "  r> lf-rmemo-entry memo-find dup if @ true 14 cnt+ then 13 cnt+ ;"),
    ('src/kernel/caches.fs', ": lf-cache-count ( flag cache -- flag )\n",
     ": lf-cache-count ( flag cache -- flag )\n  2dup 0 lf-cache-nth - /lf-cache / 2* 20 + swap 0= - cnt+\n"),
    ('src/core/terms.fs', ": lf-term-cons ( tag first second -- index true | false )\n",
     ": lf-term-cons ( tag first second -- index true | false )\n  15 cnt+\n"),
]
