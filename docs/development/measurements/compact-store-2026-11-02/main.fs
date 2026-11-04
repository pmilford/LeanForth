\ Prototype driver (ADR 0016, measurement code). Usage, from this folder:
\   gforth-fast main.fs -e 's" FILE" full bye'      load, statistics, lookups, walks
\   gforth-fast main.fs -e 's" FILE" dump-file bye'      load, then re-emit names/levels/exprs
\   gforth-fast main.fs -e '100000000 s" FILE" trees bye'   walks without a cache, capped
require ./measure.fs
: phase-load ( c-addr u -- )
  start load-file outcome-ok <> abort" load failed" s" load" lap
  start index-decls s" index-decls" lap ;
: full ( c-addr u -- ) phase-load stats lookup-text lookup-ids walk-dense
  vset-init walk-hashed proof-only ;
: dump-file ( c-addr u -- ) phase-load emit-all ;
: trees ( cap c-addr u -- ) phase-load walk-tree ;
: .native ( -- ) ." u32-native=" u32-native . cr ;
