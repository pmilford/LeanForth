\ The symbol table for the sampling profiler (scripts/profile-sample.py;
\ docs/development/PROFILING.md, "Where a check spends its time"): loaded
\ after src/main.fs, it writes every word's threaded-code start, kind, name
\ and source position, one a line ("hexaddr kind name file:line"), to the
\ file $PROF_SYMS names, then the return stack's and the data stack's
\ bottoms (RP0, SP0), so that the sampler can map the return addresses it
\ reads from a running check to the colon definitions that hold them and
\ class each by its file. kind: c a colon definition, d a DOES> word's body,
\ o other. Nothing is written when PROF_SYMS is not set.
\ A development tool, not part of the product: Gforth 1.0 only (voclink,
\ traverse-wordlist, name>view, loadfilename#>str); first written as the
\ perf-scan's tools/symdump.fs (agent PERF1, 2026-11-12; kept in
\ docs/development/measurements/perf-scan-2026-11-18/tools/), with the
\ source position added 2026-11-25.
0 wordlist-link constant sym-wl-off
0 value sym-fid
create sym-c 1 allot
: sym-hex ( u -- c-addr u ) base @ >r hex 0 <# #s #> r> base ! ;
: sym-dec ( u -- c-addr u ) base @ >r decimal 0 <# #s #> r> base ! ;
: sym-kind ( xt -- c )
  >code-address dup docol: = if drop [char] c exit then
  dodoes: = if [char] d else [char] o then ;
\ Each piece goes straight to the file: a line has no length limit.
: sym-type ( c-addr u -- ) sym-fid write-file throw ;
: sym-char ( c -- ) sym-c c! sym-c 1 sym-type ;
: sym-end ( -- ) s" " sym-fid write-line throw ;
: sym-where ( nt -- )
  name>view dup view>filename# loadfilename#>str sym-type
  [char] : sym-char view>line sym-dec sym-type ;
: sym-line ( nt -- )
  dup name>interpret dup >body sym-hex sym-type
  bl sym-char sym-kind sym-char bl sym-char
  dup name>string sym-type bl sym-char sym-where sym-end ;
: sym-one ( nt -- true ) sym-line true ;
: sym-walk ( -- )
  voclink @ begin dup while
    dup sym-wl-off - ['] sym-one swap traverse-wordlist @ repeat drop ;
: sym-stack ( c-addr u addr -- ) >r sym-type r> @ sym-hex sym-type sym-end ;
: sym-dump ( -- )
  s" PROF_SYMS" getenv dup 0= if 2drop exit then
  w/o create-file throw to sym-fid  sym-walk
  s" RP0 " rp0 sym-stack  s" SP0 " sp0 sym-stack  sym-fid close-file throw ;
sym-dump
