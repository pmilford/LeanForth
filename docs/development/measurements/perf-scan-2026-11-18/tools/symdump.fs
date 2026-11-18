\ PERF1 profiler aid (not part of the repository): after main.fs is loaded,
\ write every colon definition's threaded-code start and name, one per line
\ ("hexaddr kind name"), to the file named by $PROF_SYMS, so the ptrace
\ sampler (sample.py) can map return-stack addresses to Forth words.
\ kind: c colon, d does-word body, o other.
0 wordlist-link constant sym-wl-off
0 value sym-fid
create sym-buf 256 allot
: sym-hex ( u -- c-addr u ) base @ >r hex 0 <# #s #> r> base ! ;
: sym-kind ( xt -- c )
  >code-address dup docol: = if drop [char] c exit then
  dodoes: = if [char] d else [char] o then ;
: sym-line ( nt -- )
  dup name>interpret dup >body sym-hex sym-buf place
  s"  " sym-buf +place  sym-kind sym-buf count + c! 1 sym-buf c+!
  s"  " sym-buf +place  name>string sym-buf +place
  sym-buf count sym-fid write-line throw ;
: sym-one ( nt -- true ) sym-line true ;
: sym-walk ( -- )
  voclink @ begin dup while
    dup sym-wl-off - ['] sym-one swap traverse-wordlist @ repeat drop ;
: sym-dump ( -- )
  s" PROF_SYMS" getenv dup 0= if 2drop exit then
  w/o create-file throw to sym-fid  sym-walk
  s" RP0 " sym-buf place rp0 @ sym-hex sym-buf +place
  sym-buf count sym-fid write-line throw
  s" SP0 " sym-buf place sp0 @ sym-hex sym-buf +place
  sym-buf count sym-fid write-line throw
  sym-fid close-file throw ;
sym-dump
