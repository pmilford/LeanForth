\ The declarations a natural LeanForth text makes, as the elaborator
\ (src/front/elab-decl.fs) builds them: for each, "NAME type SX" and
\ "NAME value SX", SX the S-expression of tests/front/s1-now.lean's
\ printer ((app F A), (lam T B), (pi T B), #i, Name.{levels}, Sort l, a
\ literal's value), so tests/front/check_elab.py compares them with pinned
\ Lean's node for node. The library and its elaboration data are the S1
\ slice's (run mode, as the command line binds them).
\ Usage: gforth tests/front/elab-dump.fs -e 's" FILE.lf" elab-dump bye'
require ../../src/main.fs
decimal

: dump-lib ( -- c-addr u ) s" tests/front/s1-slice.ndjson" ;
: dump-data ( -- c-addr u ) s" tests/front/s1-slice.elab.ndjson" ;
: dump-must ( outcome -- ) ok? 0= abort" elab-dump: a loading step failed" ;
: .nm ( name -- ) dup lf-name-prefix@ ?dup if recurse ." ." then lf-name-text type ;
: .lv ( level -- )
  0 swap begin dup lf-level-tag@ lf-level-tag-succ = while lf-level-first@ swap 1+ swap repeat
  lf-level-tag@ lf-level-tag-zero = if 0 .r else drop ." ?l" then ;
: .levels ( slot -- )
  lf-cref-pairs 0 ?do i if ." ," then dup i lf-cref-pair@ drop .lv loop drop ;
: .const ( t -- ) lf-term-first@ lf-cref-slot dup lf-cref-name@ drop .nm ." .{" .levels ." }" ;
defer .t
: .pair ( t c-addr u -- ) ." (" type space dup lf-term-first@ .t space lf-term-second@ .t ." )" ;
:noname ( t -- )
  dup lf-term-tag@ lf-tag-symbolic-sort = if ." Sort " lf-term-first@ .lv exit then
  dup lf-lit-leaf? if lf-lit-cell 0 .r exit then
  dup lf-term-tag@ case
    lf-tag-app of s" app" .pair endof  lf-tag-lam of s" lam" .pair endof
    lf-tag-pi of s" pi" .pair endof  lf-tag-bvar of ." #" lf-term-first@ 0 .r endof
    lf-tag-constant of .const endof  >r drop ." ??" r> endcase ; is .t
: .decl ( decl -- )
  dup lf-fdecl-name @ .nm ."  type " dup lf-fdecl-type @ .t cr
  dup lf-fdecl-name @ .nm ."  value " lf-fdecl-value @ .t cr ;
: dump-own ( i -- ) dup lfa-library? if drop else lf-author-decl .decl then ;
: elab-dump ( c-addr u -- )
  dump-lib true lfc-library-open dump-must
  dump-data ck-stage ck-stage stage-manifest manifest-digest elab-read dump-must
  lfc-rooms dump-must lf-author-begin lf-author-file
  dup ok? 0= if ." stopped: " lf-author-error. cr drop exit then drop
  lf-author-count 0 ?do i dump-own loop ;
